use std::cell::RefCell;
use std::collections::VecDeque;
use crate::mem::{Memory, MemoryError};

use bitmatch::bitmatch;
use thiserror::Error;
use crate::cpu::CPUError::{InvalidValueSize, MissingCapabilities, UnsupportedCapabilities};

mod tests;

macro_rules! expect_set {
    ($x:expr, $y:expr, $err:expr) => {
        if $x & $y != $y {
            return Err($err.into());
        }
    }
}

pub const CP1_FI: u64 = 1 << 0;
pub const CP1_SAF: u64 = 1 << 1;
pub const CP1_INT: u64 = 1 << 2;
pub const CP1_BYTE: u64 = 1 << 3;
pub const CP1_COND: u64 = 1 << 4;
pub const CP1_REX: u64 = 1 << 5;
pub const CP1_CI: u64 = 1 << 6;
pub const CP1_ASP: u64 = 1 << 7;
pub const CP1_MO2: u64 = 1 << 13;
pub const CP1_DW: u64 = 1 << 14;
pub const CP1_QW: u64 = 1 << 15;
pub const CP1_DWAS: u64 = 1 << 16;
pub const CP1_QWAS: u64 = 1 << 32;

pub const CP2_EXOP: u64 = 1 << 0;
pub const CP2_MO1: u64 = 1 << 1;
pub const CP2_PM: u64 = 1 << 2;
pub const CP2_MD: u64 = 1 << 3;

pub const FT_VON: u64 = 1 << 0;
pub const FT_UMA: u64 = 1 << 1;
pub const FT_CC: u64 = 1 << 2;
pub const FT_MMAI: u64 = 1 << 3;

pub const ALL_CP1: u64 = 0x1_0001_E0FF;
pub const ALL_CP2: u64 = 0xF;
pub const ALL_FT: u64 = 0xF;

pub const MAX_INSTRUCTION_SIZE: usize = 16;

const CACHE_LINE_SIZE: usize = 0;

type Result<T> = std::result::Result<T, CPUError>;

#[derive(Error, Debug)]
pub enum CPUError {
    #[error(transparent)]
    Memory(#[from] MemoryError),
    #[error("CPU cannot have capabilities or features unsupported by the simulator: {0}")]
    UnsupportedCapabilities(String),
    #[error("CPU is missing required capabilities or features: {0}")]
    MissingCapabilities(String),
    #[error("Invalid value for size: {0}")]
    InvalidValueSize(u8)
}

pub struct CPUInfo {
    pub cpuid_1: u64,
    pub cpuid_2: u64,
    pub feat: u64,
    pub force_allow_single_byte_nop: bool,
    _private: ()
}

impl CPUInfo {
    pub fn new(cpuid_1: u64, cpuid_2: u64, feat: u64, force_allow_single_byte_nop: bool) -> Result<CPUInfo> {
        expect_set!(ALL_CP1, cpuid_1, UnsupportedCapabilities(format!("CP1 has unknown bits set: {}", (ALL_CP1 & cpuid_1) ^ cpuid_1)));
        expect_set!(ALL_CP2, cpuid_2, UnsupportedCapabilities(format!("CP2 has unknown bits set: {}", (ALL_CP2 & cpuid_2) ^ cpuid_2)));
        expect_set!(ALL_FT, feat, UnsupportedCapabilities(format!("FT has unknown bits set: {}", (ALL_FT & feat) ^ feat)));

        if cpuid_1 & CP1_INT != 0 {
            expect_set!(cpuid_1, CP1_SAF, MissingCapabilities("Interrupt extension requires Stack and Functions extension".to_string()));
            expect_set!(feat, FT_VON, MissingCapabilities("Interrupt extension requires Von Neumann feature".to_string()));
        }

        if cpuid_1 & CP1_ASP != 0 {
            expect_set!(cpuid_1, CP1_SAF, MissingCapabilities("Arbitrary Stack Pointer extension requires Stack and Functions extension".to_string()));
        }

        if cpuid_1 & CP1_DWAS != 0 {
            expect_set!(cpuid_1, CP1_DW, MissingCapabilities("Double Word Address Space extension requires Double Word extension".to_string()));
        }

        if cpuid_1 & CP1_QWAS != 0 {
            expect_set!(cpuid_1, CP1_QW, MissingCapabilities("Quad Word Address Space extension requires Quad Word extension".to_string()));
        }

        if cpuid_2 & CP2_PM != 0 {
            expect_set!(cpuid_1, CP1_INT, MissingCapabilities("Privileged Mode extension requires Interrupt extension".to_string()));
        }

        if cpuid_2 & CP2_MD != 0 {
            expect_set!(cpuid_2, CP2_EXOP, MissingCapabilities("Multiply Divide extension requires Expanded Opcodes extension".to_string()));
        }

        if feat & FT_MMAI != 0 && cpuid_1 & CP1_MO2 == 0 && cpuid_2 & CP2_MO1 == 0 {
            println!("INFO: Multiple Memory Access Instructions feature is useless without Memory Operands 1 or Memory Operands 2 extension");
        }

        Ok(CPUInfo {
            cpuid_1,
            cpuid_2,
            feat,
            force_allow_single_byte_nop,
            _private: ()
        })
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum ValueSize {
    HALF,
    WORD,
    DOUBLE,
    QUAD
}

impl TryFrom<u8> for ValueSize {
    type Error = CPUError;

    fn try_from(value: u8) -> Result<Self> {
        match value {
            0 => Ok(ValueSize::HALF),
            1 => Ok(ValueSize::WORD),
            2 => Ok(ValueSize::DOUBLE),
            3 => Ok(ValueSize::QUAD),
            x => Err(InvalidValueSize(x))
        }
    }
}

impl ValueSize {
    #[inline]
    fn from_u8(num: u8) -> ValueSize {
        ValueSize::try_from(num).unwrap()
    }

    #[inline]
    pub const fn mask(&self) -> u64 {
        match self {
            ValueSize::HALF => 0xFF,
            ValueSize::WORD => 0xFFFF,
            ValueSize::DOUBLE => 0xFFFF_FFFF,
            ValueSize::QUAD => u64::MAX
        }
    }

    #[inline]
    pub const fn inverse_mask(&self) -> u64 {
        match self {
            ValueSize::HALF => !0xFFu64,
            ValueSize::WORD => !0xFFFFu64,
            ValueSize::DOUBLE => !0xFFFF_FFFFu64,
            ValueSize::QUAD => 0
        }
    }

    #[inline]
    pub const fn is_supported(&self, cpu_info: &CPUInfo) -> bool {
        match self {
            ValueSize::HALF => cpu_info.cpuid_1 & CP1_BYTE != 0,
            ValueSize::WORD => true,
            ValueSize::DOUBLE => cpu_info.cpuid_1 & CP1_DW != 0,
            ValueSize::QUAD => cpu_info.cpuid_1 & CP1_QW != 0
        }
    }

    #[inline]
    pub const fn num_bytes(&self) -> usize {
        match self {
            ValueSize::HALF => 1,
            ValueSize::WORD => 2,
            ValueSize::DOUBLE => 4,
            ValueSize::QUAD => 8
        }
    }

    #[inline]
    pub const fn is_aligned(&self, address: usize) -> bool {
        match self {
            ValueSize::HALF => true,
            ValueSize::WORD => address & 1 == 0,
            ValueSize::DOUBLE => address & 3 == 0,
            ValueSize::QUAD => address & 7 == 0
        }
    }

    #[inline]
    pub const fn sign_extend(&self, value: u64) -> u64 {
        match self {
            ValueSize::HALF => (value as i8) as u64,
            ValueSize::WORD => (value as i16) as u64,
            ValueSize::DOUBLE => (value as i32) as u64,
            ValueSize::QUAD => value
        }
    }

    #[inline]
    pub const fn zero_extend(&self, value: u64) -> u64 {
        value & self.mask()
    }

    #[inline]
    pub const fn get_msb(&self) -> u64 {
        match self {
            ValueSize::HALF => 0x80,
            ValueSize::WORD => 0x8000,
            ValueSize::DOUBLE => 0x8000_0000,
            ValueSize::QUAD => 0x8000_0000_0000_0000
        }
    }
}

const COND_ALWAYS: u8 = 0xE;
const COND_NEVER: u8 = 0xF;

#[derive(Default, Clone, Copy)]
pub struct Register {
    value: u64
}

impl Register {
    pub fn new(value: u64) -> Self {
        Register {
            value
        }
    }

    #[cfg(test)]
    pub fn value(&self) -> u64 {
        self.value
    }

    pub fn read(&self, cpu_info: &CPUInfo, size: ValueSize) -> u64 {
        assert!(size.is_supported(cpu_info));

        self.value & size.mask()
    }

    pub fn write(&mut self, cpu_info: &CPUInfo, size: ValueSize, sign_extend: bool, value: u64) {
        assert!(size.is_supported(cpu_info));

        let value = value & size.mask();
        self.value = if sign_extend {
            size.sign_extend(value)
        } else {
            value
        };
    }
}

#[derive(Default, Clone)]
pub struct CPUState {
    registers: [RefCell<Register>; 16],
    cr_flags: u8,
    cr_int_pc: usize,
    cr_int_ret_pc: usize,
    cr_int_mask: u64,
    cr_int_pending: u64,
    cr_int_cause: u64,
    cr_int_data: u64,
    cr_int_scratch_0: u64,
    cr_int_scratch_1: u64,
    cr_priv: u8,
    cr_int_ret_priv: u8,
    cr_cache_line_size: usize,
    cr_no_cache_start: usize,
    cr_no_cache_end: usize,
    cr_address_mode: u8,
    instruction_pointer: usize,
}

impl CPUState {
    pub fn new() -> CPUState {
        CPUState {
            cr_priv: 1,
            cr_cache_line_size: CACHE_LINE_SIZE,
            cr_no_cache_end: usize::MAX & !CACHE_LINE_SIZE.wrapping_sub(1),
            instruction_pointer: 0xFFFF_FFFF_FFFF_8000,
            .. CPUState::default()
        }
    }

    #[cfg(test)]
    pub fn take_registers(self) -> [Register; 16] {
        self.registers.map(|r| r.take())
    }
    
    pub fn dump_values(&self) {
        println!("Registers");
        for (idx, register) in self.registers.iter().enumerate() {
            println!("\tr{:02}: 0x{:016X}", idx, register.borrow().value)
        }
        
        // todo Add more details
    }

    fn address_width(&self) -> ValueSize {
        if self.cr_address_mode & 4 != 0 {
            ValueSize::QUAD
        } else if self.cr_address_mode & 2 != 0 {
            ValueSize::DOUBLE
        } else {
            ValueSize::WORD
        }
    }
}

#[derive(Copy, Clone)]
struct REX {
    q: bool,
    a: bool,
    b: bool,
    x: bool
}

impl REX {
    fn new(value: u8) -> REX {
        REX {
            q: value & 8 != 0,
            a: value & 4 != 0,
            b: value & 2 != 0,
            x: value & 1 != 0
        }
    }
}

#[bitmatch]
pub fn tick(mut cpu_state: CPUState, cpu_info: &CPUInfo, memory: &mut Memory) -> Result<CPUState> {
    // instruction_data is assumed to be contiguous since data is never added to it after read_instruction_data returns
    let instruction_data = memory.read_instruction_data(cpu_state.instruction_pointer);
    let mut instruction_data = VecDeque::from(instruction_data);

    if instruction_data.len() < 1 {
        if cpu_info.cpuid_1 & CP1_INT != 0 {
            todo!("General Protection Fault, no data at address")
        } else {
            return Err(CPUError::Memory(MemoryError::UnmappedMemory(cpu_state.instruction_pointer)))
        }
    }

    let mut instruction_size = 0usize;
    let mut condition_code: Option<u8> = None;
    let mut rex: Option<u8> = None;

    // look for prefixes
    let prefix = instruction_data[0];
    if cpu_info.cpuid_1 & CP1_COND != 0 && prefix & 0xF0 == 0b1010_0000 && prefix & 0b1110 != 0b1110 {
        condition_code = Some(prefix & 0xF);
        instruction_data.pop_front();
        instruction_size += 1;
    } else if cpu_info.cpuid_1 & CP1_REX != 0 && prefix & 0xF0 == 0b1100_0000 {
        rex = Some(prefix & 0xF);
        instruction_data.pop_front();
        instruction_size += 1;
    }

    if instruction_data.len() < 1 {
        if cpu_info.cpuid_1 & CP1_INT != 0 {
            todo!("General Protection Fault, no data at address")
        } else {
            return Err(CPUError::Memory(MemoryError::UnmappedMemory(cpu_state.instruction_pointer + instruction_size)))
        }
    }

    let prefix = instruction_data[0];
    if rex.is_none() && cpu_info.cpuid_1 & CP1_REX != 0 && prefix & 0xF0 == 0b1100_0000 {
        rex = Some(prefix & 0xF);
        instruction_data.pop_front();
        instruction_size += 1;
    }

    let rex = REX::new(rex.unwrap_or(0));

    // prefixes have been parsed

    if instruction_data.len() < 1 {
        if cpu_info.cpuid_1 & CP1_INT != 0 {
            todo!("General Protection Fault, no data at address")
        } else {
            return Err(CPUError::Memory(MemoryError::UnmappedMemory(cpu_state.instruction_pointer + instruction_size)))
        }
    }

    let first_byte = instruction_data[0];
    #[bitmatch]
    match first_byte {
        "0???_????" => {
            let used_bytes = handle_base_operations(&mut cpu_state, cpu_info, memory, &mut instruction_data, condition_code.unwrap_or(0xE), rex)?;
            cpu_state.instruction_pointer += instruction_size + used_bytes;
        }
        "100?_????" => {
            // base isa relative immediate jump
            if instruction_data.len() >= 2 && condition_code.is_none() {
                // cache instructions in the non-canonical NOP section are ignored since there is no cache
                let condition_code = first_byte & 0xF;
                let displacement = instruction_data[1] as usize;
                let offset = if first_byte & 0x10 != 0 {
                    displacement | !255usize
                } else {
                    displacement
                };
                if check_condition(condition_code, cpu_state.cr_flags) {
                    cpu_state.instruction_pointer = cpu_state.instruction_pointer.wrapping_add(offset);
                } else {
                    cpu_state.instruction_pointer += instruction_size + 2;
                }
            } else if instruction_data.len() < 2 {
                // not enough bytes
                todo!("Handle exceptional situation")
            } else {
                // conditional prefix on a conditional jump
                todo!("Illegal instruction")
            }
        }
        "1010_0???" => {
            // multiple conditional prefixes
            todo!("Illegal instruction")
        }
        "1010_10??" => {
            // multiple conditional prefixes
            todo!("Illegal instruction")
        }
        "1010_110?" => {
            // multiple conditional prefixes
            todo!("Illegal instruction")
        }
        "1010_1110" => {
            // single byte NOP

            // there is technically nothing preventing this from being implemented without a VWI extension
            if cpu_info.force_allow_single_byte_nop || cpu_info.cpuid_1 & 0x2031 != 0 || cpu_info.cpuid_2 & 0x3 != 0 {
                // condition code does not matter since a skipped nop is the same as an executed nop
                cpu_state.instruction_pointer += instruction_size + 1;
            } else {
                todo!("Illegal instruction")
            }
        }
        "1010_1111" => {
            // SAF register jump/call
            if instruction_data.len() >= 2 && cpu_info.cpuid_1 & CP1_SAF != 0 {
                if condition_code.is_none() {
                    let second_byte = instruction_data[1];
                    let call = second_byte & 0x10 != 0;
                    let condition_code = second_byte & 0xF;
                    let register_index = if rex.a {
                        (second_byte >> 5) | 8
                    } else {
                        second_byte >> 5
                    } as usize;

                    if check_condition(condition_code, cpu_state.cr_flags) {
                        if call {
                            cpu_state.registers[7].get_mut().value = (cpu_state.instruction_pointer + instruction_size + 2) as u64;
                        }
                        cpu_state.instruction_pointer = cpu_state.registers[register_index].borrow().value as usize;
                    } else {
                        cpu_state.instruction_pointer += instruction_size + 2;
                    }
                } else {
                    // conditional prefix on a conditional jump/call
                    todo!("Illegal instruction")
                }
            } else if instruction_data.len() < 2 {
                // not enough bytes
                todo!("Handle exceptional situation")
            } else {
                // SAF is unsupported
                todo!("Illegal instruction")
            }
        }
        "1011_????" => {
            // SAF relative immediate call
            if instruction_data.len() >= 2 && cpu_info.cpuid_1 & CP1_SAF != 0 {
                let second_byte = instruction_data[1];
                let displacement = second_byte as usize | ((first_byte as usize & 0xF) << 8);
                let displacement = if displacement & 0x800 != 0 {
                    displacement | !0xFFF
                } else {
                    displacement
                };

                if check_condition(condition_code.unwrap_or(COND_ALWAYS), cpu_state.cr_flags) {
                    cpu_state.registers[7].get_mut().value = (cpu_state.instruction_pointer + instruction_size + 2) as u64;
                    cpu_state.instruction_pointer = cpu_state.instruction_pointer.wrapping_add(displacement);
                } else {
                    cpu_state.instruction_pointer += instruction_size + 2;
                }
            } else if instruction_data.len() < 2 {
                // not enough bytes
                todo!("Handle exceptional situation")
            } else {
                // SAF not supported
                todo!("Illegal instruction")
            }
        }
        "110?_????" => {
            // multiple REX prefixes or illegal prefix
            todo!("Illegal instruction")
        }
        "1110_????" => {
            let used_bytes = handle_exop_operations(&mut cpu_state, cpu_info, memory, &mut instruction_data, condition_code.unwrap_or(COND_ALWAYS), rex)?;
            todo!()
        }
        "1111_????" => {
            let used_bytes = handle_exop_jump_call(&mut cpu_state, cpu_info, &mut instruction_data, condition_code.unwrap_or(COND_ALWAYS))?;
            cpu_state.instruction_pointer += instruction_size + used_bytes;
        }
    }

    cpu_state.instruction_pointer = cpu_state.address_width().sign_extend(cpu_state.instruction_pointer as u64) as usize;

    Ok(cpu_state)
}

fn handle_base_operations(cpu_state: &mut CPUState, cpu_info: &CPUInfo, memory: &mut Memory, instruction_data: &mut VecDeque<u8>, condition_code: u8, rex: REX) -> Result<usize> {
    let first_byte = instruction_data[0];
    if first_byte & 0x40 == 0 {
        let second_byte = instruction_data[1];
        if second_byte & 0x3 == 0 {
            handle_base_register_operation(cpu_state, cpu_info, memory, instruction_data, condition_code, rex)
        } else {
            handle_base_mem_operation(cpu_state, cpu_info, memory, instruction_data, condition_code, rex)
        }
    } else {
        handle_base_immediate_operation(cpu_state, cpu_info, memory, instruction_data, condition_code, rex)
    }
}

fn handle_base_register_operation(cpu_state: &mut CPUState, cpu_info: &CPUInfo, memory: &mut Memory, instruction_data: &mut VecDeque<u8>, condition_code: u8, rex: REX) -> Result<usize> {
    let first_byte = instruction_data[0];
    let second_byte = instruction_data[1];
    let operation = first_byte & 0xF;
    let size = ValueSize::from_u8((first_byte >> 4) & 0x3);
    let register_index_a = if rex.a {
        ((second_byte >> 5) & 0x7) | 8
    } else {
        (second_byte >> 5) & 0x7
    } as usize;
    let register_index_b = if rex.b {
        ((second_byte >> 2) & 0x7) | 8
    } else {
        (second_byte >> 2) & 0x7
    } as usize;

    let address_width = cpu_state.address_width();
    let register_a = &cpu_state.registers[register_index_a];
    let register_b = &cpu_state.registers[register_index_b];
    
    if (operation == 12 || operation == 13) && cpu_info.cpuid_1 & CP1_SAF == 0 {
        // SAF not supported
        todo!("Illegal instruction")
    }
    if operation == 14 {
        // illegal by spec
        todo!("Illegal instruction")
    }
    // operation == 15 is checked below
    
    if !check_condition(condition_code, cpu_state.cr_flags) {
        if operation < 12 {
            return Ok(2)
        } else if operation == 12 || operation == 13 {
            return Ok(2)
        }
        // operation == 14 is illegal
        // operation == 15 is checked below
    }

    if operation < 8 {
        let (result, flags) = perform_base_operation(operation as u64, register_a.borrow().read(cpu_info, size), register_b.borrow().read(cpu_info, size), size);
        if let Some(result) = result {
            register_a.borrow_mut().write(cpu_info, size, true, result)
        }
        cpu_state.cr_flags = flags
    } else {
        match operation {
            8 => {
                // movz
                register_a.borrow_mut().write(cpu_info, size, false, register_b.borrow().value);
            }
            9 => {
                // movs
                register_a.borrow_mut().write(cpu_info, size, true, register_b.borrow().value);
            }
            10 => {
                // load
                let address = address_width.sign_extend(register_b.borrow().value) as usize;
                let data = memory.read(address, size, cpu_info.feat & FT_UMA != 0)?;
                register_a.borrow_mut().write(cpu_info, size, true, data);
            }
            11 => {
                // store
                let value = register_a.borrow().read(cpu_info, size);
                let address = address_width.sign_extend(register_b.borrow().value) as usize;
                memory.write(address, size, value, cpu_info.feat & FT_UMA != 0)?;
            }
            12 => {
                // pop
                let stack_pointer = register_b.borrow().value.wrapping_sub(address_width.num_bytes() as u64);
                let address = address_width.sign_extend(stack_pointer) as usize;
                memory.write(address, size, register_b.borrow().value, cpu_info.feat & FT_UMA != 0)?;
                register_b.borrow_mut().write(cpu_info, address_width, false, address as u64);
            }
            13 => {
                // push
                let stack_pointer = register_a.borrow().value.wrapping_sub(address_width.num_bytes() as u64);
                let address = address_width.sign_extend(stack_pointer) as usize;
                memory.write(address, size, register_b.borrow().value, cpu_info.feat & FT_UMA != 0)?;
                register_a.borrow_mut().write(cpu_info, address_width, false, address as u64);
            }
            14 => {
                // Illegal instruction
                // handled above
                unreachable!()
            }
            15 => {
                if register_index_b > 1 || cpu_info.cpuid_1 & CP1_CI == 0 {
                    todo!("Illegal instruction")
                }
                
                // condition is ignored since cache instructions are NOP on a system without a cache
                return Ok(2)
            }
            _ => unreachable!()
        }
    }

    Ok(2)
}

fn handle_base_immediate_operation(mut cpu_state: &mut CPUState, cpu_info: &CPUInfo, memory: &mut Memory, instruction_data: &mut VecDeque<u8>, condition_code: u8, rex: REX) -> Result<usize> {
    let first_byte = instruction_data[0];
    let second_byte = instruction_data[1];
    let operation = first_byte & 0xF;
    let size = ValueSize::from_u8((first_byte >> 4) & 0x3);
    let immediate = (second_byte & 0x1F) as u64;
    let immediate = if (operation < 8 || operation == 9) && immediate & 0x10 != 0 {
        immediate | !0x1F
    } else {
        immediate
    };
    let register_index = if rex.a {
        ((second_byte >> 5) & 0x7) | 8
    } else {
        (second_byte >> 5) & 0x7
    } as usize;

    let address_width = cpu_state.address_width();
    let register = &mut cpu_state.registers[register_index].get_mut();

    if operation < 8 {
        let (result, flags) = perform_base_operation(operation as u64, register.read(cpu_info, size), immediate, size);
        if let Some(result) = result {
            register.write(cpu_info, size, true, result)
        }
        cpu_state.cr_flags = flags
    } else {
        match operation {
            8 => {
                // movz
                register.write(cpu_info, size, false, immediate);
            }
            9 => {
                // movs
                register.write(cpu_info, size, true, immediate);
            }
            10 => {
                // load
                let address = address_width.sign_extend(immediate) as usize;
                let data = memory.read(address, size, cpu_info.feat & FT_UMA != 0)?;
                register.write(cpu_info, size, true, data);
            }
            11 => {
                // store
                let value = register.read(cpu_info, size);
                let address = address_width.sign_extend(immediate) as usize;
                memory.write(address, size, value, cpu_info.feat & FT_UMA != 0)?;
            }
            12 => {
                // slo
                let new_value = (register.read(cpu_info, size) << 5) | immediate;
                register.write(cpu_info, size, true, new_value);
            }
            13 => {
                // push
                let value = register.value.wrapping_sub(address_width.num_bytes() as u64);
                let address = address_width.sign_extend(value) as usize;
                memory.write(address, size, immediate, cpu_info.feat & FT_UMA != 0)?;
                register.write(cpu_info, address_width, false, address as u64);
            }
            14 => {
                // readcr
                let data = read_cr(&mut cpu_state, cpu_info, immediate as usize);

                if let Some(data) = data {
                    // needed to drop the old reference before calling read_cr
                    let register = &mut cpu_state.registers[register_index];
                    register.get_mut().write(cpu_info, size, true, data);
                }
            }
            15 => {
                // writecr
                let data = register.read(cpu_info, size);
                write_cr(&mut cpu_state, cpu_info, immediate as usize, data);
            }
            _ => unreachable!()
        }
    }

    Ok(2)
}

fn handle_base_mem_operation(cpu_state: &mut CPUState, cpu_info: &CPUInfo, memory: &mut Memory, instruction_data: &mut VecDeque<u8>, condition_code: u8, rex: REX) -> Result<usize> {
    todo!()
}

fn perform_base_operation(operation: u64, input_a: u64, input_b: u64, size: ValueSize) -> (Option<u64>, u8) {
    match operation {
        0 => {
            let result = size.sign_extend(input_a.wrapping_add(input_b));
            let flags = calculate_flags(input_a, input_b, result, size);

            (Some(result), flags)
        }
        1 => {
            let result = size.sign_extend(input_a.wrapping_sub(input_b));
            let flags = calculate_flags(input_a, !input_b, result, size);

            (Some(result), flags)
        }
        2 => {
            let result = size.sign_extend(input_b.wrapping_sub(input_a));
            let flags = calculate_flags(input_b, !input_a, result, size);

            (Some(result), flags)
        }
        3 => {
            let result = size.sign_extend(input_a.wrapping_sub(input_b));
            let flags = calculate_flags(input_a, !input_b, result, size);

            (None, flags)
        }
        4 => {
            let result = size.sign_extend(input_a | input_b);
            let flags = calculate_flags(input_a, input_b, result, size);

            (Some(result), flags)
        }
        5 => {
            let result = size.sign_extend(input_a ^ input_b);
            let flags = calculate_flags(input_a, input_b, result, size);

            (Some(result), flags)
        }
        6 => {
            let result = size.sign_extend(input_a & input_b);
            let flags = calculate_flags(input_a, input_b, result, size);

            (Some(result), flags)
        }
        7 => {
            let result = size.sign_extend(input_a & input_b);
            let flags = calculate_flags(input_a, input_b, result, size);

            (None, flags)
        }
        x => unreachable!("Invalid operation {x}")
    }
}

fn calculate_flags(input_a: u64, input_b: u64, result: u64, size: ValueSize) -> u8 {
    let mut flags = 0;
    let mask = size.mask();
    let msb = size.get_msb();

    if result == 0 {
        flags |= 1;
    }
    if result & msb != 0 {
        flags |= 2;
    }
    if result & mask < input_a & mask {
        flags |= 4;
    }
    if input_a & msb == input_b & msb && input_a & msb != result & msb {
        flags |= 8;
    }

    flags
}

// Since cr_priv is initialized to 1 (system mode) and only matters when PM is implemented, it's ok to not check for the existence of PM.
// Also, since reading from and writing to reserved CRs is unspecified behavior, treating PM as implemented doesn't cause any issues since
// the only way to make it not 1 on a system without PM is to write to a reserved CR.
fn read_cr(cpu_state: &mut CPUState, cpu_info: &CPUInfo, index: usize) -> Option<u64> {
    match index {
        0 => Some(cpu_info.cpuid_1),
        1 => Some(cpu_info.cpuid_2),
        2 => Some(cpu_info.feat),
        3 => Some(cpu_state.cr_flags as u64),
        4 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_pc as u64)
            } else {
                todo!("Handle exceptional state")
            }
        }
        5 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_ret_pc as u64)
            } else {
                todo!("Handle exceptional state")
            }
        }
        6 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_mask)
            } else {
                todo!("Handle exceptional state")
            }
        }
        7 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_pending)
            } else {
                todo!("Handle exceptional state")
            }
        }
        8 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_cause)
            } else {
                todo!("Handle exceptional state")
            }
        }
        9 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_data)
            } else {
                todo!("Handle exceptional state")
            }
        }
        10 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_scratch_0)
            } else {
                todo!("Handle exceptional state")
            }
        }
        11 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_scratch_1)
            } else {
                todo!("Handle exceptional state")
            }
        }
        12 => {
            Some(cpu_state.cr_priv as u64)
        }
        13 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_int_ret_priv as u64)
            } else {
                todo!("Handle exceptional state")
            }
        }
        14 => {
            Some(cpu_state.cr_cache_line_size as u64)
        }
        15 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_no_cache_start as u64)
            } else {
                todo!("Handle exceptional state")
            }
        }
        16 => {
            if cpu_state.cr_priv == 1 {
                Some(cpu_state.cr_no_cache_end as u64)
            } else {
                todo!("Handle exceptional state")
            }
        }
        17 => {
            Some(cpu_state.cr_address_mode as u64)
        }
        _ => Some(0)
    }
}

fn write_cr(cpu_state: &mut CPUState, cpu_info: &CPUInfo, index: usize, data: u64) {
    match index {
        0..=2 => {}
        3 => cpu_state.cr_flags = data as u8,
        4 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_pc = data as usize
            } else {
                todo!("Handle exceptional state")
            }
        }
        5 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_ret_pc = data as usize
            } else {
                todo!("Handle exceptional state")
            }
        }
        6 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_mask = data
            } else {
                todo!("Handle exceptional state")
            }
        }
        7 => {
            if cpu_state.cr_priv == 0 {
                todo!("Handle exceptional state")
            }
        }
        8 => {
            if cpu_state.cr_priv == 0 {
                todo!("Handle exceptional state")
            }
        }
        9 => {
            if cpu_state.cr_priv == 0 {
                todo!("Handle exceptional state")
            }
        }
        10 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_scratch_0 = data
            } else {
                todo!("Handle exceptional state")
            }
        }
        11 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_scratch_1 = data
            } else {
                todo!("Handle exceptional state")
            }
        }
        12 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_priv = (data & 1) as u8
            }
        }
        13 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_int_ret_priv = (data & 1) as u8
            } else {
                todo!("Handle exceptional state")
            }
        }
        14 => {}
        15 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_no_cache_start = (data as usize) & !CACHE_LINE_SIZE.wrapping_sub(1)
            } else {
                todo!("Handle exceptional state")
            }
        }
        16 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_no_cache_end = (data as usize) & !CACHE_LINE_SIZE.wrapping_sub(1)
            } else {
                todo!("Handle exceptional state")
            }
        }
        17 => {
            if cpu_state.cr_priv == 1 {
                cpu_state.cr_address_mode = data as u8
            } else {
                todo!("Handle exceptional state")
            }
        }
        _ => {}
    }
}

fn handle_exop_operations(cpu_state: &mut CPUState, cpu_info: &CPUInfo, memory: &mut Memory, instruction_data: &mut VecDeque<u8>, condition_code: u8, rex: REX) -> Result<usize> {
    unimplemented!()
}

fn handle_exop_jump_call(cpu_state: &mut CPUState, cpu_info: &CPUInfo, instruction_data: &mut VecDeque<u8>, condition_code: u8) -> Result<usize> {
    let address_width = cpu_state.address_width();
    let first_byte = instruction_data[0];
    let call = first_byte & 8 != 0;
    let absolute = first_byte & 4 != 0;
    let size = ValueSize::from_u8(first_byte & 3);
    if (size == ValueSize::DOUBLE && address_width < ValueSize::DOUBLE) || (size == ValueSize::QUAD && address_width < ValueSize::QUAD) {
        todo!("Handle invalid size jump for address mode")
    }

    let (immediate, read_bytes) = match size {
        ValueSize::HALF => {
            let value = if !absolute {
                instruction_data[1] as usize | !(u8::MAX as usize)
            } else {
                instruction_data[1] as usize
            };
            (value, 2)
        }
        ValueSize::WORD => {
            let value = u16::from_le_bytes(instruction_data.as_slices().0[1..3].try_into().unwrap()) as usize;
            let value = if !absolute {
                value | !(u16::MAX as usize)
            } else {
                value
            };
            (value, 3)
        }
        ValueSize::DOUBLE => {
            let value = u32::from_le_bytes(instruction_data.as_slices().0[1..5].try_into().unwrap()) as usize;
            let value = if !absolute {
                value | !(u32::MAX as usize)
            } else {
                value
            };
            (value, 5)
        }
        ValueSize::QUAD => {
            let value = u64::from_le_bytes(instruction_data.as_slices().0[1..9].try_into().unwrap()) as usize;
            (value, 9)
        }
    };

    if check_condition(condition_code, cpu_state.cr_flags) {
        if call {
            cpu_state.registers[7].get_mut().write(cpu_info, address_width, true, cpu_state.instruction_pointer as u64)
        }

        cpu_state.instruction_pointer = if absolute {
            (cpu_state.instruction_pointer & address_width.inverse_mask() as usize) | (immediate & address_width.mask() as usize)
        } else {
            cpu_state.instruction_pointer.wrapping_add(immediate)
        };

        Ok(0)
    } else {
        Ok(read_bytes)
    }
}

fn check_condition(condition_code: u8, flags: u8) -> bool {
    let invert = condition_code & 1 != 0;
    let condition_code = (condition_code >> 1) & 0x7;

    let zero = flags & 1 != 0;
    let negative = flags & 2 != 0;
    let carry = flags & 4 != 0;
    let overflow = flags & 8 != 0;

    let result = match condition_code {
        0 => zero,
        1 => negative,
        2 => carry,
        3 => overflow,
        4 => carry | zero,
        5 => negative ^ overflow,
        6 => zero | (negative ^ overflow),
        7 => true,
        _ => unreachable!("Impossible condition code reached")
    };

    return result ^ invert;
}