use std::cell::RefCell;
use std::cmp::min;
use std::collections::VecDeque;
use std::fmt::format;
use std::rc::Rc;
use crate::mem::Memory;

macro_rules! expect_set {
    ($x:expr, $y:expr, $msg:expr) => {
        if $x & $y != $y {
            return Err($msg.into());
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

const CACHE_LINE_SIZE: usize = 8;

pub struct CPUInfo {
    pub cpuid_1: u64,
    pub cpuid_2: u64,
    pub feat: u64,
    pub force_allow_single_byte_nop: bool,
    _private: ()
}

impl CPUInfo {
    pub fn new(cpuid_1: u64, cpuid_2: u64, feat: u64, force_allow_single_byte_nop: bool) -> Result<CPUInfo, String> {
        expect_set!(ALL_CP1, cpuid_1, format!("CP1 has unknown bits set: {}", (ALL_CP1 & cpuid_1) ^ cpuid_1));
        expect_set!(ALL_CP2, cpuid_2, format!("CP2 has unknown bits set: {}", (ALL_CP2 & cpuid_2) ^ cpuid_2));
        expect_set!(ALL_FT, feat, format!("FT has unknown bits set: {}", (ALL_FT & feat) ^ feat));

        if cpuid_1 & CP1_INT != 0 {
            expect_set!(cpuid_1, CP1_SAF, "Interrupt extension requires Stack and Functions extension");
            expect_set!(feat, FT_VON, "Interrupt extension requires Von Neumann feature");
        }

        if cpuid_1 & CP1_ASP != 0 {
            expect_set!(cpuid_1, CP1_SAF, "Arbitrary Stack Pointer extension requires Stack and Functions extension");
        }

        if cpuid_1 & CP1_DWAS != 0 {
            expect_set!(cpuid_1, CP1_DW, "Double Word Address Space extension requires Double Word extension");
        }

        if cpuid_1 & CP1_QWAS != 0 {
            expect_set!(cpuid_1, CP1_QW, "Quad Word Address Space extension requires Quad Word extension");
        }

        if cpuid_2 & CP2_PM != 0 {
            expect_set!(cpuid_1, CP1_INT, "Privileged Mode extension requires Interrupt extension");
        }

        if cpuid_2 & CP2_MD != 0 {
            expect_set!(cpuid_2, CP2_EXOP, "Multiply Divide extension requires Expanded Opcodes extension");
        }

        if feat & FT_MMAI != 0 && cpuid_1 & CP1_MO2 == 0 && cpuid_2 & CP2_MO1 == 0 {
            println!("INFO: Multiple Memory Access Instructions feature is useless without Memory Operands 1 or Memory Operands 2 extension");
        }

        let invalid_cp1 = cpuid_1 & !ALL_CP1;
        let invalid_cp2 = cpuid_2 & !ALL_CP2;
        let invalid_ft = feat & !ALL_FT;

        if invalid_cp1 != 0 || invalid_cp2 != 0 || invalid_ft != 0 {
            return Err(format!("Unsupported extension(s) and/or feature(s) detected ({invalid_cp1}, {invalid_cp2}, {invalid_ft})"))
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

#[derive(Copy, Clone)]
pub enum ValueSize {
    HALF,
    WORD,
    DOUBLE,
    QUAD
}

impl TryFrom<u8> for ValueSize {
    type Error = String;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(ValueSize::HALF),
            1 => Ok(ValueSize::WORD),
            2 => Ok(ValueSize::DOUBLE),
            3 => Ok(ValueSize::QUAD),
            x => Err(format!("Invalid value for size: {x}"))
        }
    }
}

impl ValueSize {
    #[inline]
    fn from_u8(num: u8) -> ValueSize {
        ValueSize::try_from(num).unwrap()
    }

    #[inline]
    pub fn mask(&self) -> u64 {
        match self {
            ValueSize::HALF => 0xFF,
            ValueSize::WORD => 0xFFFF,
            ValueSize::DOUBLE => 0xFFFF_FFFF,
            ValueSize::QUAD => u64::MAX
        }
    }

    #[inline]
    pub fn inverse_mask(&self) -> u64 {
        match self {
            ValueSize::HALF => !0xFFu64,
            ValueSize::WORD => !0xFFFFu64,
            ValueSize::DOUBLE => !0xFFFF_FFFFu64,
            ValueSize::QUAD => 0
        }
    }

    #[inline]
    pub fn is_supported(&self, cpu_info: &CPUInfo) -> bool {
        match self {
            ValueSize::HALF => cpu_info.cpuid_1 & CP1_BYTE != 0,
            ValueSize::WORD => true,
            ValueSize::DOUBLE => cpu_info.cpuid_1 & CP1_DW != 0,
            ValueSize::QUAD => cpu_info.cpuid_1 & CP1_QW != 0
        }
    }

    #[inline]
    pub fn num_bytes(&self) -> usize {
        match self {
            ValueSize::HALF => 1,
            ValueSize::WORD => 2,
            ValueSize::DOUBLE => 4,
            ValueSize::QUAD => 8
        }
    }

    #[inline]
    pub fn is_aligned(&self, address: usize) -> bool {
        match self {
            ValueSize::HALF => true,
            ValueSize::WORD => address & 1 == 0,
            ValueSize::DOUBLE => address & 3 == 0,
            ValueSize::QUAD => address & 7 == 0
        }
    }

    #[inline]
    pub fn sign_extend(&self, value: u64) -> u64 {
        match self {
            ValueSize::HALF => (value as i8) as u64,
            ValueSize::WORD => (value as i16) as u64,
            ValueSize::DOUBLE => (value as i32) as u64,
            ValueSize::QUAD => value
        }
    }

    #[inline]
    pub fn zero_extend(&self, value: u64) -> u64 {
        value & self.mask()
    }

    #[inline]
    pub fn get_msb(&self) -> u64 {
        match self {
            ValueSize::HALF => 0x80,
            ValueSize::WORD => 0x8000,
            ValueSize::DOUBLE => 0x8000_0000,
            ValueSize::QUAD => 0x8000_0000_0000_0000
        }
    }
}

#[derive(Default)]
pub struct Register {
    value: u64
}

impl Register {
    pub fn new(value: u64) -> Self {
        Register {
            value
        }
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

#[derive(Default)]
pub struct CPUState {
    registers: [Register; 16],
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
            cr_no_cache_end: usize::MAX & !(CACHE_LINE_SIZE - 1),
            instruction_pointer: 0xFFFF_FFFF_FFFF_8000,
            .. CPUState::default()
        }
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

pub fn tick(mut cpu_state: CPUState, cpu_info: &CPUInfo, memory: &mut Memory) -> Result<CPUState, String> {
    // instruction_data is assumed to be contiguous since data is never added to it after read_instruction_data returns
    let mut instruction_data = memory.read_instruction_data(cpu_state.instruction_pointer).unwrap();
    assert_eq!(instruction_data.as_slices().1.len(), 0, "instruction_data should be contiguous");

    if instruction_data.len() < 1 {
        return Err(format!("No data at address {}", cpu_state.instruction_pointer))
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
        return Err(format!("No data at address {}", cpu_state.instruction_pointer))
    }

    let prefix = instruction_data[0];
    if rex.is_none() && cpu_info.cpuid_1 & CP1_REX != 0 && prefix & 0xF0 == 0b1100_0000 {
        rex = Some(prefix & 0xF);
        instruction_data.pop_front();
        instruction_size += 1;
    }

    let rex = rex.unwrap_or(0);

    // prefixes have been parsed

    // check for single byte NOP

    if instruction_data.len() < 1 {
        return Err(format!("No data at address {}", cpu_state.instruction_pointer))
    }

    // there is technically nothing preventing this from being implemented without a VWI extension
    if (cpu_info.force_allow_single_byte_nop || cpu_info.cpuid_1 & 0x2031 != 0 || cpu_info.cpuid_2 & 0x3 != 0) && instruction_data[0] == 0b1010_1110 {
        // condition code does not matter since a skipped nop is the same as an executed nop
        cpu_state.instruction_pointer += instruction_size + 1;
        return Ok(cpu_state)
    }

    if instruction_data.len() < 2 {
        return Err(format!("No data at address {}", cpu_state.instruction_pointer))
    }

    // check for base-isa jump

    {
        let jump_instr = u16::from_le_bytes(instruction_data.as_slices().0[0..2].try_into().unwrap());
        if jump_instr & 0xE0 == 0b1000_0000 {
            // cache instructions in the non-canonical NOP section are ignored since there is no cache
            return if condition_code.is_some() {
                Err(format!("Invalid instruction at address {}. Cannot use condition prefix with conditional jumps", cpu_state.instruction_pointer))
            } else {
                let condition_code = (jump_instr & 0xF) as u8;
                let offset = if jump_instr & 0x10 != 0 {
                    (jump_instr >> 8) as usize | !255usize
                } else {
                    (jump_instr >> 8) as usize
                };
                if check_condition(condition_code, cpu_state.cr_flags) {
                    cpu_state.instruction_pointer = cpu_state.instruction_pointer.wrapping_add(offset);
                } else {
                    cpu_state.instruction_pointer += instruction_size + 2;
                }
                Ok(cpu_state)
            }
        }
    }

    // check for SAF reg jump/call

    {
        let saf_reg_jump_call = u16::from_le_bytes(instruction_data.as_slices().0[0..2].try_into().unwrap());
        if cpu_info.cpuid_1 & CP1_SAF != 0 && saf_reg_jump_call & 0xFF == 0b1010_1111 {
            if condition_code.is_some() {
                return Err(format!("Invalid instruction at address {}. Cannot use a condition prefix with conditional jumps/calls", cpu_state.instruction_pointer))
            }

            let call = saf_reg_jump_call & 0x1000 != 0;
            let condition_code = ((saf_reg_jump_call >> 8) & 0xF) as u8;
            let register_index = if rex & 0x4 != 0 {
                ((saf_reg_jump_call >> 13) & 0x7) | 8
            } else {
                (saf_reg_jump_call >> 13) & 0x7
            } as usize;

            if check_condition(condition_code, cpu_state.cr_flags) {
                if call {
                    cpu_state.registers[7].value = (cpu_state.instruction_pointer + instruction_size + 2) as u64;
                }
                cpu_state.instruction_pointer = cpu_state.registers[register_index].value as usize;
            } else {
                cpu_state.instruction_pointer += instruction_size + 2;
            }

            return Ok(cpu_state)
        }
    }

    // check for SAF immediate call

    {
        let saf_imm_call = u16::from_le_bytes(instruction_data.as_slices().0[0..2].try_into().unwrap());
        if cpu_info.cpuid_1 & CP1_SAF != 0 && saf_imm_call & 0xF0 == 0b1011_0000 {
            let displacement = ((saf_imm_call >> 8) | ((saf_imm_call & 0xF) << 8)) as usize;
            let displacement = if displacement & 0x800 != 0 {
                displacement | !0xFFF
            } else {
                displacement
            };

            cpu_state.registers[7].value = (cpu_state.instruction_pointer + instruction_size + 2) as u64;
            cpu_state.instruction_pointer = cpu_state.instruction_pointer.wrapping_add(displacement);

            return Ok(cpu_state)
        }
    }

    Err(format!("Invalid instruction at address {}.", cpu_state.instruction_pointer))
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