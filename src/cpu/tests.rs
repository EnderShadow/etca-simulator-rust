#[cfg(test)]

use std::num::NonZeroUsize;
use crate::cpu::{ALL_CP1, ALL_CP2, ALL_FT, CP1_BYTE, CP1_INT, CP1_QW, CPUInfo, CPUState, Register, UndefinedBehaviorMode, ValueSize};
use crate::mem::Memory;

#[test]
fn cpu_info_no_extensions() {
    let cpu_info = CPUInfo::new(0, 0, 0, false, UndefinedBehaviorMode::Relaxed);
    assert!(cpu_info.is_ok())
}

#[test]
fn cpu_info_all_defined_extensions() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT, false, UndefinedBehaviorMode::Relaxed);
    assert!(cpu_info.is_ok())
}

#[test]
fn cpu_info_missing_extensions() {
    let cpu_info = CPUInfo::new(CP1_INT, 0, 0, false, UndefinedBehaviorMode::Relaxed);
    assert!(cpu_info.is_err())
}

#[test]
fn cpu_info_all_extensions() {
    let cpu_info = CPUInfo::new(u64::MAX, u64::MAX, u64::MAX, false, UndefinedBehaviorMode::Relaxed);
    assert!(cpu_info.is_err())
}

#[test]
fn register_sign_extension() {
    let cpu_info = CPUInfo::new(CP1_BYTE | CP1_QW, 0, 0, false, UndefinedBehaviorMode::Relaxed).unwrap();
    let mut register = Register::default();

    register.write(&cpu_info, ValueSize::HALF, true, 255);
    assert_eq!(register.read(&cpu_info, ValueSize::QUAD), u64::MAX)
}

#[test]
fn register_zero_extension() {
    let cpu_info = CPUInfo::new(CP1_BYTE | CP1_QW, 0, 0, false, UndefinedBehaviorMode::Relaxed).unwrap();
    let mut register = Register::default();

    register.write(&cpu_info, ValueSize::HALF, false, 255);
    assert_eq!(register.read(&cpu_info, ValueSize::QUAD), 255)
}

#[test]
#[should_panic]
fn register_unimplemented_size() {
    let cpu_info = CPUInfo::new(CP1_BYTE, 0, 0, false, UndefinedBehaviorMode::Relaxed).unwrap();
    let mut register = Register::default();

    register.write(&cpu_info, ValueSize::DOUBLE, false, 255);
}

#[test]
fn inverse_mask_test() {
    assert_eq!(ValueSize::HALF.inverse_mask(), 0xFFFF_FFFF_FFFF_FF00u64);
}

#[cfg(test)]
fn basic_16bit_memory(rom_data: &[u8]) -> Memory{
    let mut memory = Memory::new();
    let mem_seg_size = NonZeroUsize::new(1 << 15).unwrap();
    memory.add_ram(0, mem_seg_size).unwrap();
    memory.add_rom((1usize << 15).wrapping_neg(), mem_seg_size, rom_data).unwrap();

    memory
}

#[test]
fn basic_addition_test() {
    let rom_data: [u8; 6] = [0x58, 0x0F, 0x58, 0x23, 0x10, 0x04];
    let mut memory = basic_16bit_memory(rom_data.as_slice());
    let cpu_info = CPUInfo::new(0, 0, 0, false, UndefinedBehaviorMode::Relaxed).unwrap();
    let mut cpu_state = CPUState::new();

    for _ in 0..3 {
        let result = cpu_state.tick(&cpu_info, &mut memory);
        match result {
            Ok(new_cpu_state) => cpu_state = new_cpu_state,
            Err(msg) => {
                panic!("{}", msg);
            }
        }
    }

    let registers = cpu_state.take_registers();
    let result_register = registers[0];
    assert_eq!(result_register.value(), 18)
}

#[test]
fn basic_addition_test2() {
    let rom_data: [u8; 4] = [0x58, 0x0F, 0x10, 0x00];
    let mut memory = basic_16bit_memory(rom_data.as_slice());
    let cpu_info = CPUInfo::new(0, 0, 0, false, UndefinedBehaviorMode::Relaxed).unwrap();
    let mut cpu_state = CPUState::new();

    for _ in 0..2 {
        let result = cpu_state.tick(&cpu_info, &mut memory);
        match result {
            Ok(new_cpu_state) => cpu_state = new_cpu_state,
            Err(msg) => {
                panic!("{}", msg);
            }
        }
    }

    let registers = cpu_state.take_registers();
    let result_register = registers[0];
    assert_eq!(result_register.value(), 30)
}