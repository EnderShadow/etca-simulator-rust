mod cpu;
mod tests;
mod mem;

use cpu::*;
use crate::mem::Memory;

fn main() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT, false).unwrap();
    let cpu_state = CPUState::new();
    let mut memory = Memory::new();
    let _ = tick(cpu_state, &cpu_info, &mut memory).unwrap();
}