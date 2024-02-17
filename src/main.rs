mod cpu;
mod tests;

use cpu::*;

fn main() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT, false).unwrap();
    let cpu_state = CPUState::new(3);
    let mut memory = vec![MemoryMapSegment::new_ram(0, 1 << 16)];
    let _ = tick(cpu_state, &cpu_info, memory.as_mut_slice()).unwrap();
}