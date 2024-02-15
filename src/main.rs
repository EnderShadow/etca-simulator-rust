mod cpu;
mod tests;

use cpu::*;

fn main() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT).unwrap();
    let cpu_state = CPUState::new();
}