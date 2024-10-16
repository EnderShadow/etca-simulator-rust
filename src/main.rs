mod mem;
mod cpu;

use std::num::NonZeroUsize;
use cpu::*;
use crate::mem::Memory;

fn main() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT, false).unwrap();
    let cpu_state = CPUState::new();
    let mut memory = Memory::new();
    let mem_seg_size = NonZeroUsize::new(1 << 15).unwrap();
    memory.add_ram(0, mem_seg_size).unwrap();
    memory.add_rom((1usize << 15).wrapping_neg(), mem_seg_size, vec![].as_slice()).unwrap();
    memory.add_tiled_ram(1 << 15, NonZeroUsize::new((1usize << 16).wrapping_neg()).unwrap(), 4096).unwrap();
    for line in memory.dump_memory_map() {
        println!("{}", line)
    }
    let _ = tick(cpu_state, &cpu_info, &mut memory).unwrap();
}