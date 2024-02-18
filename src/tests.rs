#[cfg(test)]
mod tests {
    use std::io::repeat;
    use std::num::NonZeroUsize;
    use crate::cpu::{ALL_CP1, ALL_CP2, ALL_FT, CP1_BYTE, CP1_INT, CP1_QW, CPUInfo, Register, ValueSize};
    use crate::mem::Memory;

    #[test]
    fn cpu_info_no_extensions() {
        let cpu_info = CPUInfo::new(0, 0, 0, false);
        assert!(cpu_info.is_ok())
    }

    #[test]
    fn cpu_info_all_defined_extensions() {
        let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT, false);
        assert!(cpu_info.is_ok())
    }

    #[test]
    fn cpu_info_missing_extensions() {
        let cpu_info = CPUInfo::new(CP1_INT, 0, 0, false);
        assert!(cpu_info.is_err())
    }

    #[test]
    fn cpu_info_all_extensions() {
        let cpu_info = CPUInfo::new(u64::MAX, u64::MAX, u64::MAX, false);
        assert!(cpu_info.is_err())
    }

    #[test]
    fn register_sign_extension() {
        let cpu_info = CPUInfo::new(CP1_BYTE | CP1_QW, 0, 0, false).unwrap();
        let mut register = Register::default();

        register.write(&cpu_info, ValueSize::HALF, true, 255);
        assert_eq!(register.read(&cpu_info, ValueSize::QUAD), u64::MAX)
    }

    #[test]
    fn register_zero_extension() {
        let cpu_info = CPUInfo::new(CP1_BYTE | CP1_QW, 0, 0, false).unwrap();
        let mut register = Register::default();

        register.write(&cpu_info, ValueSize::HALF, false, 255);
        assert_eq!(register.read(&cpu_info, ValueSize::QUAD), 255)
    }

    #[test]
    #[should_panic]
    fn register_unimplemented_size() {
        let cpu_info = CPUInfo::new(CP1_BYTE, 0, 0, false).unwrap();
        let mut register = Register::default();

        register.write(&cpu_info, ValueSize::DOUBLE, false, 255);
    }

    #[test]
    fn inverse_mask_test() {
        assert_eq!(ValueSize::HALF.inverse_mask(), 0xFFFF_FFFF_FFFF_FF00u64);
    }

    #[test]
    fn non_overlapping_memory() {
        let mut memory = Memory::new();
        let page_size = NonZeroUsize::new(4096).unwrap();
        memory.add_ram(0, page_size).unwrap();
        memory.add_ram(4096, page_size).unwrap();
    }

    #[test]
    fn non_consecutive_memory() {
        let mut memory = Memory::new();
        let page_size = NonZeroUsize::new(4096).unwrap();
        memory.add_ram(0, page_size).unwrap();
        memory.add_ram(8192, page_size).unwrap();
        memory.add_ram(4096, page_size).unwrap();
    }

    #[test]
    #[should_panic]
    fn overlapping_memory() {
        let mut memory = Memory::new();
        let page_size = NonZeroUsize::new(4096).unwrap();
        memory.add_ram(0, page_size).unwrap();
        memory.add_ram(2048, page_size).unwrap();
    }

    #[test]
    #[should_panic]
    fn unaligned_memory_segment() {
        let mut memory = Memory::new();
        memory.add_ram(1, NonZeroUsize::new(1).unwrap()).unwrap();
    }

    #[test]
    fn ram_write_read_test() {
        let mut memory = Memory::new();
        memory.add_ram(0, NonZeroUsize::new(256).unwrap()).unwrap();

        for i in 0usize..256 {
            memory.write(i, ValueSize::HALF, i as u64 + 1, false).unwrap();
        }

        for i in 0usize..256 {
            let value = memory.read(i, ValueSize::HALF, false).unwrap();
            assert_eq!(value, ValueSize::HALF.zero_extend(i as u64 + 1))
        }
    }

    #[test]
    fn tiled_ram_write_read_test() {
        let mut memory = Memory::new();
        memory.add_tiled_ram(0, NonZeroUsize::new(256).unwrap(), 128).unwrap();

        for i in 0usize..256 {
            memory.write(i, ValueSize::HALF, i as u64 + 1, false).unwrap();
        }

        for i in 0usize..128 {
            let value = memory.read(i, ValueSize::HALF, false).unwrap();
            assert_eq!(value, ValueSize::HALF.zero_extend(i as u64 + 129))
        }
    }

    #[test]
    #[should_panic]
    fn failing_unaligned_memory_access() {
        let mut memory = Memory::new();
        memory.add_ram(0, NonZeroUsize::new(256).unwrap()).unwrap();

        memory.read(1, ValueSize::QUAD, false).unwrap();
    }

    #[test]
    fn successful_unaligned_memory_access() {
        let mut memory = Memory::new();
        memory.add_ram(0, NonZeroUsize::new(256).unwrap()).unwrap();

        memory.write(1, ValueSize::DOUBLE, 0x12345678, true).unwrap();
        let value = memory.read(1, ValueSize::DOUBLE, true).unwrap();

        assert_eq!(value, 0x12345678)
    }

    #[test]
    fn multi_segment_memory_read() {
        let mut memory = Memory::new();
        memory.add_ram(0, NonZeroUsize::new(256).unwrap()).unwrap();
        memory.add_ram(256, NonZeroUsize::new(256).unwrap()).unwrap();

        memory.write(254, ValueSize::DOUBLE, 0x12345678, true).unwrap();
        let value = memory.read(254, ValueSize::DOUBLE, true).unwrap();

        assert_eq!(value, 0x12345678)
    }
}