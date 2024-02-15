#[cfg(test)]
mod tests {
    use crate::cpu::{ALL_CP1, ALL_CP2, ALL_FT, CP1_BYTE, CP1_INT, CP1_QW, CPUInfo, Register, ValueSize};

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
}