mod cpu;
mod tests;

use cpu::*;

pub enum ValueSize {
    HALF,
    WORD,
    DOUBLE,
    QUAD
}

impl ValueSize {
    #[inline]
    fn mask(&self) -> u64 {
        match self {
            ValueSize::HALF => 0xFF,
            ValueSize::WORD => 0xFFFF,
            ValueSize::DOUBLE => 0xFFFF_FFFF,
            ValueSize::QUAD => u64::MAX
        }
    }

    #[inline]
    fn inverse_mask(&self) -> u64 {
        match self {
            ValueSize::HALF => !0xFFu64,
            ValueSize::WORD => !0xFFFFu64,
            ValueSize::DOUBLE => !0xFFFF_FFFFu64,
            ValueSize::QUAD => 0
        }
    }

    #[inline]
    fn is_supported(&self, cpu_info: &CPUInfo) -> bool {
        match self {
            ValueSize::HALF => cpu_info.cpuid_1 & CP1_BYTE != 0,
            ValueSize::WORD => true,
            ValueSize::DOUBLE => cpu_info.cpuid_1 & CP1_DW != 0,
            ValueSize::QUAD => cpu_info.cpuid_1 & CP1_QW != 0
        }
    }

    #[inline]
    fn num_bytes(&self) -> usize {
        match self {
            ValueSize::HALF => 1,
            ValueSize::WORD => 2,
            ValueSize::DOUBLE => 4,
            ValueSize::QUAD => 8
        }
    }

    #[inline]
    fn is_aligned(&self, address: usize) -> bool {
        match self {
            ValueSize::HALF => true,
            ValueSize::WORD => address & 1 == 0,
            ValueSize::DOUBLE => address & 3 == 0,
            ValueSize::QUAD => address & 7 == 0
        }
    }

    #[inline]
    fn sign_extend(&self, value: u64) -> u64 {
        match self {
            ValueSize::HALF => (value as i8) as u64,
            ValueSize::WORD => (value as i16) as u64,
            ValueSize::DOUBLE => (value as i32) as u64,
            ValueSize::QUAD => value
        }
    }

    #[inline]
    fn zero_extend(&self, value: u64) -> u64 {
        value & self.mask()
    }
}

#[derive(Default)]
pub struct Register {
    value: u64
}

impl Register {
    fn read(&self, cpu_info: &CPUInfo, size: ValueSize) -> u64 {
        assert!(size.is_supported(cpu_info));

        self.value & size.mask()
    }

    fn write(&mut self, cpu_info: &CPUInfo, size: ValueSize, sign_extend: bool, value: u64) {
        assert!(size.is_supported(cpu_info));

        let value = value & size.mask();
        self.value = if sign_extend {
            size.sign_extend(value)
        } else {
            value
        };
    }
}

fn main() {
    let cpu_info = CPUInfo::new(ALL_CP1, ALL_CP2, ALL_FT).unwrap();
    let cpu_state = CPUState::new();
}