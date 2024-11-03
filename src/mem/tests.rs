#[cfg(test)]

use std::num::NonZeroUsize;
use crate::cpu::ValueSize;
use crate::mem::{Memory, MMIOConfig, MMIODevice};

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

struct TestMMIODevice {
    config: MMIOConfig
}

impl TestMMIODevice {
    fn new() -> Self {
        TestMMIODevice {
            config: MMIOConfig {
                address: 0,
                size: 32
            }
        }
    }
}

impl MMIODevice for TestMMIODevice {
    fn identifier(&self) -> &str {
        "Test Device"
    }

    fn configure(&mut self, new_configuration: MMIOConfig) -> MMIOConfig {
        if new_configuration.size < 512 {
            self.config = new_configuration;
        }
        self.config
    }

    fn get_configuration(&self) -> MMIOConfig {
        self.config
    }

    fn read(&mut self, address: usize) -> usize {
        0
    }

    fn read_bytes(&mut self, address: usize, num_bytes: usize, buffer: &mut Vec<u8>) {

    }

    fn write(&mut self, address: usize, data: u64) {

    }

    fn write_bytes(&mut self, address: usize, num_bytes: usize, data: &[u8]) {

    }
}

#[test]
fn configure_mmio_success() {
    let mut memory = Memory::new();
    let test_device = Box::from(TestMMIODevice::new());
    let result = memory.add_mmio(0, NonZeroUsize::new(64).unwrap(), test_device);
    result.unwrap();
}

#[test]
fn configure_mmio_fail() {
    let mut memory = Memory::new();
    let test_device = Box::from(TestMMIODevice::new());
    let result = memory.add_mmio(0, NonZeroUsize::new(1024).unwrap(), test_device);
    result.unwrap_err();
}

#[test]
fn non_overlapping_mmio() {
    let mut memory = Memory::new();
    let test_device = Box::from(TestMMIODevice::new());
    memory.add_mmio(0, NonZeroUsize::new(64).unwrap(), test_device).unwrap();
    let test_device2 = Box::from(TestMMIODevice::new());
    memory.add_mmio(64, NonZeroUsize::new(128).unwrap(), test_device2).unwrap();
}

#[test]
fn overlapping_mmio() {
    let mut memory = Memory::new();
    let test_device = Box::from(TestMMIODevice::new());
    memory.add_mmio(0, NonZeroUsize::new(64).unwrap(), test_device).unwrap();
    let test_device2 = Box::from(TestMMIODevice::new());
    memory.add_mmio(32, NonZeroUsize::new(128).unwrap(), test_device2).unwrap_err();
}