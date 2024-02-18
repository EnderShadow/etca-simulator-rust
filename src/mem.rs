use std::cell::RefCell;
use std::cmp::min;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::num::NonZeroUsize;
use std::rc::Rc;
use range_ext::intersect::{Intersect, Intersection};
use crate::cpu::{MAX_INSTRUCTION_SIZE, ValueSize};

enum MemoryMapType {
    Ram(Rc<RefCell<Box<[u8]>>>),
    Rom(Rc<RefCell<Box<[u8]>>>),
    TileRam(Rc<RefCell<Box<[u8]>>>)
}

struct MemoryMapSegment {
    start: usize,
    size: usize,
    mm_type: MemoryMapType
}

impl MemoryMapSegment {
    fn read_aligned(&self, address: usize, size: ValueSize) -> u64 {
        let offset = address - self.start;
        let read_from_bytes: Box<dyn Fn(&[u8]) -> u64> = match size {
            ValueSize::HALF => Box::new(|mem: &[u8]| -> u64 {u8::from_le_bytes(mem[offset..offset + size.num_bytes()].try_into().unwrap()) as u64}),
            ValueSize::WORD => Box::new(|mem: &[u8]| -> u64 {u16::from_le_bytes(mem[offset..offset + size.num_bytes()].try_into().unwrap()) as u64}),
            ValueSize::DOUBLE => Box::new(|mem: &[u8]| -> u64 {u32::from_le_bytes(mem[offset..offset + size.num_bytes()].try_into().unwrap()) as u64}),
            ValueSize::QUAD => Box::new(|mem: &[u8]| -> u64 {u64::from_le_bytes(mem[offset..offset + size.num_bytes()].try_into().unwrap())})
        };
        match &self.mm_type {
            MemoryMapType::Ram(data) => {
                read_from_bytes(&**data.borrow())
            }
            MemoryMapType::Rom(data) => {
                read_from_bytes(&**data.borrow())
            }
            MemoryMapType::TileRam(data) => {
                let mut temp_buffer: Vec<u8> = Vec::with_capacity(8);
                while temp_buffer.len() < 8 {
                    temp_buffer.extend(data.borrow().iter());
                }

                read_from_bytes(&temp_buffer)
            }
        }
    }
    
    fn read_bytes(&self, address: usize, buffer: &mut Vec<u8>, num_bytes_to_read: usize) -> usize {
        let offset = address - self.start;
        let num_bytes = min(self.size - offset, num_bytes_to_read);

        match &self.mm_type {
            MemoryMapType::Ram(data) => {
                buffer.extend_from_slice(&data.borrow()[offset..offset + num_bytes]);
            }
            MemoryMapType::Rom(data) => {
                buffer.extend_from_slice(&data.borrow()[offset..offset + num_bytes]);
            }
            MemoryMapType::TileRam(data) => {
                let tile_length = data.borrow().len();
                let mut offset = offset % tile_length;
                let mut read_bytes = 0usize;
                while read_bytes < num_bytes {
                    let num_to_copy = min(tile_length - offset, num_bytes - read_bytes);
                    buffer.extend_from_slice(&data.borrow()[offset..offset + num_to_copy]);
                    offset = 0;
                    read_bytes += num_to_copy;
                }
            }
        };

        num_bytes
    }

    fn write_aligned(&mut self, address: usize, size: ValueSize, value: u64) {
        let offset = address - self.start;
        match &self.mm_type {
            MemoryMapType::Ram(data) => {
                match size {
                    ValueSize::HALF => data.borrow_mut()[offset] = value as u8,
                    ValueSize::WORD => data.borrow_mut()[offset..offset + 2].copy_from_slice(&(value as u16).to_le_bytes()[..]),
                    ValueSize::DOUBLE => data.borrow_mut()[offset..offset + 4].copy_from_slice(&(value as u32).to_le_bytes()[..]),
                    ValueSize::QUAD => data.borrow_mut()[offset..offset + 8].copy_from_slice(&value.to_le_bytes()[..])
                }
            }
            MemoryMapType::Rom(_) => {
                // ignore writes
            }
            MemoryMapType::TileRam(data) => {
                let byte_vec = match size {
                    ValueSize::HALF => vec![value as u8],
                    ValueSize::WORD => (value as u16).to_le_bytes().to_vec(),
                    ValueSize::DOUBLE => (value as u32).to_le_bytes().to_vec(),
                    ValueSize::QUAD => value.to_le_bytes().to_vec()
                };

                let mut mut_data = data.borrow_mut();
                let mut offset = offset % mut_data.len();
                for byte in byte_vec.iter() {
                    mut_data[offset] = *byte;
                    offset = (offset + 1) % mut_data.len();
                }
            }
        };
    }

    fn write_bytes(&self, address: usize, data_to_write: &[u8], write_amount: usize) -> usize {
        let offset = address - self.start;
        let num_bytes = min(self.size - offset, write_amount);

        match &self.mm_type {
            MemoryMapType::Ram(data) => {
                data.borrow_mut()[offset..offset + num_bytes].copy_from_slice(&data_to_write[0..num_bytes]);
            }
            MemoryMapType::Rom(_) => {
                // ignore writes
            }
            MemoryMapType::TileRam(data) => {
                let tile_length = data.borrow().len();
                let mut offset = offset % tile_length;
                let mut written_bytes = 0usize;
                let mut data_to_write = data_to_write;

                // if more than 2 full overwrites will occur, skip writes which are guaranteed to be lost.
                if num_bytes > 2 * tile_length {
                    let num_overwrites = num_bytes % tile_length - 2;
                    written_bytes = num_overwrites * tile_length;
                    data_to_write = &data_to_write[written_bytes..];
                }

                while written_bytes < num_bytes {
                    let num_to_copy = min(tile_length - offset, num_bytes - written_bytes);
                    data.borrow_mut()[offset..offset + num_to_copy].copy_from_slice(&data_to_write[0..num_to_copy]);
                    offset = 0;
                    written_bytes += num_to_copy;
                    data_to_write = &data_to_write[num_to_copy..];
                }
            }
        };

        num_bytes
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum MemoryError {
    NotMapped,
    Unaligned
}

pub struct Memory {
    memory_segments: Vec<MemoryMapSegment>
}

impl Memory {
    pub fn new() -> Memory {
        Memory {
            memory_segments: Vec::new()
        }
    }

    pub fn dump_memory_map(&self) -> Vec<String> {
        let mut mapping = Vec::new();

        let mut sorted_segments = self.memory_segments.iter().map(|ms| {
            let mem_type = match ms.mm_type {
                MemoryMapType::Rom(_) => "ROM",
                _ => "RAM"
            };
            (ms.start, ms.start + (ms.size - 1), mem_type)
        }).collect::<Vec<_>>();
        sorted_segments.sort_by_key(|x| x.0);
        for (start, end, mem_type) in sorted_segments {
            let text = format!("{start:#018X} - {end:#018X}\t{mem_type}");
            mapping.push(text);
        }

        mapping
    }

    pub fn add_ram(&mut self, start: usize, size: NonZeroUsize) -> Result<(), String> {
        let size = size.into();
        // require 8 byte aligned segments
        assert_eq!(start & 0x7, 0);
        assert_eq!(size & 0x7, 0);

        let range = start..=(start + (size - 1));
        if self.memory_segments.iter().any(|x| {
            let mem_range = x.start..=(x.start + (x.size - 1));
            mem_range.intersect(&range) != Intersection::Empty
        }) {
            return Err(format!("Cannot add ram from address {start} to {} because it would overlap with another memory segment.", start + size))
        }

        let memory = vec![0u8; size].into_boxed_slice();

        let segment = MemoryMapSegment {
            start,
            size,
            mm_type: MemoryMapType::Ram(Rc::new(RefCell::new(memory)))
        };

        self.memory_segments.push(segment);
        Ok(())
    }

    pub fn add_rom(&mut self, start: usize, size: NonZeroUsize, data: &[u8]) -> Result<(), String> {
        let size = size.into();
        // require 8 byte aligned segments
        assert_eq!(start & 0x7, 0);
        assert_eq!(size & 0x7, 0);

        let range = start..=(start + (size - 1));
        if self.memory_segments.iter().any(|x| {
            let mem_range = x.start..=(x.start + (x.size - 1));
            mem_range.intersect(&range) != Intersection::Empty
        }) {
            return Err(format!("Cannot add rom from address {start} to {} because it would overlap with another memory segment.", start + size))
        }

        let fill_length = min(data.len(), size);
        let mut memory = Vec::with_capacity(size);
        memory.extend_from_slice(&data[..fill_length]);
        memory.resize(size, 0);
        let memory = memory.into_boxed_slice();

        let segment = MemoryMapSegment {
            start,
            size,
            mm_type: MemoryMapType::Rom(Rc::new(RefCell::new(memory)))
        };

        self.memory_segments.push(segment);
        Ok(())
    }

    pub fn add_tiled_ram(&mut self, start: usize, size: NonZeroUsize, tile_size: usize) -> Result<(), String> {
        let size = size.into();
        // require 8 byte aligned segments
        assert_eq!(start & 0x7, 0);
        assert_eq!(size & 0x7, 0);
        assert!(tile_size <= size);

        let range = start..=(start + (size - 1));
        if self.memory_segments.iter().any(|x| {
            let mem_range = x.start..=(x.start + (x.size - 1));
            mem_range.intersect(&range) != Intersection::Empty
        }) {
            return Err(format!("Cannot add tiled ram from address {start} to {} because it would overlap with another memory segment.", start + size))
        }

        let memory = vec![0u8; tile_size].into_boxed_slice();

        let segment = MemoryMapSegment {
            start,
            size,
            mm_type: MemoryMapType::TileRam(Rc::new(RefCell::new(memory)))
        };

        self.memory_segments.push(segment);
        Ok(())
    }

    pub fn read(&self, address: usize, size: ValueSize, allow_unaligned: bool) -> Result<u64, MemoryError> {
        if size.is_aligned(address) {
            let segment = self.memory_segments.iter().find(|x| x.start <= address && address - x.start < x.size);
            if let Some(segment) = segment {
                Ok(segment.read_aligned(address, size))
            } else {
                Err(MemoryError::NotMapped)
            }
        } else if allow_unaligned {
            let num_bytes_to_read = size.num_bytes();
            let mut buffer = Vec::with_capacity(num_bytes_to_read);
            let mut address = address;
            while buffer.len() < num_bytes_to_read {
                let segment = self.memory_segments.iter().find(|x| x.start <= address && address - x.start < x.size);
                if let Some(segment) = segment {
                    let buffer_length = buffer.len();
                    let num_read = segment.read_bytes(address, &mut buffer, num_bytes_to_read - buffer_length);
                    address += num_read;
                } else {
                    return Err(MemoryError::NotMapped)
                }
            }

            let result = match size {
                ValueSize::HALF => u8::from_le_bytes(buffer[..].try_into().unwrap()) as u64,
                ValueSize::WORD => u16::from_le_bytes(buffer[..].try_into().unwrap()) as u64,
                ValueSize::DOUBLE => u32::from_le_bytes(buffer[..].try_into().unwrap()) as u64,
                ValueSize::QUAD => u64::from_le_bytes(buffer[..].try_into().unwrap())
            };

            Ok(result)
        } else {
            Err(MemoryError::Unaligned)
        }
    }

    pub fn write(&mut self, address: usize, size: ValueSize, value: u64, allow_unaligned: bool) -> Result<(), MemoryError> {
        if size.is_aligned(address) {
            let segment = self.memory_segments.iter_mut().find(|x| x.start <= address && address - x.start < x.size);
            if let Some(segment) = segment {
                segment.write_aligned(address, size, value);
                Ok(())
            } else {
                Err(MemoryError::NotMapped)
            }
        } else if allow_unaligned {
            let mut data = match size {
                ValueSize::HALF => (value as u8).to_le_bytes().to_vec(),
                ValueSize::WORD => (value as u16).to_le_bytes().to_vec(),
                ValueSize::DOUBLE => (value as u32).to_le_bytes().to_vec(),
                ValueSize::QUAD => value.to_le_bytes().to_vec()
            }.into_boxed_slice();

            let mut address = address;
            while data.len() > 0 {
                let segment = self.memory_segments.iter().find(|x| x.start <= address && address - x.start < x.size);
                if let Some(segment) = segment {
                    let num_written = segment.write_bytes(address, &*data, data.len());
                    address += num_written;
                    data = Box::from(&data[num_written..])
                } else {
                    return Err(MemoryError::NotMapped)
                }
            }

            Ok(())
        } else {
            Err(MemoryError::Unaligned)
        }
    }

    pub fn read_instruction_data(&self, mut address: usize) -> Result<VecDeque<u8>, MemoryError> {
        let num_bytes_to_read = MAX_INSTRUCTION_SIZE;
        let mut buffer = Vec::with_capacity(num_bytes_to_read);
        while buffer.len() < num_bytes_to_read {
            let segment = self.memory_segments.iter().find(|x| x.start <= address && address - x.start < x.size);
            if let Some(segment) = segment {
                let buffer_length = buffer.len();
                let num_read = segment.read_bytes(address, &mut buffer, num_bytes_to_read - buffer_length);
                address += num_read;
            } else {
                // if we encounter an unmapped memory segment, we should stop reading since it might not be a problem
                break
            }
        }

        Ok(VecDeque::from(buffer))
    }
}