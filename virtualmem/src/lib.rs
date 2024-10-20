use lazy_static::lazy_static;
use std::alloc::{alloc, dealloc, Layout};
use std::sync::Mutex;

extern crate lazy_static;

const PAGE_SIZE: usize = 4096;

struct Page {
    physical_address: *mut u8,
    is_allocated: bool,
}

unsafe impl Sync for Page {}
unsafe impl Send for Page {}

struct VirtualMemory {
    pages: Vec<Page>,
    total_pages: usize,
}

impl VirtualMemory {
    fn new(total_pages: usize) -> Self {
        let mut pages = Vec::with_capacity(total_pages);
        for _ in 0..total_pages {
            pages.push(Page {
                physical_address: std::ptr::null_mut(),
                is_allocated: false,
            });
        }
        VirtualMemory { pages, total_pages }
    }

    fn allocate_page(&mut self, page_index: usize) -> bool {
        if page_index >= self.total_pages || self.pages[page_index].is_allocated {
            return false;
        }
        let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            return false;
        }
        self.pages[page_index].physical_address = ptr;
        self.pages[page_index].is_allocated = true;

        true
    }

    fn free_page(&mut self, page_index: usize) {
        if page_index < self.total_pages && self.pages[page_index].is_allocated {
            let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
            unsafe {
                dealloc(self.pages[page_index].physical_address, layout);
            }
            self.pages[page_index].physical_address = std::ptr::null_mut();
            self.pages[page_index].is_allocated = false;
        }
    }

    fn read(&self, page_index: usize, offset: usize) -> Option<u8> {
        if page_index < self.total_pages
            && self.pages[page_index].is_allocated
            && offset < PAGE_SIZE
        {
            unsafe { Some(*self.pages[page_index].physical_address.add(offset)) }
        } else {
            None
        }
    }

    fn write(&mut self, page_index: usize, offset: usize, value: u8) -> bool {
        if page_index < self.total_pages
            && self.pages[page_index].is_allocated
            && offset < PAGE_SIZE
        {
            unsafe {
                *self.pages[page_index].physical_address.add(offset) = value;
            }
            true
        } else {
            false
        }
    }
}

lazy_static! {
    static ref VIRTUAL_MEMORY: Mutex<VirtualMemory> = Mutex::new(VirtualMemory::new(1024)); // 1024 pages
}

#[no_mangle]
pub extern "C" fn allocate_page(page_index: usize) -> bool {
    VIRTUAL_MEMORY
        .lock()
        .expect("Failed to allocate page")
        .allocate_page(page_index)
}

#[no_mangle]
pub extern "C" fn free_page(page_index: usize) {
    VIRTUAL_MEMORY
        .lock()
        .expect("Failed to free page")
        .free_page(page_index)
}

#[no_mangle]
pub extern "C" fn read_memory(page_index: usize, offset: usize) -> i32 {
    match VIRTUAL_MEMORY
        .lock()
        .expect("Failed to read memory")
        .read(page_index, offset)
    {
        Some(value) => value as i32,
        None => -1,
    }
}

#[no_mangle]
pub extern "C" fn write_memory(page_index: usize, offset: usize, value: u8) -> bool {
    VIRTUAL_MEMORY
        .lock()
        .expect("Failed to write to memory")
        .write(page_index, offset, value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate_and_free_page() {
        let mut vm = VirtualMemory::new(10);
        assert!(vm.allocate_page(0));
        assert!(vm.pages[0].is_allocated);
        vm.free_page(0);
        assert!(!vm.pages[0].is_allocated)
    }

    #[test]
    fn test_read_and_write() {
        let mut vm = VirtualMemory::new(10);
        vm.allocate_page(0);
        assert!(vm.write(0, 0, 42));
        assert_eq!(vm.read(0, 0), Some(42));
    }
    #[test]
    fn test_out_of_bounds() {
        let mut vm = VirtualMemory::new(10);
        assert!(!vm.allocate_page(10));
        assert!(!vm.write(0, 0, 42));
        assert_eq!(vm.read(0, 0), None);
    }
}
