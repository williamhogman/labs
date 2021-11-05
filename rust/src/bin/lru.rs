use std::mem::{MaybeUninit, swap};

use heapless::FnvIndexMap;
use hash32::Hash;

struct LRU<K: Sized + Hash + Eq, V: Sized, const SIZE: usize> {
    indexes: FnvIndexMap<K, V , SIZE>,
}

impl <K: Sized + Hash + Eq, V: Sized, const SIZE: usize> Default for LRU<K, V, SIZE> {
    fn default() -> Self {
	LRU {
	    indexes: Default::default(),
	}
    }
}

impl <K: Sized + Hash + Eq + Clone, V: Sized, const SIZE: usize> LRU<K, V, SIZE> {

    fn add(&mut self, k: K, v: V) -> () {
	self.indexes.insert(k, self.length).map_err(|_| ()).expect("foo");
    }

    fn get(&mut self, k: K) -> Option<&V> {
	if let Some(v) = self.indexes.shift_remove(&k) {

	} else {
	    None
	}
    }
}

unsafe fn assume_init_ref<'l, T: Sized>(x: &'l MaybeUninit<T>) -> &'l T {
    &*x.as_ptr()
}

fn main() {
    let mut lru: LRU<usize, usize, 3> = Default::default();
    lru.add(1, 10);
    lru.add(2, 20);
    lru.add(3, 30);
    lru.add(4, 40);
    let mut f = |a: usize, b: usize| {
	assert_eq!(lru.get(a), Some(&b))
    };
    f(2, 20);
    f(3, 30);
    f(4, 40);
}
