use core::marker::PhantomData;

pub trait HashMap<K, V> {
    fn insert(&mut self, key: K, val: V) -> bool;
    fn erase(&mut self, key: &K) -> bool;

    /// NOTE: get an immutable reference to the value, need to use inner
    ///       mutability to change (e.g wrap in RefCell)
    fn find<'a>(&self, key: &K) -> Option<&'a V>;
    fn contains(&self, key: &K) -> bool;
}

// We use phantomData (zero-sized) as generic parameters cannot be unused
pub struct EmptyMap<K, V> {
    key: PhantomData<K>,
    value: PhantomData<V>,
}

impl<K, V> EmptyMap<K, V> {
    fn new() -> Self {
        EmptyMap::<K, V> {
            key: PhantomData,
            value: PhantomData,
        }
    }
}

impl<K, V> HashMap<K, V> for EmptyMap<K, V> {
    fn insert(&mut self, _key: K, _val: V) -> bool {
        false
    }
    fn erase(&mut self, _key: &K) -> bool {
        false
    }
    fn find<'a>(&self, _key: &K) -> Option<&'a V> {
        None
    }
    fn contains(&self, _key: &K) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_map_stays_empty() {
        let mut m = EmptyMap::<i32, i32>::new();
        assert!(!m.insert(3, 3))
    }
}
