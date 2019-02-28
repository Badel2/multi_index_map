//! EitherMap: store a value using multiple keys and use either key to retrieve the value
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;

struct EitherMap<K: EitherOrBoth, V> {
    map: HashMap<K::Both, V>,
}

impl<K: Eq + Hash + EitherOrBoth, V> EitherMap<K, V> {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    fn insert(&mut self, k: K::Both, v: V) -> Option<V> {
        self.map.insert(k, v)
    }

    // Warning: O(n) get! This is only a proof of concept!
    fn get(&self, key: &K::Either) -> Option<&V> {
        self.map
            .iter()
            .filter(|(k, v)| K::contains(k, key))
            .map(|(k, v)| v)
            .next()
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
struct Both<A, B>(A, B);

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
enum Either<A, B> {
    A(A),
    B(B),
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
enum Multi<A, B> {
    A(A),
    B(B),
    AB(A, B),
}

trait EitherOrBoth {
    type Either: Hash + Eq;
    type Both: Hash + Eq;

    fn contains(a: &Self::Both, b: &Self::Either) -> bool;
}

impl<A: Hash + Eq, B: Hash + Eq> EitherOrBoth for Multi<A, B> {
    type Either = Either<A, B>;
    type Both = Both<A, B>;

    fn contains(a: &Self::Both, b: &Self::Either) -> bool {
        match b {
            Either::A(b0) => &a.0 == b0,
            Either::B(b1) => &a.1 == b1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dual_keys() {
        let mut m: EitherMap<Multi<String, u32>, bool> = EitherMap::new();

        m.insert(Both(format!("Hi"), 4), true);

        assert_eq!(m.get(&Either::A(format!("Hi"))), Some(&true));
        assert_eq!(m.get(&Either::B(4)), Some(&true));
    }
}
