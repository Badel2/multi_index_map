use std::borrow::Borrow;
use std::collections::btree_map::{Range, RangeMut};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::convert::{AsMut, AsRef};
use std::hash::Hash;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::RangeBounds;
use std::rc::Rc;

mod either_map;

// Desired interface:
// let m: MultiIndexMap< Unordered<String>, Multi<Ordered<u8>, Ordered<u16>>, Book> = MultiIndexMap::new();
// Using K1 and K2 as keys and maps at the same time was a mistake.
// Better to have M1 and M2, and M1::Inner, M2::Inner will be the raw types.
// This avoids the problem where K1 is Ordered<u8> so the map cannot be indexed using u8,
// it must be a Ordered<u8>.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct MultiIndexMap<
    K1: IntoValueMap<(
        <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
        V,
    )>,
    K2: IntoKeyMap<Rc<K1>>,
    V,
> {
    // Map<Rc<K1>, (K2::BothRc, V)>
    value_map: K1::ValueMap,
    // Map<Rc<K2::Either>, Rc<K1>>
    key_map: K2::KeyMap,
}

impl<K1, K2, V> MultiIndexMap<K1, K2, V>
where
    K1: IntoValueMap<(
        <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
        V,
    )>,
    K2: IntoKeyMap<Rc<K1>>,
    <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth: Clone,
{
    fn new() -> Self {
        Self {
            value_map: K1::ValueMap::new(),
            key_map: K2::KeyMap::new(),
        }
    }

    fn insert<IK1: Into<K1>>(
        &mut self,
        primary_key: IK1,
        extra_keys: <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
        value: V,
    ) -> Option<V> {
        let primary_key = Rc::new(primary_key.into());
        self.key_map.insert(extra_keys.clone(), primary_key.clone());
        self.value_map
            .insert(primary_key, (extra_keys, value))
            .map(|x| x.1)
    }

    fn get(&self, k: &K1) -> Option<&V> {
        self.value_map.get(k).map(|x| &x.1)
    }

    fn get_extra(
        &self,
        k: &<<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedEither,
    ) -> Option<&V> {
        if let Some(a) = self.key_map.get(k) {
            self.get(&a)
        } else {
            None
        }
    }
}

impl<K1, K2, V> MultiIndexMap<K1, K2, V>
where
    K1: IntoValueMap<(
        <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
        V,
    )>,
    K2: IntoKeyMap<Rc<K1>>,
    K1: Clone,
    <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth: Clone,
    K1::ValueMap: OrderedMapExtensions<
        K1,
        (
            <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
            V,
        ),
    >,
{
    fn range<T, R>(
        &self,
        range: R,
    ) -> Range<
        Rc<K1>,
        (
            <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
            V,
        ),
    >
    where
        Rc<K1>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        self.value_map.range(range)
    }

    fn range_mut<T, R>(
        &mut self,
        range: R,
    ) -> RangeMut<
        Rc<K1>,
        (
            <<K2 as IntoKeyMap<Rc<K1>>>::KeyMap as MMap<K2, Rc<K1>>>::NestedBoth,
            V,
        ),
    >
    where
        Rc<K1>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        self.value_map.range_mut(range)
    }
}

trait IntoValueMap<V>
where
    Self: Sized,
{
    type ValueMap: Map<Self, V>;
}

trait IntoKeyMap<V>: EitherOrBoth
where
    Self: Sized,
{
    type KeyMap: MMap<Self, V>;
}

trait Map<K, V> {
    fn new() -> Self;
    fn get(&self, k: &K) -> Option<&V>;
    fn insert(&mut self, k: Rc<K>, v: V) -> Option<V>;
}

trait MMap<K: EitherOrBoth, V> {
    type NestedEither;
    type NestedBoth;

    fn new() -> Self;
    fn get(&self, k: &Self::NestedEither) -> Option<&V>;
    fn insert(&mut self, k: Self::NestedBoth, v: V);
}

trait EitherOrBoth {
    type Either;
    type Both;

    fn for_each_either<F: FnMut(Self::Either)>(x: Self::Both, f: F);
}

impl<A, B> EitherOrBoth for Multi<A, B> {
    type Either = Either<A, B>;
    type Both = Both<A, B>;

    fn for_each_either<F: FnMut(Self::Either)>(x: Self::Both, f: F) {
        x.for_each_either(f);
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Both<A, B>(A, B);

impl<A, B> Both<A, B> {
    fn new<IA, IB>(a: IA, b: IB) -> Self
    where
        IA: Into<A>,
        IB: Into<B>,
    {
        Self(a.into(), b.into())
    }
    fn for_each_either<F: FnMut(Either<A, B>)>(self, mut f: F) {
        f(Either::A(self.0));
        f(Either::B(self.1));
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Either<A, B> {
    A(A),
    B(B),
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Multi<A, B> {
    A(A),
    B(B),
    AB(A, B),
}

struct MultiM<A: IntoKeyMap<V>, B: IntoKeyMap<V>, V>(A::KeyMap, B::KeyMap);

/*******************
 * IMPLEMENTATIONS *
 *******************/

impl<A, B, V> IntoKeyMap<V> for Multi<A, B>
where
    A: IntoKeyMap<V>,
    B: IntoKeyMap<V>,
    V: Clone,
{
    type KeyMap = MultiM<A, B, V>;
}

impl<A, B, V> MMap<Multi<A, B>, V> for MultiM<A, B, V>
where
    A: IntoKeyMap<V>,
    B: IntoKeyMap<V>,
    V: Clone,
{
    type NestedEither = Either<
        <<A as IntoKeyMap<V>>::KeyMap as MMap<A, V>>::NestedEither,
        <<B as IntoKeyMap<V>>::KeyMap as MMap<B, V>>::NestedEither,
    >;
    type NestedBoth = Both<
        <<A as IntoKeyMap<V>>::KeyMap as MMap<A, V>>::NestedBoth,
        <<B as IntoKeyMap<V>>::KeyMap as MMap<B, V>>::NestedBoth,
    >;

    fn new() -> Self {
        MultiM(A::KeyMap::new(), B::KeyMap::new())
    }
    fn get(&self, k: &Self::NestedEither) -> Option<&V> {
        match k {
            Either::A(k) => self.0.get(k),
            Either::B(k) => self.1.get(k),
        }
    }
    fn insert(&mut self, k: Self::NestedBoth, v: V) {
        self.0.insert(k.0, v.clone());
        self.1.insert(k.1, v);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Ordered<K>(K);
struct OrderedMap<K, V>(BTreeMap<Rc<K>, V>);

impl<K> From<K> for Ordered<K> {
    fn from(k: K) -> Self {
        Ordered(k)
    }
}

impl<K: Ord, V> IntoValueMap<V> for Ordered<K> {
    type ValueMap = OrderedMap<Self, V>;
}

impl<K: Ord, V> Map<K, V> for OrderedMap<K, V> {
    fn new() -> Self {
        OrderedMap(BTreeMap::new())
    }
    fn get(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }
    fn insert(&mut self, k: Rc<K>, v: V) -> Option<V> {
        self.0.insert(k, v)
    }
}

impl<K> EitherOrBoth for Ordered<K> {
    type Either = Ordered<K>;
    type Both = Ordered<K>;

    fn for_each_either<F: FnMut(Ordered<K>)>(x: Ordered<K>, mut f: F) {
        f(x);
    }
}

impl<K: Ord, V: Clone> IntoKeyMap<V> for Ordered<K> {
    type KeyMap = OrderedMap<Self, V>;
}

impl<K: EitherOrBoth, V> MMap<K, V> for OrderedMap<K::Either, V>
where
    K::Either: Ord,
    V: Clone,
{
    type NestedEither = K::Either;
    type NestedBoth = K::Both;

    fn new() -> Self {
        OrderedMap(BTreeMap::new())
    }
    fn get(&self, k: &K::Either) -> Option<&V> {
        self.0.get(k)
    }
    fn insert(&mut self, k: K::Both, v: V) {
        K::for_each_either(k, |k| {
            self.0.insert(Rc::new(k), v.clone());
        })
    }
}

trait OrderedMapExtensions<K, V> {
    fn range<T, R>(&self, range: R) -> Range<Rc<K>, V>
    where
        Rc<K>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized;
    fn range_mut<T, R>(&mut self, range: R) -> RangeMut<Rc<K>, V>
    where
        Rc<K>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized;
}

impl<K: Ord, V> OrderedMapExtensions<K, V> for OrderedMap<K, V> {
    fn range<T, R>(&self, range: R) -> Range<Rc<K>, V>
    where
        Rc<K>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        self.0.range(range)
    }

    fn range_mut<T, R>(&mut self, range: R) -> RangeMut<Rc<K>, V>
    where
        Rc<K>: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        self.0.range_mut(range)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Unordered<K>(K);
struct UnorderedMap<K, V>(HashMap<Rc<K>, V>);

impl<K> From<K> for Unordered<K> {
    fn from(k: K) -> Self {
        Unordered(k)
    }
}

impl<K: Hash + Eq, V> IntoValueMap<V> for Unordered<K> {
    type ValueMap = UnorderedMap<Self, V>;
}

impl<K: Hash + Eq, V> Map<K, V> for UnorderedMap<K, V> {
    fn new() -> Self {
        UnorderedMap(HashMap::new())
    }
    fn get(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }
    fn insert(&mut self, k: Rc<K>, v: V) -> Option<V> {
        self.0.insert(k, v)
    }
}

impl<K> EitherOrBoth for Unordered<K> {
    type Either = Unordered<K>;
    type Both = Unordered<K>;

    fn for_each_either<F: FnMut(Unordered<K>)>(x: Unordered<K>, mut f: F) {
        f(x);
    }
}

impl<K: Hash + Eq, V: Clone> IntoKeyMap<V> for Unordered<K> {
    type KeyMap = UnorderedMap<Self, V>;
}

impl<K: EitherOrBoth, V> MMap<K, V> for UnorderedMap<K::Either, V>
where
    K::Either: Hash + Eq,
    V: Clone,
{
    type NestedEither = K::Either;
    type NestedBoth = K::Both;

    fn new() -> Self {
        UnorderedMap(HashMap::new())
    }
    fn get(&self, k: &K::Either) -> Option<&V> {
        self.0.get(k)
    }
    fn insert(&mut self, k: K::Both, v: V) {
        K::for_each_either(k, |k| {
            self.0.insert(Rc::new(k), v.clone());
        })
    }
}

/*********
 * TESTS *
 *********/
#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    struct Book {
        title: String,
        author: String,
        rating: u8,
        pages: u16,
    }

    #[test]
    fn insert() {
        let book1 = Book {
            title: format!("Title1"),
            author: format!("anon"),
            rating: 6,
            pages: 999,
        };

        let mut m2: MultiIndexMap<Unordered<String>, Multi<Ordered<u8>, Ordered<u16>>, Book> =
            MultiIndexMap::new();
        m2.insert(format!("Title1"), Both::new(6, 123), book1.clone());
        assert_eq!(m2.get(&Unordered(format!("Title1"))), Some(&book1));
        assert_eq!(m2.get_extra(&Either::A(Ordered(6))), Some(&book1));

        let mut m3: MultiIndexMap<
            Unordered<String>,
            Multi<Multi<Ordered<u8>, Unordered<i8>>, Multi<Ordered<String>, Ordered<u16>>>,
            Book,
        > = MultiIndexMap::new();
        m3.insert(
            format!("Title1"),
            Both::new(Both::new(6, -6), Both::new(format!("Nice"), 999)),
            book1.clone(),
        );
        assert_eq!(m3.get(&Unordered(format!("Title1"))), Some(&book1));
        assert_eq!(
            m3.get_extra(&Either::A(Either::A(Ordered(6)))),
            Some(&book1)
        );
        assert_eq!(
            m3.get_extra(&Either::B(Either::B(Ordered(999)))),
            Some(&book1)
        );
    }

    #[test]
    fn range() {
        let book1 = format!("I'm a book!");
        let book2 = format!("Me too!");
        let book3 = format!("Hi :D");
        // Changing the main key from Ordered to Unordered will stop this test
        // from compiling, because Unordered does not implement range
        let mut m2: MultiIndexMap<Ordered<u8>, Multi<Unordered<u8>, Unordered<String>>, _> =
            MultiIndexMap::new();
        m2.insert(1, Both::new(6, format!("Book1")), book1.clone());
        m2.insert(3, Both::new(5, format!("Book3")), book3.clone());
        m2.insert(2, Both::new(5, format!("Book2")), book2.clone());

        let mut m2range = m2.range(Rc::new(Ordered(1))..Rc::new(Ordered(4)));
        assert_eq!(
            m2range.next().map(|(k1, (k2, v))| (k1, v)),
            Some((&Rc::new(Ordered(1)), &book1))
        );
        assert_eq!(
            m2range.next().map(|(k1, (k2, v))| (k1, v)),
            Some((&Rc::new(Ordered(2)), &book2))
        );
        assert_eq!(
            m2range.next().map(|(k1, (k2, v))| (k1, v)),
            Some((&Rc::new(Ordered(3)), &book3))
        );
        assert_eq!(m2range.next(), None);
    }
}
