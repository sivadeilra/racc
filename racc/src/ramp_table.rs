use core::ops::Range;

/// A _ramp table_ is a data structure that stores values in an efficient, indexed form that is
/// well-suited for some algorithms. Conceptually, a ramp table is a mapping from integers (keys) to
/// small vectors of values. The keys are expected to cluster near 0 and are non-negative.
///
/// RampTable stored its contents in `index` and `values` vectors. The `values` vector contains all
/// of the items in the table, contiguously, with no gaps. The `index` table contains positions
/// within the `values` table.
///
/// The values stored in the `index` table are in non-decreasing order. For each key `k` in the ramp
/// table, we find the values for that key by `values[index[k] .. index[k + 1]]`. For convenience,
/// the length of `index` is always equal to 1 + the number of keys in the table. Also,
/// `index[0] == `, and (normally) `index[num_keys] == values.len()`.
///
/// ## Building a RampTable
///
/// To build a RampTable, often the most convenient approach is to call `push_value` and
/// `finish_key`. This _implicitly_ identifies the keys of the `RampTable`; each call to
/// `finish_key` increases the current key index, and each call to `push_value` pushes another
/// value into the item set of the current key.
///
/// For example:
///
/// ```ignore
/// # use ramp_table::RampTable;
/// let mut rt = RampTable::new();
/// rt.push_value("A");
/// rt.push_value("B");
/// rt.finish_key(); // finish key 0 (which has two values)
/// rt.finish_key(); // finish key 1 (which has no values)
/// rt.push_value("bees");
/// rt.push_value("knees");
/// rt.finish_key(); // finish key 2 (which has two values)
/// ```
///
/// This would build a `RampTable` with these entries:
///
/// ```text
/// [0] --> ["A", "B"]
/// [1] --> []
/// [2] --> ["bees", "knees"]
/// ```
#[derive(Clone, Debug)]
pub struct RampTable<T> {
    pub index: Vec<usize>,
    pub values: Vec<T>,
}

impl<T> RampTable<T> {
    pub fn with_capacity(num_keys: usize, num_values: usize) -> Self {
        Self {
            index: {
                let mut ii = Vec::with_capacity(num_keys + 1);
                ii.push(0);
                ii
            },
            values: Vec::with_capacity(num_values),
        }
    }

    pub fn new() -> Self {
        Self {
            index: vec![0],
            values: Vec::new(),
        }
    }

    pub fn num_keys(&self) -> usize {
        self.index.len() - 1
    }

    pub fn num_values(&self) -> usize {
        self.values.len()
    }

    pub fn values<Q: Into<usize>>(&self, key: Q) -> &[T] {
        let key: usize = key.into();
        let start = self.index[key];
        let end = self.index[key + 1];
        &self.values[start..end]
    }

    #[allow(dead_code)]
    pub fn values_mut(&mut self, key: usize) -> &[T] {
        let start = self.index[key];
        let end = self.index[key + 1];
        &mut self.values[start..end]
    }

    pub fn values_range<Q: Into<usize>>(&self, key: Q) -> Range<usize> {
        let key: usize = key.into();
        self.index[key]..self.index[key + 1]
    }

    #[allow(dead_code)]
    pub fn all_values(&self) -> &[T] {
        &self.values
    }

    pub fn value(&self, value_index: usize) -> &T {
        &self.values[value_index]
    }

    #[allow(dead_code)]
    pub fn value_mut(&mut self, value_index: usize) -> &mut T {
        &mut self.values[value_index]
    }

    pub fn iter_sets(&self) -> impl Iterator<Item = (usize, &[T])> {
        self.index
            .windows(2)
            .map(move |w| &self.values[w[0]..w[1]])
            .enumerate()
    }

    pub fn iter_entries_mut(&mut self) -> impl Iterator<Item = &mut [T]> {
        // We can't just use self.index.windows(2).map(...) for this.
        // We have to implement this iterator manually. Fortunately it's
        // a fairly elegant iterator.

        struct EntriesMut<'a, T> {
            last_end: usize,
            ends: core::slice::Iter<'a, usize>,
            values: &'a mut [T],
        }
        impl<'a, T> Iterator for EntriesMut<'a, T> {
            type Item = &'a mut [T];
            fn next(&mut self) -> Option<Self::Item> {
                let end = *self.ends.next()?;
                let len = end - self.last_end;
                self.last_end = end;
                let (low, high) = std::mem::replace(&mut self.values, &mut []).split_at_mut(len);
                self.values = high;
                Some(low)
            }
        }

        let mut ends = self.index.iter();
        let last_end = *ends.next().unwrap();
        EntriesMut {
            last_end,
            ends,
            values: &mut self.values,
        }
    }

    /// Iterates &[T], one for each key in the table.
    pub fn iter_entries(&self) -> impl Iterator<Item = &[T]> {
        self.index.windows(2).map(move |w| &self.values[w[0]..w[1]])
    }

    /// Use like this:
    ///
    ///   rt.push_value(...);
    ///   rt.push_value(...);
    ///   rt.push_value(...);
    ///   rt.finish_key();
    pub fn push_value(&mut self, value: T) {
        self.values.push(value);
    }

    pub fn finish_key(&mut self) {
        let end = self.values.len();
        self.index.push(end);
    }

    pub fn push_entry(&mut self, iter: impl Iterator<Item = T>) {
        self.values.extend(iter);
        self.finish_key();
    }

    pub fn push_entry_copy_slice(&mut self, values: &[T])
    where
        T: Copy,
    {
        self.values.extend(values);
        self.finish_key();
    }
}
