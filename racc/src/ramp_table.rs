use core::ops::Range;

#[derive(Clone, Debug)]
pub struct RampTable<T> {
    pub index: Vec<usize>,
    pub table: Vec<T>,
}

#[allow(dead_code)]
impl<T> RampTable<T> {
    pub fn new_empty() -> Self {
        Self {
            index: Vec::new(),
            table: Vec::new(),
        }
    }

    pub fn new() -> Self {
        Self {
            index: vec![0],
            table: Vec::new(),
        }
    }

    pub fn num_keys(&self) -> usize {
        self.index.len() - 1
    }

    pub fn num_values(&self) -> usize {
        self.table.len()
    }

    pub fn values<Q: Into<usize>>(&self, key: Q) -> &[T] {
        let key: usize = key.into();
        let start = self.index[key];
        let end = self.index[key + 1];
        &self.table[start..end]
    }

    pub fn values_mut(&mut self, key: usize) -> &[T] {
        let start = self.index[key];
        let end = self.index[key + 1];
        &mut self.table[start..end]
    }

    pub fn values_range<Q: Into<usize>>(&self, key: Q) -> Range<usize> {
        let key: usize = key.into();
        self.index[key]..self.index[key + 1]
    }

    pub fn all_values(&self) -> &[T] {
        &self.table
    }

    pub fn value(&self, value_index: usize) -> &T {
        &self.table[value_index]
    }

    pub fn value_mut(&mut self, value_index: usize) -> &mut T {
        &mut self.table[value_index]
    }

    pub fn iter_sets(&self) -> impl Iterator<Item = (usize, &[T])> {
        self.index
            .windows(2)
            .map(move |w| &self.table[w[0]..w[1]])
            .enumerate()
    }

    pub fn iter_entries_mut(&mut self) -> impl Iterator<Item = &mut [T]> {
        // We can't just use self.index.windows(2).map(...) for this.
        // We have to implement this iterator manually. Fortunately it's
        // a fairly elegant iterator.

        struct EntriesMut<'a, T> {
            last_end: usize,
            ends: core::slice::Iter<'a, usize>,
            table: &'a mut [T]
        }
        impl<'a, T> Iterator for EntriesMut<'a, T> {
            type Item = &'a mut [T];
            fn next(&mut self) -> Option<Self::Item> {
                let end = *self.ends.next()?;
                let len = end - self.last_end;
                self.last_end = end;
                let (low, high) = std::mem::replace(&mut self.table, &mut []).split_at_mut(len);
                self.table = high;
                Some(low)
            }
        }

        let mut ends = self.index.iter();
        let last_end = *ends.next().unwrap();
        EntriesMut {
            last_end,
            ends,
            table: &mut self.table
        }
    }

    /// Iterates &[T], one for each key in the table.
    pub fn iter_entries(&self) -> impl Iterator<Item = &[T]> {
        self.index.windows(2).map(move |w| &self.table[w[0]..w[1]])
    }

    /// Use like this:
    ///
    ///   rt.push_value(...);
    ///   rt.push_value(...);
    ///   rt.push_value(...);
    ///   rt.finish_key();
    pub fn push_value(&mut self, value: T) {
        self.table.push(value);
    }

    pub fn finish_key(&mut self) {
        let end = self.table.len();
        self.index.push(end);
    }

    pub fn push_entry(&mut self, iter: impl Iterator<Item = T>) {
        self.table.extend(iter);
        self.finish_key();
    }

    pub fn push_entry_copy_slice(&mut self, values: &[T]) where T: Copy {
        self.table.extend(values);
        self.finish_key();
    }
}

pub struct RampTableBuilder<T> {
    index: Vec<usize>,
    table: Vec<T>,
}

impl<T> RampTableBuilder<T> {
    pub fn new() -> Self {
        Self {
            index: Vec::new(),
            table: Vec::new(),
        }
    }

    pub fn with_capacity(keys: usize, values: usize) -> Self {
        Self {
            index: Vec::with_capacity(keys + 1),
            table: Vec::with_capacity(values),
        }
    }

    pub fn start_key(&mut self) {
        self.index.push(self.table.len());
    }

    pub fn push_value(&mut self, item: T) {
        self.table.push(item);
    }

    pub fn finish(mut self) -> RampTable<T> {
        let end = self.table.len();
        self.index.push(end);
        RampTable {
            index: self.index,
            table: self.table,
        }
    }
}
