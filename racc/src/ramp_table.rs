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

    pub fn values(&self, key: usize) -> &[T] {
        let start = self.index[key];
        let end = self.index[key + 1];
        &self.table[start..end]
    }

    pub fn values_mut(&mut self, key: usize) -> &[T] {
        let start = self.index[key];
        let end = self.index[key + 1];
        &mut self.table[start..end]
    }

    pub fn values_range(&self, key: usize) -> Range<usize> {
        self.index[key]..self.index[key + 1]
    }

    pub fn all_values(&self) -> &[T] {
        &self.table
    }

    pub fn iter_sets(&self) -> impl Iterator<Item = (usize, &[T])> {
        self.index
            .windows(2)
            .map(move |w| &self.table[w[0]..w[1]])
            .enumerate()
    }

    /// Iterates &[T], one for each key in the table.
    pub fn iter_values(&self) -> impl Iterator<Item = &[T]> {
        self.index.windows(2).map(move |w| &self.table[w[0]..w[1]])
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
            table: Vec::with_capacity(values)
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
