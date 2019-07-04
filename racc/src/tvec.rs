#![allow(dead_code)]

use core::convert::TryFrom;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::marker::PhantomData;
use core::ops::Index;
use core::ops::IndexMut;

pub struct TVec<I, T> {
    vec: Vec<T>,
    phantom_i: PhantomData<I>,
}

impl<I, T> TVec<I, T> {
    pub fn new() -> Self {
        Self {
            vec: Vec::new(),
            phantom_i: PhantomData,
        }
    }

    pub fn push(&mut self, value: T) {
        self.vec.push(value);
    }

    pub fn vec(&self) -> &Vec<T> {
        &self.vec
    }

    pub fn vec_mut(&mut self) -> &mut Vec<T> {
        &mut self.vec
    }

    pub fn to_vec(self) -> Vec<T> {
        self.vec
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self {
            vec,
            phantom_i: PhantomData,
        }
    }
}

impl<I: Debug, T: Debug> core::fmt::Debug for TVec<I, T> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        self.vec.fmt(fmt)
    }
}

fn to_usize<I>(index: I) -> usize
where
    usize: TryFrom<I>,
{
    match usize::try_from(index) {
        Ok(v) => v,
        Err(_) => panic!("failed to convert index"),
    }
}

impl<I, T> Index<I> for TVec<I, T>
where
    usize: TryFrom<I>,
{
    type Output = T;
    fn index(&self, index: I) -> &T {
        let u = to_usize(index);
        &self.vec[u]
    }
}

impl<I, T> IndexMut<I> for TVec<I, T>
where
    usize: TryFrom<I>,
{
    fn index_mut(&mut self, index: I) -> &mut T {
        let u = to_usize(index);
        &mut self.vec[u]
    }
}
