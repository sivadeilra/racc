use core::iter::repeat;
use core::sync::atomic::{AtomicU64, Ordering::SeqCst};
use log::trace;

pub const BITS_PER_WORD: usize = 32;

static NEXT_BITMAT_ID: AtomicU64 = AtomicU64::new(1);

// An M x N matrix of bits
// The representation is in row-major form.
// The representation is exposed.
#[derive(Clone)]
pub struct Bitmat {
    // Contains all bits in matrix, in row-major form, with padding at end of row
    pub data: Vec<u32>,
    // Number of rows
    pub rows: usize,
    // Number of columns
    pub cols: usize,
    // Number of u32 elements per row
    pub rowsize: usize,

    id: u64,
}

impl Bitmat {
    pub fn new(rows: usize, cols: usize) -> Bitmat {
        let id = NEXT_BITMAT_ID.fetch_add(1, SeqCst);
        trace!("(bitmat {}) new: rows {} cols {}", id, rows, cols);
        let rowsize = word_size(cols);
        let total = rowsize * rows;
        Bitmat {
            data: vec![0; total],
            rows: rows,
            cols: cols,
            rowsize: rowsize,
            id,
        }
    }

    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn cols(&self) -> usize {
        self.cols
    }

    // note: bit() and set_bit() are carried over from the C definitions
    // 'r' is an index directly into self.data for a particular row, and
    // so it does not need to be multipled by rowsize.

    // note: r is a word index, not a bit/row index, for the start of a row
    /*
        pub fn bit(&self, r: usize, n: usize) -> bool {
            (((self.data[r + (n >> 5)]) >> (n & 31)) & 1u32) != 0
        }
    */

    /*
        // note: r is a word index, not a bit/row index, for the start of a row
        pub fn set_bit(&mut self, r: usize, c: usize) {
            assert!(r < self.rows * self.rowsize);
            assert!(c < self.cols);
            self.data[r + (c >> 5)] |= 1u32 << (c & 31);
        }
    */

    // sets an entry to 1, given a row/column index.
    // note that r and c are row and column indices, not word offsets.
    pub fn set(&mut self, r: usize, c: usize) {
        assert!(r < self.rows);
        assert!(c < self.cols);
        trace!("(bitmat {}): set: row {} col {}", self.id, r, c);
        self.data[r * self.rowsize + (c >> 5)] |= 1u32 << (c & 31);
    }

    pub fn get(&self, r: usize, c: usize) -> bool {
        assert!(r < self.rows);
        assert!(c < self.cols);
        trace!("get: data = {:x?}", self.data);
        (self.data[r * self.rowsize + (c >> 5)] & (1u32 << (c & 31))) != 0u32
    }

    // note: r is a row index, not a word index, for identifying a row.
    // This method returns an iterator which gives the positions of all
    // columns within a particular row 'r' where the row/col = 1.
    pub fn iter_ones_in_row<'a>(&'a self, r: usize) -> BitMaskIterator<'a> {
        assert!(r < self.rows);
        // debug!("Bitmat.iter_ones_in_row: rows={} cols={} rowsize={} r={} (rowsize * r)={}", self.rows, self.cols, self.rowsize, r, self.rowsize * r);
        let rpos = self.rowsize * r;
        bit_vector_iter_ones(&self.data[rpos..rpos + self.rowsize], self.cols)
    }

    // Performs a row-major scan for bits that are set to one, and enumerates (row,col) items.
    pub fn iter_ones<'a>(&'a self) -> BitmatIterOnes<'a> {
        BitmatIterOnes {
            row: 0,
            col: 0,
            current: 0,
            xormask: 0,
            mat: self,
        }
    }
}

pub struct BitmatIterOnes<'a> {
    /// index of current row
    row: usize,
    /// index of current col
    col: usize,
    /// contents of current word
    current: u32,
    /// xor mask used when loading current, used to select true/false
    xormask: u32,
    mat: &'a Bitmat,
}

impl<'a> Iterator for BitmatIterOnes<'a> {
    type Item = (usize, usize);
    // This could be made faster with a "find first set bit" intrinsic.
    fn next(&mut self) -> Option<(usize, usize)> {
        const LOW_MASK: usize = BITS_PER_WORD - 1;

        loop {
            // loop over rows
            while self.col < self.mat.cols {
                // loop over columns
                // Are we at a word boundary?  If so, we need to load 'current'.
                let nextbit = self.col & LOW_MASK;
                if nextbit == 0 {
                    // Load another word of data.
                    self.current = self.mat.data
                        [self.row * self.mat.rowsize + self.col / BITS_PER_WORD]
                        ^ self.xormask;

                    // Fast path.  Step over entire words, if they are empty.
                    if self.col + BITS_PER_WORD <= self.mat.cols && self.current == 0 {
                        self.col += BITS_PER_WORD;
                        continue;
                    }
                }

                let oldcol = self.col;
                self.col += 1;
                if ((self.current >> nextbit) & 1) != 0 {
                    trace!(
                        "(bitmat {}) found, row {}, col {}",
                        self.mat.id,
                        self.row,
                        oldcol
                    );
                    return Some((self.row, oldcol));
                }
            }

            // reached the end of one row.  check to see if there are more rows.
            if self.row + 1 == self.mat.rows {
                // No more columns, no more rows.  Do not change state.
                trace!("bitmat iter: none");
                return None;
            }
            // Yes, we have more rows.  Reset column.
            self.col = 0;
            self.row += 1;
        }
    }
}

pub fn word_size(n: usize) -> usize {
    (n + (BITS_PER_WORD - 1)) / BITS_PER_WORD
}

pub struct BitMaskIterator<'a> {
    words: &'a [u32],
    // contains the bits that we are currently reading
    current: u32,
    // xor mask used when loading current, used to select true/false
    xormask: u32,
    // number of bits remaining in entire sequence
    nbits: usize,
    // current bit position
    bitpos: usize,
}

impl<'a> Iterator for BitMaskIterator<'a> {
    type Item = usize;
    // This could be made faster with a "find first set bit" intrinsic.
    fn next(&mut self) -> Option<usize> {
        const LOW_MASK: usize = BITS_PER_WORD - 1;

        while self.bitpos < self.nbits {
            // Are we at a word boundary?  If so, we need to load 'current'.
            let nextbit = self.bitpos & LOW_MASK;
            if nextbit == 0 {
                // Load another word of data.
                self.current = self.words[self.bitpos / BITS_PER_WORD] ^ self.xormask;

                // Fast path.  Step over entire words, if they are empty.
                if self.bitpos + BITS_PER_WORD <= self.nbits && self.current == 0 {
                    self.bitpos += BITS_PER_WORD;
                    continue;
                }
            }

            let cpos = self.bitpos;
            self.bitpos += 1;
            assert!(
                nextbit < 32,
                "nextbit = {}, bitpos = {}, low_mask = {:#x}",
                nextbit,
                self.bitpos,
                LOW_MASK
            );
            if ((self.current >> nextbit) & 1) != 0 {
                return Some(cpos);
            }
        }

        None
    }
}

/// Iterates the indices of all of the bits set to 1 in a given bit vector.
pub fn bit_vector_iter_ones<'a>(words: &'a [u32], nbits: usize) -> BitMaskIterator<'a> {
    assert!(words.len() >= ((nbits + BITS_PER_WORD - 1) / BITS_PER_WORD));
    BitMaskIterator {
        words: words,
        current: 0,
        nbits: nbits,
        bitpos: 0,
        xormask: 0,
    }
}

pub struct Bitv32 {
    pub data: Vec<u32>,
    pub nbits: usize,
}

impl Bitv32 {
    pub fn from_elem(n: usize, value: bool) -> Bitv32 {
        let w = if value { !0u32 } else { 0u32 };
        let nwords = (n + BITS_PER_WORD - 1) / BITS_PER_WORD;
        Bitv32 {
            data: repeat(w).take(nwords).collect(),
            nbits: n,
        }
    }

    pub fn set_all(&mut self, value: bool) {
        let w = if value { !0u32 } else { 0u32 };
        for i in self.data.iter_mut() {
            *i = w;
        }
    }

    pub fn iter_ones<'a>(&'a self) -> BitMaskIterator<'a> {
        bit_vector_iter_ones(&self.data, self.nbits)
    }
}

pub fn fill_copy<T: Copy>(dst: &mut [T], value: T) {
    for ii in dst.iter_mut() {
        *ii = value;
    }
}

impl core::fmt::Debug for Bitmat {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        struct Values<'a>(&'a Bitmat);

        impl<'a> core::fmt::Debug for Values<'a> {
            fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if false {
                    let mut dl = fmt.debug_map();
                    let mut s = Vec::new();
                    for i in 0..self.0.rows {
                        s.clear();
                        for j in 0..self.0.cols {
                            if self.0.get(i, j) {
                                s.push(j);
                            }
                        }
                        if !s.is_empty() {
                            dl.entry(&i, &s);
                        }
                    }
                    dl.finish()
                } else {
                    let mut dl = fmt.debug_list();
                    for (i, j) in self.0.iter_ones() {
                        dl.entry(&(i, j));
                    }
                    dl.finish()
                }
            }
        }

        let mut b = fmt.debug_struct("Bitmat");
        b.field("rows", &self.rows);
        b.field("cols", &self.cols);
        b.field("values", &Values(self));
        b.finish()
    }
}
