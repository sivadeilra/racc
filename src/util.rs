use std::num::Int;

pub const BITS_PER_WORD: uint = 32;

// An M x N matrix of bits
// The representation is in row-major form.
// The representation is exposed.
pub struct Bitmat
{
	pub data: Vec<u32>,			// contains all bits in matrix, in row-major form, with padding at end of row
	pub rows: uint,				// number of rows
	pub cols: uint,				// number of columns
	pub rowsize: uint			// number of u32 elements per row
}

impl Bitmat
{
	pub fn new(rows: uint, cols: uint) -> Bitmat
	{
		let rowsize = word_size(cols);
		let total = rowsize * rows;
		Bitmat {
			data: Vec::from_elem(total, 0),
			rows: rows, cols: cols, rowsize: rowsize
		}
	}

	// note: bit() and set_bit() are carried over from the C definitions
	// 'r' is an index directly into self.data for a particular row, and
	// so it does not need to be multipled by rowsize.

    // note: r is a word index, not a bit/row index, for the start of a row
/*
	pub fn bit(&self, r: uint, n: uint) -> bool {
    	(((self.data[r + (n >> 5)]) >> (n & 31)) & 1u32) != 0
	}
*/

/*
    // note: r is a word index, not a bit/row index, for the start of a row
	pub fn set_bit(&mut self, r: uint, c: uint) {
        assert!(r < self.rows * self.rowsize);
        assert!(c < self.cols);
    	self.data[r + (c >> 5)] |= 1u32 << (c & 31);
	}
*/

    // sets an entry to 1, given a row/column index.
    // note that r and c are row and column indices, not word offsets.
    pub fn set(&mut self, r: uint, c: uint) {
        assert!(r < self.rows);
        assert!(c < self.cols);
        self.data[r * self.rowsize + (c >> 5)] |= 1u32 << (c & 31);
    }

    pub fn get(&self, r: uint, c: uint) -> bool {
        assert!(r < self.rows);
        assert!(c < self.cols);
        (self.data[r * self.rowsize + (c >> 5)] & (1u32 << (c & 31))) != 0u32
    }

    // note: r is a row index, not a word index, for identifying a row.
    // This method returns an iterator which gives the positions of all
    // columns within a particular row 'r' where the row/col = 1.
    pub fn iter_ones_in_row<'a>(&'a self, r: uint) -> BitMaskIterator<'a> {
        assert!(r < self.rows);
        // debug!("Bitmat.iter_ones_in_row: rows={} cols={} rowsize={} r={} (rowsize * r)={}", self.rows, self.cols, self.rowsize, r, self.rowsize * r);
        let rpos = self.rowsize * r;
        bit_vector_iter_ones(self.data.slice(rpos, rpos + self.rowsize), self.cols)
    }

    // Performs a row-major scan for bits that are set to one, and enumerates (row,col) items.
    pub fn iter_ones<'a>(&'a self) -> BitmatIterOnes<'a> {
        BitmatIterOnes {
            row: 0,
            col: 0,
            current: 0,
            xormask: 0,
            mat: self
        }
    }
}

pub struct BitmatIterOnes<'a>
{
    row: uint,          // index of current row
    col: uint,          // index of current col
    current: u32,       // contents of current word
    xormask: u32,       // xor mask used when loading current, used to select true/false
    mat: &'a Bitmat
}

impl<'a> Iterator<(uint, uint)> for BitmatIterOnes<'a> {
    // This could be made faster with a "find first set bit" intrinsic.
    fn next(&mut self) -> Option<(uint, uint)> {
        const LOW_MASK: uint = (1 << BITS_PER_WORD) - 1;

        loop { // loop over rows
            while self.col < self.mat.cols { // loop over columns
                // Are we at a word boundary?  If so, we need to load 'current'.
                let nextbit = self.col & LOW_MASK;
                if nextbit == 0 {
                    // Load another word of data.
                    self.current = self.mat.data[self.row * self.mat.rowsize + self.col / BITS_PER_WORD] ^ self.xormask;

                    // Fast path.  Step over entire words, if they are empty.
                    if self.col + BITS_PER_WORD <= self.mat.cols && self.current == 0 {
                        self.col += BITS_PER_WORD;
                        continue;
                    }
                }

                let oldcol = self.col;
                self.col += 1;
                if ((self.current >> nextbit) & 1) != 0 {
                    return Some((self.row, oldcol));
                }
            }

            // reached the end of one row.  check to see if there are more rows.
            if self.row + 1 == self.mat.rows {
                // No more columns, no more rows.  Do not change state.
                return None;
            }
            // Yes, we have more rows.  Reset column.
            self.col = 0;
            self.row += 1;
        }
    }
}

pub fn word_size(n: uint) -> uint
{
    (n + (BITS_PER_WORD - 1)) / BITS_PER_WORD
}

pub struct BitMaskIterator<'a>
{
    words: &'a [u32],
    current: u32,       // contains the bits that we are currently reading
    xormask: u32,       // xor mask used when loading current, used to select true/false
    nbits: uint,        // number of bits remaining in entire sequence
    bitpos: uint,       // current bit position
}

impl<'a> Iterator<uint> for BitMaskIterator<'a>
{
    // This could be made faster with a "find first set bit" intrinsic.
    fn next(&mut self) -> Option<uint> {
        const LOW_MASK: uint = (1 << BITS_PER_WORD) - 1;

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
            if ((self.current >> nextbit) & 1) != 0 {
                return Some(cpos);
            }
        }

        None
    }
}

/// Iterates the indices of all of the bits set to 1 in a given bit vector.
pub fn bit_vector_iter_ones<'a>(words: &'a [u32], nbits: uint) -> BitMaskIterator<'a> {
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
    pub nbits: uint
}

impl Bitv32 {
    pub fn from_elem(n: uint, value: bool) -> Bitv32 {
        let w = if value { !0u32 } else { 0u32 };
        let nwords = (n + BITS_PER_WORD - 1) / BITS_PER_WORD;
        Bitv32 {
            data: Vec::from_elem(nwords, w),
            nbits: n
        }
    }

    pub fn set_all(&mut self, value: bool) {
        let w = if value { 0u32 } else { 0u32 };
        for i in self.data.iter_mut() {
            *i = w;
        }
    }

    pub fn iter_ones<'a>(&'a self) -> BitMaskIterator<'a> {
        bit_vector_iter_ones(self.data.as_slice(), self.nbits)
    }
}

pub struct ReverseRange<A:Int> {
    state: A,
    stop: A,
    one: A,
}

pub fn reverse_range<A:Int>(start: A, stop: A) -> ReverseRange<A> {
    ReverseRange {
        state: start,
        stop: stop,
        one: Int::one(),
    }
}

impl<A:Int> Iterator<A> for ReverseRange<A> {
    fn next(&mut self) -> Option<A> {
        if self.state > self.stop {
            self.state = self.state - self.one;
            Some(self.state)
        }
        else {
            None
        }
    }
}


