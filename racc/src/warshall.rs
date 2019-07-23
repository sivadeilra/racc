use crate::util::Bitmat;
use crate::util::BITS_PER_WORD;

fn transitive_closure(r: &mut Bitmat) {
    let relend = r.rows * r.rowsize;

    let mut cword: usize = 0;
    let mut i: usize = 0;
    let mut rowi: usize = 0;

    while rowi < relend {
        let mut ccol = cword;
        let mut rowj: usize = 0;

        assert_eq!(rowi % BITS_PER_WORD, i);
        assert_eq!(rowi / BITS_PER_WORD, cword);

        while rowj < relend {
            if (r.data[ccol] & (1 << i)) != 0 {
                let mut rp = rowi;
                let rend = rowj + r.rowsize;
                while rowj < rend {
                    r.data[rowj] |= r.data[rp];
                    rowj += 1;
                    rp += 1;
                }
            } else {
                rowj += r.rowsize;
            }

            ccol += r.rowsize;
        }

        i += 1;
        if i >= BITS_PER_WORD {
            i = 0;
            cword += 1;
        }

        rowi += r.rowsize;
    }
}

pub fn reflexive_transitive_closure(r: &mut Bitmat) {
    assert!(r.rows == r.cols);

    transitive_closure(r);

    // set diagonals
    for i in 0..r.rows {
        r.set(i, i);
    }
}
