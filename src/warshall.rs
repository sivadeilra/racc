use util::{BITS_PER_WORD};
use util::Bitmat;

fn transitive_closure(r: &mut Bitmat)
{
    let relend = r.rows * r.rowsize;

    let mut cword: uint = 0;
    let mut i: uint = 0;
    let mut rowi: uint = 0;

    while rowi < relend {
        let mut ccol = cword;
        let mut rowj: uint = 0;

        while rowj < relend {
            if (r.data[ccol] & (1 << i)) != 0 {
                let mut rp = rowi;
                let rend = rowj + r.rowsize;
                while rowj < rend {
                    r.data[rowj] |= r.data[rp];
                    rowj += 1;
                    rp += 1;
                }
            }
            else {
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

pub fn reflexive_transitive_closure(r: &mut Bitmat)
{
    assert!(r.rows == r.cols);

    transitive_closure(r);

    let relend = r.rows * r.rowsize;

    let mut i: uint = 0;
    let mut rp: uint = 0;
    
    while rp < relend {
        r.data[rp] |= 1 << i;
        i += 1;
        if i >= BITS_PER_WORD {
            i = 0;
            rp += 1;
        }

        rp += r.rowsize;
    }
}
