use super::{fixed_size, is_basic, is_compatible, validate, TypeDescriptor as D};
use crate::error::CodecError as E;

mod compatibility;
mod reference;
mod reference_cases;
mod validation;
mod widths;

const BYTE: D = D::Uint(1);
const BOOL: D = D::Boolean;
const BAD: D = D::Uint(3);
const VARIABLE: D = D::ByteList(0);
const OVERFLOW: D = D::Vector(&D::Uint(usize::MAX), 2);

fn compatible(left: &D, right: &D, expected: bool) {
    assert_eq!(is_compatible(left, right), expected, "{left:?}, {right:?}");
    assert_eq!(is_compatible(right, left), expected, "symmetry");
}
