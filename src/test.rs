struct BKind;
struct CKind;

trait RingWithIdentity {
    type Which;
}

trait EuclideanRing: RingWithIdentity {
    fn bar(&self) -> u32;
}
trait PartialInts {}
trait Field {}

pub struct PartialInt32();

impl RingWithIdentity for PartialInt32 {
    type Which = BKind;
}
impl PartialInts for PartialInt32 {}

pub struct Field7();

impl RingWithIdentity for Field7 {
    type Which = CKind;
}
impl Field for Field7 {}

//////////////////////

impl<T, Kind> EuclideanRing for T
where
    T: RingWithIdentity<Which = Kind>,
    T: EuclideanRingImpl<Kind>,
{
    fn bar(&self) -> u32 {
        EuclideanRingImpl::impl_bar(self)
    }
}

trait EuclideanRingImpl<Kind> {
    fn impl_bar(&self) -> u32;
}

impl<T: PartialInts> EuclideanRingImpl<BKind> for T {
    fn impl_bar(&self) -> u32 {
        1
    }
}

impl<T: Field> EuclideanRingImpl<CKind> for T {
    fn impl_bar(&self) -> u32 {
        2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn main() {
        assert_eq!(PartialInt32().bar(), 1);
        assert_eq!(Field7().bar(), 2);
    }
}
