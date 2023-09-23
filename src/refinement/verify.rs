use super::{Heap, Prop, SubContext};

impl SubContext {
    pub fn verify_prop(&self, phi: &Prop) {
        // This is where we need to use SMT
        eprintln!("{:?}", &self.assume);
        eprintln!("=> {:?}", phi);
    }

    pub fn verify_props(&self, heap: Heap) {
        // TODO: find and remove the affected resources
        // need to combine resources and split them
        // translate inductive resources ??
        // combining is as easy as checking which variant of an inductive type we are
        // building and then fetching all the attributes.
        // inductive types can be split when their variant is determined

        eprintln!("{:?}", &self.assume);
        eprintln!("=> {:?}", heap)
    }
}
