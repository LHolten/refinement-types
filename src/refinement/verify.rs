use std::rc::Rc;

use super::{Prop, SubContext};

impl SubContext {
    pub fn verify_prop(&self, phi: &Prop) {
        // This is where we need to use SMT
        eprintln!("{:?}", &self.assume);
        eprintln!("=> {:?}", phi);
    }

    pub fn verify_props(&self, props: Vec<Rc<Prop>>) {
        eprintln!("{:?}", &self.assume);
        eprintln!("=> {:?}", props)
    }
}
