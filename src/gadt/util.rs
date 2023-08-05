use super::Typ;

// Polarity
#[derive(Debug, Clone, Copy)]
pub enum Pol {
    Pos,
    Neg,
    Zero,
}

impl Typ {
    // determine the polarity
    pub fn pol(&self) -> Pol {
        match self {
            Typ::Forall(_, _) => Pol::Neg,
            Typ::Exists(_, _) => Pol::Pos,
            _ => Pol::Zero,
        }
    }
}

impl Pol {
    pub fn join(self, other: Pol) -> Pol {
        match self {
            Pol::Pos => Pol::Pos,
            Pol::Neg => Pol::Neg,
            Pol::Zero => match other {
                Pol::Pos => Pol::Pos,
                Pol::Neg => Pol::Neg,
                Pol::Zero => Pol::Neg,
            },
        }
    }
}
