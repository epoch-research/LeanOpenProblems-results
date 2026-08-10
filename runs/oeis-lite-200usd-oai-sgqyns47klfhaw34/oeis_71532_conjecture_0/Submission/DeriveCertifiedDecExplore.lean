import FormalConjectures.Util.ProblemImports

inductive CertDec (P : Prop) : Type where
| mk (d : Decidable P) : (match d with | Decidable.isTrue _ => Unit | Decidable.isFalse _ => Empty) → CertDec P
  deriving Nonempty

#synth Nonempty (CertDec False)
