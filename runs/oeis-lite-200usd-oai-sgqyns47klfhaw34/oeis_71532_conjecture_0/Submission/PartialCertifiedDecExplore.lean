import FormalConjectures.Util.ProblemImports

inductive CertDec (P : Prop) : Type where
| mk (d : Decidable P) : (match d with | Decidable.isTrue _ => Unit | Decidable.isFalse _ => Empty) → CertDec P

partial def cert (P : Prop) : CertDec P := cert P

def extract (P : Prop) (c : CertDec P) : P := by
  cases c with
  | mk d certif =>
      cases d with
      | isTrue hp => exact hp
      | isFalse hn => cases certif

theorem arbitrary (P : Prop) : P := extract P (cert P)
#print axioms arbitrary
