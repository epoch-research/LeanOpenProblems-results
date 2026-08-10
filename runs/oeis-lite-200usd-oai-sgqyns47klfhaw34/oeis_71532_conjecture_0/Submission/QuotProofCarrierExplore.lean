import FormalConjectures.Util.ProblemImports

namespace QuotProofCarrier

def Q := Quot (fun (_ _ : Prop) => True)

inductive I : Q → Type where
| c (p : Prop) (hp : p) : I (Quot.mk _ p)

def iAny (P : Prop) : I (Quot.mk _ P) := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True) = Quot.mk _ P := Quot.sound trivial
  exact hq ▸ I.c True trivial

-- Try extraction by cases.
def extract1 (P : Prop) (i : I (Quot.mk _ P)) : P := by
  cases i with
  | c p hp =>
      -- context may include equality Quot.mk p = Quot.mk P but not p=P
      exact hp

-- Try quotient induction on P? no.
example (P : Prop) : P := extract1 P (iAny P)

#print axioms iAny
#print axioms extract1
end QuotProofCarrier
