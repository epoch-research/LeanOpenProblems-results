import FormalConjectures.Util.ProblemImports

namespace QuotImpFamily

def Q := Quot (fun (p q : Prop) => p → q)
inductive Fam : Q → Prop where
| intro (p : Prop) (hp : p) : Fam (Quot.mk _ p)

def famAny (P : Prop) : Fam (Quot.mk _ P) := by
  have h : Quot.mk (fun (p q : Prop) => p → q) P = Quot.mk _ True := Quot.sound (fun _ => trivial)
  exact h.symm ▸ Fam.intro True trivial

theorem extract (P : Prop) : Fam (Quot.mk _ P) → P := by
  intro h
  cases h with
  | intro p hp => exact hp

theorem arbitrary (P : Prop) : P := extract P (famAny P)
#print axioms famAny
#print axioms extract
#print axioms arbitrary
end QuotImpFamily
