import FormalConjectures.Util.ProblemImports

namespace QuotMatchExplore

def Q := Quot (fun (_ _ : Prop) => True)

def F (q : Q) : Prop :=
  match q with
  | Quot.mk p => p

example (P : Prop) : P := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True) = Quot.mk _ P := Quot.sound trivial
  change F (Quot.mk _ P)
  exact hq ▸ (show F (Quot.mk _ True) from trivial)

end QuotMatchExplore
