import FormalConjectures.Util.ProblemImports

namespace QIdx

def Q := Quot (fun (_ _ : Prop) => True)

inductive Fam : Q → Prop where
| intro : Fam (Quot.mk _ True)

theorem fam_any (P : Prop) : Fam (Quot.mk _ P) := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True) = Quot.mk _ P := Quot.sound trivial
  exact hq ▸ Fam.intro

-- Can we get P from Fam (mk P)?
theorem out? (P : Prop) : Fam (Quot.mk _ P) → P := by
  intro h
  cases h with
  | intro =>
      -- goal becomes P? or True?
      trivial

example (P : Prop) : P := out? P (fam_any P)
#print axioms fam_any
#print axioms out?
end QIdx
