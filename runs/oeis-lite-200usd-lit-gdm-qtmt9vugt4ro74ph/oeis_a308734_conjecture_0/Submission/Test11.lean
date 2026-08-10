import FormalConjectures.Util.ProblemImports

inductive Bad : Prop
  | mk : (∀ (α : Prop), (α → False) → Bad) → Bad

def unmk : Bad → ∀ (α : Prop), (α → False) → Bad
  | .mk f => f

noncomputable def f (α : Prop) (h : α → False) : Bad :=
  if heq : α = Bad then
    let h_cast : Bad → False := heq ▸ h
    False.elim (h_cast (Bad.mk f))
  else
    Bad.mk f
