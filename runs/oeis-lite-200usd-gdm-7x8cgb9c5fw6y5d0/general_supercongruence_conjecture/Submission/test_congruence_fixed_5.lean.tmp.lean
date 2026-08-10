import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk {β : Prop} : Bad α ((β → False) → False) → Bad α (β → False)

open Classical

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h =>
  let recurse := f α ((β' → False) → False) h
  Classical.byContradiction recurse

theorem false_proof : False := by
  have bad_true : Bad True True := Bad.base True.intro
  have bad_false : Bad True False := @Bad.mk True True bad_true
  have f_res : False := f True False bad_false
  exact f_res

#print axioms false_proof
