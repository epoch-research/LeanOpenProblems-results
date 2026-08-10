import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α (¬ ¬ β) → Bad α β

open Classical

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h => Classical.byContradiction (f α (¬ ¬ β') h)

theorem false_proof : False := by
  have bad_true : Bad True True := Bad.base True.intro
  have bad_false : Bad True False := @Bad.mk True False (by
    -- we need Bad True (¬ ¬ False)
    -- ¬ ¬ False is False. So we need Bad True False.
    -- Loop?
    sorry
  )
  exact f True False bad_false

#print axioms false_proof

#print axioms false_proof
