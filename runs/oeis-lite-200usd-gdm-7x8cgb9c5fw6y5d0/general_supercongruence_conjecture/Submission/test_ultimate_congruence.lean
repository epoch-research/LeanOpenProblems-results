import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α (β → False) → Bad α β

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h => Classical.byContradiction (f α (β' → False) h)

theorem h_eq : (True → False) = False := by
  have h_iff : (True → False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h True.intro
    · intro h
      exact False.elim h
  exact propext h_iff

theorem false_proof : False := by
  have bad_true : Bad True True := Bad.base True.intro
  have bad_false : Bad True (True → False) := Bad.mk bad_true
  have bad_target : Bad True False := h_eq ▸ bad_false
  exact f True False bad_target
