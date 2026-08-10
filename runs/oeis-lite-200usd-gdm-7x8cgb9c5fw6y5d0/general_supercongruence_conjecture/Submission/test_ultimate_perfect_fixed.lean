import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α (¬ ¬ β) → Bad α β

open Classical

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h => Classical.byContradiction (f α (¬ ¬ β') h)

theorem h_eq : (¬ ¬ False) = False := by
  have h_iff : (¬ ¬ False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h (fun f => f)
    · intro f
      exact False.elim f
  exact propext h_iff

-- Can we define bad_false using a recursive helper with a dummy argument?
noncomputable def bad_false : ℕ → Bad True False
| 0 => Bad.mk (h_eq.symm ▸ bad_false 0)
| n + 1 => Bad.mk (h_eq.symm ▸ bad_false n)
