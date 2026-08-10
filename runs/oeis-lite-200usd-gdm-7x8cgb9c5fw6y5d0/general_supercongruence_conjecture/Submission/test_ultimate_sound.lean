import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad True
| mk {α : Prop} : Bad ((α → False) → False) → Bad α

open Classical

noncomputable def f : (α : Prop) → Bad α → α
| _, Bad.base => True.intro
| _, @Bad.mk α' h =>
  let recurse := f ((α' → False) → False) h
  Classical.byContradiction recurse

-- Let's prove False using this!
-- We need to construct Bad False.
-- To do that, we start with Bad True.
-- We want to prove some equality between True and ((False → False) → False).
-- Let's define the steps:
theorem h1 : ((False → False) → False) = False := by
  have h_iff : ((False → False) → False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h (fun f => f)
    · intro f
      exact False.elim f
  exact propext h_iff

theorem h2 : True = ((True → False) → False) := by
  have h_iff : True ↔ ((True → False) → False) := by
    apply Iff.intro
    · intro _ h
      exact h True.intro
    · intro _
      exact True.intro
  exact propext h_iff

theorem h3 : ((True → False) → False) = ((False → False) → False) := by
  -- We know (True -> False) = False. Let's prove it.
  have h_not_true : (True → False) = False := by
    have h_iff : (True → False) ↔ False := by
      apply Iff.intro
      · intro h
        exact h True.intro
      · intro f
        exact False.elim f
    exact propext h_iff
  rw [h_not_true]

theorem h_eq : True = ((False → False) → False) := h2.trans h3

theorem false_proof : False := by
  have bad_true : Bad True := Bad.base
  -- Since True = ((False -> False) -> False)
  have bad_double_neg_false : Bad ((False → False) → False) := h_eq ▸ bad_true
  have bad_false : Bad False := Bad.mk bad_double_neg_false
  exact f False bad_false
