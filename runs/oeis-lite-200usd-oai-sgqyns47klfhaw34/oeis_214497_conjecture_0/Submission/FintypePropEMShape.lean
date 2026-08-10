import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
abbrev NegTarget : Prop := ¬ Target

example : Target ∨ NegTarget := by
  classical exact em Target

-- The finite enumeration route gives only excluded middle, not either side.
example : Target ∨ NegTarget := by
  have hm : Target ∈ (Fintype.elems : Finset Prop) := Fintype.complete Target
  -- `Fintype.elems : Finset Prop` is definitionally the two propositions.
  simpa [NegTarget] using hm

example : ¬ ((Target ∨ NegTarget) → Target) := by
  intro h
  -- instantiate the tautology with a false proposition shape via a local analogue
  have bad : False := h (Or.inr (fun hf : False => hf))
  exact bad
