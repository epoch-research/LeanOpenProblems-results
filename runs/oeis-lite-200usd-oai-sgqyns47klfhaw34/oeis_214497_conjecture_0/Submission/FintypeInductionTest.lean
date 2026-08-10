import FormalConjectures.Util.ProblemImports
#check Fintype.induction_empty_option
#check Fintype.induction
#check Fintype.induction_subsingleton_or_nontrivial

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target := by
  -- try instantiate P constantly Target in finite induction over Prop or Empty
  let P : ∀ (α : Type) [Fintype α], Prop := fun _ _ => Target
  apply Fintype.induction_empty_option (P := P)
  · -- empty case
    exact?
  · intro α inst ih
    exact ih

example : Target := by
  -- if induction reduces to finite chain starting at Empty, constant target still needs base
  exact?
