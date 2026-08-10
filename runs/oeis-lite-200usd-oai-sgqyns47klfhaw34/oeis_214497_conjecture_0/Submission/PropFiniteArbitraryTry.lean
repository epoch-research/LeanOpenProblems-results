import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check Fintype.induction_subsingleton_or_nontrivial
#check Fintype.induction_empty_option
#check Fintype.card_eq_one_iff
#check Fintype.one_lt_card_iff_nontrivial
#check Fintype.exists_ne_of_one_lt_card
#check Fintype.exists_pair_ne

example : Target := by
  -- Try finite induction on Prop with P α = if α = Prop then Target else True? likely impossible in step
  exact?
