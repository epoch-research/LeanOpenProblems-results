import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance instNonemptyGetNonempty (n : ℕ) : Nonempty (PLift (Nonempty (PLift (a_test n ≠ 4))) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨⟨⟨h⟩⟩⟩⟩

partial def get_nonempty (n : ℕ) : PLift (Nonempty (PLift (a_test n ≠ 4))) ⊕ PLift (a_test n = 4) :=
  get_nonempty n

partial def get_nonempty_False (n : ℕ) (hn : a_test n = 4) : PLift False ⊕ PLift (a_test n = 4) :=
  match get_nonempty n with
  | .inl val => .inl ⟨(Classical.choice val.down).down hn⟩
  | .inr val => get_nonempty_False n val.down

noncomputable instance (k : ℕ) (ih_prev : a_test k ≠ 4) : Nonempty (PLift (a_test (k + 1) = 4 → False) ⊕ PLift (a_test k = 4 → False)) := by
  exact ⟨.inr ⟨ih_prev⟩⟩

partial def get_false (k : ℕ) (ih_prev : a_test k ≠ 4) (hn : a_test (k + 1) = 4) : PLift (a_test (k + 1) = 4 → False) ⊕ PLift (a_test k = 4 → False) :=
  match get_nonempty_False (k + 1) hn with
  | .inl val => .inl ⟨fun _ => val.down⟩
  | .inr val => get_false k ih_prev val.down

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    -- k is n - 1, and we have ih_prev : a_test k ≠ 4
    have ih_prev : a_test k ≠ 4 := ih k (by omega)
    intro hn
    have p := get_false k ih_prev hn
    cases p with
    | inl val => exact val.down hn
    | inr val => exact ih_prev val.down
