import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def MyType (n : ℕ) :=
  PLift (a_test n ≠ 4) ⊕ (PLift (a_test n = 4) × (PLift (a_test n ≠ 4) → PLift False) × (PLift (a_test (n - 1) = 4) ⊕ PLift (a_test (n - 1) ≠ 4 → False)))

noncomputable instance (n : ℕ) : Nonempty (MyType n) := by
  by_cases h : a_test n = 4
  · -- inr is nonempty
    have h_fn : PLift (a_test n ≠ 4) → PLift False := by
      intro h_ne
      exact ⟨h_ne.down h⟩
    have h_prev : PLift (a_test (n - 1) = 4) ⊕ PLift (a_test (n - 1) ≠ 4 → False) := by
      by_cases h2 : a_test (n - 1) = 4
      · exact .inl ⟨h2⟩
      · exact .inr ⟨h2⟩
    exact ⟨.inr (⟨h⟩, h_fn, h_prev)⟩
  · -- inl is nonempty
    exact ⟨.inl ⟨h⟩⟩

partial def get_proof (n : ℕ) : MyType n :=
  get_proof n

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    have ih_prev : a_test k ≠ 4 := ih k (by omega)
    have p := get_proof (k + 1)
    cases p with
    | inl val => exact val.down
    | inr val =>
      rcases val.2.2 with val_eq | val_false
      · -- val_eq has type PLift (a_test (k + 1 - 1) = 4), which is PLift (a_test k = 4)
        exact (ih_prev val_eq.down).elim
      · -- val_false has type PLift (a_test (k + 1 - 1) ≠ 4 → False), which is PLift (a_test k ≠ 4 → False)
        exact (val_false.down ih_prev).elim
