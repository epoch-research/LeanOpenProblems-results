import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def MyType (n : ℕ) :=
  PLift (a_test n ≠ 4) ⊕ (PLift (a_test n = 4) × (PLift (a_test (n - 1) = 4) ⊕ ((PLift (a_test (n - 1) = 4) → PLift False) → PLift False)))

noncomputable instance (n : ℕ) : Nonempty (MyType n) := by
  by_cases h : a_test n = 4
  · have h_prev : PLift (a_test (n - 1) = 4) ⊕ ((PLift (a_test (n - 1) = 4) → PLift False) → PLift False) := by
      by_cases h2 : a_test (n - 1) = 4
      · exact .inl ⟨h2⟩
      · exact .inr (fun f => f ⟨h2⟩)
    exact ⟨.inr (⟨h⟩, h_prev)⟩
  · exact ⟨.inl ⟨h⟩⟩

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
      rcases val.2 with val_eq | f_false
      · exact (ih_prev val_eq.down).elim
      · have h_arg : PLift (a_test k = 4) → PLift False := by
          intro h_eq
          exact ⟨(ih_prev h_eq.down).elim⟩
        exact (f_false h_arg).down.elim
