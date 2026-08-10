import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyType (n : ℕ) where
  | inl (val : PLift (a_test n ≠ 4))
  | inr (val : PLift (a_test n = 4)) (next : MyType (n - 1))

noncomputable def MyType_nonempty (n : ℕ) : Nonempty (MyType n) := by
  induction n with
  | zero =>
    have h : a_test 0 ≠ 4 := by decide
    exact ⟨.inl ⟨h⟩⟩
  | succ n ih =>
    by_cases h : a_test (n + 1) = 4
    · have ih_val := Classical.choice ih
      exact ⟨.inr ⟨h⟩ ih_val⟩
    · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MyType n) := MyType_nonempty n

partial def get_sum (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MyType n :=
  match n with
  | 0 => .inl ⟨by decide⟩
  | k + 1 =>
    have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
    match get_sum k ih_prev with
    | .inl _ => get_sum (k + 1) ih
    | .inr val next_val => (ih k (by omega) val.down).elim

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    have p := get_sum (k + 1) ih
    cases p with
    | inl val => exact val.down
    | inr val next_val =>
      -- val : PLift (a_test (k + 1) = 4)
      -- next_val : MyType k
      cases next_val with
      | inl val_ne =>
        -- val_ne has type PLift (a_test k ≠ 4).
        -- wait, how do we get a contradiction?
        -- Oh, we have ih k (by omega) : a_test k ≠ 4.
        -- Still no contradiction.
        sorry
      | inr val_eq next_val2 =>
        -- val_eq has type PLift (a_test k = 4).
        -- contradicts ih_prev!
        exact (ih k (by omega) val_eq.down).elim
