import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def MyType : ℕ → Type
  | 0 => PLift (a_test 0 = 4) → PLift False
  | n + 1 => PLift (a_test (n + 1) ≠ 4) ⊕ PLift (a_test (n + 1) = 4) × (PLift (a_test (n + 1) = 4) → MyType n)

noncomputable def MyType_nonempty (n : ℕ) : Nonempty (MyType n) := by
  induction n with
  | zero =>
    have h : a_test 0 ≠ 4 := by decide
    exact ⟨fun h_eq => ⟨(h h_eq.down).elim⟩⟩
  | succ n ih =>
    by_cases h : a_test (n + 1) = 4
    · have ih_val := Classical.choice ih
      exact ⟨.inr (⟨h⟩, fun _ => ih_val)⟩
    · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MyType n) := MyType_nonempty n

partial def get_sum (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MyType n :=
  match n with
  | 0 => fun h_eq => ⟨(ih 0 (by omega) h_eq.down).elim⟩
  | k + 1 =>
    have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
    match get_sum k ih_prev with
    | .inl _ => get_sum (k + 1) ih
    | .inr val => (ih k (by omega) val.1.down).elim

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    -- k is n - 1, and we have ih k (by omega) : a_test k ≠ 4
    have p := get_sum (k + 1) ih
    cases p with
    | inl val => exact val.down
    | inr val =>
      -- val.1 : PLift (a_test (k + 1) = 4)
      -- val.2 : PLift (a_test (k + 1) = 4) → MyType k
      -- We want to prove a_test (k + 1) ≠ 4.
      -- So let's apply val.2 to val.1!
      have hk := val.2 val.1
      -- hk has type MyType k!
      -- Since k = j + 1 (or k = 0):
      -- If k = 0: hk has type MyType 0 = PLift (a_test 0 = 4) → PLift False.
      --   Wait, we don't get a contradiction.
      -- If k = j + 1: hk has type MyType (j + 1) = PLift (a_test k ≠ 4) ⊕ PLift (a_test k = 4) × (PLift (a_test k = 4) → MyType j).
      --   If we match on hk:
      --   - Case .inl val_ne: consistent.
      --   - Case .inr val_eq_pair: val_eq_pair.1 has type PLift (a_test k = 4).
      --     This contradicts ih k (by omega) : a_test k ≠ 4!
      --     So we get False!
      sorry
