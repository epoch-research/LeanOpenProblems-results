import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MyType : ℕ → Type where
  | inl (n : ℕ) (val : PLift (a_test n ≠ 4)) : MyType n
  | inr (n : ℕ) (val : PLift (a_test n = 4)) (next : MyType (n - 1)) : MyType n

noncomputable def MyType_nonempty : (n : ℕ) → Nonempty (MyType n)
  | 0 => by
    have h : a_test 0 ≠ 4 := by decide
    exact ⟨.inl 0 ⟨h⟩⟩
  | n + 1 => by
    by_cases h : a_test (n + 1) = 4
    · have ih_val := MyType_nonempty n
      have ih_elem := Classical.choice ih_val
      have h_eq : n + 1 - 1 = n := by omega
      have ih_elem_casted : MyType (n + 1 - 1) := h_eq.symm ▸ ih_elem
      exact ⟨.inr (n + 1) ⟨h⟩ ih_elem_casted⟩
    · exact ⟨.inl (n + 1) ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MyType n) := MyType_nonempty n

partial def get_sum (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MyType n :=
  match n with
  | 0 => .inl 0 ⟨by decide⟩
  | k + 1 =>
    have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
    match get_sum k ih_prev with
    | .inl _ _ => get_sum (k + 1) ih
    | .inr _ val next_val => (ih k (by omega) val.down).elim

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    have p := get_sum (k + 1) ih
    cases p with
    | inl _ val => exact val.down
    | inr _ val next_val =>
      -- val : PLift (a_test (k + 1) = 4)
      -- next_val : MyType k
      -- We want to prove False!
      -- Let's match on next_val (which is of type MyType k)!
      -- Wait, if k = 0, next_val is of type MyType 0.
      -- If k = j + 1, next_val is of type MyType (j + 1).
      -- But wait!
      -- If we do `cases next_val`, Lean will generate two cases:
      -- 1) next_val is .inl: then we have val2 : PLift (a_test k ≠ 4).
      --    But wait, if val2 has type PLift (a_test k ≠ 4), and we have ih k (by omega) : a_test k ≠ 4.
      --    They don't contradict!
      --    So we can't prove False from the .inl case!
      -- Oh!
      sorry
