import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def MyType (n : ℕ) :=
  MySum (PLift (a_test n ≠ 4)) (PLift (a_test n = 4) × (PLift (a_test n ≠ 4) → PLift False))

noncomputable instance (n : ℕ) : Nonempty (MyType n) := by
  by_cases h : a_test n = 4
  · have h_fn : PLift (a_test n ≠ 4) → PLift False := by
      intro h_ne
      exact ⟨h_ne.down h⟩
    exact ⟨.inr (⟨h⟩, h_fn)⟩
  · exact ⟨.inl ⟨h⟩⟩

partial def get_sum (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MyType n :=
  match n with
  | 0 => .inl ⟨by decide⟩
  | k + 1 =>
    have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
    match get_sum k ih_prev with
    | .inl val => get_sum (k + 1) ih
    | .inr val => (ih k (by omega) val.1.down).elim

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  have p := get_sum n ih
  cases p with
  | inl val => exact val.down
  | inr val =>
    -- val.1 : PLift (a_test n = 4)
    -- val.2 : PLift (a_test n ≠ 4) → PLift False
    -- We want to prove a_test n ≠ 4.
    -- Since we want to prove a_test n ≠ 4, we can do intro hn:
    intro hn
    exact (val.2 ⟨hn⟩).down.elim
