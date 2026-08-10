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
