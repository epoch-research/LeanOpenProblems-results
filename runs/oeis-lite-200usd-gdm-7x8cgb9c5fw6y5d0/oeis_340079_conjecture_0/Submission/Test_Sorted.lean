import FormalConjectures.Util.ProblemImports

open List

lemma chain_le_of_mem {α : Type*} [Preorder α] {x y : α} {l : List α} (h : List.Chain (· ≤ ·) x (y :: l)) (a : α) (ha : a ∈ l) : y ≤ a := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    cases ha with
    | head =>
      -- ha is a ∈ b :: l, which is a = b
      -- We have List.Chain (· ≤ ·) x (y :: b :: l)
      -- which means x ≤ y and List.Chain (· ≤ ·) y (b :: l)
      -- which means y ≤ b
      rw [List.chain_cons] at h
      exact h.2.1
    | tail _ h_mem =>
      -- ha is a ∈ l
      rw [List.chain_cons] at h
      -- we have List.Chain (· ≤ ·) y (b :: l)
      -- which is what we need for induction!
      exact ih h.2 h_mem
