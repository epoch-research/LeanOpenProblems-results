import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False))) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

noncomputable instance (n : ℕ) : Nonempty (PSum (PLift (a_test n ≠ 4)) ((∀ m, a_test m = 4 → False) → False)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr (fun h_all => h_all n h)⟩
  · exact ⟨.inl ⟨h⟩⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_proof (n : ℕ) : PSum (PLift (a_test n ≠ 4)) ((∀ m, a_test m = 4 → False) → False) :=
    match get_sum n with
    | .inl val => .inl val
    | .inr val => .inr (fun h_all => val.down (h_all n))
end

partial def get_all_proof (u : Unit) : PLift (∀ m, a_test m = 4 → False) :=
  -- wait, is PLift (∀ m, a_test m = 4 → False) nonempty?
  -- We need to prove it is nonempty to define get_all_proof!
  get_all_proof u
