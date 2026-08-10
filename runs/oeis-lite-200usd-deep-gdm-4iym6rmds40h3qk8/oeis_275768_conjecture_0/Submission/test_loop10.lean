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

noncomputable instance inst_sum (n : ℕ) : Nonempty (PLift False ⊕ PLift (a_test 0 = 4 → False)) := by
  have h : a_test 0 = 4 → False := by decide
  exact ⟨.inr ⟨h⟩⟩

partial def get_false_ultimate (n : ℕ) (hn : a_test n = 4) : PLift False ⊕ PLift (a_test 0 = 4 → False) :=
  match get_nonempty_False n hn with
  | .inl val => .inl val
  | .inr val => get_false_ultimate n val.down

#print axioms get_false_ultimate
