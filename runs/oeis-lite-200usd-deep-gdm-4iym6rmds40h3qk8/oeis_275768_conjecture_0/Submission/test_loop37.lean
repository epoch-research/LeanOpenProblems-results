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

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n = 4 → False) ⊕ (PLift (a_test n = 4) → PLift (a_test 0 = 4 → False) ⊕ PLift (a_test n = 4 → False))) := by
  by_cases h : a_test n = 4
  · have h0 : a_test 0 = 4 → False := by decide
    exact ⟨.inr (fun _ => .inl ⟨h0⟩)⟩
  · exact ⟨.inl ⟨h⟩⟩

partial def get_false (n : ℕ) (hn : a_test n = 4) : PLift (a_test n = 4 → False) ⊕ (PLift (a_test n = 4) → PLift (a_test 0 = 4 → False) ⊕ PLift (a_test n = 4 → False)) :=
  match get_nonempty_False n hn with
  | .inl val => .inl ⟨fun _ => val.down⟩
  | .inr val => .inr (fun h =>
    match get_false n h.down with
    | .inl val2 => .inr val2
    | .inr val2 => val2 h
  )

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  intro hn
  have p := get_false n hn
  cases p with
  | inl val => exact val.down hn
  | inr val =>
    have h_cases := val ⟨hn⟩
    cases h_cases with
    | inl val2 =>
      -- val2 : PLift (a_test 0 = 4 → False).
      -- Still no False!
      sorry
    | inr val2 => exact val2.down hn
