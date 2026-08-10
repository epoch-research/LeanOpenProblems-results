import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := 0

def S (n : ℕ) := PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4)

noncomputable instance (n : ℕ) : Nonempty (S n) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨fun h_eq => ⟨(h h_eq.down).elim⟩⟩⟩

partial def get_false_f (n : ℕ) : S n :=
  match get_false_f n with
  | .inl val => .inl val
  | .inr val =>
    let rec f (h : PLift (a_test n = 4)) : PLift False :=
      match get_false_f n with
      | .inl val_inl => val_inl.down h
      | .inr val_inr => f h
    .inl ⟨f⟩
