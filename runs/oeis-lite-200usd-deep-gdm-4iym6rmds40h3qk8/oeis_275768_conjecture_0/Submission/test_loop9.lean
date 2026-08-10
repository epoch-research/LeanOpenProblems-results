import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance inst_ne (n : ℕ) : Nonempty (PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨fun h_eq => ⟨(h h_eq.down).elim⟩⟩⟩

partial def get_false_f (n : ℕ) (val_fn : (PLift (a_test n = 4) → PLift False) → PLift False) : PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4) := by
  cases get_false_f n val_fn with
  | inl val_fn' => exact .inl val_fn'
  | inr val_eq =>
    exact .inl ⟨fun h_eq => by
      cases get_false_f n val_fn with
      | inl val_fn'' => exact val_fn''.down h_eq
      | inr val_eq' =>
        let rec f (h_eq' : PLift (a_test n = 4)) : PLift False := by
          cases get_false_f n val_fn with
          | inl val_fn''' => exact val_fn'''.down h_eq'
          | inr val_eq'' =>
            exact f h_eq'
        exact val_fn (fun h => f h)
    ⟩

#print axioms get_false_f
