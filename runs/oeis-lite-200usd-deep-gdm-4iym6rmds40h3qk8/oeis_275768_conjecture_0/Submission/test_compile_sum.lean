import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (Nonempty (PLift (a_test n ≠ 4)) ∨ Nonempty (PLift (a_test n ≠ 4 → False))) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨Or.inl ⟨⟨h⟩⟩⟩
  · exact ⟨Or.inr ⟨⟨h⟩⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ (a_test n = 4 → PLift (a_test (n - 1) ≠ 4) ⊕ PLift (a_test (n - 1)  ≠ 4 → False))) := by
  by_cases h : a_test n = 4
  · by_cases h_prev : a_test (n - 1) ≠ 4
    · exact ⟨.inr (fun _ => .inl ⟨h_prev⟩)⟩
    · exact ⟨.inr (fun _ => .inr ⟨h_prev⟩)⟩
  · exact ⟨.inl ⟨h⟩⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_proof (n : ℕ) : PLift (a_test n ≠ 4) ⊕ (a_test n = 4 → PLift (a_test (n - 1)  ≠ 4) ⊕ PLift (a_test (n - 1)  ≠ 4 → False)) :=
    match get_sum n with
    | .inl val => .inl val
    | .inr val =>
      -- val : PLift (a_test n ≠ 4 → False)
      .inr (fun h_eq =>
        match get_proof n with
        | .inl val2 => (val.down val2.down).elim
        | .inr val2 =>
          match val2 h_eq with
          | .inl val3 =>
            -- val3 : PLift (a_test (n - 1) ≠ 4)
            -- We want to return PLift (a_test (n - 1) ≠ 4) ⊕ PLift (a_test (n - 1) ≠ 4 → False)
            .inl val3
          | .inr val3 =>
            -- val3 : PLift (a_test (n - 1) ≠ 4 → False)
            .inr val3
      )
end
