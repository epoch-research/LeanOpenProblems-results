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
  · exact ⟨.inl ⟨⟨h⟩⟩⟩
  · exact ⟨.inr ⟨⟨h⟩⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_proof (n : ℕ) : PLift (a_test n ≠ 4) ⊕ PLift True :=
    match get_sum n with
    | .inl val => .inl val
    | .inr val =>
      match get_proof n with
      | .inl val2 => .inl ⟨fun _ => val.down val2.down⟩
      | .inr _ => .inr ⟨()⟩
end

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
  intro ⟨n, hn⟩
  have p := get_proof n
  cases p with
  | inl val => exact val.down hn
  | inr val =>
    -- val : PLift True
    -- wait! If we are in the .inr val case, we still don't have contradiction!
    -- how to get contradiction in the .inr case?
    sorry
