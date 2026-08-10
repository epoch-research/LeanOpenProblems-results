import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive CustomSum (n : ℕ) (f : (x : ℕ) → PLift (a x ≠ 4) ⊕ PLift (a x = 4)) where
  | inl (val : PLift (a n ≠ 4))
  | inr (val2 : PLift (a n = 4)) (heq : ∀ val3 : PLift (a n ≠ 4), f n = .inl val3 → False)

noncomputable instance (n : ℕ) (f : (x : ℕ) → PLift (a x ≠ 4) ⊕ PLift (a x = 4)) : Nonempty (CustomSum n f) := by
  by_cases h : a n = 4
  · exact ⟨.inr ⟨h⟩ (by
      intro val3 heq
      exact val3.down h
    )⟩
  · exact ⟨.inl ⟨h⟩⟩


noncomputable instance (n : ℕ) : Nonempty (PLift (a n ≠ 4) ⊕ PLift (a n = 4)) := by
  by_cases h : a n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩


noncomputable instance (n : ℕ) (f : (x : ℕ) → PLift (a x ≠ 4) ⊕ PLift (a x = 4)) : Nonempty (CustomSum n f ⊕ PLift (a n ≠ 4)) := by
  by_cases h : a n = 4
  · exact ⟨.inl (.inr ⟨h⟩ (by
      intro val3 heq
      exact val3.down h
    ))⟩
  · exact ⟨.inr ⟨h⟩⟩



mutual
  partial def get_proof (n : ℕ) : CustomSum n (fun x => get_proof_inner x) ⊕ PLift (a n ≠ 4) :=
    get_proof n

  partial def get_proof_inner (n : ℕ) : PLift (a n ≠ 4) ⊕ PLift (a n = 4) :=
    get_proof_inner n
end








