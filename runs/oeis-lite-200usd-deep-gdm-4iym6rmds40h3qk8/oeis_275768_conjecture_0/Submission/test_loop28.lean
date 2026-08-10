import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def MyType (n : ℕ) :=
  PLift (a_test n ≠ 4) ⊕ (PLift (a_test n = 4) × (PLift (a_test n = 4) → PLift False))

noncomputable instance (n : ℕ) : Nonempty (MyType n) := by
  by_cases h : a_test n = 4
  · have h_fn : PLift (a_test n = 4) → PLift False := by
      intro h_eq
      exact ⟨(by
        -- wait! we want PLift False.
        -- We have h_eq : PLift (a_test n = 4).
        -- We don't need to do anything, because this is just proving Nonempty!
        -- Wait, how do we prove Nonempty?
        -- We can just return any function!
        -- But wait, PLift (a_test n = 4) → PLift False is inhabited if we have a proof of False.
        -- But since we have h : a_test n = 4, wait, does h help us prove PLift (a_test n = 4) → PLift False?
        -- No, if h : a_test n = 4 is true, then PLift (a_test n = 4) is true, so PLift (a_test n = 4) → PLift False is false!
        -- So we CANNOT construct this function when h is true!
        sorry
      )⟩
    exact ⟨.inr (⟨h⟩, h_fn)⟩
  · exact ⟨.inl ⟨h⟩⟩
