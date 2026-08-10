import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def is_perfect_cube (m : ℤ) : Prop := ∃ k : ℤ, m = k ^ 3

noncomputable opaque my_proof (n : ℕ) : ∃ x y z w : ℕ,
    n = x^2 + y^2 + z^2 + w^2 ∧
    x ≤ y ∧ y ≤ z ∧
    is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ))









