import FormalConjectures.Util.ProblemImports

open Nat

def in_H0 (m : ℕ) : Prop :=
  ∃ x y z, x^2 + y^2 + z^2 = m ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2

lemma H0_scale (C : ℕ) (hC : in_H0 C) (k : ℕ) : in_H0 (C * k^2) := by
  rcases hC with ⟨x, y, z, h_sum, h_ge, h_sq⟩
  use x * k, y * k, z * k
  refine ⟨?_, ?_, ?_⟩
  · rw [← h_sum]
    ring
  · nlinarith
  · have h_eq : (x * k)^2 + 8 * (y * k)^2 + 16 * (z * k)^2 = k^2 * (x^2 + 8 * y^2 + 16 * z^2) := by ring
    rw [h_eq]
    have h_prod : k^2 * (x^2 + 8 * y^2 + 16 * z^2) = (k * (x^2 + 8 * y^2 + 16 * z^2).sqrt) * (k * (x^2 + 8 * y^2 + 16 * z^2).sqrt) := by
      nth_rw 1 [← h_sq]
      ring
    rw [h_prod]
    rw [Nat.sqrt_eq]
