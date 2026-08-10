import FormalConjectures.Util.ProblemImports

open Nat

def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

def Good (b c n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧
    is_square (9 * x ^ 2 + b * y ^ 2 + c * z ^ 2)

/-- Scaling reduction: if `s` is representable then so is `s * k^2`. -/
lemma good_scale {b c s : ℕ} (k : ℕ) (h : Good b c s) : Good b c (s * k ^ 2) := by
  obtain ⟨x, y, z, w, hsum, hxy, m, hm⟩ := h
  refine ⟨k * x, k * y, k * z, k * w, ?_, ?_, k * m, ?_⟩
  · have : (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 + (k * w) ^ 2
        = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
    rw [this, hsum]; ring
  · exact Nat.mul_le_mul (le_refl k) hxy
  · have : 9 * (k * x) ^ 2 + b * (k * y) ^ 2 + c * (k * z) ^ 2
        = k ^ 2 * (9 * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by ring
    rw [this, hm]; ring

/-- Reduction of the full statement to the squarefree case. -/
lemma reduce_to_squarefree {b c : ℕ}
    (hcore : ∀ a : ℕ, Squarefree a → Good b c a) : ∀ n : ℕ, Good b c n := by
  intro n
  obtain ⟨a, k, hak, ha⟩ := Nat.sq_mul_squarefree n
  -- hak : k ^ 2 * a = n,  ha : Squarefree a
  have : Good b c (a * k ^ 2) := good_scale k (hcore a ha)
  rwa [mul_comm, hak] at this
