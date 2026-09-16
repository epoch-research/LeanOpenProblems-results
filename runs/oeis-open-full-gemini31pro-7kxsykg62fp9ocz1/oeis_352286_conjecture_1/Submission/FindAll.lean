import Mathlib
open Finset Nat

def A352286 (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

def A352286_exceptions : Set ℕ := {106, 744, 5469, 331269}

theorem oeis_352286_conjecture_1.disproof : ¬ (∀ n : ℕ, (A352286 n = 0 ↔ n ∈ A352286_exceptions)) := by
  intro h
  have hz : A352286 10 = 0 := by sorry
  -- BUT HOW do I prove it?
  -- w + x^2 + 2y^2 + 3z^2 + xyz
  -- It's related to integer quadratic forms Universal theorems, but with a cubic term xyz and a linear term w.
  sorry
