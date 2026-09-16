import Submission.Spec
import Mathlib

open Filter Asymptotics

theorem oeis_363414_conjecture_type2_asymptotics_proof :
  ∀ p : ℕ, Nat.Prime p → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by
  exact?
