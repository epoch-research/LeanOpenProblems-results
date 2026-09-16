import Submission.Spec
import Mathlib
import Submission.ProofFinal

open Nat Finset

lemma a_pqr (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) 
  (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r) :
  a (p * q * r) = 1 + 2 * (p + q + r) + 4 * (p * q + q * r + p * r) := by
  sorry
