import Submission.Spec
open Nat Finset

lemma factorial_lemma (k m : ℕ) :
  (3*k+3*m).factorial * (3*k).factorial * (2*k).factorial * k.factorial * (3*m).factorial * (2*m).factorial * m.factorial
  ∣ (6*k).factorial * (6*m).factorial * (k+m).factorial * (2*k+2*m).factorial := by
  sorry
