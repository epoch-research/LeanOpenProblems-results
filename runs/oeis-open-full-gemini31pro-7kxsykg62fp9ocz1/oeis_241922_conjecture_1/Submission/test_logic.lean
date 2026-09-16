import Submission.Spec
open Nat

lemma prove_G_from_disproof (h : ¬ (goldbach_binary_conjecture ↔ False)) : goldbach_binary_conjecture := by
  cases em goldbach_binary_conjecture with
  | inl hG => exact hG
  | inr hnG =>
    have h_iff : goldbach_binary_conjecture ↔ False := by
      constructor
      · intro hG; exact hnG hG
      · intro hF; exact False.elim hF
    exact False.elim (h h_iff)
