import Submission.UpperPowerOverlap

/-! Exact-type and permitted-axiom checks for the conditional overlap bounds. -/

open Nat Filter
open scoped Classical

example (α η ε : ℝ) (hα : 0 < α) (hη : η < 2) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (Erdos821.g n : ℝ) ≤ (n : ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset (ℕ × ℕ),
      (∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) →
      (P.card : ℝ) ≤ (n : ℝ)^((2-η)*α+ε) :=
  Erdos821.eventually_large_overlap_pairs_le_of_g_upper α η ε hα hη hε H

example (α η ε δ : ℝ) (hα : 0 < α) (hη : η < 2) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (Erdos821.g n : ℝ) ≤ (n : ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset ℕ,
      (∀ a ∈ F, totient a = n) →
      (n : ℝ)^(α-δ) ≤ (F.card : ℝ) →
      (n : ℝ)^(α*η-2*δ-ε) *
          ((Erdos821.LogarithmicOverlap.largePairs F n η).card : ℝ) ≤
        (F.card : ℝ)^2 :=
  Erdos821.eventually_relative_largePairs_bound α η ε δ hα hη hε H

#print axioms Erdos821.eventually_large_overlap_pairs_le_of_g_upper
#print axioms Erdos821.eventually_largePairs_le_of_g_upper
#print axioms Erdos821.eventually_relative_largePairs_bound
