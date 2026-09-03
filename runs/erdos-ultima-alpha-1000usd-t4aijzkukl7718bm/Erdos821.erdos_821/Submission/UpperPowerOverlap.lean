import Submission.LcmFibers
import Submission.LogarithmicOverlap

/-!
# Large-overlap pairs under an upper multiplicity exponent

A hypothetical eventual upper bound on g bounds the number of pairs in a
single totient fiber with a large gcd totient. In a near-extremal fiber, it
therefore gives an upper bound, not the lower bound needed for the lcm
amplification. The upper bound on g remains an explicit hypothesis.
These results do not settle Erdős 821.
-/

open Nat Filter Finset
open scoped Classical

namespace Erdos821

set_option maxHeartbeats 2000000

/-- The loss in this pair-count estimate can be any positive epsilon.
The divisor-count losses have already been accounted for in the lcm
amplification theorem used here. -/
theorem eventually_large_overlap_pairs_le_of_g_upper
    (α η ε : ℝ) (hα : 0 < α) (hη : η < 2) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset (ℕ × ℕ),
      (∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) →
      (P.card : ℝ) ≤ (n : ℝ)^((2-η)*α+ε) := by
  have hfinite : {n : ℕ | (g n : ℝ) > (n : ℝ)^α}.Finite := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp H
    apply (Set.finite_Iio N).subset
    intro n hn
    exact lt_of_not_ge (fun h => (hN n h).not_gt hn)
  have hnot : ¬ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ P : Finset (ℕ × ℕ),
      (n : ℝ)^((2-η)*α+ε) < (P.card : ℝ) ∧
      ∀ ab ∈ P, totient ab.1 = n ∧ totient ab.2 = n ∧
        (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ)) := by
    intro h
    apply hfinite.not_infinite
    exact infinite_g_gt_of_large_overlap_pairs η ((2-η)*α+ε) α
      hη hα (by nlinarith) h
  push_neg at hnot
  obtain ⟨N,hN⟩ := hnot
  filter_upwards [eventually_gt_atTop N] with n hn
  intro P hP
  by_contra h
  obtain ⟨ab,hab,he⟩ := hN n hn P (lt_of_not_ge h)
  exact (hP ab hab).2.2.not_gt (he (hP ab hab).1 (hP ab hab).2.1)

/-- Applied to any finite subfamily of a totient fiber. Squarefreeness
is not required. -/
theorem eventually_largePairs_le_of_g_upper
    (α η ε : ℝ) (hα : 0 < α) (hη : η < 2) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset ℕ,
      (∀ a ∈ F, totient a = n) →
      ((LogarithmicOverlap.largePairs F n η).card : ℝ) ≤
        (n : ℝ)^((2-η)*α+ε) := by
  filter_upwards [eventually_large_overlap_pairs_le_of_g_upper α η ε hα hη hε H]
    with n hn
  intro F hF
  apply hn
  intro ab hab
  obtain ⟨hab,hlarge⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  exact ⟨hF _ ha,hF _ hb,hlarge⟩

/-- In a fiber of size at least n^(alpha-delta), the relative large-pair
frequency is at most n^(-alpha*eta+2*delta+epsilon), expressed without
dividing by the fiber cardinality. This is not a supply of such fibers. -/
theorem eventually_relative_largePairs_bound
    (α η ε δ : ℝ) (hα : 0 < α) (hη : η < 2) (hε : 0 < ε)
    (H : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Finset ℕ,
      (∀ a ∈ F, totient a = n) →
      (n : ℝ)^(α-δ) ≤ (F.card : ℝ) →
      (n : ℝ)^(α*η-2*δ-ε) *
          ((LogarithmicOverlap.largePairs F n η).card : ℝ) ≤
        (F.card : ℝ)^2 := by
  filter_upwards [eventually_largePairs_le_of_g_upper α η ε hα hη hε H,
    eventually_ge_atTop 1] with n hn hn1
  intro F hF hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    _ ≤ (n : ℝ)^(α*η-2*δ-ε) * (n : ℝ)^((2-η)*α+ε) :=
      mul_le_mul_of_nonneg_left (hn F hF) (Real.rpow_nonneg hnR.le _)
    _ = ((n : ℝ)^(α-δ))^2 := by
      rw [← Real.rpow_add hnR, ← Real.rpow_mul_natCast hnR.le]
      congr 1
      norm_num
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hnR.le _) hcard 2

end Erdos821
