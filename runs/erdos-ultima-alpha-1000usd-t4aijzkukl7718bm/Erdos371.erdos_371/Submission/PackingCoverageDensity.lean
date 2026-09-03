import Submission.TwoSidedFactorPacking
import Submission.QuadraticSmoothBound

/-! Bounded-length two-sided factor certificates cover all but an arbitrarily
small proportion of actual comparisons. This is unsigned coverage only. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma square_lt_power_of_power_cutoff (N p K : ℕ) (hK : 0 < K)
    (hp : (N : ℝ)^(2/(K : ℝ)) < p) : N^2 < p^K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have he : (2/(K : ℝ))*(K : ℝ) = 2 := by field_simp
  have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    hp hKr
  rw [← Real.rpow_mul (Nat.cast_nonneg N),he,Real.rpow_two,Real.rpow_natCast] at hpow
  exact_mod_cast hpow

noncomputable def packingFailureCount (K N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n =>
    ¬PackedPrimePair K (primeWinner n) (losingNumber n) (winningNumber n)).card

lemma packingFailureCount_le_smooth (K N : ℕ) (hK : 0 < K) :
    packingFailureCount K N ≤ 2 +
      ((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(2/(K : ℝ))).card := by
  classical
  have hsub : ((range N).filter fun n =>
      ¬PackedPrimePair K (primeWinner n) (losingNumber n) (winningNumber n)) ⊆
      range 2 ∪ ((range N).filter fun n =>
        (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(2/(K : ℝ))) := by
    intro n hn
    obtain ⟨hnN,hnfail⟩ := mem_filter.mp hn
    by_cases hnsmall : n < 2
    · exact mem_union_left _ (mem_range.mpr hnsmall)
    · apply mem_union_right
      refine mem_filter.mpr ⟨hnN,?_⟩
      have hp : (primeWinner n : ℝ) ≤ (N : ℝ)^(2/(K : ℝ)) := by
        by_contra h
        apply hnfail
        exact comparison_packedPrimePair K N n (by omega) (mem_range.mp hnN)
          (square_lt_power_of_power_cutoff N (primeWinner n) K hK (lt_of_not_ge h))
      have hle : Nat.maxPrimeFac (n+1) ≤ primeWinner n := le_max_right _ _
      exact (show (Nat.maxPrimeFac (n+1) : ℝ) ≤ primeWinner n by exact_mod_cast hle).trans hp
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  simpa only [card_range] using hc

/-- Explicit unsigned failure proportion for every fixed positive length K. -/
theorem packingFailureCount_ratio_eventually_le (K : ℕ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (packingFailureCount K N : ℝ)/N ≤ 320/(K : ℝ)^2 + ε := by
  have hs := FiniteSieve.smooth_power_count_eventually_le (2/(K : ℝ))
    (by positivity) (ε/2) (by positivity)
  have he := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually_lt_const
    (show (0 : ℝ) < ε/2 by positivity)
  filter_upwards [hs,he] with N hs he
  have hc : (packingFailureCount K N : ℝ) ≤ 2 +
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(2/(K : ℝ))).card : ℝ) := by
    exact_mod_cast packingFailureCount_le_smooth K N hK
  have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hd
  have hid : 80*(2/(K : ℝ))^2 = 320/(K : ℝ)^2 := by ring
  rw [hid] at hs
  linarith

/-- The list length can be fixed before N tends to infinity, with unsigned
coverage as close to full density as desired. No signed balance follows. -/
theorem packingFailureCount_uniform_rarity (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (packingFailureCount K N : ℝ)/N < ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1 : ℝ) (640/ε))
  have hK1 : (1 : ℝ) < K := (le_max_left _ _).trans_lt hK
  have hKpos : 0 < K := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hK1)
  have hK0 : (0 : ℝ) < K := by positivity
  have hlarge : 640 < (K : ℝ)*ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hK)
  have hmain : 320/(K : ℝ)^2 < ε/2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hK0)).mpr
    have hs : (K : ℝ) ≤ (K : ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs hε.le
    nlinarith
  refine ⟨K,hKpos,?_⟩
  filter_upwards [packingFailureCount_ratio_eventually_le K hKpos (ε/2) (by positivity)] with N hN
  linarith

#print axioms square_lt_power_of_power_cutoff
#print axioms packingFailureCount_ratio_eventually_le
#print axioms packingFailureCount_uniform_rarity
end Erdos371
