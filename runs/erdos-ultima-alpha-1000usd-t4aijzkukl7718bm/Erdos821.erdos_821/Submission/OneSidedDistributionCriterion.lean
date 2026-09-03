import Submission.GeometricDistributionCriterion

/-!
# A cofinal, one-sided smooth-modulus criterion

The full all-modulus distribution hypothesis is stronger than the implication
needs. It suffices to control an aggregate signed deficit for smooth moduli,
at arbitrarily large scales, for an unbounded set of smoothness parameters.

The resulting criterion is still an explicit, unproved hypothesis. This file
does not claim an unconditional settlement of Erdős 821.
-/

open scoped Classical BigOperators
open Nat Finset Filter

namespace Erdos821

open AnalyticSieve

/-- Only unboundedly many parameters t, and unboundedly many scales for each
such parameter, are requested. The deficits have no absolute values. -/
def CofinalSmoothModulusCondition : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, max 3 T ≤ t ∧ ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧
    geometricSmoothModulusDeficit t m ≤ (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t

lemma eventually_signed_deficit_supplies_family (t : ℕ) (ht : 3 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      geometricSmoothModulusDeficit t m ≤ (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t →
      ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * t * m) ∧
          p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m))) ∧
        2 ^ ((64 * t - 1) * m) ≤ P.card := by
  have hpoly₁ := eventually_nat_poly_le_two_pow 1 (4096 * (t - 2)) 1
  have hpoly₂ := eventually_nat_poly_le_two_pow 1 (geometricSmoothCountConstant t) (2 * (t - 2) + 1)
  simp only [one_mul, pow_one] at hpoly₁
  simp only [one_mul] at hpoly₂
  filter_upwards [hpoly₁, hpoly₂,
    eventually_ge_atTop (max (max 2 (t - 2)) (256 * t * primeProductMassConstant (t - 2)))]
    with m hsmall hpoly hm
  intro herr
  have hm' : max 2 (t - 2) ≤ m := (le_max_left _ _).trans hm
  have hbudget : 256 * t * primeProductMassConstant (t - 2) ≤ m + 1 :=
    ((le_max_right _ _).trans hm).trans (Nat.le_succ m)
  have hsmall' : 4096 * (t - 2) * (m + 1) ≤ progressionScaleN m :=
    hsmall.trans (Nat.pow_le_pow_right (by decide) (by omega))
  let P := ((2 ^ (64 * t * m) + 1).primesBelow).filter
    (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpP, hps⟩ := mem_filter.mp hp
    obtain ⟨hpN, hp⟩ := Nat.mem_primesBelow.mp hpP
    exact ⟨hp, by omega, hps⟩
  · have herr' : geometricSmoothModulusDeficit t m ≤
        (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ ((t - 2) + 2) := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ t)] using herr
    have hc := geometric_signed_deficit_smooth_prime_count t m ht hm' hsmall' hbudget herr'
    have hpow : 2 ^ m * 2 ^ ((64 * t - 1) * m) = 2 ^ (64 * t * m) := by
      rw [← pow_add]
      congr 1
      calc
        m + (64 * t - 1) * m = (1 + (64 * t - 1)) * m := by ring
        _ = _ := by rw [Nat.add_sub_of_le (by omega : 1 ≤ 64 * t)]
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ m) _ (by positivity)
    rw [hpow]
    exact hc.trans (Nat.mul_le_mul_right P.card hpoly)

lemma smooth_prime_family_of_frequent_signed_deficit (t : ℕ) (ht : 3 ≤ t)
    (H : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ geometricSmoothModulusDeficit t m ≤
      (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m))) ∧
      2 ^ ((64 * t - 1) * m) ≤ P.card := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (eventually_signed_deficit_supplies_family t ht)
  obtain ⟨m, hmm, hdef⟩ := H (max M m₀)
  exact ⟨m, (le_max_left _ _).trans hmm, hm₀ m ((le_max_right _ _).trans hmm) hdef⟩

lemma infinite_g_gt_of_frequent_signed_deficit (t : ℕ) (ht : 3 ≤ t)
    (H : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ geometricSmoothModulusDeficit t m ≤
      (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - 131 / (64 * (t : ℝ)))}.Infinite := by
  have hinf := infinite_g_gt_of_general_dyadic_density (64 * t) (64 * t - 1) 128
    (by omega) (by omega) (by omega) (smooth_prime_family_of_frequent_signed_deficit t ht H)
  have hnat : 64 * t - 1 - 128 - 2 = 64 * t - 131 := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hexp : (((64 * t - 1 - 128 - 2 : ℕ) : ℝ) / ((64 * t : ℕ) : ℝ)) =
      1 - 131 / (64 * (t : ℝ)) := by
    rw [hnat, Nat.cast_sub (by omega : 131 ≤ 64 * t)]
    push_cast
    field_simp
  simpa only [hexp] using hinf

/-- The earlier Elliott–Halberstam-type hypothesis implies this weaker sufficient condition. -/
lemma cofinal_smooth_modulus_condition_of_geometric_distribution
    (H : GeometricProgressionDistribution) : CofinalSmoothModulusCondition := by
  intro T
  let t := max 3 T
  have ht : 3 ≤ t := le_max_left _ _
  refine ⟨t, le_rfl, ?_⟩
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (H t ht t)
  intro M
  let m := max M (max m₀ (max 2 (t - 2)))
  have hMm : M ≤ m := le_max_left _ _
  have hm₀m : m₀ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have htm : max 2 (t - 2) ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨m, hMm, (geometric_smooth_deficit_le_error t m ht htm).trans (hm₀ m hm₀m)⟩

/-- Only the cofinal one-sided hypothesis is used. It remains explicit and unproved. -/
theorem erdos_821_of_cofinal_smooth_modulus_condition (H : CofinalSmoothModulusCondition) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_gt (max 3 (131 / (64 * ε)))
  obtain ⟨t, ht, Ht⟩ := H T
  have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
  have hTt : T ≤ t := (le_max_right _ _).trans ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htbound : 131 / (64 * ε) < (t : ℝ) :=
    ((le_max_right _ _).trans_lt hT).trans_le (by exact_mod_cast hTt)
  have hprod : 131 < (t : ℝ) * (64 * ε) := (div_lt_iff₀ (by positivity)).mp htbound
  have hexp : 1 - ε ≤ 1 - 131 / (64 * (t : ℝ)) := by
    have h : 131 / (64 * (t : ℝ)) ≤ ε := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hprod])
    linarith
  have hinf := infinite_g_gt_of_frequent_signed_deficit t ht3 Ht
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans_lt hn.1

end Erdos821
