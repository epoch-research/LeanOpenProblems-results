import Submission.Work
import Submission.GapTailCriterion
import Submission.BoundedPrimeCover
import Submission.PrimeSetMertens

/-! An explicit conditional route to Erdős 970 from an exponential void bound.
The void bound is a hypothesis, not a proved theorem. This file does not settle
the original conjecture. It handles arbitrary, not only bounded, prime sets. -/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- The missing probabilistic estimate. Even some positive absolute c would suffice. -/
def ExponentialVoidBound (c : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
    coveredFraction P m ≤ exp (-(c * (m : ℝ) * density P))

lemma eventually_entropy_small {E : ℝ} (hE : 0 < E) :
    ∀ᶠ k : ℕ in atTop, 12 * log ((k : ℝ) + 2) ^ 2 < E * k := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith : ∀ k : ℕ, (k : ℝ) ≤ (k : ℝ) + 2)
      tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun k : ℕ => log ((k : ℝ) + 2) ^ 2 / k) atTop (nhds 0) := by
    convert (tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 (by norm_num)).comp ht using 1 <;>
      simp [Function.comp_def]
  have he := hl.eventually (gt_mem_nhds (show 0 < E / 12 by positivity))
  filter_upwards [he, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hh := (div_lt_iff₀ hk0).mp hk
  linarith

lemma quadratic_cap {q k : ℕ} (hq : q ≤ 256 * (k ^ 2 + k + 1) ^ 2) :
    (q : ℝ) ≤ ((k : ℝ) + 2) ^ 12 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have h256 : (256 : ℝ) ≤ ((k : ℝ) + 2) ^ 8 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 8 using 1 <;> norm_num
  have hbase : (k : ℝ) ^ 2 + k + 1 ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 + k + 1) hbase 2
  calc
    (q : ℝ) ≤ 256 * ((k : ℝ) ^ 2 + k + 1) ^ 2 := by exact_mod_cast hq
    _ ≤ ((k : ℝ) + 2) ^ 8 * (((k : ℝ) + 2) ^ 2) ^ 2 :=
      mul_le_mul h256 hsq (by positivity) (by positivity)
    _ = ((k : ℝ) + 2) ^ 12 := by ring

/-- Exponential decay, if proved uniformly, gives h(k)<=k^2 for all sufficiently
large k. The small-k constant is handled separately below. -/
theorem eventually_quadratic_of_exponential_void {c : ℝ} (hc : 0 < c)
    (htail : ExponentialVoidBound c) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ k ^ 2 := by
  let d := exp (-WeightedMertens.reciprocalConstant - 1)
  have hd : 0 < d := exp_pos _
  filter_upwards [eventually_entropy_small (mul_pos hc hd), eventually_ge_atTop 1]
    with k hsmall hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hy : (1 : ℝ) < (k : ℝ) + 2 := by linarith
  have hlog : 0 < log ((k : ℝ) + 2) := log_pos hy
  apply (jacobsthalFunction_le_iff k (k ^ 2)).mpr
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcov⟩ := (not_isJacobsthalBound_iff_cover k (k ^ 2)).mp hbad
  obtain ⟨Q, s, hQ, hQk, hcap, hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have hdensity : d / log ((k : ℝ) + 2) ≤ density Q := by
    simpa only [density, one_div, d] using WeightedMertens.prime_set_density_lower Q hQ k hQk
  have hden := (div_le_iff₀ hlog).mp hdensity
  have hleft := mul_lt_mul_of_pos_left hsmall hk0
  have hright := mul_le_mul_of_nonneg_left hden (show 0 ≤ c * (k : ℝ) ^ 2 by positivity)
  have hbudget : (k : ℝ) * log (((k : ℝ) + 2) ^ 12) < c * (k : ℝ) ^ 2 * density Q := by
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    apply (mul_lt_mul_iff_right₀ hlog).mp
    nlinarith only [hleft, hright]
  have htail' : coveredFraction Q (k ^ 2) ≤ exp (-(c * (k : ℝ) ^ 2 * density Q)) := by
    have hh := htail Q hQ (k ^ 2)
    change coveredFraction Q (k ^ 2) ≤ exp (-(c * ((k ^ 2 : ℕ) : ℝ) * density Q)) at hh
    simpa only [Nat.cast_pow] using hh
  have hB : (1 : ℝ) ≤ ((k : ℝ) + 2) ^ 12 := one_le_pow₀ hy.le
  obtain ⟨x, hx, hxa⟩ := survivor_of_exponential_tail_of_cap hQ hQk hB
    (fun q hq => quadratic_cap (hcap q hq)) htail' hbudget s
  obtain ⟨q, hq, hxq⟩ := hcov' x hx
  exact hxa q hq hxq

/-- The full statement of the target follows from the stated tail hypothesis.
There is no unconditional proof of that hypothesis in this development. -/
theorem quadratic_bound_of_exponential_void {c : ℝ} (hc : 0 < c)
    (htail : ExponentialVoidBound c) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_quadratic_of_exponential_void hc htail)
  refine ⟨(jacobsthalFunction N : ℝ) + 1, by positivity, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hnonneg : (0 : ℝ) ≤ jacobsthalFunction N := Nat.cast_nonneg _
  by_cases hNk : N ≤ k
  · have hh : (jacobsthalFunction k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hN k hNk
    nlinarith
  · have hh : (jacobsthalFunction k : ℝ) ≤ jacobsthalFunction N := by
      exact_mod_cast jacobsthalFunction_strictMono.monotone (show k ≤ N by omega)
    nlinarith

/-- A still stronger candidate tail inequality. It remains unproved. -/
def GeometricVoidBound : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ,
    coveredFraction P m ≤ (1 - density P) ^ m

lemma density_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : density P ≤ 1 := by
  have hnonneg (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 - 1 / (p : ℝ) := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hh := (div_le_one hp0).mpr hp1
    linarith
  calc
    density P ≤ ∏ _p ∈ P, (1 : ℝ) := prod_le_prod hnonneg
      (fun p _ => sub_le_self 1 (by positivity))
    _ = 1 := by simp

lemma exponential_void_of_geometric (h : GeometricVoidBound) : ExponentialVoidBound 1 := by
  intro P hP m
  have hbase : 1 - density P ≤ exp (-density P) := by
    have hh := add_one_le_exp (-density P)
    linarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr (density_le_one P hP)) hbase m
  have hh := (h P hP m).trans hpow
  rw [← exp_nat_mul] at hh
  simpa only [one_mul, mul_neg] using hh

/-- The geometric candidate also implies the original quadratic statement,
but this theorem explicitly retains that unproved candidate as a hypothesis. -/
theorem quadratic_bound_of_geometric_void (h : GeometricVoidBound) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 :=
  quadratic_bound_of_exponential_void (by norm_num) (exponential_void_of_geometric h)

#print axioms quadratic_bound_of_geometric_void
#print axioms eventually_quadratic_of_exponential_void
#print axioms quadratic_bound_of_exponential_void
end Erdos970.GapAverages
