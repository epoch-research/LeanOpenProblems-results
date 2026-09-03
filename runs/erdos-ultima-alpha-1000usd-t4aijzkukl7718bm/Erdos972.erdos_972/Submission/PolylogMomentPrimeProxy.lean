import Submission.FiniteMomentPrimeProxy

/-! An output-dependent damping parameter gives a polylogarithmic finite-moment
prime detector with a globally summable composite contribution. Divergence of
its prime-input sum at a prescribed irrational slope is not asserted. -/
namespace Erdos972PolylogMomentPrimeProxy

open Finset Filter
open scoped Topology
open Erdos972NonlinearPrimeProxy Erdos972FiniteMomentPrimeProxy
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 2000000

def logSize (n : ℕ) : ℕ := Nat.log 2 n + 1

def momentBudget (n : ℕ) : ℕ := (logSize n)^8

noncomputable def parameter (n : ℕ) : ℝ :=
  8 * Real.log (logSize n) / Real.log n

noncomputable def weight (n : ℕ) : ℝ := (logSize n : ℝ)^2 / n

noncomputable def finiteProxy (n : ℕ) : ℝ :=
  if 1 < n then ∑ j ∈ range (momentBudget n),
    Real.exp (-parameter n * Real.log n) * (expDivisorSum (parameter n) n)^j
  else 0

noncomputable def detector (n : ℕ) : ℝ := weight n * finiteProxy n

lemma logSize_pos (n : ℕ) : 0 < logSize n := by simp [logSize]

lemma parameter_nonneg (n : ℕ) : 0 ≤ parameter n := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
    (Real.log_natCast_nonneg _)

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

lemma finiteProxy_nonneg (n : ℕ) : 0 ≤ finiteProxy n := by
  unfold finiteProxy
  split_ifs
  · exact sum_nonneg fun j _ => mul_nonneg (Real.exp_nonneg _)
      (pow_nonneg (expDivisorSum_nonneg (parameter_nonneg n) n) j)
  · exact le_rfl

lemma detector_nonneg (n : ℕ) : 0 ≤ detector n :=
  mul_nonneg (weight_nonneg n) (finiteProxy_nonneg n)

lemma exp_parameter {n : ℕ} (hn : 1 < n) :
    Real.exp (-parameter n * Real.log n) = ((logSize n : ℝ)^8)⁻¹ := by
  have hlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
  have he : -parameter n * Real.log n = -(8 * Real.log (logSize n)) := by
    unfold parameter
    field_simp
  rw [he, Real.exp_neg, show 8 * Real.log (logSize n) = Real.log ((logSize n : ℝ)^8) by
    rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL _)]

lemma exp_half_parameter {n : ℕ} (hn : 1 < n) :
    Real.exp (-(parameter n / 2) * Real.log n) = ((logSize n : ℝ)^4)⁻¹ := by
  have hlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
  have he : -(parameter n / 2) * Real.log n = -(4 * Real.log (logSize n)) := by
    unfold parameter
    field_simp
    ring
  rw [he, Real.exp_neg, show 4 * Real.log (logSize n) = Real.log ((logSize n : ℝ)^4) by
    rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL _)]

lemma finiteProxy_le (n : ℕ) : finiteProxy n ≤ primeProxy (parameter n) n := by
  by_cases hn : 1 < n
  · rw [finiteProxy, if_pos hn]
    have hs := hasSum_primeProxy (parameter_nonneg n) hn
    exact (hs.summable.sum_le_tsum _ (fun j _ =>
      mul_nonneg (Real.exp_nonneg _)
        (pow_nonneg (expDivisorSum_nonneg (parameter_nonneg n) n) j))).trans_eq hs.tsum_eq
  · simp only [finiteProxy, primeProxy, if_neg hn, le_refl]

lemma finiteProxy_prime_eq {q : ℕ} (hq : q.Prime) :
    finiteProxy q = 1 - (1 - ((logSize q : ℝ)^8)⁻¹)^(momentBudget q) := by
  have he : expDivisorSum (parameter q) q = 1 - ((logSize q : ℝ)^8)⁻¹ := by
    simpa only [pow_one, exp_parameter hq.one_lt] using
      expDivisorSum_prime_pow (parameter q) hq (by decide : 0 < 1)
  rw [finiteProxy, if_pos hq.one_lt, exp_parameter hq.one_lt, he, ← mul_sum]
  have hh := geom_sum_mul_neg (1 - ((logSize q : ℝ)^8)⁻¹) (momentBudget q)
  simp only [sub_sub_cancel] at hh
  nlinarith only [hh]

/-- Only (1 + log_2 q)^8 moments are needed for a fixed fraction of the
prime value at this output-dependent parameter. -/
theorem finiteProxy_prime_bounds {q : ℕ} (hq : q.Prime) :
    (1 / 2 : ℝ) ≤ finiteProxy q ∧ finiteProxy q ≤ 1 := by
  have hL : (0 : ℝ) < logSize q := Nat.cast_pos.mpr (logSize_pos q)
  have hL1 : (1 : ℝ) ≤ logSize q := by exact_mod_cast logSize_pos q
  have hp : (1 : ℝ) ≤ (logSize q : ℝ)^8 := one_le_pow₀ hL1
  have hx1 : ((logSize q : ℝ)^8)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp
  have hJ : (momentBudget q : ℝ) * ((logSize q : ℝ)^8)⁻¹ = 1 := by
    simp only [momentBudget, Nat.cast_pow]
    exact mul_inv_cancel₀ (ne_of_gt (pow_pos hL _))
  refine ⟨?_, (finiteProxy_le q).trans_eq (primeProxy_prime (parameter_nonneg q) hq)⟩
  rw [finiteProxy_prime_eq hq]
  have hh := geometric_loss_lower (inv_nonneg.mpr (pow_nonneg hL.le _)) hx1 (momentBudget q)
  simpa only [hJ, one_add_one_eq_two] using hh

theorem detector_prime_bounds {q : ℕ} (hq : q.Prime) :
    weight q / 2 ≤ detector q ∧ detector q ≤ weight q := by
  have hh := finiteProxy_prime_bounds hq
  constructor
  · simpa only [detector, mul_one_div] using
      mul_le_mul_of_nonneg_left hh.1 (weight_nonneg q)
  · simpa only [detector, mul_one] using
      mul_le_mul_of_nonneg_left hh.2 (weight_nonneg q)

noncomputable def envelope (n : ℕ) : ℝ := 1 / ((n : ℝ) * (logSize n : ℝ)^2)

lemma envelope_nonneg (n : ℕ) : 0 ≤ envelope n := by unfold envelope; positivity

/-- The full composite contribution has an elementary logarithmic envelope;
no prime-counting or correlation estimate enters this bound. -/
theorem detector_composite_bound {n : ℕ} (hnp : ¬ n.Prime) :
    detector n ≤ envelope n := by
  by_cases hn : 1 < n
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
    have hb := (finiteProxy_le n).trans (primeProxy_composite_bound (parameter_nonneg n) hn hnp)
    rw [exp_half_parameter hn] at hb
    apply (mul_le_mul_of_nonneg_left hb (weight_nonneg n)).trans_eq
    unfold weight envelope
    field_simp
  · simpa only [detector, finiteProxy, if_neg hn, mul_zero] using envelope_nonneg n

noncomputable def blockBudget (k : ℕ) : ℝ := 2 / (((k+1 : ℕ) : ℝ)^2)

lemma blockBudget_nonneg (k : ℕ) : 0 ≤ blockBudget k := by unfold blockBudget; positivity

lemma summable_blockBudget : Summable blockBudget := by
  have hs : Summable (fun k : ℕ => (((k+1 : ℕ) : ℝ)^2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2))
  simpa only [blockBudget, div_eq_mul_inv] using hs.mul_left 2

lemma fiber_card_bound (S : Finset ℕ) (k : ℕ) :
    (S.filter (fun n => Nat.log 2 n = k)).card ≤ 2^(k+1) := by
  classical
  have hsub : S.filter (fun n => Nat.log 2 n = k) ⊆ range (2^(k+1)) := by
    intro n hn
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    rw [(mem_filter.mp hn).2] at h
    exact mem_range.mpr h
  exact (card_le_card hsub).trans_eq (card_range _)

lemma fiber_envelope_bound (S : Finset ℕ) (k : ℕ) :
    (∑ n ∈ S.filter (fun n => Nat.log 2 n = k), envelope n) ≤ blockBudget k := by
  classical
  have hbound (n : ℕ) (hn : n ∈ S.filter (fun n => Nat.log 2 n = k)) :
      envelope n ≤ 1 / ((2 : ℝ)^k * ((k+1 : ℕ) : ℝ)^2) := by
    by_cases hn0 : n = 0
    · simp only [hn0, envelope, Nat.cast_zero, zero_mul, div_zero]
      positivity
    have hpow := Nat.pow_log_le_self 2 hn0
    have hlog := (mem_filter.mp hn).2
    rw [hlog] at hpow
    have hcast : (2 : ℝ)^k ≤ (n : ℝ) := by exact_mod_cast hpow
    unfold envelope logSize
    rw [hlog]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right hcast (sq_nonneg _))
  calc
    _ ≤ ∑ n ∈ S.filter (fun n => Nat.log 2 n = k),
        1 / ((2 : ℝ)^k * ((k+1 : ℕ) : ℝ)^2) := sum_le_sum hbound
    _ = ((S.filter (fun n => Nat.log 2 n = k)).card : ℝ) *
        (1 / ((2 : ℝ)^k * ((k+1 : ℕ) : ℝ)^2)) := by simp
    _ ≤ ((2^(k+1) : ℕ) : ℝ) * (1 / ((2 : ℝ)^k * ((k+1 : ℕ) : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (fiber_card_bound S k)) (by positivity)
    _ = _ := by
      unfold blockBudget
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      have hk0 : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hp0 : (2 : ℝ)^k ≠ 0 := by positivity
      field_simp

theorem summable_envelope : Summable envelope := by
  classical
  apply summable_of_sum_le (c := ∑' k : ℕ, blockBudget k) envelope_nonneg
  intro S
  rw [← sum_fiberwise_of_maps_to (s := S) (t := S.image (Nat.log 2)) (g := Nat.log 2)
    (fun n hn => mem_image.mpr ⟨n, hn, rfl⟩) envelope]
  exact (sum_le_sum (fun k _ => fiber_envelope_bound S k)).trans
    (summable_blockBudget.sum_le_tsum _ (fun k _ => blockBudget_nonneg k))

noncomputable def compositeError (n : ℕ) : ℝ := if n.Prime then 0 else detector n

lemma compositeError_bounds (n : ℕ) : 0 ≤ compositeError n ∧ compositeError n ≤ envelope n := by
  unfold compositeError
  split_ifs with h
  · exact ⟨le_rfl, envelope_nonneg n⟩
  · exact ⟨detector_nonneg n, detector_composite_bound h⟩

theorem summable_compositeError : Summable compositeError :=
  summable_envelope.of_nonneg_of_le (fun n => (compositeError_bounds n).1)
    (fun n => (compositeError_bounds n).2)

#print axioms finiteProxy_prime_bounds
#print axioms detector_composite_bound
#print axioms summable_envelope
#print axioms summable_compositeError

end Erdos972PolylogMomentPrimeProxy
