import Submission.DampedMeanTailBound

/-! Signed Abel bounds for the scalar damped Möbius tail. These do not
bound the prime-input divisor-row tail. -/
namespace Erdos972SignedDampedMeanTail

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972FixedDampedCorrelation Erdos972SmoothDivisorTail
open Erdos972DivisorCovariance Erdos972DampedMeanTailBound
open Erdos972MobiusPartialSums Erdos972MobiusLaplace Erdos972ExponentialSum

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma abs_antitone_weighted_prefix (w z : ℕ → ℝ) (K : ℕ) {E : ℝ}
    (hE : 0 ≤ E) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (hz : ∀ j : ℕ, j ≤ K → |∑ n ∈ range j, z n| ≤ E) :
    |∑ n ∈ range K, w n*z n| ≤ w 0*E := by
  by_cases hK : K = 0
  · simp only [hK, range_zero, sum_empty, abs_zero]
    exact mul_nonneg (hw0 0) hE
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  have he := sum_range_by_parts w z K
  simp only [smul_eq_mul] at he
  rw [he]
  apply (abs_sub _ _).trans
  have hmain : |w (K-1)*(∑ n ∈ range K, z n)| ≤ w (K-1)*E := by
    rw [abs_mul, abs_of_nonneg (hw0 _)]
    exact mul_le_mul_of_nonneg_left (hz K le_rfl) (hw0 _)
  have htail : |∑ n ∈ range (K-1), (w (n+1)-w n)*(∑ i ∈ range (n+1), z i)| ≤
      (w 0-w (K-1))*E := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ range (K-1), (w n-w (n+1))*E := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ n))), neg_sub]
        apply mul_le_mul_of_nonneg_left (hz (n+1) (by have := mem_range.mp hn; omega))
          (sub_nonneg.mpr (hw (Nat.le_succ n)))
      _ = _ := by rw [← sum_mul, sum_range_sub']
  linarith only [hmain, htail]

lemma sum_shift_Ioc {E : Type*} [AddCommMonoid E] (f : ℕ → E) (D j : ℕ) :
    (∑ n ∈ range j, f (D+n+1)) = ∑ n ∈ Ioc D (D+j), f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, show D+(j+1) = D+j+1 by omega,
      sum_Ioc_succ_top (Nat.le_add_right D j)]

lemma shifted_reciprocalMoebius_sum (D j : ℕ) :
    (∑ n ∈ range j, (μ (D+n+1):ℝ)/(D+n+1:ℕ)) =
      reciprocalMoebius (D+j)-reciprocalMoebius D := by
  rw [sum_shift_Ioc (fun n : ℕ => (μ n:ℝ)/n)]
  have hh := sum_Ioc_consecutive (fun n : ℕ => (μ n:ℝ)/n) (Nat.zero_le D) (Nat.le_add_right D j)
  unfold reciprocalMoebius
  linarith only [hh]

lemma damping_antitone {t : ℝ} (ht : 0 ≤ t) : Antitone (damping t) := by
  intro m n hmn
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (monotone_log_natCast hmn) (neg_nonpos.mpr ht)

lemma dampedMean_interval_signed_bound {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    {D M : ℕ} (hDM : D ≤ M)
    (hm : ∀ n : ℕ, D ≤ n → |reciprocalMoebius n| ≤ ε) :
    |divisorMean M (dampedCoefficient t)-divisorMean D (dampedCoefficient t)| ≤
      2*ε*damping t D := by
  let w : ℕ → ℝ := fun n => damping t (D+n+1)
  let z : ℕ → ℝ := fun n => (μ (D+n+1):ℝ)/(D+n+1:ℕ)
  have hw : Antitone w := (damping_antitone ht).comp_monotone
    (fun a b hab => by omega)
  have hz (j : ℕ) (_hj : j ≤ M-D) : |∑ n ∈ range j, z n| ≤ 2*ε := by
    rw [show (∑ n ∈ range j, z n) = reciprocalMoebius (D+j)-reciprocalMoebius D from
      shifted_reciprocalMoebius_sum D j]
    exact (abs_sub _ _).trans (by linarith only [hm (D+j) (Nat.le_add_right _ _), hm D le_rfl])
  have hh := abs_antitone_weighted_prefix w z (M-D) (by positivity) hw
    (fun n => (damping_pos t _).le) hz
  have he : (∑ n ∈ range (M-D), w n*z n) =
      divisorMean M (dampedCoefficient t)-divisorMean D (dampedCoefficient t) := by
    have hs : (∑ n ∈ range (M-D), w n*z n) =
        ∑ n ∈ Ioc D M, dampedCoefficient t n/n := by
      have ht : (∑ n ∈ range (M-D), w n*z n) =
          ∑ n ∈ range (M-D), dampedCoefficient t (D+n+1)/(D+n+1:ℕ) := by
        apply sum_congr rfl
        intro n hn
        dsimp only [w, z, dampedCoefficient, damping]
        ring
      rw [ht, sum_shift_Ioc (fun n : ℕ => dampedCoefficient t n/n), Nat.add_sub_of_le hDM]
    rw [hs]
    have hc := sum_Ioc_consecutive (fun n : ℕ => dampedCoefficient t n/n) (Nat.zero_le D) hDM
    unfold divisorMean
    linarith only [hc]
  rw [he] at hh
  apply hh.trans
  have h := mul_le_mul_of_nonneg_right (damping_antitone ht (show D ≤ D+0+1 by omega))
    (show 0 ≤ 2*ε by positivity)
  dsimp only [w] at hh ⊢
  nlinarith only [h]

/-- The signed scalar tail has NO inverse-t loss before normalizing the
smooth Mangoldt function. The cutoff must satisfy the stated actual
reciprocal Möbius bound. -/
theorem dampedMean_tail_signed {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) {D : ℕ}
    (hm : ∀ n : ℕ, D ≤ n → |reciprocalMoebius n| ≤ ε) :
    |divisorMean D (dampedCoefficient t)-dampedMean t| ≤ 2*ε*damping t D := by
  have hh := ((divisorMean_tendsto ht).sub_const (divisorMean D (dampedCoefficient t))).abs
  have hb := le_of_tendsto hh (by
    filter_upwards [eventually_ge_atTop D] with M hM
    exact dampedMean_interval_signed_bound ht.le hε hM hm)
  rwa [abs_sub_comm] at hb

/-- One cutoff works uniformly for EVERY positive damping parameter. -/
theorem eventually_uniform_signed_dampedMean_tail {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ, 0 < t →
      |divisorMean D (dampedCoefficient t)-dampedMean t| ≤ ε*damping t D := by
  have hlim := reciprocalMoebius_tendsto_zero.abs
  simp only [abs_zero] at hlim
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (ε/2) (by positivity))
  filter_upwards [eventually_ge_atTop B] with D hD
  intro t ht
  have hh := dampedMean_tail_signed ht (show 0 ≤ ε/2 by positivity)
    (fun n hn => (hB n (hD.trans hn)).le)
  simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hh

#print axioms dampedMean_tail_signed
#print axioms eventually_uniform_signed_dampedMean_tail

end Erdos972SignedDampedMeanTail
