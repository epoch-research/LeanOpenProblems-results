import Submission.ParityFloorPrefix

/-! A Fourier estimate near normalized frequency 1/2. Unlike fixed integer
modes, these frequencies move proportionally to the full Fourier modulus. -/
namespace Erdos972MidpointFourierBounds

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972FiniteFloorFourierBounds
open Erdos972ParityFloorPrefix Erdos972ExponentialSum
open Erdos972DivisorMeanRecenter Erdos972MobiusPartialSums
open Erdos972DivisorPairCount Erdos972DualPrimeRows

set_option maxHeartbeats 1500000

lemma paritySign_eq_neg_one_pow (n : ℕ) : paritySign n = (-1 : ℝ)^n := by
  by_cases h : 2 ∣ n
  · rw [paritySign, if_pos h, (even_iff_two_dvd.mpr h).neg_one_pow]
  · have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => h he.two_dvd)
    rw [paritySign, if_neg h, ho.neg_one_pow]

lemma phase_half_nat (n : ℕ) : phase ((n : ℝ)/2) = (paritySign n : ℂ) := by
  have hh : phase (1/2 : ℝ) = -1 := by
    rw [phase, show ((2*Real.pi : ℝ) : ℂ)*Complex.I*((1/2 : ℝ) : ℂ) =
      (Real.pi : ℂ)*Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  rw [show (n : ℝ)/2 = (1/2 : ℝ)*n by ring, phase_nat_mul, hh, paritySign_eq_neg_one_pow]
  push_cast
  rfl

lemma phase_parity_split (θ : ℝ) (n : ℕ) :
    phase (θ*n) = phase ((θ-1/2)*n)*(paritySign n : ℂ) := by
  rw [← phase_half_nat, ← phase_add]
  congr 1
  ring

/-- A bound from the PARITY-TWISTED centered prefixes; this is not the
ordinary low-frequency prefix bound with a large k substituted into it. -/
theorem midpoint_input_transform_bound {α : ℝ} (hα : 1 ≤ α) {N : ℕ}
    (hN : 0 < N) (f : ℕ → ℝ) {E H : ℝ}
    (hp : ∀ X ≤ N, |total X (fun n => (f n-total N f/N)*paritySign (floorMul α n))| ≤ E)
    (k : ℤ) (hk : |(k : ℝ)-(floorMul α N+1 : ℕ)/2| ≤ H) :
    ‖centeredFloorTransform α N f (k : ZMod (floorMul α N+1))‖ ≤
      (1+2*Real.pi*H)*E := by
  let J : ℝ := (floorMul α N+1 : ℕ)
  have hJ : 0 < J := by dsimp only [J]; positivity
  let θ : ℝ := (k : ℝ)/J-1/2
  have heq : |θ| *J = |(k : ℝ)-J/2| := by
    calc
      _ = |θ*J| := by rw [abs_mul, abs_of_pos hJ]
      _ = _ := by congr 1; dsimp only [θ]; field_simp
  have hE : 0 ≤ E := by simpa only [total, Ioc_self, sum_empty, abs_zero] using hp 0 (Nat.zero_le N)
  have hb := positive_phase_prefix_bound hN
    (fun n => (f n-total N f/N)*paritySign (floorMul α n))
    (fun n => (floorMul α n : ℝ))
    (fun a b h => Nat.cast_le.mpr ((floorMul_strictMono hα).monotone h)) θ hp
    (J := J) (by
      dsimp only [J]
      push_cast
      linarith only [Nat.cast_nonneg (α := ℝ) (floorMul α 1)])
  have hident : centeredFloorTransform α N f (k : ZMod (floorMul α N+1)) =
      ∑ n ∈ Ioc 0 N, phase (θ*floorMul α n)*
        (((f n-total N f/N)*paritySign (floorMul α n) : ℝ) : ℂ) := by
    unfold centeredFloorTransform
    apply sum_congr rfl
    intro n hn
    rw [stdAddChar_int_mul_nat, phase_parity_split, Complex.ofReal_mul]
    dsimp only [θ, J]
    ring
  rw [hident]
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*Real.pi by positivity)
  rw [mul_assoc (2*Real.pi), heq]
  exact mul_le_mul_of_nonneg_right (by linarith only [hh]) hE

lemma dft_pointwise_bound (M : ℕ) (f : ℕ → ℝ) (hf : f 0 = 0) {A : ℝ}
    (hA : 0 ≤ A) (hp : ∀ n ∈ Ioc 0 M, |f n| ≤ A) (k : ℤ) :
    ‖ZMod.dft (outputLift M f) (k : ZMod (M+1))‖ ≤ A*(M+1 : ℕ) := by
  rw [dft_positive_sum M f hf k]
  apply (norm_sum_le _ _).trans
  have hh : (∑ n ∈ Ioc 0 M, ‖phase (-(k : ℝ)/(M+1 : ℕ)*n)*(f n : ℂ)‖) ≤ (M : ℝ)*A := by
    simp only [norm_mul, norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (sum_le_sum hp).trans_eq (by simp)
  have hm : (M : ℝ) ≤ (M+1 : ℕ) := by exact_mod_cast Nat.le_succ M
  exact hh.trans ((mul_le_mul_of_nonneg_right hm hA).trans_eq (by ring))

/-- Complete finite normalized Fourier-term estimate near the midpoint.
It includes the actual output remainder rather than an unweighted count. -/
theorem midpoint_fourier_term_bound {α : ℝ} (hα : 1 ≤ α) {W v N : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N)
    {L Ep Bd H : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1)
    (hlogM : Real.log (floorMul α N) ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hBd : 0 ≤ Bd)
    (hprime : ∀ X ≤ N, |inputDivisorRow α 2 X-Chebyshev.psi X/2| ≤ Ep)
    (hdiv : ∀ X ≤ N, ∀ a ∈ Ioc 0 v, ∀ b ∈ Ioc 0 2,
      |((divisorPairs α X a b).card : ℝ)-(X : ℝ)/(a*b)| ≤ Bd)
    (k : ℤ) (hk : |(k : ℝ)-(floorMul α N+1 : ℕ)/2| ≤ H) :
    ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
        (fun n => meanCenteredTypeII W W n) (k : ZMod (floorMul α N+1)) /
      ((floorMul α N+1 : ℕ) : ℂ)‖ ≤
      5*(1+2*Real.pi*H)*(v : ℝ)*L^2*(2*Ep+64*(v : ℝ)*L^3*(Bd+1)) := by
  have hN : 0 < N := (Nat.mul_pos hW hW).trans_le (hWv.trans hvN)
  have hJ : (0 : ℝ) < (floorMul α N+1 : ℕ) := by positivity
  have hEp : 0 ≤ Ep := by
    have hh := hprime 0 (Nat.zero_le N)
    simpa [inputDivisorRow, Chebyshev.psi] using hh
  have hH : 0 ≤ H := (abs_nonneg _).trans hk
  have hA := midpoint_input_transform_bound hα hN
    (fun n => meanCenteredTypeII W W n)
    (fun X hX => centered_parity_prefix_bound α hW hWv hvN hX hL hlog hm hBd hprime hdiv) k hk
  have hB := dft_pointwise_bound (floorMul α N) (fun n => meanCenteredTypeII W W n)
    (by simp) (show 0 ≤ 5*(v : ℝ)*L^2 by positivity) (by
      intro n hn
      exact meanCenteredTypeII_abs_bound hW hW hWv (mem_Ioc.mp hn).1 hL
        ((Erdos972ExponentialSum.monotone_log_natCast (hWv.trans hvN)).trans hlog)
        ((Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hn).2).trans hlogM) hm) k
  rw [norm_div, covarianceFourierTerm, norm_mul, Complex.norm_natCast]
  apply (div_le_iff₀ hJ).mpr
  have hh := mul_le_mul hA hB (norm_nonneg _)
    (show 0 ≤ (1+2*Real.pi*H)*(2*Ep+64*(v : ℝ)*L^3*(Bd+1)) by positivity [hL])
  exact hh.trans_eq (by ring)

/-- Integer representatives of a fixed-width band around J/2. -/
def midpointFrequency (J : ℕ) (j : ℤ) : ℤ := (J/2 : ℕ)+j

lemma midpointFrequency_near (J : ℕ) (j : ℤ) :
    |(midpointFrequency J j : ℝ)-(J : ℝ)/2| ≤ |(j : ℝ)|+1 := by
  have hlo : ((J/2 : ℕ) : ℝ) ≤ (J : ℝ)/2 := Nat.cast_div_le
  have hhi : (J : ℝ)/2 < ((J/2 : ℕ) : ℝ)+1 := by
    have hh := Nat.lt_floor_add_one ((J : ℝ)/2)
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Nat.floor_div_natCast, Nat.floor_natCast] at hh
    exact hh
  have hround : |((J/2 : ℕ) : ℝ)-(J : ℝ)/2| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith only [hhi]
  have hh := abs_add_le (((J/2 : ℕ) : ℝ)-(J : ℝ)/2) (j : ℝ)
  simp only [midpointFrequency, Int.cast_add, Int.cast_natCast]
  have he : ((J/2 : ℕ) : ℝ)+(j : ℝ)-(J : ℝ)/2 =
      (((J/2 : ℕ) : ℝ)-(J : ℝ)/2)+(j : ℝ) := by ring
  rw [he]
  linarith only [hh, hround]

#print axioms midpoint_fourier_term_bound
#print axioms midpointFrequency_near

end Erdos972MidpointFourierBounds
