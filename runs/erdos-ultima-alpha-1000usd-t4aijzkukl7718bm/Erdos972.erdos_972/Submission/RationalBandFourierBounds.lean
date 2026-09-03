import Submission.ResidueRemainderPrefix
import Submission.MidpointFourierBounds

/-! Fourier modes near any fixed nonintegral rational fraction of the modulus.
The input phase is decomposed using every residue class of the floor output. -/
namespace Erdos972RationalBandFourierBounds

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972FiniteFloorFourierBounds
open Erdos972ResiduePrimeRows Erdos972ResidueDivisorCounts Erdos972ResidueRemainderPrefix
open Erdos972ExponentialSum Erdos972DivisorMeanRecenter Erdos972MobiusPartialSums
open Erdos972ParityFloorPrefix Erdos972MidpointFourierBounds Erdos972MellinDivisorCoefficient

set_option maxHeartbeats 2000000

lemma rational_character_sum {q : ℕ} (hq : 0 < q) (a : ℤ) (ha : (a : ZMod q) ≠ 0) :
    (∑ j ∈ range q, phase ((a : ℝ)/q*j)) = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hh := AddChar.sum_mulShift (a : ZMod q) (ZMod.isPrimitive_stdAddChar q)
  simp only [ha, if_false, Nat.cast_zero] at hh
  rw [zmod_sum_range] at hh
  simpa only [mul_comm (_ : ZMod q) (a : ZMod q), stdAddChar_int_mul_nat] using hh

lemma rational_character_residue_expansion (α : ℝ) {q : ℕ} (hq : 0 < q)
    (a : ℤ) (ha : (a : ZMod q) ≠ 0) (n : ℕ) :
    phase ((a : ℝ)/q*floorMul α n) =
      ∑ j ∈ range q, phase ((a : ℝ)/q*j)*(centeredResidue α q j n : ℂ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hsum := rational_character_sum hq a ha
  have he : (∑ j ∈ range q, phase ((a : ℝ)/q*j)*
      ((if floorMul α n%q = j then 1 else 0 : ℝ) : ℂ)) =
        phase ((a : ℝ)/q*(floorMul α n%q : ℕ)) := by
    rw [sum_eq_single (floorMul α n%q)]
    · simp
    · intro j hj hne
      simp [Ne.symm hne]
    · intro hh
      exact (hh (mem_range.mpr (Nat.mod_lt _ hq))).elim
  have hmod : phase ((a : ℝ)/q*(floorMul α n%q : ℕ)) = phase ((a : ℝ)/q*floorMul α n) := by
    rw [← stdAddChar_int_mul_nat, ← stdAddChar_int_mul_nat]
    simp
  simp only [centeredResidue, Complex.ofReal_sub, mul_sub, sum_sub_distrib, ← sum_mul]
  rw [he, hmod, hsum, zero_mul, sub_zero]

lemma rational_character_prefix_bound (α : ℝ) {q X : ℕ} (hq : 0 < q)
    (a : ℤ) (ha : (a : ZMod q) ≠ 0) (f : ℕ → ℝ) {E : ℝ}
    (h : ∀ j < q, |total X (fun n => f n*centeredResidue α q j n)| ≤ E) :
    ‖∑ n ∈ Ioc 0 X, phase ((a : ℝ)/q*floorMul α n)*(f n : ℂ)‖ ≤ (q : ℝ)*E := by
  have he : (∑ n ∈ Ioc 0 X, phase ((a : ℝ)/q*floorMul α n)*(f n : ℂ)) =
      ∑ j ∈ range q, phase ((a : ℝ)/q*j)*
        (total X (fun n => f n*centeredResidue α q j n) : ℂ) := by
    simp only [rational_character_residue_expansion α hq a ha, sum_mul,
      total, Complex.ofReal_sum, Complex.ofReal_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro n hn
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (sum_le_sum (fun j hj => h j (mem_range.mp hj))).trans_eq (by simp)

lemma positive_phase_prefix_bound_complex {N : ℕ} (hN : 0 < N) (f : ℕ → ℂ)
    (g : ℕ → ℝ) (hg : Monotone g) (θ : ℝ) {E J : ℝ}
    (hprefix : ∀ X ≤ N, ‖∑ n ∈ Ioc 0 X, f n‖ ≤ E) (hspan : g N-g 1 ≤ J) :
    ‖∑ n ∈ Ioc 0 N, phase (θ*g n)*f n‖ ≤ (1+2*Real.pi*|θ| *J)*E := by
  let w : ℕ → ℂ := fun n => phase (θ*g (n+1))
  let z : ℕ → ℂ := fun n => f (n+1)
  have hp (X : ℕ) (hX : X ≤ N) : ‖∑ n ∈ range X, z n‖ ≤ E := by
    dsimp only [z]
    rw [← sum_Ioc_zero_eq_sum_range_succ]
    exact hprefix X hX
  have hv := phase_variation_monotone (fun n => g (n+1))
    (fun a b hab => hg (Nat.add_le_add_right hab 1)) θ (N-1)
  rw [Nat.sub_add_cancel hN] at hv
  have hV : (∑ n ∈ range (N-1), ‖w (n+1)-w n‖) ≤ 2*Real.pi*|θ| *J :=
    hv.trans (mul_le_mul_of_nonneg_left hspan (by positivity))
  have hh := norm_weighted_prefix w z N E 1 (2*Real.pi*|θ| *J) hp
    (by dsimp only [w]; rw [norm_phase]) hV
  simpa only [w, z, mul_comm, sum_Ioc_zero_eq_sum_range_succ] using hh

/-- Residue-twisted prefixes, not ordinary prefixes, control the moving band. -/
theorem rational_input_transform_bound {α : ℝ} (hα : 1 ≤ α) {N q : ℕ}
    (hN : 0 < N) (hq : 0 < q) (a : ℤ) (ha : (a : ZMod q) ≠ 0)
    (f : ℕ → ℝ) {E H : ℝ}
    (hp : ∀ X ≤ N, ∀ j < q,
      |total X (fun n => (f n-total N f/N)*centeredResidue α q j n)| ≤ E)
    (k : ℤ) (hk : |(k : ℝ)-(a : ℝ)/q*(floorMul α N+1 : ℕ)| ≤ H) :
    ‖centeredFloorTransform α N f (k : ZMod (floorMul α N+1))‖ ≤
      (1+2*Real.pi*H)*(q : ℝ)*E := by
  let J : ℝ := (floorMul α N+1 : ℕ)
  have hJ : 0 < J := by dsimp only [J]; positivity
  let θ : ℝ := (k : ℝ)/J-(a : ℝ)/q
  have heq : |θ| *J = |(k : ℝ)-(a : ℝ)/q*J| := by
    calc
      _ = |θ*J| := by rw [abs_mul, abs_of_pos hJ]
      _ = _ := by congr 1; dsimp only [θ]; field_simp
  have hE : 0 ≤ E := by
    simpa only [total, Ioc_self, sum_empty, abs_zero] using hp 0 (Nat.zero_le N) 0 hq
  have hb := positive_phase_prefix_bound_complex hN
    (fun n => phase ((a : ℝ)/q*floorMul α n)*((f n-total N f/N : ℝ) : ℂ))
    (fun n => (floorMul α n : ℝ))
    (fun a b h => Nat.cast_le.mpr ((floorMul_strictMono hα).monotone h)) θ
    (fun X hX => rational_character_prefix_bound α hq a ha (fun n => f n-total N f/N) (hp X hX))
    (J := J) (by dsimp only [J]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) (floorMul α 1)])
  have hident : centeredFloorTransform α N f (k : ZMod (floorMul α N+1)) =
      ∑ n ∈ Ioc 0 N, phase (θ*floorMul α n)*
        (phase ((a : ℝ)/q*floorMul α n)*((f n-total N f/N : ℝ) : ℂ)) := by
    unfold centeredFloorTransform
    apply sum_congr rfl
    intro n hn
    rw [stdAddChar_int_mul_nat, ← mul_assoc, ← phase_add]
    dsimp only [θ, J]
    rw [show ((k : ℝ)/(floorMul α N+1 : ℕ)-(a : ℝ)/q)*floorMul α n+
      (a : ℝ)/q*floorMul α n = (k : ℝ)/(floorMul α N+1 : ℕ)*floorMul α n by ring]
    ring
  rw [hident]
  apply hb.trans
  rw [mul_assoc (2*Real.pi), heq]
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*Real.pi by positivity)
  have hh' := mul_le_mul_of_nonneg_right (show 1+2*Real.pi*|(k : ℝ)-(a : ℝ)/q*J| ≤
      1+2*Real.pi*H by linarith only [hh]) (show 0 ≤ (q : ℝ)*E by positivity)
  exact hh'.trans_eq (by ring)

/-- The complete finite estimate includes the actual recentered output DFT. -/
theorem rational_fourier_term_bound {α : ℝ} (hα : 1 ≤ α) {W v N q : ℕ}
    (hW : 0 < W) (hWv : W*W ≤ v) (hvN : v ≤ N) (hq : 0 < q)
    (a : ℤ) (ha : (a : ZMod q) ≠ 0) {L Ep B H : ℝ}
    (hL : 1 ≤ L) (hlog : Real.log N ≤ L-1) (hlogM : Real.log (floorMul α N) ≤ L-1)
    (hm : |reciprocalMoebius W| ≤ 1) (hB : 0 ≤ B)
    (hprime : ∀ X ≤ N, ∀ j < q, |inputResidueRow α q j X-Chebyshev.psi X/q| ≤ Ep)
    (hdiv : ∀ X ≤ N, ∀ d ∈ Ioc 0 v, ∀ j < q,
      |((residueDivisorPairs α X d q j).card : ℝ)-(X : ℝ)/(d*q)| ≤ B)
    (k : ℤ) (hk : |(k : ℝ)-(a : ℝ)/q*(floorMul α N+1 : ℕ)| ≤ H) :
    ‖covarianceFourierTerm α N (fun n => meanCenteredTypeII W W n)
        (fun n => meanCenteredTypeII W W n) (k : ZMod (floorMul α N+1)) /
      ((floorMul α N+1 : ℕ) : ℂ)‖ ≤
      5*(1+2*Real.pi*H)*(q : ℝ)*(v : ℝ)*L^2*(Ep+40*(v : ℝ)*L^2*(B+1)) := by
  have hN : 0 < N := (Nat.mul_pos hW hW).trans_le (hWv.trans hvN)
  have hJ : (0 : ℝ) < (floorMul α N+1 : ℕ) := by positivity
  have hEp : 0 ≤ Ep := by
    have hh := hprime 0 (Nat.zero_le N) 0 hq
    simpa [inputResidueRow, Chebyshev.psi] using hh
  have hH : 0 ≤ H := (abs_nonneg _).trans hk
  have hA := rational_input_transform_bound hα hN hq a ha
    (fun n => meanCenteredTypeII W W n)
    (fun X hX j hj => centered_residue_remainder_prefix α hW hWv hvN hX hq j hL hlog hm hB
      (hprime X hX j hj) (fun Y hY d hd => hdiv Y hY d hd j hj)) k hk
  have hB' := dft_pointwise_bound (floorMul α N) (fun n => meanCenteredTypeII W W n)
    (by simp) (show 0 ≤ 5*(v : ℝ)*L^2 by positivity) (by
      intro n hn
      exact meanCenteredTypeII_abs_bound hW hW hWv (mem_Ioc.mp hn).1 hL
        ((Erdos972ExponentialSum.monotone_log_natCast (hWv.trans hvN)).trans hlog)
        ((Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp hn).2).trans hlogM) hm) k
  rw [norm_div, covarianceFourierTerm, norm_mul, Complex.norm_natCast]
  apply (div_le_iff₀ hJ).mpr
  have hh := mul_le_mul hA hB' (norm_nonneg _)
    (show 0 ≤ (1+2*Real.pi*H)*(q : ℝ)*(Ep+40*(v : ℝ)*L^2*(B+1)) by positivity [hL])
  exact hh.trans_eq (by ring)

noncomputable def rationalFrequency (J q : ℕ) (a j : ℤ) : ℤ := ⌊(a : ℝ)/q*J⌋+j

lemma rationalFrequency_near (J q : ℕ) (a j : ℤ) :
    |(rationalFrequency J q a j : ℝ)-(a : ℝ)/q*J| ≤ |(j : ℝ)|+1 := by
  have hlo := Int.floor_le ((a : ℝ)/q*J)
  have hhi := Int.lt_floor_add_one ((a : ℝ)/q*J)
  have hr : |(⌊(a : ℝ)/q*J⌋ : ℝ)-(a : ℝ)/q*J| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith only [hhi]
  have hh := abs_add_le ((⌊(a : ℝ)/q*J⌋ : ℝ)-(a : ℝ)/q*J) (j : ℝ)
  simp only [rationalFrequency, Int.cast_add]
  rw [show (⌊(a : ℝ)/q*J⌋ : ℝ)+(j : ℝ)-(a : ℝ)/q*J =
    ((⌊(a : ℝ)/q*J⌋ : ℝ)-(a : ℝ)/q*J)+(j : ℝ) by ring]
  linarith only [hh, hr]

#print axioms rational_fourier_term_bound
#print axioms rationalFrequency_near
end Erdos972RationalBandFourierBounds
