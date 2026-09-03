import Submission.FloorCovarianceFourier
import Submission.RecenteredPrefixScales

/-! Finite low-frequency estimates for the exact floor Fourier formula.
The bounds are obtained from actual arithmetic prefix errors. -/
namespace Erdos972FiniteFloorFourierBounds

open Finset ArithmeticFunction
open Erdos972ExponentialSum Erdos972MellinDivisorCoefficient
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier

set_option maxHeartbeats 1500000

lemma zmod_sum_range {J : ℕ} [NeZero J] (f : ZMod J → ℂ) :
    (∑ j : ZMod J, f j) = ∑ n ∈ range J, f (n : ZMod J) := by
  apply sum_bij (fun j _ => j.val)
  · intro j hj; exact mem_range.mpr j.val_lt
  · intro a ha b hb h; exact ZMod.val_injective J h
  · intro n hn
    exact ⟨(n : ZMod J), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
  · intro j hj; rw [ZMod.natCast_zmod_val]

lemma stdAddChar_int_mul_nat {J : ℕ} [NeZero J] (k : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((k : ZMod J)*(n : ZMod J)) = phase ((k : ℝ)/J*n) := by
  rw [show (k : ZMod J)*(n : ZMod J) = ((k*(n : ℤ) : ℤ) : ZMod J) by push_cast; rfl,
    ZMod.stdAddChar_coe, phase]
  congr 1
  push_cast
  ring

lemma phase_variation_monotone (w : ℕ → ℝ) (hw : Monotone w) (θ : ℝ) (K : ℕ) :
    (∑ n ∈ range K, ‖phase (θ*w (n+1))-phase (θ*w n)‖) ≤
      2*Real.pi*|θ| *(w K-w 0) := by
  calc
    _ ≤ ∑ n ∈ range K, 2*Real.pi*|θ| *(w (n+1)-w n) := by
      apply sum_le_sum
      intro n hn
      have hh := norm_phase_sub_le (θ*w (n+1)) (θ*w n)
      rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hw (Nat.le_succ n)))] at hh
      exact hh.trans_eq (by ring)
    _ = _ := by rw [← mul_sum, sum_range_sub]

lemma positive_phase_prefix_bound {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ)
    (g : ℕ → ℝ) (hg : Monotone g) (θ : ℝ) {E J : ℝ}
    (hprefix : ∀ X ≤ N, |total X f| ≤ E) (hspan : g N-g 1 ≤ J) :
    ‖∑ n ∈ Ioc 0 N, phase (θ*g n)*(f n : ℂ)‖ ≤ (1+2*Real.pi*|θ| *J)*E := by
  let w : ℕ → ℂ := fun n => phase (θ*g (n+1))
  let z : ℕ → ℂ := fun n => (f (n+1) : ℂ)
  have hp (X : ℕ) (hX : X ≤ N) : ‖∑ n ∈ range X, z n‖ ≤ E := by
    dsimp only [z]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      ← sum_Ioc_zero_eq_sum_range_succ]
    exact hprefix X hX
  have hv := phase_variation_monotone (fun n => g (n+1))
    (fun a b hab => hg (Nat.add_le_add_right hab 1)) θ (N-1)
  rw [Nat.sub_add_cancel hN] at hv
  have hV : (∑ n ∈ range (N-1), ‖w (n+1)-w n‖) ≤ 2*Real.pi*|θ| *J :=
    hv.trans (mul_le_mul_of_nonneg_left hspan (by positivity))
  have hh := norm_weighted_prefix w z N E 1 (2*Real.pi*|θ| *J) hp
    (by dsimp only [w]; rw [norm_phase]) hV
  simpa only [w, z, mul_comm, sum_Ioc_zero_eq_sum_range_succ] using hh

lemma dft_positive_sum (M : ℕ) (f : ℕ → ℝ) (hf : f 0 = 0) (k : ℤ) :
    ZMod.dft (outputLift M f) (k : ZMod (M+1)) =
      ∑ n ∈ Ioc 0 M, phase ((-(k : ℝ))/(M+1 : ℕ)*n)*(f n : ℂ) := by
  rw [ZMod.dft_apply, zmod_sum_range]
  have ht (n : ℕ) (hn : n ∈ range (M+1)) :
      ZMod.stdAddChar (-((n : ZMod (M+1))*(k : ZMod (M+1)))) • outputLift M f (n : ZMod (M+1)) =
        phase ((-(k : ℝ))/(M+1 : ℕ)*n)*(f n : ℂ) := by
    rw [outputLift, ZMod.val_natCast_of_lt (mem_range.mp hn), smul_eq_mul,
      show -((n : ZMod (M+1))*(k : ZMod (M+1))) = ((-k : ℤ) : ZMod (M+1))*(n : ZMod (M+1)) by push_cast; ring,
      stdAddChar_int_mul_nat]
    simp only [Int.cast_neg]
  rw [sum_congr rfl ht]
  exact (sum_Ioc_zero_eq_sum_range_of_zero _ (by simp [hf]) M).symm

lemma positive_character_sum {M : ℕ} (k : ℤ) (hk : (k : ZMod (M+1)) ≠ 0) :
    (∑ n ∈ Ioc 0 M, phase ((-(k : ℝ))/(M+1 : ℕ)*n)) = -1 := by
  have hh := AddChar.sum_mulShift (-(k : ZMod (M+1))) (ZMod.isPrimitive_stdAddChar (M+1))
  simp only [neg_ne_zero.mpr hk, if_false, Nat.cast_zero] at hh
  rw [zmod_sum_range] at hh
  have ht (n : ℕ) : ZMod.stdAddChar ((n : ZMod (M+1))*(-(k : ZMod (M+1)))) =
      phase ((-(k : ℝ))/(M+1 : ℕ)*n) := by
    rw [mul_comm, ← Int.cast_neg, stdAddChar_int_mul_nat, Int.cast_neg]
  simp only [ht] at hh
  rw [sum_range_succ'] at hh
  rw [← sum_Ioc_zero_eq_sum_range_succ (fun n : ℕ => phase ((-(k : ℝ))/(M+1 : ℕ)*n))] at hh
  have hz : phase ((-(k : ℝ))/(M+1 : ℕ)*(0 : ℕ)) = 1 := by simp [phase]
  rw [hz] at hh
  linear_combination hh

/-- An uncentered output Fourier coefficient at a nonzero frequency is
bounded after retaining its constant-model contribution exactly. -/
theorem output_dft_prefix_bound {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) (hf : f 0 = 0)
    {ρ E : ℝ} (hρ : |ρ| ≤ E) (hp : ∀ X ≤ M, |total X f-ρ*X| ≤ E)
    (k : ℤ) (hk : (k : ZMod (M+1)) ≠ 0) :
    ‖ZMod.dft (outputLift M f) (k : ZMod (M+1))‖ ≤ (2+2*Real.pi*|(k : ℝ)|)*E := by
  let J : ℝ := (M+1 : ℕ)
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hprefix (X : ℕ) (hX : X ≤ M) : |total X (fun n => f n-ρ)| ≤ E := by
    simpa only [total, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero,
      nsmul_eq_mul, mul_comm] using hp X hX
  have hb := positive_phase_prefix_bound hM (fun n => f n-ρ) (fun n => (n : ℝ))
    (fun a b h => Nat.cast_le.mpr h) (-(k : ℝ)/J) hprefix
    (J := J) (by
      change (M : ℝ)-(1 : ℕ) ≤ J
      dsimp only [J]
      push_cast
      linarith)
  have hcoef : |-(k : ℝ)/J| *J = |(k : ℝ)| := by
    rw [abs_div, abs_neg, abs_of_pos hJ]
    exact div_mul_cancel₀ _ hJ.ne'
  have he : ZMod.dft (outputLift M f) (k : ZMod (M+1)) =
      (∑ n ∈ Ioc 0 M, phase (-(k : ℝ)/J*n)*((f n-ρ : ℝ) : ℂ))-(ρ : ℂ) := by
    rw [dft_positive_sum M f hf k]
    simp only [Complex.ofReal_sub, mul_sub, sum_sub_distrib, ← sum_mul]
    rw [show (∑ n ∈ Ioc 0 M, phase (-(k : ℝ)/J*n)) = -1 from positive_character_sum k hk]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hb' : ‖∑ n ∈ Ioc 0 M, phase (-(k : ℝ)/J*n)*((f n-ρ : ℝ) : ℂ)‖ ≤
      (1+2*Real.pi*|(k : ℝ)|)*E := by
    convert hb using 1
    rw [mul_assoc (2*Real.pi), hcoef]
  linarith only [hb', hρ]

/-- The floor phase is retained. Its variation is controlled by monotonicity,
not by replacing floor(alpha*n) with alpha*n. -/
theorem input_floor_transform_prefix_bound {α : ℝ} (hα : 1 ≤ α)
    {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) {E : ℝ}
    (hp : ∀ X ≤ N, |total X f-(X : ℝ)/N*total N f| ≤ E) (k : ℤ) :
    ‖centeredFloorTransform α N f (k : ZMod (floorMul α N+1))‖ ≤
      (1+2*Real.pi*|(k : ℝ)|)*E := by
  let J : ℝ := (floorMul α N+1 : ℕ)
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hprefix (X : ℕ) (hX : X ≤ N) : |total X (fun n => f n-total N f/N)| ≤ E := by
    have he : total X (fun n => f n-total N f/N) = total X f-(X : ℝ)/N*total N f := by
      simp only [total, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      ring
    rw [he]
    exact hp X hX
  have hb := positive_phase_prefix_bound hN (fun n => f n-total N f/N)
    (fun n => (floorMul α n : ℝ))
    (fun a b h => Nat.cast_le.mpr ((floorMul_strictMono hα).monotone h))
    ((k : ℝ)/J) hprefix
    (show (floorMul α N : ℝ)-(floorMul α 1 : ℝ) ≤ J by
      dsimp only [J]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) (floorMul α 1)])
  have hcoef : |(k : ℝ)/J| *J = |(k : ℝ)| := by
    rw [abs_div, abs_of_pos hJ]
    exact div_mul_cancel₀ _ hJ.ne'
  rw [mul_assoc (2*Real.pi), hcoef] at hb
  simpa only [centeredFloorTransform, stdAddChar_int_mul_nat, J, mul_comm] using hb

#print axioms output_dft_prefix_bound
#print axioms input_floor_transform_prefix_bound

end Erdos972FiniteFloorFourierBounds
