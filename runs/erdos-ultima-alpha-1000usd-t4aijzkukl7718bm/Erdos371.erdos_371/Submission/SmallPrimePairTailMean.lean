import Submission.SmallPrimePairOvershoot
import Submission.RoughEndpointScale

/-! The small-prime edge of the quadratic large-product tail has small mean
multiplicity. In particular every subpower edge is absolutely negligible. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false
set_option maxRecDepth 2048

lemma smallCrossPrimePairs_normalized_bound (N X z : ℕ) (hN : 1 < N) (hX : 1 ≤ X)
    (hz : 1 ≤ z) (hX40 : (X+1)^40 ≤ N) (hz128 : (z+1)^128 ≤ N)
    (hNz : N ≤ (z+1)^512) :
    (∑ n ∈ range N, ((smallCrossPrimePairs N X n).card : ℝ))/N ≤
      36864*Real.exp 2*(Real.log (X+1 : ℝ)/Real.log N)+4/(Real.sqrt N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlogz : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hX2 : (X+1)^2 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ X+1) (by decide : 2 ≤ 40)).trans hX40
  have hz2 : (z+1)^2 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ z+1) (by decide : 2 ≤ 128)).trans hz128
  have hsize : X*z ≤ N := by
    have hh := Nat.mul_le_mul hX2 hz2
    nlinarith only [hh]
  have hXD : X ≤ N := by nlinarith only [hX2]
  have hb := div_le_div_of_nonneg_right (smallCrossPrimePairs_finite_bound N X z hX hXD hz hsize) hNR.le
  have hloglower : Real.log N ≤ 512*Real.log (z+1 : ℝ) := by
    have hh := Real.log_le_log hNR (show (N : ℝ) ≤ (z+1 : ℝ)^512 by exact_mod_cast hNz)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hratio : Real.log (X+1 : ℝ)/Real.log (z+1 : ℝ) ≤
      512*(Real.log (X+1 : ℝ)/Real.log N) := by
    apply (div_le_iff₀ hlogz).mpr
    apply (le_of_eq (show Real.log (X+1 : ℝ)=
        (Real.log (X+1 : ℝ)/Real.log N)*Real.log N by field_simp)).trans
    have hh := mul_le_mul_of_nonneg_left hloglower
      (div_nonneg (Real.log_natCast_nonneg (X+1)) hlogN.le)
    convert hh using 1 <;> push_cast <;> ring
  let A : ℝ := (X+1 : ℝ)^10
  let B : ℝ := (z+1 : ℝ)^32
  have hA : A^4 ≤ N := by
    dsimp [A]
    rw [← pow_mul]
    exact_mod_cast hX40
  have hB : B^4 ≤ N := by
    dsimp [B]
    rw [← pow_mul]
    exact_mod_cast hz128
  have hAB : (A*B)^4 ≤ (N : ℝ)^2 := by
    rw [mul_pow,pow_two]
    exact mul_le_mul hA hB (by positivity) hNR.le
  have hsq : (A*B)^2 ≤ (N : ℝ) := by
    apply (sq_le_sq₀ (sq_nonneg (A*B)) hNR.le).mp
    simpa only [← pow_mul] using hAB
  have hprod : A*B ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hsq
  have herr : 4*(X+1 : ℝ)^10*(z+1 : ℝ)^32/N ≤ 4/Real.sqrt N := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)) hNR.le
    have he : Real.sqrt (N : ℝ)/(N : ℝ)=(Real.sqrt N)⁻¹ := Real.sqrt_div_self
    dsimp [A,B] at hh
    convert hh using 1 <;> rw [mul_div_assoc] <;> simp only [he,div_eq_mul_inv] <;> ring
  have hmain := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 72*Real.exp 2)
  apply hb.trans
  have he : (72*Real.exp 2*N*Real.log (X+1 : ℝ)/Real.log (z+1 : ℝ)+
        4*(X+1 : ℝ)^10*(z+1 : ℝ)^32)/(N : ℝ) =
      72*Real.exp 2*(Real.log (X+1 : ℝ)/Real.log (z+1 : ℝ))+
        4*(X+1 : ℝ)^10*(z+1 : ℝ)^32/N := by field_simp
  rw [he]
  convert add_le_add hmain herr using 1 <;> ring

lemma smallCrossPrimePairs_eventually_normalized_bound (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hsmall : ∀ᶠ N : ℕ in atTop, Real.log (X N+1 : ℝ)/Real.log N ≤ 1/40) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, ((smallCrossPrimePairs N (X N) n).card : ℝ))/N ≤
        36864*Real.exp 2*(Real.log (X N+1 : ℝ)/Real.log N)+4/Real.sqrt N := by
  let z := rootRoughCutoff 511
  filter_upwards [hX,hsmall,(rootRoughCutoff_atTop 511).eventually_ge_atTop 1,
    rootRoughCutoff_succ_power_eventually_le 511 128 (by decide),
    eventually_gt_atTop (1 : ℕ)] with N hXN hx hzN hz128 hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hx40 : (X N+1)^40 ≤ N := by
    apply nat_pow_le_of_log_le _ N 40 (by omega) (by omega)
    have hh := (div_le_iff₀ hlogN).mp hx
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    linarith
  have hNz : N ≤ (z N+1)^512 :=
    (rootRoughCutoff_power 511 N).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  exact smallCrossPrimePairs_normalized_bound N (X N) (z N) hN hXN hzN hx40 hz128 hNz

/-- Fixed small prime exponents can be made uniformly negligible by first
making the exponent small. No sign is used in this edge estimate. -/
theorem smallCrossPrimePairs_eventually_mean_le (X : ℕ → ℕ) (v : ℝ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N) (hv : v < 1/40)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 v))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, ((smallCrossPrimePairs N (X N) n).card : ℝ))/N ≤
        36864*Real.exp 2*v+ε := by
  have hsmall := (hlim.eventually_lt_const hv).mono (fun N hN => hN.le)
  have hroot : Tendsto (fun N : ℕ => (4 : ℝ)/Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := (hlim.const_mul (36864*Real.exp 2)).add hroot
  simp only [add_zero] at ht
  filter_upwards [smallCrossPrimePairs_eventually_normalized_bound X hX hsmall,
    ht.eventually_lt_const (show 36864*Real.exp 2*v < 36864*Real.exp 2*v+ε by linarith)] with N hb hN
  exact hb.trans hN.le

/-- The entire actual low-prime part is negligible for ANY subpower
cutoff, not just a specially selected diagonal. -/
theorem smallCrossPrimePairs_subpower_mean_zero (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ((smallCrossPrimePairs N (X N) n).card : ℝ))/N)
      atTop (𝓝 0) := by
  have hsmall := (hlim.eventually_lt_const (by norm_num : (0 : ℝ)<1/40)).mono (fun N hN => hN.le)
  have hroot : Tendsto (fun N : ℕ => (4 : ℝ)/Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := (hlim.const_mul (36864*Real.exp 2)).add hroot
  simp only [mul_zero,zero_add] at ht
  exact squeeze_zero' (Eventually.of_forall (fun N => by positivity))
    (smallCrossPrimePairs_eventually_normalized_bound X hX hsmall) ht

#print axioms smallCrossPrimePairs_normalized_bound
#print axioms smallCrossPrimePairs_eventually_mean_le
#print axioms smallCrossPrimePairs_subpower_mean_zero
end Erdos371
