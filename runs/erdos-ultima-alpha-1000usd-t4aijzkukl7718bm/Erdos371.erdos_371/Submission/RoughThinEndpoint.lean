import Submission.RoughEndpointScale

/-! Rough reciprocal mass in a band whose lower endpoint has logarithmic
ratio tending to one. The sieve power is fixed before the limit. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma rough_interval_power_bound (S : Finset ℕ) (z A N K : ℕ)
    (hz : 1 ≤ z) (hA : 1 ≤ A) (hAN : A ≤ N) (hN : 1 < N)
    (hNK : N ≤ (z+1)^K) (hz128 : (z+1)^128 ≤ N) (hNA : N ≤ A^2)
    (hS : ∀ m ∈ S, A ≤ m ∧ m ≤ N ∧ ∀ p ∈ (z+1).primesBelow, ¬p ∣ m) :
    (∑ m ∈ S, (1 : ℝ)/m) ≤
      4*Real.exp 1*K*((1-Real.log A/Real.log N)/Real.log 2+2/Real.log N)+
      4*((K : ℝ)/Real.log 2*(Real.log (z+1 : ℝ)/(z+1 : ℝ)^32)+2/(z+1 : ℝ)^32) := by
  let b : ℝ := z+1
  let w : ℝ := (Real.log N-Real.log A)/Real.log 2+2
  have hb : 0 < b := by dsimp [b]; positivity
  have hlb : 0 < Real.log b := Real.log_pos (by dsimp [b]; exact_mod_cast (show 1 < z+1 by omega))
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAR : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hw : 0 ≤ w := by
    have hlogAN := Real.log_le_log hAR (show (A : ℝ) ≤ N by exact_mod_cast hAN)
    dsimp [w]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hlogAN) hl2.le) (by norm_num)
  have hlogNK : Real.log N ≤ (K : ℝ)*Real.log b := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)
      (show (N : ℝ) ≤ b^K by dsimp [b]; exact_mod_cast hNK)
    simpa only [Real.log_pow] using hh
  have hA64 : (z+1)^64 ≤ A := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    rw [← pow_mul]
    exact hz128.trans hNA
  have herror : b^32/(A : ℝ) ≤ 1/b^32 := by
    apply (div_le_div_iff₀ hAR (by positivity : 0 < b^32)).mpr
    rw [← pow_add]
    simpa only [one_mul] using (show b^64 ≤ (A : ℝ) by dsimp [b]; exact_mod_cast hA64)
  have hwlog : w/Real.log b ≤ (K : ℝ)*w/Real.log N := by
    apply (div_le_div_iff₀ hlb hlN).mpr
    have hh := mul_le_mul_of_nonneg_left hlogNK hw
    nlinarith
  have hwupper : w ≤ (K : ℝ)*Real.log b/Real.log 2+2 := by
    dsimp only [w]
    apply add_le_add _ le_rfl
    exact div_le_div_of_nonneg_right ((sub_le_self _ (Real.log_natCast_nonneg A)).trans hlogNK) hl2.le
  have hratio : w/Real.log N = (1-Real.log A/Real.log N)/Real.log 2+2/Real.log N := by
    dsimp [w]
    field_simp
    <;> ring
  calc
    _ ≤ w*(4*Real.exp 1/Real.log b+4*b^32/A) := rough_interval_reciprocal_le S z A N hz hA hAN hS
    _ = 4*Real.exp 1*(w/Real.log b)+4*w*(b^32/A) := by ring
    _ ≤ 4*Real.exp 1*((K : ℝ)*w/Real.log N)+4*w*(1/b^32) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hwlog (by positivity)
      · exact mul_le_mul_of_nonneg_left herror (by positivity)
    _ ≤ 4*Real.exp 1*((K : ℝ)*w/Real.log N)+4*((K : ℝ)*Real.log b/Real.log 2+2)*(1/b^32) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwupper (by norm_num)) (by positivity)
    _ = _ := by
      rw [mul_div_assoc,hratio]
      dsimp only [b]
      ring

/-- The reciprocal mass of W-rough integers in a logarithmically thin
endpoint band tends to zero, with W bounded below by a fixed power. -/
theorem rough_thin_endpoint_reciprocals_zero (S : ℕ → Finset ℕ) (A W : ℕ → ℕ)
    (L : ℕ) (hL : 0 < L) (hW : ∀ᶠ N : ℕ in atTop, N ≤ (W N)^L)
    (hA : ∀ᶠ N : ℕ in atTop, 1 ≤ A N ∧ A N ≤ N)
    (hlogA : Tendsto (fun N : ℕ => Real.log (A N)/Real.log N) atTop (𝓝 1))
    (hS : ∀ᶠ N : ℕ in atTop, ∀ m ∈ S N, A N ≤ m ∧ m ≤ N ∧
      ∀ p ∈ (W N+1).primesBelow, ¬p ∣ m) :
    Tendsto (fun N : ℕ => ∑ m ∈ S N, (1 : ℝ)/m) atTop (𝓝 0) := by
  obtain ⟨K,z,hz,hscale⟩ := exists_rough_endpoint_scale W L hL hW
  have hzR : Tendsto (fun N : ℕ => (z N+1 : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hz).atTop_add tendsto_const_nhds
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun N : ℕ => (2 : ℝ)/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogN
  have hmain := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hlogA).div_const (Real.log 2)).add htwo).const_mul
    (4*Real.exp 1*K)
  simp only [sub_self,zero_div,add_zero,mul_zero] at hmain
  have hlogpow : Tendsto (fun x : ℝ => Real.log x/x^32) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (show (0 : ℝ) < (32 : ℕ) by norm_num)).tendsto_div_nhds_zero
  have hinvpow : Tendsto (fun N : ℕ => (2 : ℝ)/(z N+1 : ℝ)^32) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 32 ≠ 0)).comp hzR)
  have herr := (((hlogpow.comp hzR).const_mul ((K : ℝ)/Real.log 2)).add hinvpow).const_mul 4
  simp only [mul_zero,add_zero] at herr
  have ht := hmain.add herr
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => sum_nonneg (fun m _ => by positivity))) _ ht
  filter_upwards [hscale,hA,hS,hlogA.eventually_const_lt (show (1/2 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (1 : ℕ)] with N hs ha hm halog hN
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hNA : N ≤ (A N)^2 := by
    have hh := (lt_div_iff₀ hlN).mp halog
    have hlog : Real.log N ≤ Real.log ((A N : ℝ)^2) := by
      rw [Real.log_pow]
      norm_num
      linarith
    have hAR : (0 : ℝ) < A N := by exact_mod_cast (show 0 < A N by omega)
    exact_mod_cast (Real.log_le_log_iff
      (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)
      (by positivity : (0 : ℝ) < (A N : ℝ)^2)).mp hlog
  apply rough_interval_power_bound (S N) (z N) (A N) N K hs.1 ha.1 ha.2 hN hs.2.2.1 hs.2.2.2 hNA
  intro m hmem
  obtain ⟨hl,hu,hr⟩ := hm m hmem
  refine ⟨hl,hu,?_⟩
  intro p hp
  apply hr p
  obtain ⟨hpz,hpp⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨hpz.trans_le (Nat.add_le_add_right hs.2.1 1),hpp⟩

#print axioms rough_thin_endpoint_reciprocals_zero
#print axioms rough_interval_power_bound
end Erdos371.FiniteSieve
