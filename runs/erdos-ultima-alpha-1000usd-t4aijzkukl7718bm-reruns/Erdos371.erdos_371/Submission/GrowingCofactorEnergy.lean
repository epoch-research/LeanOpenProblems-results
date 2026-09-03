import FormalConjecturesUtil
import Submission.BoundedCofactorEnergy

/-! An explicit growing cofactor range with logarithmically small signed
energy. This does not estimate the complementary range of prime groups,
and does not settle Erdős 371. -/

namespace Erdos371GrowingCofactorEnergy

open Finset Filter Erdos371PrimeDiscrepancy Erdos371BoundedCofactorEnergy
open Erdos371BoundedCofactorCancellation Erdos371SieveParameters
open Erdos371SieveScaleBands
open scoped Topology

/-- The largest available index for the explicit two-linear-form sieve. -/
def sieveIndex (N : ℕ) : ℕ := Nat.findGreatest (fun k => threshold k ≤ N) N

/-- The cofactor bound at sieve index `k`. -/
def atIndex (k : ℕ) : ℕ := 2^(k/10)

def cofactorCutoff (N : ℕ) : ℕ := atIndex (sieveIndex N)

lemma index_le_threshold (k : ℕ) : k ≤ threshold k := by
  rw [threshold_eq_pow]
  exact (index_le_exponent k).trans (Nat.lt_two_pow_self.le)

lemma sieveIndex_ge {K N : ℕ} (hN : threshold K ≤ N) : K ≤ sieveIndex N :=
  Nat.le_findGreatest ((index_le_threshold K).trans hN) hN

lemma sieveIndex_spec {N : ℕ} (hN : threshold 0 ≤ N) : threshold (sieveIndex N) ≤ N :=
  Nat.findGreatest_spec (P := fun k => threshold k ≤ N) (Nat.zero_le N) hN

lemma sieveIndex_next (N : ℕ) : N < threshold (sieveIndex N+1) := by
  by_cases h : sieveIndex N+1 ≤ N
  · have hh := Nat.findGreatest_is_greatest (P := fun k => threshold k ≤ N)
      (show sieveIndex N < sieveIndex N+1 by omega) h
    omega
  · have hh := index_le_threshold (sieveIndex N+1)
    omega

lemma sieveIndex_tendsto : Tendsto sieveIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  exact (eventually_ge_atTop (threshold K)).mono fun _ h => sieveIndex_ge h

lemma indexQuotient_tendsto :
    Tendsto (fun N => sieveIndex N/10) atTop atTop :=
  (Nat.tendsto_div_const_atTop (by decide : (10:ℕ) ≠ 0)).comp sieveIndex_tendsto

theorem cofactorCutoff_tendsto : Tendsto cofactorCutoff atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).comp indexQuotient_tendsto

lemma atIndex_pos (k : ℕ) : 0 < atIndex k := by unfold atIndex; positivity

lemma atIndex_fifth_le (k : ℕ) : (atIndex k)^5 ≤ cutoff k := by
  have hq : 5*(k/10) ≤ k := by have := Nat.mul_div_le k 10; omega
  have he : (atIndex k)^5 = 2^(5*(k/10)) := by
    rw [atIndex, ← pow_mul, Nat.mul_comm]
  rw [he]
  exact (Nat.pow_le_pow_right (by decide) hq).trans
    (Nat.pow_le_pow_right (by decide) Nat.lt_two_pow_self.le)

lemma cutoff_fourth_le_threshold (k : ℕ) : (cutoff k)^4 ≤ threshold k := by
  unfold threshold
  apply Nat.pow_le_pow_right (by have := cutoff_two_le k; omega)
  have := depth_pos k
  omega

lemma log_bound {k N : ℕ} (hN : 0 < N) (hnext : N < threshold (k+1)) :
    Real.log (N:ℝ) ≤ exponent (k+1) := by
  have hh := Real.log_le_log (Nat.cast_pos.mpr hN)
    (Nat.cast_le.mpr hnext.le : (N:ℝ) ≤ threshold (k+1))
  rw [threshold_eq_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hh
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  exact hh.trans (by simpa using (mul_le_mul_of_nonneg_left hl
    (Nat.cast_nonneg (exponent (k+1)) : (0:ℝ) ≤ exponent (k+1))))

noncomputable def indexError (j : ℕ) : ℝ :=
  884736*((j:ℝ)+1)^2*(1/32:ℝ)^j

lemma fifth_coefficient_bound (k : ℕ) :
    (atIndex k:ℝ)^5 * coefficient k ≤ indexError (k/10) := by
  let j := k/10
  have hlow : 10*j ≤ k := Nat.mul_div_le k 10
  have hhigh : k+2 ≤ 12*(j+1) := by
    have hh := Nat.lt_mul_div_succ k (by decide : 0 < (10:ℕ))
    dsimp [j]
    omega
  have hhighR : (k:ℝ)+2 ≤ 12*((j:ℝ)+1) := by exact_mod_cast hhigh
  have hpower : (atIndex k:ℝ)^5*(1/2:ℝ)^k ≤ (1/32:ℝ)^j := by
    calc
      _ ≤ (atIndex k:ℝ)^5*(1/2:ℝ)^(10*j) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hlow) (by positivity)
      _ = ((2:ℝ)^5)^j*((1/2:ℝ)^10)^j := by
        simp only [atIndex, Nat.cast_pow, Nat.cast_ofNat, pow_mul]
        rw [← pow_mul, ← pow_mul, Nat.mul_comm j 5, pow_mul]
      _ = _ := by rw [← mul_pow]; norm_num
  have hsq : ((k:ℝ)+2)^2 ≤ 144*((j:ℝ)+1)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (k:ℝ)+2) hhighR 2
    nlinarith
  rw [coefficient_eq]
  calc
    _ = 6144*((k:ℝ)+2)^2*((atIndex k:ℝ)^5*(1/2:ℝ)^k) := by ring
    _ ≤ 6144*(144*((j:ℝ)+1)^2)*(1/32:ℝ)^j := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      · exact hpower
      · positivity
      · positivity
    _ = indexError (k/10) := by unfold indexError; dsimp [j]; ring

lemma indexError_tendsto_zero : Tendsto indexError atTop (𝓝 0) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (r := 1/32) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := 1/32) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 1/32) (by norm_num)
  have hh := ((h2.add (h1.mul_left 2)).add h0).mul_left 884736
  have hs : Summable indexError := hh.congr (fun j => by unfold indexError; ring)
  exact hs.tendsto_atTop_zero

noncomputable def constant : ℝ := 2+18*(Real.exp 1)^2

lemma constant_nonneg : 0 ≤ constant := by unfold constant; positivity

lemma energy_sieve_bound {A k N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (hlarge : threshold k ≤ N) :
    highEnergy A N ≤ constant*(A:ℝ)^5*(1+(cutoff k:ℝ)+(N+1:ℕ)/(4:ℝ)^k)+1 := by
  have hs := irregularPrimes_sieve_bound hA k (N+1) (by omega) (by omega)
  have hc : (A:ℝ)^2*((A:ℝ)+1+6*(Real.exp 1)^2*(A+2)*A^2) ≤ constant*(A:ℝ)^5 := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
    have he : 0 ≤ (Real.exp 1)^2 := sq_nonneg _
    have h1 : (A:ℝ)+1 ≤ 2*(A:ℝ)^3 := by nlinarith [sq_nonneg ((A:ℝ)-1)]
    have h2 : ((A:ℝ)+2)*A^2 ≤ 3*(A:ℝ)^3 := by nlinarith [sq_nonneg (A:ℝ)]
    have hh := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 6*(Real.exp 1)^2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left (add_le_add h1 hh) (sq_nonneg (A:ℝ))
    unfold constant
    nlinarith only [hh']
  have hbase : 0 ≤ 1+(cutoff k:ℝ)+(N+1:ℕ)/(4:ℝ)^k := by positivity
  calc
    _ ≤ (A:ℝ)^2*(irregularPrimes A (N+1)).card+1 := highEnergy_bound A N
    _ ≤ (A:ℝ)^2*
        (((A:ℝ)+1+6*(Real.exp 1)^2*(A+2)*A^2)*
          (1+(cutoff k:ℝ)+(N+1:ℕ)/(4:ℝ)^k))+1 := by gcongr
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hc hbase]

lemma fifth_boundary_bound {k N : ℕ} (hlarge : threshold k ≤ N) :
    (atIndex k:ℝ)^5*(1+(cutoff k:ℝ)) ≤ 2*Real.sqrt N := by
  have hA : (atIndex k:ℝ)^5 ≤ cutoff k := by exact_mod_cast atIndex_fifth_le k
  have hz : (1:ℝ) ≤ cutoff k := by exact_mod_cast (cutoff_two_le k).trans' (by norm_num)
  have hz4 : (cutoff k:ℝ)^4 ≤ N := by
    exact_mod_cast (cutoff_fourth_le_threshold k).trans hlarge
  have hz2 : (cutoff k:ℝ)^2 ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hz4]
  calc
    _ ≤ (cutoff k:ℝ)*(1+(cutoff k:ℝ)) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ 2*(cutoff k:ℝ)^2 := by nlinarith
    _ ≤ _ := by linarith

lemma main_term_bound {k N : ℕ} (hN : 0 < N) (hnext : N < threshold (k+1)) :
    (atIndex k:ℝ)^5*Real.log (N:ℝ)/(4:ℝ)^k ≤ indexError (k/10) := by
  calc
    _ ≤ (atIndex k:ℝ)^5*(exponent (k+1):ℝ)/(4:ℝ)^k := by
      gcongr
      exact log_bound hN hnext
    _ = (atIndex k:ℝ)^5*coefficient k := by unfold coefficient; ring
    _ ≤ _ := fifth_coefficient_bound k

/-- Finite, common-endpoint estimate in the growing cofactor range. -/
lemma normalized_energy_bound {k N : ℕ} (hN : 0 < N)
    (hlarge : threshold k ≤ N) (hnext : N < threshold (k+1)) :
    highEnergy (atIndex k) N*Real.log N/N ≤
      2*constant*(Real.log N/Real.sqrt N)+
        2*constant*indexError (k/10)+Real.log N/N := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hs : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hl := Real.log_natCast_nonneg N
  have hr : 0 ≤ Real.log (N:ℝ)/N := div_nonneg hl hn.le
  have hbound := mul_le_mul_of_nonneg_right
    (energy_sieve_bound (atIndex_pos k) hN hlarge) hr
  have hfirst : (atIndex k:ℝ)^5*(1+(cutoff k:ℝ))*Real.log N/N ≤
      2*(Real.log N/Real.sqrt N) := by
    calc
      _ ≤ 2*Real.sqrt N*Real.log N/N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (fifth_boundary_bound hlarge) hl) hn.le
      _ = _ := by
        have hh := Real.sq_sqrt hn.le
        field_simp
        rw [hh]
        ring
  have hratio : ((N+1:ℕ):ℝ)/N ≤ 2 := by
    apply (div_le_iff₀ hn).mpr
    exact_mod_cast (by omega : N+1 ≤ 2*N)
  have hsecond : ((N+1:ℕ):ℝ)/N*
      ((atIndex k:ℝ)^5*Real.log N/(4:ℝ)^k) ≤ 2*indexError (k/10) := by
    apply (mul_le_mul_of_nonneg_right hratio (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (main_term_bound hN hnext) (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hfirst constant_nonneg
  have h2 := mul_le_mul_of_nonneg_left hsecond constant_nonneg
  have he :
      (constant*(atIndex k:ℝ)^5*(1+(cutoff k:ℝ)+(N+1:ℕ)/(4:ℝ)^k)+1)*
        (Real.log N/N) =
      constant*((atIndex k:ℝ)^5*(1+(cutoff k:ℝ))*Real.log N/N)+
        constant*(((N+1:ℕ):ℝ)/N*((atIndex k:ℝ)^5*Real.log N/(4:ℝ)^k))+
          Real.log N/N := by ring
  rw [he] at hbound
  convert hbound.trans (add_le_add (add_le_add h1 h2) (le_refl (Real.log (N:ℝ)/N))) using 1 <;> ring

/-- The explicit cutoff tends to infinity. Even with this growing cutoff,
the energy from primes `p` with `N/p ≤ cofactorCutoff N` is `o(N/log N)`.
No assertion is made about the complementary prime groups. -/
theorem growing_highEnergy_log_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => highEnergy (cofactorCutoff N) N*Real.log N/N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)/N) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun N : ℕ => Real.log (N:ℝ)/Real.sqrt N) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have herr := indexError_tendsto_zero.comp indexQuotient_tendsto
  have hu := ((hroot.const_mul (2*constant)).add (herr.const_mul (2*constant))).add hlog
  simp only [mul_zero,add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg
      (mul_nonneg (highEnergy_nonneg _ _) (Real.log_natCast_nonneg N)) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop (threshold 0),eventually_gt_atTop 0] with N hN hpos
    exact normalized_energy_bound hpos (sieveIndex_spec hN) (sieveIndex_next N)

lemma cutoff_tenth_le_log {k N : ℕ} (hlarge : threshold k ≤ N) :
    (atIndex k:ℝ)^10 ≤ Real.log (N:ℝ) := by
  have hlow : 10*(k/10) ≤ k := Nat.mul_div_le k 10
  have hA : (atIndex k:ℝ)^10 ≤ (2:ℝ)^k := by
    simp only [atIndex, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hTpos : 0 < threshold k := by rw [threshold_eq_pow]; positivity
  have hh := Real.log_le_log (Nat.cast_pos.mpr hTpos) (Nat.cast_le.mpr hlarge)
  rw [threshold_eq_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hh
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : (2:ℝ)*(2:ℝ)^k ≤ exponent k := by
    have hd : 0 < depth k := depth_pos k
    have hn : 2*2^k ≤ exponent k := by
      exact Nat.mul_le_mul_right (2^k) (show 2 ≤ 12*depth k by omega)
    exact_mod_cast hn
  have hm := mul_le_mul he hl2 (by norm_num : (0:ℝ) ≤ 1/2)
    (Nat.cast_nonneg (exponent k))
  nlinarith only [hA,hh,hm]

lemma exponent_div_twentieth_bound (k : ℕ) :
    (exponent (k+1):ℝ)/(atIndex k:ℝ)^20 ≤
      905969664*((k/10:ℕ)+1:ℝ)^2*(1/1024:ℝ)^(k/10) := by
  let j := k/10
  have hk : k < 10*(j+1) := Nat.lt_mul_div_succ k (by norm_num)
  have hhigh : (k:ℝ)+2 ≤ 12*((j:ℝ)+1) := by
    have hn : k+2 ≤ 12*(j+1) := by omega
    exact_mod_cast hn
  have hsq : ((k:ℝ)+2)^2 ≤ 144*((j:ℝ)+1)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (k:ℝ)+2) hhigh 2
    nlinarith
  have hp : (2:ℝ)^k/(atIndex k:ℝ)^20 ≤ 1024*(1/1024:ℝ)^j := by
    calc
      _ ≤ (2:ℝ)^(10*(j+1))/(atIndex k:ℝ)^20 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk.le) (by positivity)
      _ = 1024*(1/1024:ℝ)^j := by
        simp only [atIndex, Nat.cast_pow, Nat.cast_ofNat]
        change (2:ℝ)^(10*(j+1))/((2:ℝ)^j)^20 = _
        have hden : ((2:ℝ)^j)^20 = ((2:ℝ)^20)^j := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm j 20]
        rw [pow_mul, pow_succ, hden, mul_comm (((2:ℝ)^10)^j), mul_div_assoc, ← div_pow]
        norm_num
  have he : (exponent (k+1):ℝ) = 6144*((k:ℝ)+2)^2*(2:ℝ)^k := by
    unfold exponent depth
    push_cast
    rw [pow_succ]
    ring
  rw [he]
  calc
    _ = 6144*((k:ℝ)+2)^2*((2:ℝ)^k/(atIndex k:ℝ)^20) := by ring
    _ ≤ 6144*(144*((j:ℝ)+1)^2)*(1024*(1/1024:ℝ)^j) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      · exact hp
      · positivity
      · positivity
    _ = _ := by dsimp [j]; ring

lemma log_div_cutoff_twentieth_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N:ℝ)/(cofactorCutoff N:ℝ)^20) atTop (𝓝 0) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (r := 1/1024) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := 1/1024) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 1/1024) (by norm_num)
  have hs : Summable (fun j : ℕ => 905969664*((j:ℝ)+1)^2*(1/1024:ℝ)^j) := by
    apply (((h2.add (h1.mul_left 2)).add h0).mul_left 905969664).congr
    intro j
    ring
  have hu := hs.tendsto_atTop_zero.comp indexQuotient_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact (div_le_div_of_nonneg_right (log_bound hN (sieveIndex_next N)) (by positivity)).trans
      (exponent_div_twentieth_bound (sieveIndex N))

/-- The explicit growing cutoff lies between two fixed positive powers of
`log N`, expressed without real roots. -/
theorem cofactorCutoff_log_window :
    ∀ᶠ N : ℕ in atTop,
      (cofactorCutoff N:ℝ)^10 ≤ Real.log N ∧ Real.log N ≤ (cofactorCutoff N:ℝ)^20 := by
  filter_upwards [eventually_ge_atTop (threshold 0),
    log_div_cutoff_twentieth_tendsto_zero.eventually_le_const (by norm_num : (0:ℝ) < 1)]
      with N hN hlog
  refine ⟨cutoff_tenth_le_log (sieveIndex_spec hN),?_⟩
  have hA : (0:ℝ) < cofactorCutoff N := Nat.cast_pos.mpr (atIndex_pos _)
  simpa using (div_le_iff₀ (pow_pos hA 20)).mp hlog

lemma highEnergy_mono {A B : ℕ} (hAB : A ≤ B) (N : ℕ) :
    highEnergy A N ≤ highEnergy B N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hpa⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hpa.trans hAB⟩
  · intro p _ _
    exact sq_nonneg _

/-- Standard-form cutoff, avoiding the auxiliary sieve index. -/
noncomputable def logCutoff (N : ℕ) : ℕ := ⌊(Real.log (N:ℝ))^(1/20:ℝ)⌋₊

lemma logCutoff_tendsto : Tendsto logCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/20)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma logCutoff_power_le (N : ℕ) : (logCutoff N:ℝ)^20 ≤ Real.log (N:ℝ) := by
  have hL := Real.log_natCast_nonneg N
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (logCutoff N) : (0:ℝ) ≤ logCutoff N)
    (Nat.floor_le (Real.rpow_nonneg hL (1/20:ℝ))) 20
  have he : ((Real.log (N:ℝ))^(1/20:ℝ))^20 = Real.log (N:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  rwa [he] at hh

lemma logCutoff_eventually_le : ∀ᶠ N : ℕ in atTop, logCutoff N ≤ cofactorCutoff N := by
  filter_upwards [cofactorCutoff_log_window] with N hN
  apply (Nat.cast_le (α := ℝ)).mp
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by decide : (20:ℕ) ≠ 0)).mp ((logCutoff_power_le N).trans hN.2)

/-- Unconditional common-endpoint energy estimate with the explicit cutoff
`floor ((log N)^(1/20))`. This is still only the high-prime portion of the energy. -/
theorem logCutoff_highEnergy_log_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => highEnergy (logCutoff N) N*Real.log N/N) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    growing_highEnergy_log_ratio_tendsto_zero
  · exact Eventually.of_forall fun N => div_nonneg
      (mul_nonneg (highEnergy_nonneg _ _) (Real.log_natCast_nonneg N)) (Nat.cast_nonneg N)
  · filter_upwards [logCutoff_eventually_le] with N hN
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (highEnergy_mono hN N) (Real.log_natCast_nonneg N))
        (Nat.cast_nonneg N)

noncomputable def absoluteGroups (A N : ℕ) : ℝ :=
  ∑ p ∈ highPrimes A N, |(group p N:ℝ)|

lemma absoluteGroups_nonneg (A N : ℕ) : 0 ≤ absoluteGroups A N :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma absoluteGroups_sq_le (A N : ℕ) :
    (absoluteGroups A N)^2 ≤ (Nat.primeCounting N:ℝ)*highEnergy A N := by
  have hh := sq_sum_le_card_mul_sum_sq (s := highPrimes A N)
    (f := fun p => |(group p N:ℝ)|)
  simp only [sq_abs] at hh
  have hc : ((highPrimes A N).card:ℝ) ≤ Nat.primeCounting N := by
    have hn := Finset.card_le_card (Finset.filter_subset
      (fun p => N/p ≤ A) ((N+1).primesBelow))
    rw [Nat.primesBelow_card_eq_primeCounting'] at hn
    exact_mod_cast hn
  exact hh.trans (mul_le_mul_of_nonneg_right hc (highEnergy_nonneg A N))

/-- The total absolute signed discrepancy of these high-prime groups is also
`o(N/log N)`. The absolute value is taken AFTER summing within each prime group. -/
theorem logCutoff_absoluteGroups_log_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => absoluteGroups (logCutoff N) N*Real.log N/N) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE := logCutoff_highEnergy_log_ratio_tendsto_zero
  have hu := (hE.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at hu
  have hpc : ∀ᶠ N : ℕ in atTop, (Nat.primeCounting N:ℝ) ≤ C*N/Real.log N := by
    simpa [C] using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg
      (mul_nonneg (absoluteGroups_nonneg _ _) (Real.log_natCast_nonneg N)) (Nat.cast_nonneg N)
  · filter_upwards [hpc,eventually_gt_atTop 1] with N hpc hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    apply Real.le_sqrt_of_sq_le
    calc
      _ = (absoluteGroups (logCutoff N) N)^2 * (Real.log (N:ℝ)/N)^2 := by ring
      _ ≤ ((Nat.primeCounting N:ℝ)*highEnergy (logCutoff N) N) *
          (Real.log (N:ℝ)/N)^2 :=
        mul_le_mul_of_nonneg_right (absoluteGroups_sq_le _ _) (sq_nonneg _)
      _ ≤ (C*N/Real.log N*highEnergy (logCutoff N) N)*(Real.log (N:ℝ)/N)^2 := by
        gcongr
        exact highEnergy_nonneg _ _
      _ = C*(highEnergy (logCutoff N) N*Real.log N/N) := by field_simp

end Erdos371GrowingCofactorEnergy

#print axioms Erdos371GrowingCofactorEnergy.cofactorCutoff_tendsto
#print axioms Erdos371GrowingCofactorEnergy.growing_highEnergy_log_ratio_tendsto_zero

#print axioms Erdos371GrowingCofactorEnergy.cofactorCutoff_log_window

#print axioms Erdos371GrowingCofactorEnergy.logCutoff_highEnergy_log_ratio_tendsto_zero
#print axioms Erdos371GrowingCofactorEnergy.logCutoff_absoluteGroups_log_ratio_tendsto_zero
