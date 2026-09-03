import Submission.RankinPrimeHarmonic
import Submission.DyadicHighWinnerHarmonic

/-! An explicit moving lower-prime boundary has finite reciprocal mass.
The cutoffs grow almost like a power on the logarithmic scale. No interior
signed cancellation is asserted. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

def lowPrimeBandIndex (k : ℕ) : ℕ :=
  Nat.findGreatest (fun j => 512*(j+1)*2^j ≤ k+1) k

def lowPrimeBandCutoff (k : ℕ) : ℕ := 2^(2^(lowPrimeBandIndex k))

lemma lowPrimeBandIndex_budget (k : ℕ) (hk : 511 ≤ k) :
    512*(lowPrimeBandIndex k+1)*2^(lowPrimeBandIndex k) ≤ k+1 := by
  exact Nat.findGreatest_spec (P := fun j => 512*(j+1)*2^j ≤ k+1) (m := 0) (by omega) (by norm_num; omega)

lemma lowPrimeBandIndex_pos (k : ℕ) (hk : 2047 ≤ k) : 1 ≤ lowPrimeBandIndex k := by
  exact Nat.le_findGreatest (m := 1) (by omega) (by norm_num; omega)

lemma lowPrimeBandIndex_next (k : ℕ) :
    k+1 < 512*(lowPrimeBandIndex k+2)*2^(lowPrimeBandIndex k+1) := by
  have hj : lowPrimeBandIndex k ≤ k := Nat.findGreatest_le k
  by_cases h : lowPrimeBandIndex k+1 ≤ k
  · by_contra! he
    have hh : lowPrimeBandIndex k+1 ≤ lowPrimeBandIndex k :=
      Nat.le_findGreatest h (by simpa only [Nat.add_assoc] using he)
    omega
  · have he : lowPrimeBandIndex k=k := by omega
    rw [he]
    have hp : 1 ≤ (2 : ℕ)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hh := Nat.mul_le_mul_left (512*(k+2)) hp
    omega

lemma lowPrimeBandIndex_upper_endpoint (k : ℕ) :
    k+1 ≤ 2^(2*lowPrimeBandIndex k+12) := by
  let j := lowPrimeBandIndex k
  have hj : j+2 ≤ (2 : ℕ)^(j+1) := by have := Nat.lt_two_pow_self (n := j+1); omega
  calc
    _ ≤ 512*(j+2)*2^(j+1) := (lowPrimeBandIndex_next k).le
    _ ≤ (2 : ℕ)^9*2^(j+1)*2^(j+1) := by norm_num; gcongr
    _ = 2^(2*j+11) := by rw [← pow_add,← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

lemma lowPrimeBandIndex_tendsto : Tendsto lowPrimeBandIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop (max j (512*(j+1)*2^j))] with k hk
  apply Nat.le_findGreatest
  · exact (le_max_left _ _).trans hk
  · exact ((le_max_right _ _).trans hk).trans (Nat.le_succ _)

lemma lowPrimeBand_smooth_ratio (k : ℕ) (hk : 2047 ≤ k) :
    (Nat.smoothNumbersUpTo (2^(k+1)) (lowPrimeBandCutoff k)).card / (2 : ℝ)^(k+1) ≤
      1/(k+1 : ℝ)^2 := by
  let j := lowPrimeBandIndex k
  have hj : 1 ≤ j := lowPrimeBandIndex_pos k hk
  have hb := lowPrimeBandIndex_budget k (by omega)
  have hbr : 512*(j+1 : ℝ)*(2 : ℝ)^j ≤ k+1 := by exact_mod_cast hb
  have hd : 512*(j+1 : ℝ) ≤ (k+1 : ℝ)/(2 : ℝ)^j :=
    (le_div_iff₀ (by positivity)).mpr hbr
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlhalf : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlone : Real.log 2 ≤ (1 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hexp : 96*(j+1 : ℝ)-((k+1 : ℝ)/(2 : ℝ)^j)*Real.log 2 ≤
      -((4*j+24 : ℕ) : ℝ)*Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_right hd hl0.le
    have h2 := mul_le_mul_of_nonneg_left hlhalf (show 0 ≤ 512*(j+1 : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hlone (show (0 : ℝ) ≤ ((4*j+24 : ℕ) : ℝ) by positivity)
    push_cast at h3 ⊢
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hr := smooth_double_power_rankin_ratio j k hj
  change (Nat.smoothNumbersUpTo (2^(k+1)) (2^(2^j))).card / (2 : ℝ)^(k+1) ≤ _
  apply hr.trans
  calc
    _ ≤ Real.exp (-((4*j+24 : ℕ) : ℝ)*Real.log 2) := Real.exp_le_exp.mpr hexp
    _ = 1/(2 : ℝ)^(4*j+24) := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2),one_div]
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      have hb : (k+1 : ℝ) ≤ (2 : ℝ)^(2*j+12) := by exact_mod_cast lowPrimeBandIndex_upper_endpoint k
      have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤k+1) hb 2
      convert hs using 1
      rw [← pow_mul]
      congr 1
      omega

noncomputable def dyadicLowPrime (n : ℕ) : Prop :=
  Nat.maxPrimeFac n < lowPrimeBandCutoff (Nat.log 2 n)

noncomputable def dyadicLowPrimeReciprocal (n : ℕ) : ℝ := by
  classical
  exact if dyadicLowPrime n then 1/n else 0

lemma dyadicLowPrimeReciprocal_nonneg (n : ℕ) : 0 ≤ dyadicLowPrimeReciprocal n := by
  unfold dyadicLowPrimeReciprocal
  split_ifs <;> positivity

lemma lowPrime_block_count_bound (k : ℕ) (t : ℕ) (ht : t ≤ 1) :
    (((Ico (2^k) (2^(k+1))).filter fun n =>
      Nat.maxPrimeFac (n+t) < lowPrimeBandCutoff k).card : ℝ) ≤
        (Nat.smoothNumbersUpTo (2^(k+1)) (lowPrimeBandCutoff k)).card := by
  classical
  apply Nat.cast_le.mpr
  let S := (Ico (2^k) (2^(k+1))).filter fun n => Nat.maxPrimeFac (n+t) < lowPrimeBandCutoff k
  have hi : Set.InjOn (fun n : ℕ => n+t) S := by intro a _ b _ h; dsimp only at h; omega
  rw [← card_image_of_injOn hi]
  apply card_le_card
  intro m hm
  obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
  obtain ⟨hn,hp⟩ := mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
  have hn0 : n+t ≠ 0 := by have := pow_pos (by omega : 0<(2 : ℕ)) k; omega
  apply Nat.mem_smoothNumbersUpTo.mpr
  refine ⟨by omega,Nat.mem_smoothNumbers'.mpr ?_⟩
  intro p hpp hpd
  exact (Nat.le_maxPrimeFac hn0 hpp hpd).trans_lt hp

lemma dyadicLowPrimeReciprocal_block_bound (k : ℕ) (hk : 2047 ≤ k) :
    (∑ n ∈ Ico (2^k) (2^(k+1)), dyadicLowPrimeReciprocal n) ≤ 2/(k+1 : ℝ)^2 := by
  classical
  let S := (Ico (2^k) (2^(k+1))).filter (dyadicLowPrime)
  have he : S = (Ico (2^k) (2^(k+1))).filter fun n => Nat.maxPrimeFac n < lowPrimeBandCutoff k := by
    ext n
    simp only [S,mem_filter]
    apply and_congr_right
    intro hn
    simp only [dyadicLowPrime,Nat.log_eq_of_pow_le_of_lt_pow (mem_Ico.mp hn).1 (mem_Ico.mp hn).2]
  have hb : (∑ n ∈ Ico (2^k) (2^(k+1)), dyadicLowPrimeReciprocal n) ≤
      (S.card : ℝ)/(2 : ℝ)^k := by
    simp only [dyadicLowPrimeReciprocal,← sum_filter]
    calc
      _ ≤ ∑ _n ∈ S, (1 : ℝ)/(2 : ℝ)^k := by
        apply sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
      _ = _ := by simp only [sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul]
  have hc : (S.card : ℝ) ≤ (Nat.smoothNumbersUpTo (2^(k+1)) (lowPrimeBandCutoff k)).card := by
    rw [he]
    simpa only [Nat.add_zero] using lowPrime_block_count_bound k 0 (by omega)
  have hd := hb.trans (div_le_div_of_nonneg_right hc (by positivity))
  have hratio := lowPrimeBand_smooth_ratio k hk
  have heq (x : ℝ) : x/(2 : ℝ)^k = 2*(x/(2 : ℝ)^(k+1)) := by rw [pow_succ]; field_simp
  rw [heq] at hd
  exact hd.trans (by have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ)≤2); simpa only [mul_one_div] using h)

theorem summable_dyadicLowPrimeReciprocal : Summable dyadicLowPrimeReciprocal := by
  apply summable_of_nonneg_dyadic_blocks _ dyadicLowPrimeReciprocal_nonneg
  have hs : Summable (fun k : ℕ => (1 : ℝ)/(k+1 : ℝ)^2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1<(2 : ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  apply (hs.mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2047 : ℕ)] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (sum_nonneg fun n _ => dyadicLowPrimeReciprocal_nonneg n),mul_one_div]
  exact dyadicLowPrimeReciprocal_block_bound k hk

lemma lowPrimeBandIndex_mono : Monotone lowPrimeBandIndex := by
  intro k l hkl
  by_cases hj : lowPrimeBandIndex k=0
  · simp only [hj,Nat.zero_le]
  · have hs := (Nat.findGreatest_eq_iff.mp (rfl :
        Nat.findGreatest (fun j => 512*(j+1)*2^j ≤ k+1) k=lowPrimeBandIndex k)).2.1 hj
    exact Nat.le_findGreatest ((Nat.findGreatest_le k).trans hkl) (hs.trans (by omega))

lemma lowPrimeBandCutoff_mono : Monotone lowPrimeBandCutoff := by
  intro k l hkl
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (lowPrimeBandIndex_mono hkl))

lemma lowPrimeBandCutoff_tendsto : Tendsto lowPrimeBandCutoff atTop atTop := by
  apply tendsto_atTop_mono _ lowPrimeBandIndex_tendsto
  intro k
  exact (Nat.lt_two_pow_self (n := lowPrimeBandIndex k)).le.trans (Nat.lt_two_pow_self.le)

/-- Explicit two-sided control of the logarithmic cutoff size. -/
lemma lowPrimeBand_log_ratio_bounds (k : ℕ) (hk : 2047 ≤ k) :
    1/(1024*(lowPrimeBandIndex k+2 : ℝ)) <
        Real.log (lowPrimeBandCutoff k)/Real.log ((2 : ℝ)^(k+1)) ∧
    Real.log (lowPrimeBandCutoff k)/Real.log ((2 : ℝ)^(k+1)) ≤
        1/(512*(lowPrimeBandIndex k+1 : ℝ)) := by
  let j := lowPrimeBandIndex k
  have he : Real.log (lowPrimeBandCutoff k)/Real.log ((2 : ℝ)^(k+1)) =
      (2 : ℝ)^j/(k+1 : ℝ) := by
    simp only [lowPrimeBandCutoff,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add,Nat.cast_one]
    field_simp
    rfl
  rw [he]
  have hlo : (k+1 : ℝ) < 1024*(j+2 : ℝ)*(2 : ℝ)^j := by
    have h := lowPrimeBandIndex_next k
    have hr : (k+1 : ℝ) < 512*(j+2 : ℝ)*(2 : ℝ)^(j+1) := by exact_mod_cast h
    rw [pow_succ] at hr
    nlinarith
  have hhi : 512*(j+1 : ℝ)*(2 : ℝ)^j ≤ k+1 := by exact_mod_cast lowPrimeBandIndex_budget k (by omega)
  constructor
  · apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith

lemma lowPrimeBandIndex_log_bounds (k : ℕ) (hk : 2047 ≤ k) :
    lowPrimeBandIndex k ≤ Nat.log 2 (k+1) ∧
      Nat.log 2 (k+1) ≤ 2*lowPrimeBandIndex k+12 := by
  constructor
  · apply Nat.le_log_of_pow_le (by omega)
    have h := lowPrimeBandIndex_budget k (by omega)
    have hp : 0 < (2 : ℕ)^(lowPrimeBandIndex k) := pow_pos (by omega) _
    nlinarith
  · have h := Nat.log_mono_right (b := 2) (lowPrimeBandIndex_upper_endpoint k)
    simpa only [Nat.log_pow (by omega : 1<(2 : ℕ))] using h

lemma lowPrimeBand_log_ratio_zero :
    Tendsto (fun k => Real.log (lowPrimeBandCutoff k)/Real.log ((2 : ℝ)^(k+1))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun j : ℕ => (1 : ℝ)/(j+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := (hbase.comp lowPrimeBandIndex_tendsto).div_const (512 : ℝ)
  simp only [zero_div,Function.comp_apply] at ht
  apply squeeze_zero' (Eventually.of_forall fun k => div_nonneg (Real.log_natCast_nonneg _)
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)))) _ ht
  filter_upwards [eventually_ge_atTop (2047 : ℕ)] with k hk
  have h := (lowPrimeBand_log_ratio_bounds k hk).2
  simpa only [div_div,mul_comm] using h

noncomputable def dyadicLowLoser (n : ℕ) : Prop :=
  primeLoser n < lowPrimeBandCutoff (Nat.log 2 n)

noncomputable def dyadicLowLoserReciprocal (n : ℕ) : ℝ := by
  classical
  exact if dyadicLowLoser n then 1/n else 0

lemma dyadicLowLoserReciprocal_nonneg (n : ℕ) : 0 ≤ dyadicLowLoserReciprocal n := by
  unfold dyadicLowLoserReciprocal
  split_ifs <;> positivity

lemma dyadicLowLoserReciprocal_bound (n : ℕ) : dyadicLowLoserReciprocal n ≤
    dyadicLowPrimeReciprocal n+2*dyadicLowPrimeReciprocal (n+1) := by
  classical
  by_cases hn : n=0
  · subst n
    simp only [dyadicLowLoserReciprocal,Nat.cast_zero,div_zero,ite_self]
    exact add_nonneg (dyadicLowPrimeReciprocal_nonneg 0) (mul_nonneg (by norm_num) (dyadicLowPrimeReciprocal_nonneg _))
  by_cases hl : dyadicLowLoser n
  · rw [dyadicLowLoserReciprocal,if_pos hl]
    change min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) < lowPrimeBandCutoff (Nat.log 2 n) at hl
    rcases min_lt_iff.mp hl with h | h
    · have he : dyadicLowPrimeReciprocal n=1/n := by
        rw [dyadicLowPrimeReciprocal,if_pos (show dyadicLowPrime n from h)]
      rw [he]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (dyadicLowPrimeReciprocal_nonneg _))
    · have hm : lowPrimeBandCutoff (Nat.log 2 n) ≤ lowPrimeBandCutoff (Nat.log 2 (n+1)) :=
        lowPrimeBandCutoff_mono (Nat.log_mono_right (by omega))
      have he : dyadicLowPrimeReciprocal (n+1)=1/(n+1 : ℕ) := by
        rw [dyadicLowPrimeReciprocal,if_pos (show dyadicLowPrime (n+1) from h.trans_le hm)]
      rw [he]
      have hN : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hh : (1 : ℝ)/n ≤ 2/(n+1 : ℝ) := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
      push_cast
      rw [mul_one_div]
      exact hh.trans (le_add_of_nonneg_left (dyadicLowPrimeReciprocal_nonneg n))
  · rw [dyadicLowLoserReciprocal,if_neg hl]
    exact add_nonneg (dyadicLowPrimeReciprocal_nonneg n) (mul_nonneg (by norm_num) (dyadicLowPrimeReciprocal_nonneg _))

/-- Absolute reciprocal summability when EITHER neighboring prime factor is
below the moving lower boundary. This includes all low-winner contributions. -/
theorem summable_dyadicLowLoserReciprocal : Summable dyadicLowLoserReciprocal := by
  have hshift : Summable (fun n => dyadicLowPrimeReciprocal (n+1)) :=
    (summable_nat_add_iff 1).mpr summable_dyadicLowPrimeReciprocal
  exact (summable_dyadicLowPrimeReciprocal.add (hshift.mul_left 2)).of_nonneg_of_le
    dyadicLowLoserReciprocal_nonneg dyadicLowLoserReciprocal_bound

#print axioms smooth_rankin_primeHarmonic_bound
#print axioms lowPrimeBand_smooth_ratio
#print axioms summable_dyadicLowPrimeReciprocal
#print axioms lowPrimeBand_log_ratio_bounds
#print axioms lowPrimeBand_log_ratio_zero
#print axioms summable_dyadicLowLoserReciprocal
end Erdos371
