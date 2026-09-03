import Submission.LogCriticalVoid
import Submission.SubexponentialSquareCubicReduction

/-! Arithmetic for a logarithmically many-step square-cubic iteration.
These lemmas provide no arithmetic correlation estimate. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2000000

lemma eventually_nat_power_le_two_power (d : ℕ) :
    ∀ᶠ t : ℕ in atTop, t^d ≤ 2^t := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_pow_exp_pos_mul_atTop d hlog2).def (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hs] with t ht
  have he : exp (log 2*(t : ℝ)) = (2 : ℝ)^t := by
    rw [mul_comm,exp_nat_mul,exp_log (by norm_num)]
  have hh : (t : ℝ)^d ≤ (2 : ℝ)^t := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (show (0 : ℝ) ≤ t from Nat.cast_nonneg t) d),
      abs_of_pos (exp_pos _),one_mul,he,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) t)] using ht
  exact_mod_cast hh

noncomputable def logIterationIndex (r t : ℕ) : ℕ := Nat.log 16 (t^r)
noncomputable def logIterationRoot (r t : ℕ) : ℕ := 16^logIterationIndex r t
noncomputable def logIterationSteps (r t : ℕ) : ℕ := 16*logIterationIndex r t
noncomputable def logIterationLength (r t : ℕ) : ℕ := 2^(2*t-64*logIterationIndex r t)

lemma logIterationRoot_bounds (r t : ℕ) (ht : 0 < t) :
    0 < logIterationRoot r t ∧ logIterationRoot r t ≤ t^r ∧
      t^r ≤ 16*logIterationRoot r t := by
  refine ⟨by unfold logIterationRoot; positivity,?_,?_⟩
  · exact Nat.pow_log_le_self 16 (Nat.pow_pos ht).ne'
  · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (16 : ℕ)) (t^r)
    simpa only [pow_succ,Nat.mul_comm] using hh.le

lemma logIterationRoot_sixteenth (r t : ℕ) :
    logIterationRoot r t^16 = 2^(64*logIterationIndex r t) := by
  dsimp only [logIterationRoot]
  rw [show (16 : ℕ)=2^4 by norm_num]
  simp only [← pow_mul]
  congr 1
  ring

lemma eventually_logIterationIndex_small (r : ℕ) :
    ∀ᶠ t : ℕ in atTop, 64*logIterationIndex r t ≤ t := by
  filter_upwards [eventually_nat_power_le_two_power (16*r),eventually_ge_atTop 1] with t ht ht1
  have hq := (logIterationRoot_bounds r t ht1).2.1
  have hp := Nat.pow_le_pow_left hq 16
  rw [logIterationRoot_sixteenth] at hp
  have he : (t^r)^16=t^(16*r) := by rw [← pow_mul,Nat.mul_comm r 16]
  rw [he] at hp
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (hp.trans ht)

lemma logIterationLength_budget (r t : ℕ) (ht : 64*logIterationIndex r t ≤ t) :
    2^t ≤ logIterationLength r t ∧
    16^logIterationSteps r t*logIterationLength r t=(2^t)^2 ∧
    logIterationRoot r t^16*logIterationLength r t=(2^t)^2 := by
  have hpow : 16^logIterationSteps r t=2^(64*logIterationIndex r t) := by
    dsimp only [logIterationSteps]
    rw [show (16 : ℕ)=2^4 by norm_num,← pow_mul]
    congr 1
    ring
  have he : 2^(64*logIterationIndex r t)*logIterationLength r t=(2^t)^2 := by
    dsimp only [logIterationLength]
    rw [← pow_add,← pow_mul]
    congr 1
    omega
  refine ⟨?_,by rw [hpow]; exact he,by rw [logIterationRoot_sixteenth]; exact he⟩
  apply Nat.pow_le_pow_right (by omega)
  omega

lemma logIterationRoot_growth (r t : ℕ) :
    logIterationRoot r t^9 ≤ 5^logIterationSteps r t := by
  have hbase : (16 : ℕ)^9 ≤ 5^16 := by norm_num
  have hh := Nat.pow_le_pow_left hbase (logIterationIndex r t)
  dsimp only [logIterationRoot,logIterationSteps]
  calc
    _ = ((16 : ℕ)^9)^logIterationIndex r t := by
      rw [← pow_mul,← pow_mul]
      congr 1
      omega
    _ ≤ _ := hh
    _ = _ := by rw [← pow_mul]

lemma logIterationLength_log (r t : ℕ) :
    log (logIterationLength r t : ℝ) ≤ 2*(t : ℝ) := by
  simp only [logIterationLength,Nat.cast_pow,log_pow,Nat.cast_ofNat]
  have he : (2*t-64*logIterationIndex r t : ℕ) ≤ 2*t := Nat.sub_le _ _
  have hR : ((2*t-64*logIterationIndex r t : ℕ) : ℝ) ≤ 2*(t : ℝ) := by exact_mod_cast he
  have hlog : log (2 : ℝ) ≤ 1 := le_trans log_two_lt_d9.le (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (2*t-64*logIterationIndex r t))
  linarith only [hh,hR]

lemma logIterationLength_sqrt (r t : ℕ) (ht : 64*logIterationIndex r t ≤ t) :
    (logIterationRoot r t : ℝ)^8*sqrt (logIterationLength r t : ℝ)=(2 : ℝ)^t := by
  have he := (logIterationLength_budget r t ht).2.2
  have hR : (logIterationRoot r t : ℝ)^16*(logIterationLength r t : ℝ)=((2 : ℝ)^t)^2 := by
    exact_mod_cast he
  have hs : ((logIterationRoot r t : ℝ)^8*sqrt (logIterationLength r t : ℝ))^2=((2 : ℝ)^t)^2 := by
    rw [mul_pow,sq_sqrt (Nat.cast_nonneg _)]
    convert hR using 1 <;> ring
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hs

/-- Purely geometric gain: sixteen four-doubling blocks gain one full
power of the root scale after dividing by the square-root length cost. -/
lemma logIteration_rate_gain (r t b : ℕ) (ht : 0 < t)
    (hr : r=b+2) :
    (2 : ℝ)^t*(t : ℝ)^2/(25600*2^b) ≤
      ((2 : ℝ)^t/(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8))*
        (5 : ℝ)^logIterationSteps r t := by
  have hroot := logIterationRoot_bounds r t ht
  have hq0 : (0 : ℝ) < logIterationRoot r t := by exact_mod_cast hroot.1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hqhi : (t : ℝ)^r ≤ 16*(logIterationRoot r t : ℝ) := by exact_mod_cast hroot.2.2
  have hg : (logIterationRoot r t : ℝ)^9 ≤ (5 : ℝ)^logIterationSteps r t := by
    exact_mod_cast logIterationRoot_growth r t
  have h1 := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (2 : ℝ)^t/(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8) by positivity)
  apply le_trans _ h1
  have he : ((2 : ℝ)^t/(1600*2^b*(t : ℝ)^b*(logIterationRoot r t : ℝ)^8))*
      (logIterationRoot r t : ℝ)^9 =
        (2 : ℝ)^t*(logIterationRoot r t : ℝ)/(1600*2^b*(t : ℝ)^b) := by
    field_simp
    <;> ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 1600*2^b*(t : ℝ)^b)).mpr
  have hm := mul_le_mul_of_nonneg_left hqhi (show 0 ≤ (2 : ℝ)^t/16 by positivity)
  apply le_trans _ (by convert hm using 1 <;> ring)
  rw [hr,pow_add]
  field_simp
  <;> norm_num <;> ring

#print axioms logIterationLength_budget
#print axioms logIterationLength_sqrt
#print axioms logIteration_rate_gain
end Erdos970.GapAverages
