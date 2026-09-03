import Submission.GreedyBatchFailurePenalty

/-! A finite deterministic time trajectory for the verified batch profiles,
with an explicit stopping index and terminal-scale comparison. -/
namespace Erdos773.GreedyBatchTrajectory
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def time (m : ℕ) : ℕ → ℝ
  | 0 => 1
  | i+1 => time m i+step m (time m i)

@[simp] lemma time_zero (m : ℕ) : time m 0=1 := rfl
lemma time_succ (m i : ℕ) : time m (i+1)=time m i+step m (time m i) := rfl

def scale (m : ℕ) (d : ℝ) (i : ℕ) : ℝ := d*Real.exp (-a m*((time m i)^3-1))
def commonCap (m i : ℕ) : ℕ := 3+i*(4*m^52+3)

lemma time_strict (m : ℕ) (hm : 0< m) : StrictMono (time m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [time_succ]
  exact lt_add_of_pos_right _ (step_pos m (time m i) hm)

lemma time_one (m i : ℕ) (hm : 0< m) : 1≤ time m i := by
  simpa only [time_zero] using (time_strict m hm).monotone (Nat.zero_le i)

@[simp] lemma scale_zero (m : ℕ) (d : ℝ) : scale m d 0=d := by simp [scale]

lemma scale_succ (m i : ℕ) (d : ℝ) : scale m d (i+1)=nextD m (scale m d i) (time m i) := by
  dsimp [scale,nextD]
  rw [time_succ,mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  dsimp [GreedyBatchProfileLower.delta]
  ring

lemma scale_antitone (m : ℕ) (d : ℝ) (hm : 100≤ m) (hd : 0≤ d) : Antitone (scale m d) := by
  intro i j hij
  have ha := (coefficients m hm).2.2.2.1
  have hi := time_one m i (by omega)
  have htime := (time_strict m (by omega)).monotone hij
  have hp := pow_le_pow_left₀ (by linarith only [hi] : 0≤ time m i) htime 3
  have hh := mul_le_mul_of_nonneg_left hp ha
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hd
  nlinarith only [hh]

lemma scale_le_initial (m i : ℕ) (d : ℝ) (hm : 100≤ m) (hd : 0≤ d) : scale m d i≤ d := by
  simpa only [scale_zero] using scale_antitone m d hm hd (Nat.zero_le i)

lemma common_succ (m i : ℕ) : commonCap m (i+1)=commonCap m i+4*m^52+3 := by
  unfold commonCap
  ring

lemma common_one (m i : ℕ) : 1≤ commonCap m i := by unfold commonCap; omega

lemma common_bound (m i : ℕ) (hm : 100≤ m) (hi : i≤ 2*m^3) : commonCap m i≤ m^60 := by
  have hm1 : 1≤ m := by omega
  have h1 := Nat.mul_le_mul_right (4*m^52+3) hi
  have hp3 : m^3≤ m^55 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1≤ m^55 := one_le_pow₀ hm1
  have hs := nat_power_slack m 55 60 17 hm (by decide) (by decide)
  unfold commonCap
  nlinarith only [h1,hp3,hp1,hs]

/-- A terminal lower scale and upper time suffice for the whole trajectory. -/
theorem ranges (m L : ℕ) (d : ℝ) (P : ℕ) (hm : 100≤ m) (hd : 0<d)
    (hP1 : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) :
    ∀ i≤ L, Range m (scale m d i) (time m i) (commonCap m i) P := by
  intro i hi
  have ht1 := time_one m i (by omega)
  have hT1 := time_one m L (by omega)
  have hT : time m L≤ (m:ℝ) := by
    have hh : time m L≤ (time m L)^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hT1 (by decide : 1≤ 3)
    exact hh.trans hS
  exact {
    large := hm
    d := hdL.trans (scale_antitone m d hm hd.le hi)
    t_one := ht1
    t_upper := ((time_strict m (by omega)).monotone hi).trans hT
    common := common_bound m i hm (hi.trans hL)
    common_one := common_one m i
    pair_one := hP1
    pair_upper := hPm }

lemma time_progress (m n : ℕ) (T : ℝ) (hm : 0< m) (hT : ∀ i≤ n, time m i≤ T) :
    1+(n:ℝ)/((m:ℝ)^2*(1+T^2))≤ time m n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := hT n (by omega)
    have ht0 : 0≤ time m n := by have hh := time_one m n hm; linarith only [hh]
    have hm0 : (0:ℝ)< m := by exact_mod_cast hm
    have hpow := pow_le_pow_left₀ ht0 ht 2
    have hden : (m:ℝ)^2*(1+(time m n)^2)≤ (m:ℝ)^2*(1+T^2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hpow]) (sq_nonneg (m:ℝ))
    have hs : 1/((m:ℝ)^2*(1+T^2))≤ step m (time m n) :=
      one_div_le_one_div_of_le (by positivity) hden
    have hh := ih (fun i hi => hT i (by omega))
    rw [time_succ,Nat.cast_add,Nat.cast_one]
    ring_nf at hh hs ⊢
    linarith only [hh,hs]

lemma time_reaches (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ m) :
    T≤ time m (2*m^3) := by
  by_contra! hbad
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hbound (i : ℕ) (hi : i≤ 2*m^3) : time m i≤ T :=
    ((time_strict m (by omega)).monotone hi).trans hbad.le
  have hh := time_progress m (2*m^3) T (by omega) hbound
  have he : ((2*m^3:ℕ):ℝ)/((m:ℝ)^2*(1+T^2))=2*(m:ℝ)/(1+T^2) := by
    push_cast
    field_simp
  rw [he] at hh
  have ht3 : T≤ T^3 := by simpa only [pow_one] using pow_le_pow_right₀ hT (by decide : 1≤ 3)
  have ht : T≤ 2*(m:ℝ)/(1+T^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [ht3,hT3])
  linarith only [hbad,hh,ht]

/-- A least crossing has overshoot no larger than one shrinking step. -/
theorem stopping_index (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ m) :
    ∃ L : ℕ, L≤ 2*m^3 ∧ T≤ time m L ∧ time m L≤ T+1/(m:ℝ)^2 := by
  have hex : ∃ L, T≤ time m L := ⟨2*m^3,time_reaches m T hm hT hT3⟩
  let L := Nat.find hex
  have hL : L≤ 2*m^3 := Nat.find_min' hex (time_reaches m T hm hT hT3)
  refine ⟨L,hL,Nat.find_spec hex,?_⟩
  by_cases hL0 : L=0
  · rw [hL0,time_zero]
    have hz : (0:ℝ)≤ 1/(m:ℝ)^2 := by positivity
    linarith only [hT,hz]
  · obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hL0
    have hiL : i<L := by omega
    have ht : time m i<T := lt_of_not_ge (Nat.find_min hex hiL)
    have hs := step_bound m (time m i) hm
    rw [hi,time_succ]
    linarith only [ht,hs]

/-- The stopped horizon remains within the range required by the rate
profile, while reaching at least the desired physical time. -/
theorem stopping_small (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ (m:ℝ)/16) :
    ∃ L : ℕ, L≤ 2*m^3 ∧ T≤ time m L ∧ time m L≤ T+1 ∧ (time m L)^3≤ m := by
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  obtain ⟨L,hL,htL,hLT⟩ := stopping_index m T hm hT (by linarith only [hT3,hm0])
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
  have hs : (1:ℝ)/(m:ℝ)^2≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)
  have hLT' : time m L≤ T+1 := by linarith only [hLT,hs]
  have htwice : time m L≤ 2*T := by linarith only [hLT',hT]
  have ht0 : 0≤ time m L := by have := time_one m L (by omega); linarith
  have hc := pow_le_pow_left₀ ht0 htwice 3
  exact ⟨L,hL,htL,hLT',by nlinarith only [hc,hT3,hm0]⟩

lemma terminal_scale (m L : ℕ) (d T : ℝ) (hm : 100≤ m) (hd : 0≤ d) (hT : 1≤ T)
    (hLT : time m L≤ T+1) : d*Real.exp (-a m*((T+1)^3-1))≤ scale m d L := by
  have ht0 : 0≤ time m L := by have := time_one m L (by omega); linarith
  have hp := pow_le_pow_left₀ ht0 hLT 3
  have hh := mul_le_mul_of_nonneg_left hp (coefficients m hm).2.2.2.1
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hd
  nlinarith only [hh]

#print axioms time_strict
#print axioms scale_succ
#print axioms scale_antitone
#print axioms common_bound
#print axioms ranges
#print axioms stopping_index
#print axioms stopping_small
#print axioms terminal_scale
end
end Erdos773.GreedyBatchTrajectory
