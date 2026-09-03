import Submission.GreedyBatchTrajectory
import Submission.GreedyBatchSchedule

/-! Fully instantiated finite iteration of the exponential mixed-rank
profiles, with explicit time, terminal scale and volume hypotheses. -/
namespace Erdos773.GreedyBatchProfileIteration
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchDensityStep GreedyBatchDensityProfile GreedyBatchVolume GreedyBatchTrajectory
open GreedyBatchSchedule
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section
universe u

def schedule (m A L : ℕ) (d : ℝ) (P : ℕ) : Schedule where
  current i := caps m (scale m d i) (time m i) (commonCap m i) P
  target i := caps m (scale m d (i+1)) (time m (i+1)) (commonCap m i+4*m^52) P
  margins i := GreedyBatchScaledErrors.margins
    (caps m (scale m d i) (time m i) (commonCap m i) P) m
    (probability m (scale m d i) (time m i)) (scale m d i)
  p i := probability m (scale m d i) (time m i)
  eta _ := 1/(m:ℝ)^2
  density i := density m (time m L) (scale m d i) (time m i)
  failure _ := GreedyBatchScaleTails.failure m
  moment _ := m^10
  volume i := volume m A i

/-- Every finite numeric hypothesis of the abstract batch schedule is now
proved for these concrete profiles. -/
theorem valid (m A L : ℕ) (d : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) : Valid (schedule m A L d P) L := by
  have hm100 : 100≤ m := by omega
  have hr := ranges m L d P hm100 hd hP hPm hL hS hdL
  have hc (i : ℕ) (hi : i≤ L) := conditions m (scale m d i) (time m i) (commonCap m i) P (hr i hi)
  have hdI (i : ℕ) : scale m d i≤ (m:ℝ)^A := (scale_le_initial m i d hm100 hd.le).trans hdU
  have htime (i : ℕ) (hi : i≤ L) : time m i≤ time m L := (time_strict m (by omega)).monotone hi
  constructor
  · intro i hi
    exact GreedyBatchScaledErrors.margins_positive _ m _ _ (hc i hi.le)
  · intro i hi
    exact GreedyBatchScaledErrors.probability_range _ m _ _ (hc i hi.le)
  · intro i hi
    have hh := GreedyBatchProfileFits.fits m (scale m d i) (time m i) (commonCap m i) P (hr i hi.le)
    simpa only [schedule,scale_succ,time_succ] using hh
  · intro i hi
    exact le_rfl
  · intro i hi
    exact (density_bounds m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi) hm (htime i hi) hS).1
  · intro i hi
    exact (density_bounds m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi) hm (htime i hi) hS).2
  · intro i hi
    exact density_pos m (time m L) (scale m d i) (time m i) hm (hr i hi.le).d_pos (time_strict m (by omega) hi)
  · intro i hi
    unfold schedule GreedyBatchScaleTails.failure
    positivity
  · intro i hi
    exact GreedyBatchScaledErrors.vertex_errors _ m _ _ (hc i hi.le)
  · intro i hi
    exact GreedyBatchScaledErrors.pair_errors _ m _ _ (hc i hi.le)
  · intro i hi
    have hnext : time m i+step m (time m i)≤ time m L := by
      rw [← time_succ]
      exact htime (i+1) (by omega)
    have hrate := rate_margin m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi.le) hm hnext hS
    have hpen := GreedyBatchFailurePenalty.volume_penalty m A i (scale m d i) (time m i)
      (commonCap m i) P (hr i hi.le) hmV (hi.le.trans hL) (hdI i)
    rw [← scale_succ,← time_succ] at hrate
    dsimp only [schedule]
    linarith only [hrate,hpen]
  · intro i hi
    have hcopy := copies_bound m A (scale m d (i+1)) (time m (i+1)) (commonCap m (i+1)) P
      (hr (i+1) (by omega)) (hdI (i+1))
    change copies ((schedule m A L d P).target i)≤ m^(increment A) at hcopy
    exact volume_step m A i _ hcopy
  · intro i hi
    dsimp [schedule,post,caps]
    rw [common_succ]
  · simp [schedule,density]

/-- The finite regular mixed-hypergraph density bound at a prescribed final
index. No implicit asymptotic or tracking hypotheses remain. -/
theorem uniform_fixed (m A L : ℕ) (d : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) :
    UniformDensity.{u} (caps m d 1 3 P) (m^A) (efficiency m*(time m L-1)/d) := by
  have hh := iterate (schedule m A L d P) L (valid m A L d P hm hmV hd hdU hP hPm hL hS hdL) 0 (Nat.zero_le L)
  simpa [schedule,commonCap,volume,density] using hh

lemma uniform_mono (c : Caps) (V : ℕ) (δ ε : ℝ) (hδε : δ≤ ε)
    (h : UniformDensity.{u} c V ε) : UniformDensity.{u} c V δ := by
  intro β _ _ H hH hV
  obtain ⟨A,hA,hcard⟩ := h β H hH hV
  exact ⟨A,hA,(mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg _)).trans hcard⟩

/-- A desired physical time can be reached with an explicit terminal-scale
condition and at most 2m^3 bounded-volume restarts. -/
theorem uniform_horizon (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hT : 1≤ T) (hT3 : T^3≤ (m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤ d*Real.exp (-a m*((T+1)^3-1))) :
    UniformDensity.{u} (caps m d 1 3 P) (m^A) (efficiency m*(T-1)/d) := by
  obtain ⟨L,hL,hTL,hLT,hS⟩ := stopping_small m T (by omega) hT hT3
  have hdL := hterminal.trans (terminal_scale m L d T (by omega) hd.le hT hLT)
  have hh := uniform_fixed m A L d P hm hmV hd hdU hP hPm hL hS hdL
  apply uniform_mono _ _ _ _ _ hh
  have he : 0≤ efficiency m := le_trans (by norm_num) (efficiency_bounds m hm).1
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hTL]) he) hd.le

#print axioms valid
#print axioms uniform_fixed
#print axioms uniform_horizon
end
end Erdos773.GreedyBatchProfileIteration
