import Submission.PopulationLaplaceInsertion

/-! A full-resampling Gibbs estimate retaining the cost of large private
populations. Unlike an unweighted variance substitution, this is a genuine
weighted inequality. It does not assert a critical-scale row cap. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages Erdos970.CoverFibers
set_option maxHeartbeats 1500000

lemma residueMean_comm (p q : ℕ) (f : Fin p → Fin q → ℝ) :
    residueMean p (fun a => residueMean q (f a)) =
      residueMean q (fun b => residueMean p (fun a => f a b)) := by
  simp only [residueMean,← sum_div]
  rw [sum_comm]
  ring

lemma hits_after_avoid (S : Finset ℕ) (p : ℕ) (a b : Fin p) :
    classHits (avoidClass S p b) p a = if a = b then 0 else classHits S p a := by
  by_cases hab : a = b
  · subst a
    simp [classHits_avoided]
  · have hh := classHits_split S p a b
    simpa only [if_neg hab,add_zero] using hh.symm

lemma resampling_square_le_hit_caps (S : Finset ℕ) (p : ℕ) (B : ℝ)
    (hcap : ∀ a : Fin p, classHits S p a ≤ B) (a b : Fin p) :
    (remainingCount S p a-remainingCount S p b)^2 ≤
      B*(classHits (avoidClass S p b) p a+classHits (avoidClass S p a) p b) := by
  by_cases hab : a = b
  · subst a
    simp [classHits_avoided]
  · rw [remainingCount_eq,remainingCount_eq,hits_after_avoid,hits_after_avoid,
      if_neg hab,if_neg (Ne.symm hab)]
    have ha0 := classHits_nonneg S p a
    have hb0 := classHits_nonneg S p b
    have ha := mul_le_mul_of_nonneg_right (hcap a) ha0
    have hb := mul_le_mul_of_nonneg_right (hcap b) hb0
    nlinarith [mul_nonneg ha0 hb0]

lemma gibbs_resampling_weight_le (S : Finset ℕ) (p : ℕ) (t B : ℝ)
    (ht : 0 ≤ t) (hcap : ∀ a : Fin p, classHits S p a ≤ B) (a b : Fin p) :
    exp (-t*remainingCount S p b) ≤ exp (t*B)*exp (-t*remainingCount S p a) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have ha0 := classHits_nonneg S p a
  have hh : remainingCount S p a-remainingCount S p b ≤ B := by
    rw [remainingCount_eq,remainingCount_eq]
    linarith only [ha0,hcap b]
  have hm := mul_le_mul_of_nonneg_left hh ht
  nlinarith only [hm]

/-- The full second moment under the actual Gibbs weight is bounded by a
weighted population moment. The factor exp(t*B) pays for private points
exposed by resampling; it must not be silently dropped. -/
theorem gibbs_resampling_second_moment (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hcap : ∀ a : Fin p, classHits S p a ≤ B) :
    residueMean p (fun b => exp (-t*remainingCount S p b)*
      residueMean p (fun a => (remainingCount S p a-remainingCount S p b)^2)) ≤
      ((1+exp (t*B))*B/p)*
        residueMean p (fun b => exp (-t*remainingCount S p b)*remainingCount S p b) := by
  let w := fun b : Fin p => exp (-t*remainingCount S p b)
  let H := fun b a : Fin p => classHits (avoidClass S p b) p a
  have hpoint (b a : Fin p) :
      w b*(remainingCount S p a-remainingCount S p b)^2 ≤
        B*(w b*H b a+exp (t*B)*(w a*H a b)) := by
    have hs := mul_le_mul_of_nonneg_left (resampling_square_le_hit_caps S p B hcap a b)
      (exp_pos (-t*remainingCount S p b)).le
    have hw := mul_le_mul_of_nonneg_right
      (gibbs_resampling_weight_le S p t B ht hcap a b)
      (classHits_nonneg (avoidClass S p a) p b)
    have hwB := mul_le_mul_of_nonneg_left hw hB
    dsimp only [w,H]
    nlinarith only [hs,hwB]
  have hmean (b : Fin p) : residueMean p (H b) = remainingCount S p b/p := by
    exact classHits_mean (avoidClass S p b) p hp
  have hsecond : residueMean p (fun b => residueMean p (fun a => w a*H a b)) =
      residueMean p (fun a => w a*(remainingCount S p a/p)) := by
    rw [residueMean_comm]
    simp_rw [residueMean_mul,hmean]
  have hh := residueMean_mono p (fun b => residueMean_mono p (fun a => hpoint b a))
  simp only [residueMean_mul,residueMean_add] at hh
  simp_rw [hmean] at hh
  rw [hsecond] at hh
  have hid : residueMean p (fun b => w b*(remainingCount S p b/p)) =
      (1/(p : ℝ))*residueMean p (fun b => w b*remainingCount S p b) := by
    rw [← residueMean_mul]
    congr 1
    funext b
    ring
  rw [hid] at hh
  convert hh using 1
  dsimp only [w]
  ring

/-- Transfer to full prime phases, keeping both the outer Gibbs weight and
all new-coordinate resampling. The deterministic cap is still explicit. -/
theorem prime_insert_gibbs_resampling (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (hp0 : 0 < p) (m : ℕ) (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hcap : ∀ (r : Phase P) (a : Fin p), rowCount P m p a r ≤ B) :
    phaseMean P (fun r => residueMean p (fun b =>
      exp (-t*intervalCount (insert p P) m (extendPhase P p r b))*
        residueMean p (fun a =>
          (intervalCount (insert p P) m (extendPhase P p r a)-
            intervalCount (insert p P) m (extendPhase P p r b))^2))) ≤
      ((1+exp (t*B))*B/p)*phaseMean (insert p P) (fun r =>
        exp (-t*intervalCount (insert p P) m r)*intervalCount (insert p P) m r) := by
  have hcount (r : Phase P) (a : Fin p) :
      intervalCount (insert p P) m (extendPhase P p r a) =
        remainingCount (CoverFibers.phaseSurvivors P m r) p a := by
    rw [← CoverFibers.phaseSurvivors_card,phaseSurvivors_extend_eq_avoidClass P p hp m r a]
    rfl
  have hpoint (r : Phase P) := gibbs_resampling_second_moment
    (CoverFibers.phaseSurvivors P m r) p hp0 t B ht hB
    (fun a => by simpa only [rowCount_eq_classHits] using hcap r a)
  simp_rw [← hcount] at hpoint
  have hh := phaseMean_mono P hpoint
  rw [phaseMean_mul] at hh
  rw [phaseMean_insert P p hp]
  exact hh

/-- Even one point gives equality in the coefficient, for prime 2. -/
theorem singleton_gibbs_resampling_sharp (t : ℝ) :
    residueMean 2 (fun b => exp (-t*remainingCount {0} 2 b)*
      residueMean 2 (fun a => (remainingCount {0} 2 a-remainingCount {0} 2 b)^2)) =
      ((1+exp t)/2)*residueMean 2
        (fun b => exp (-t*remainingCount {0} 2 b)*remainingCount {0} 2 b) := by
  simp only [residueMean,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    remainingCount,avoidClass]
  norm_num [Finset.filter_singleton]
  rw [exp_neg]
  field_simp
  ring

lemma singleton_gibbs_population_pos (t : ℝ) :
    0 < residueMean 2 (fun b => exp (-t*remainingCount {0} 2 b)*remainingCount {0} 2 b) := by
  simp only [residueMean,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    remainingCount,avoidClass]
  norm_num [Finset.filter_singleton]
  positivity

/-- There is no coefficient independent of the tilt parameter, even for a
single point and a genuine prime coordinate. This is only an auxiliary
statement; a bound at one fixed positive parameter is not refuted here. -/
theorem no_uniform_tilt_resampling_coefficient :
    ¬∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      residueMean 2 (fun b => exp (-t*remainingCount {0} 2 b)*
        residueMean 2 (fun a => (remainingCount {0} 2 a-remainingCount {0} 2 b)^2)) ≤
      C*residueMean 2 (fun b => exp (-t*remainingCount {0} 2 b)*remainingCount {0} 2 b) := by
  rintro ⟨C,hC⟩
  let t := 2*|C|+2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hh := hC t ht
  rw [singleton_gibbs_resampling_sharp] at hh
  have hcoef := (mul_le_mul_iff_left₀ (singleton_gibbs_population_pos t)).mp hh
  have he := add_one_le_exp t
  have hCC := le_abs_self C
  dsimp [t] at he hcoef
  nlinarith only [hcoef,he,hCC]

#print axioms gibbs_resampling_second_moment
#print axioms prime_insert_gibbs_resampling
#print axioms singleton_gibbs_resampling_sharp
#print axioms no_uniform_tilt_resampling_coefficient
end Erdos970.Resampling
