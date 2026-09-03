import Submission.FiniteHerbstBound

/-! Conditional resampling uses row oscillation rather than absolute size.
The bound is genuine for each fixed conditional population. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages Erdos970.CoverFibers
set_option maxHeartbeats 1500000

lemma resampling_square_le_oscillation (S : Finset ℕ) (p : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hosc : ∀ a b : Fin p, |classHits S p a-classHits S p b| ≤ B)
    (a b : Fin p) :
    (remainingCount S p a-remainingCount S p b)^2 ≤
      B*(classHits (avoidClass S p b) p a+classHits (avoidClass S p a) p b) := by
  by_cases hab : a = b
  · subst a
    simp [classHits_avoided]
  · rw [remainingCount_eq,remainingCount_eq,hits_after_avoid,hits_after_avoid,
      if_neg hab,if_neg (Ne.symm hab)]
    have ha := classHits_nonneg S p a
    have hb := classHits_nonneg S p b
    have ho := hosc a b
    have hs : |classHits S p a-classHits S p b| ≤ classHits S p a+classHits S p b := by
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hh := mul_le_mul ho hs (abs_nonneg _) hB
    rw [← sq, sq_abs] at hh
    nlinarith only [hh]

lemma gibbs_resampling_weight_le_oscillation (S : Finset ℕ) (p : ℕ) (t B : ℝ)
    (ht : 0 ≤ t) (hosc : ∀ a b : Fin p, |classHits S p a-classHits S p b| ≤ B)
    (a b : Fin p) :
    exp (-t*remainingCount S p b) ≤ exp (t*B)*exp (-t*remainingCount S p a) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have ho := (le_abs_self (classHits S p b-classHits S p a)).trans (hosc b a)
  have hm := mul_le_mul_of_nonneg_left ho ht
  rw [remainingCount_eq,remainingCount_eq]
  nlinarith only [hm]

/-- Full Gibbs resampling with an oscillation cap, not a raw row cap.
Balanced rows have coefficient zero even when the population is large. -/
theorem gibbs_resampling_oscillation (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hosc : ∀ a b : Fin p, |classHits S p a-classHits S p b| ≤ B) :
    residueMean p (fun b => exp (-t*remainingCount S p b)*
      residueMean p (fun a => (remainingCount S p a-remainingCount S p b)^2)) ≤
      ((1+exp (t*B))*B/p)*
        residueMean p (fun b => exp (-t*remainingCount S p b)*remainingCount S p b) := by
  let w := fun b : Fin p => exp (-t*remainingCount S p b)
  let H := fun b a : Fin p => classHits (avoidClass S p b) p a
  have hpoint (b a : Fin p) :
      w b*(remainingCount S p a-remainingCount S p b)^2 ≤
        B*(w b*H b a+exp (t*B)*(w a*H a b)) := by
    have hs := mul_le_mul_of_nonneg_left (resampling_square_le_oscillation S p B hB hosc a b)
      (exp_pos (-t*remainingCount S p b)).le
    have hw := mul_le_mul_of_nonneg_right
      (gibbs_resampling_weight_le_oscillation S p t B ht hosc a b)
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

#print axioms gibbs_resampling_oscillation
end Erdos970.Resampling
