import Submission.PlanarPerturbation

/-! Crossing of continuous curves with independent linear drifts, and the
periodic extension of a finite path. -/
namespace Erdos952Investigation.PeriodicCurveCrossing
open Topology
open scoped unitInterval
set_option maxHeartbeats 0

/-- Two bounded perturbations of nonparallel lines in the plane intersect. -/
theorem bounded_drift_curves_intersect (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (d e : ℂ)
    (hdet : d.re*e.im-d.im*e.re ≠ 0) (A B : ℝ)
    (hA : ∀ t : ℝ, ‖f t-(t : ℂ)*d‖ ≤ A)
    (hB : ∀ t : ℝ, ‖g t-(t : ℂ)*e‖ ≤ B) :
    ∃ s t : ℝ, f s = g t := by
  let D := d.re*e.im-d.im*e.re
  let a : ℂ → ℝ := fun z => (z.re*e.im-z.im*e.re)/D
  let b : ℂ → ℝ := fun z => (z.re*d.im-z.im*d.re)/D
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have heq (z : ℂ) : (a z : ℂ)*d-(b z : ℂ)*e = z := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    all_goals dsimp [a,b,D]; simp only [div_eq_mul_inv]
    · linear_combination z.re * (mul_inv_cancel₀ hdet)
    · linear_combination z.im * (mul_inv_cancel₀ hdet)
  let F : ℂ → ℂ := fun z => f (a z)-g (b z)
  have hF : Continuous F := (hf.comp ha).sub (hg.comp hb)
  have hbound (z : ℂ) : ‖F z-z‖ ≤ A+B := by
    have he : F z-z = (f (a z)-(a z : ℂ)*d)-(g (b z)-(b z : ℂ)*e) := by
      dsimp [F]
      calc
        f (a z)-g (b z)-z = f (a z)-g (b z)-((a z : ℂ)*d-(b z : ℂ)*e) := by rw [heq]
        _ = _ := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (hA _) (hB _))
  obtain ⟨z,hz⟩ := PlanarPerturbation.surjective_of_bounded_sub_id F hF (A+B) hbound 0
  exact ⟨a z,b z,sub_eq_zero.mp hz⟩

/-- Repeating a finite path and translating by its endpoint displacement
gives a continuous curve at bounded distance from its linear drift. -/
theorem path_drift_extension (a d : ℂ) (p : Path a (a+d)) :
    ∃ f : ℝ → ℂ, Continuous f ∧
      (∃ B : ℝ, ∀ t : ℝ, ‖f t-(t : ℂ)*d‖ ≤ B) ∧
      ∀ t : ℝ, ∃ n : ℤ, ∃ s : I, f t = p s+(n : ℂ)*d := by
  let v : ℝ → ℂ := fun t => p.extend t-(t : ℂ)*d
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hv01 : v 0 = v 1 := by simp [v,p.extend_zero,p.extend_one]
  have hvf : Continuous (fun t : ℝ => v (Int.fract t)) := by
    apply ContinuousOn.comp_fract (f := fun (_ : ℝ) (t : ℝ) => v t)
      (s := id) _ continuous_id (fun _ => hv01)
    exact (hv.comp continuous_snd).continuousOn
  let f : ℝ → ℂ := fun t => v (Int.fract t)+(t : ℂ)*d
  refine ⟨f,hvf.add (by fun_prop),?_,?_⟩
  · obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
      (hv.norm.continuousOn)
    refine ⟨B,fun t => ?_⟩
    change ‖v (Int.fract t)+(t : ℂ)*d-(t : ℂ)*d‖ ≤ B
    rw [add_sub_cancel_right]
    exact hB ⟨Int.fract t,⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩,rfl⟩
  · intro t
    let s : I := ⟨Int.fract t,Int.fract_nonneg t,(Int.fract_lt_one t).le⟩
    refine ⟨⌊t⌋,s,?_⟩
    dsimp [f,v]
    rw [p.extend_apply s.property]
    have he : ((Int.fract t : ℝ) : ℂ)+(⌊t⌋ : ℂ) = (t : ℂ) := by
      exact_mod_cast Int.fract_add_floor t
    change p s-((Int.fract t : ℝ) : ℂ)*d+(t : ℂ)*d = p s+(⌊t⌋ : ℂ)*d
    rw [← he]
    ring

#print axioms bounded_drift_curves_intersect
#print axioms path_drift_extension
end Erdos952Investigation.PeriodicCurveCrossing
