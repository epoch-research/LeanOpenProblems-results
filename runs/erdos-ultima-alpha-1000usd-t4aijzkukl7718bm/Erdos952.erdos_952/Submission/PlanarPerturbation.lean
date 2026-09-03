import FormalConjecturesUtil

/-! A planar bounded-perturbation lemma, proved using the exponential covering.
This is topological infrastructure, not a proof of the Gaussian moat conjecture. -/
namespace Erdos952Investigation.PlanarPerturbation
open Topology
set_option maxHeartbeats 0

lemma exists_continuous_log {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocPathConnectedSpace A]
    (f : A → ℂ) (hf : Continuous f) (hne : ∀ a, f a ≠ 0) (a₀ : A) :
    ∃ g : A → ℂ, Continuous g ∧ ∀ a, Complex.exp (g a) = f a := by
  let F : C(A, {z : ℂ // z ≠ 0}) := ⟨fun a => ⟨f a,hne a⟩,hf.subtype_mk hne⟩
  obtain ⟨g,hg,-⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts F
    a₀ (Complex.log (f a₀)) (Subtype.ext (Complex.exp_log (hne a₀)))
  exact ⟨g,g.continuous,fun a => congrArg Subtype.val (congr_fun hg.2 a)⟩

/-- A continuous map on the whole plane that is strictly closer to the
identity than the radius on a circle must vanish somewhere. -/
theorem exists_zero_of_circle_close (f : ℂ → ℂ) (hf : Continuous f)
    (R : ℝ) (hR : 0 < R)
    (hclose : ∀ z : ℂ, ‖z‖ = R → ‖f z-z‖ < R) : ∃ z, f z = 0 := by
  by_contra! hne
  obtain ⟨g,hg,hgexp⟩ := exists_continuous_log f hf hne 0
  let c : ℝ → ℂ := fun t => (R : ℂ)*Complex.exp ((t : ℂ)*Complex.I)
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hcn (t : ℝ) : ‖c t‖ = R := by
    simp [c,norm_mul,Complex.norm_exp_ofReal_mul_I,abs_of_pos hR]
  have hcne (t : ℝ) : c t ≠ 0 := by
    intro he
    have := hcn t
    rw [he,norm_zero] at this
    linarith
  let q : ℝ → ℂ := fun t => f (c t)/c t
  have hq : Continuous q := (hf.comp hc).div hc hcne
  have hqne (t : ℝ) : q t ≠ 0 := div_ne_zero (hne _) (hcne _)
  have hqsmall (t : ℝ) : ‖q t-1‖ < 1 := by
    have he : q t-1 = (f (c t)-c t)/c t := by
      dsimp [q]
      rw [sub_div,div_self (hcne t)]
    rw [he,norm_div,hcn,div_lt_one hR]
    exact hclose (c t) (hcn t)
  have hqslit (t : ℝ) : q t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have hh := (Complex.abs_re_le_norm (q t-1)).trans_lt (hqsmall t)
    simp only [Complex.sub_re,Complex.one_re] at hh
    have hh' := (abs_lt.mp hh).1
    linarith
  have hlogq : Continuous (fun t => Complex.log (q t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_clog (hqslit t)).comp hq.continuousAt
  let k : ℝ → ℂ := fun t => g (c t)-Complex.log (q t)-(t : ℂ)*Complex.I
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkexp (t : ℝ) : Complex.exp (k t) = (R : ℂ) := by
    dsimp only [k]
    rw [Complex.exp_sub,Complex.exp_sub,hgexp,Complex.exp_log (hqne t)]
    dsimp only [q,c]
    field_simp [hne,Complex.exp_ne_zero]
  have hconst := Complex.isCoveringMap_exp.const_of_comp hk
    (fun s t => Subtype.ext ((hkexp s).trans (hkexp t).symm)) 0 (2*Real.pi)
  have hc0 : c 0 = (R : ℂ) := by simp [c]
  have hcP : c (2*Real.pi) = (R : ℂ) := by
    simp only [c,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.exp_two_pi_mul_I,mul_one]
  have hqP : q (2*Real.pi) = q 0 := by dsimp only [q]; rw [hc0,hcP]
  dsimp only [k] at hconst
  rw [hc0,hcP,hqP] at hconst
  have hi := congrArg Complex.im hconst
  simp only [Complex.sub_im,zero_mul,Complex.zero_im,sub_zero,
    Complex.mul_im,Complex.I_im,Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_one,mul_zero,add_zero] at hi
  linarith [Real.pi_pos]

/-- Every continuous bounded perturbation of the identity on the complex
plane is surjective. -/
theorem surjective_of_bounded_sub_id (f : ℂ → ℂ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ z, ‖f z-z‖ ≤ B) : Function.Surjective f := by
  intro w
  have hfn : Continuous (fun z => f z-w) := hf.sub continuous_const
  obtain ⟨z,hz⟩ := exists_zero_of_circle_close (fun z => f z-w) hfn
    (|B|+‖w‖+1) (by positivity) (by
      intro z _
      have he : f z-w-z = (f z-z)-w := by ring
      rw [he]
      have hh := norm_sub_le (f z-z) w
      have hb := hB z
      have hab := le_abs_self B
      linarith)
  exact ⟨z,sub_eq_zero.mp hz⟩

#print axioms surjective_of_bounded_sub_id
end Erdos952Investigation.PlanarPerturbation
