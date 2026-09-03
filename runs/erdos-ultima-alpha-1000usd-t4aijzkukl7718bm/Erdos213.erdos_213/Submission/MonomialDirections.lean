import FormalConjecturesUtil

/-! Algebra behind the monomial-direction investigation. No statement about
arbitrary integral-distance sets is asserted here. -/
namespace Erdos213.MonomialDirections
noncomputable section

/-- A point specified by its conjugate-direction ratios to 0 and 1. -/
def point (u v : ℂ) : ℂ := (1-v)/(u-v)

lemma conjugate_point {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1) :
    starRingEnd ℂ (point u v)=u*point u v := by
  by_cases huv : u=v
  · simp [point,huv]
  have hu0 : u≠0 := by intro he; simp [he] at hu
  have hv0 : v≠0 := by intro he; simp [he] at hv
  have huv0 : u-v≠0 := sub_ne_zero.mpr huv
  unfold point
  rw [map_div₀, map_sub, map_sub, map_one, ← Complex.inv_eq_conj hu,
    ← Complex.inv_eq_conj hv]
  field_simp [hu0, hv0, huv0, sub_ne_zero.mpr (Ne.symm huv)]
  ring

lemma conjugate_point_sub_one {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1)
    (huv : u≠v) : starRingEnd ℂ (point u v-1)=v*(point u v-1) := by
  rw [map_sub,map_one,conjugate_point hu hv]
  have huv0 : u-v≠0 := sub_ne_zero.mpr huv
  dsimp [point]
  field_simp
  ring

lemma difference {u v U V : ℂ} (huv : u≠v) (hUV : U≠V) :
    point u v-point U V=(U-u+v-V-v*U+V*u)/((u-v)*(U-V)) := by
  have h0 : u-v≠0 := sub_ne_zero.mpr huv
  have h1 : U-V≠0 := sub_ne_zero.mpr hUV
  dsimp [point]
  field_simp
  ring

/-- A square conjugate-direction phase turns a norm into an absolute real part. -/
lemma norm_of_square_phase {z u : ℂ} (hu : ‖u‖=1)
    (hz : starRingEnd ℂ z=u^2*z) : ‖z‖=|(u*z).re| := by
  have hu0 : u≠0 := by intro he; simp [he] at hu
  have hreal : starRingEnd ℂ (u*z)=u*z := by
    rw [map_mul,hz,← Complex.inv_eq_conj hu]
    field_simp
  have him : (u*z).im=0 := Complex.conj_eq_iff_im.mp hreal
  have he : u*z=((u*z).re : ℂ) := Complex.ext rfl (by simpa using him)
  have hn := congrArg (fun w : ℂ => ‖w‖) he
  simpa only [norm_mul,hu,one_mul,Complex.norm_real,Real.norm_eq_abs] using hn

lemma rational_norm_of_square_phase {z u : ℂ} (hu : ‖u‖=1)
    (hz : starRingEnd ℂ z=u^2*z)
    (hr : (u*z).re ∈ Set.range ((↑) : ℚ → ℝ)) :
    ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hr
  refine ⟨|r|,?_⟩
  rw [Rat.cast_abs,hr,norm_of_square_phase hu hz]

lemma fixed_conjugate_ratio {z : ℂ} {r s : ℂ} (hz : z≠0)
    (hr : starRingEnd ℂ z=r*z) (hs : starRingEnd ℂ z=s*z) : r=s := by
  exact mul_right_cancel₀ hz (hr.symm.trans hs)

/-- An exact square-phase criterion in a complex subfield with rational real parts.
The hypotheses hold, for example, for an imaginary quadratic subfield. -/
lemma rational_norm_iff_square_phase (K : Subfield ℂ)
    (hre : ∀ w ∈ K, w.re ∈ Set.range ((↑) : ℚ → ℝ))
    {z : ℂ} (hz : z ∈ K) (hz0 : z ≠ 0) (hcz : starRingEnd ℂ z ∈ K) :
    ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ) ↔
      ∃ u ∈ K, ‖u‖ = 1 ∧ starRingEnd ℂ z = u^2*z := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, Rat.cast_zero] at hr
      exact hz0 (norm_eq_zero.mp hr.symm)
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    let u : ℂ := starRingEnd ℂ z / (r : ℂ)
    have hprod : starRingEnd ℂ z*z = (r : ℂ)^2 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← hr]
      norm_cast
    have huz : u*z = (r : ℂ) := by
      dsimp [u]
      field_simp
      simpa [pow_two] using hprod
    refine ⟨u, K.div_mem hcz (SubfieldClass.ratCast_mem K r), ?_, ?_⟩
    · change ‖starRingEnd ℂ z / (r : ℂ)‖ = 1
      rw [norm_div, Complex.norm_conj, Complex.norm_ratCast, hr,
        abs_of_nonneg (norm_nonneg z)]
      exact div_self (norm_ne_zero_iff.mpr hz0)
    · calc
        starRingEnd ℂ z = u*(r : ℂ) := by simp [u, hrc]
        _ = u*(u*z) := by rw [huz]
        _ = u^2*z := by ring
  · rintro ⟨u, huK, hu, hphase⟩
    exact rational_norm_of_square_phase hu hphase (hre _ (K.mul_mem huK hz))

#print axioms conjugate_point
#print axioms difference
#print axioms rational_norm_of_square_phase
#print axioms rational_norm_iff_square_phase
end
end Erdos213.MonomialDirections
