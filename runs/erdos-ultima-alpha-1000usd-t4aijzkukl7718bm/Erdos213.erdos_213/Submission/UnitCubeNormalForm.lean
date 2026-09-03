import FormalConjecturesUtil

/-! Complete single-generator normalization for the equal-edge planar cube.
The four body-diagonal square conditions are not solved here. -/
namespace Erdos213.UnitCubeNormalForm

noncomputable section

def vx (t : ℚ) : ℚ := (1-6*t^2+t^4)/(1+t^2)^2
def vy (t : ℚ) : ℚ := 4*t*(1-t^2)/(1+t^2)^2
def point (t : ℚ) : ℂ := (vx t : ℂ)+(vy t : ℂ)*Complex.I

private lemma denom (t : ℚ) : 1+t^2 ≠ 0 := ne_of_gt (by positivity)

lemma unit_identity (t : ℚ) : vx t^2+vy t^2=1 := by
  unfold vx vy
  field_simp
  ring

lemma face_sum_identity (t s : ℚ) :
    (vx t+vx s)^2+(vy t+vy s)^2 =
      (2*((1-t^2)*(1-s^2)+4*t*s)/((1+t^2)*(1+s^2)))^2 := by
  unfold vx vy
  field_simp
  ring

lemma face_sub_identity (t s : ℚ) :
    (vx t-vx s)^2+(vy t-vy s)^2 =
      (4*(t-s)*(1+t*s)/((1+t^2)*(1+s^2)))^2 := by
  unfold vx vy
  field_simp
  ring

lemma all_faces_square (t s : ℚ) :
    IsSquare ((vx t+vx s)^2+(vy t+vy s)^2) ∧
    IsSquare ((vx t-vx s)^2+(vy t-vy s)^2) := by
  rw [face_sum_identity,face_sub_identity]
  exact ⟨IsSquare.sq _,IsSquare.sq _⟩

/-- In characteristic coordinates, equal unit norms and two rational face
lengths force the characteristic itself to be a rational square. -/
lemma characteristic_square {D x y a b : ℚ} (hy : y ≠ 0)
    (hu : x^2+D*y^2=1)
    (ha : (1+x)^2+D*y^2=a^2) (hb : (1-x)^2+D*y^2=b^2) :
    IsSquare D := by
  have hprod : (a*b)^2=4*D*y^2 := by
    have h1 : a^2=2+2*x := by nlinarith [hu,ha]
    have h2 : b^2=2-2*x := by nlinarith [hu,hb]
    calc
      (a*b)^2=a^2*b^2 := by ring
      _=(2+2*x)*(2-2*x) := by rw [h1,h2]
      _=4*D*y^2 := by nlinarith [hu]
  refine ⟨a*b/(2*y),?_⟩
  field_simp
  nlinarith [hprod]

private lemma circle_parameter {p q : ℚ} (hp : 0 < p) (hq : 0 < q)
    (h : p^2+q^2=1) :
    ∃ t : ℚ, 0 < t ∧ t < 1 ∧
      (1-t^2)/(1+t^2)=p ∧ 2*t/(1+t^2)=q := by
  let t := q/(1+p)
  have hp1 : 0 < 1+p := by linarith
  have hq1 : q < 1 := by nlinarith [sq_pos_of_pos hp]
  have ht0 : 0 < t := div_pos hq hp1
  have ht1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hp1).mpr (by linarith)
  refine ⟨t,ht0,ht1,?_,?_⟩
  · dsimp [t]
    field_simp
    nlinarith [h, mul_nonneg (sq_nonneg p) (sq_nonneg q)]
  · dsimp [t]
    field_simp
    nlinarith [h]

private lemma square_coordinates {p q t : ℚ}
    (hp : (1-t^2)/(1+t^2)=p) (hq : 2*t/(1+t^2)=q) :
    p^2-q^2=vx t ∧ 2*p*q=vy t := by
  rw [←hp,←hq]
  unfold vx vy
  constructor <;> field_simp <;> ring

/-- Every unit generator in the upper half-plane with rational plus and
minus face lengths has the displayed rational normal form. The assumption
on the imaginary part excludes parallel generators. -/
theorem complete_normal_form {z : ℂ} (hz : ‖z‖=1) (him : 0 < z.im)
    (hplus : ‖1+z‖ ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hminus : ‖1-z‖ ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ t : ℚ, 0 < t ∧ t < 1 ∧ z=point t := by
  obtain ⟨a,ha⟩ := hplus
  obtain ⟨b,hb⟩ := hminus
  have hunit : z.re^2+z.im^2=1 := by
    have h := congrArg (fun x : ℝ => x^2) hz
    dsimp only at h
    rw [Complex.sq_norm,Complex.normSq_apply] at h
    nlinarith [h]
  have hA : (a : ℝ)^2=(1+z.re)^2+z.im^2 := by
    rw [ha,Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  have hB : (b : ℝ)^2=(1-z.re)^2+z.im^2 := by
    rw [hb,Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  have ha0 : 0 < (a : ℝ) := by
    rw [ha]
    apply norm_pos_iff.mpr
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    linarith
  have hb0 : 0 < (b : ℝ) := by
    rw [hb]
    apply norm_pos_iff.mpr
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    linarith
  have hab : (a : ℝ)^2+(b : ℝ)^2=4 := by nlinarith
  have hprod : ((a : ℝ)*(b : ℝ))^2=(2*z.im)^2 := by
    have h1 : (a : ℝ)^2=2+2*z.re := by nlinarith [hunit,hA]
    have h2 : (b : ℝ)^2=2-2*z.re := by nlinarith [hunit,hB]
    calc
      ((a : ℝ)*(b : ℝ))^2=(a : ℝ)^2*(b : ℝ)^2 := by ring
      _=(2+2*z.re)*(2-2*z.re) := by rw [h1,h2]
      _=(2*z.im)^2 := by nlinarith [hunit]
  have hy : (a : ℝ)*(b : ℝ)=2*z.im := by
    nlinarith [mul_pos ha0 hb0]
  let p : ℚ := a/2
  let q : ℚ := b/2
  have hp : 0 < p := by dsimp [p]; exact div_pos (by exact_mod_cast ha0) (by norm_num)
  have hq : 0 < q := by dsimp [q]; exact div_pos (by exact_mod_cast hb0) (by norm_num)
  have hpq : p^2+q^2=1 := by
    have hab' : a^2+b^2=4 := by exact_mod_cast hab
    dsimp [p,q]
    nlinarith [hab']
  obtain ⟨t,ht0,ht1,hpt,hqt⟩ := circle_parameter hp hq hpq
  have hc := square_coordinates hpt hqt
  refine ⟨t,ht0,ht1,?_⟩
  apply Complex.ext
  · simp only [point,Complex.add_re,Complex.mul_re,Complex.ratCast_re,
      Complex.ratCast_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    have he : ((p^2-q^2 : ℚ) : ℝ)=z.re := by
      dsimp [p,q]
      push_cast
      nlinarith [hA,hB]
    rw [←hc.1]
    exact he.symm
  · simp only [point,Complex.add_im,Complex.mul_im,Complex.ratCast_re,
      Complex.ratCast_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add]
    have he : ((2*p*q : ℚ) : ℝ)=z.im := by
      dsimp [p,q]
      push_cast
      nlinarith [hy]
    rw [←hc.2]
    exact he.symm

/-- Independent sign changes of cube generators only translate and relabel
its vertices. This covers both nonreal half-planes in the normal form. -/
theorem complete_up_to_sign {z : ℂ} (hz : ‖z‖=1) (him : z.im ≠ 0)
    (hplus : ‖1+z‖ ∈ Set.range (Rat.cast : ℚ → ℝ))
    (hminus : ‖1-z‖ ∈ Set.range (Rat.cast : ℚ → ℝ)) :
    ∃ t : ℚ, 0 < t ∧ t < 1 ∧ (z=point t ∨ z= -point t) := by
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hn : ‖-z‖=1 := by simpa using hz
    have hi : 0 < (-z).im := by simpa using neg_pos.mpr hneg
    have hpa : ‖1+(-z)‖ ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      simpa only [sub_eq_add_neg] using hminus
    have hmi : ‖1-(-z)‖ ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      simpa only [sub_neg_eq_add] using hplus
    obtain ⟨t,ht0,ht1,ht⟩ := complete_normal_form hn hi hpa hmi
    exact ⟨t,ht0,ht1,Or.inr (neg_eq_iff_eq_neg.mp ht)⟩
  · obtain ⟨t,ht0,ht1,ht⟩ := complete_normal_form hz hpos hplus hminus
    exact ⟨t,ht0,ht1,Or.inl ht⟩

private lemma rational_complex_norm_sq (x y : ℚ) :
    ‖(x : ℂ)+(y : ℂ)*Complex.I‖^2=((x^2+y^2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp
  ring

lemma norm_rational_iff (x y : ℚ) :
    ‖(x : ℂ)+(y : ℂ)*Complex.I‖ ∈ Set.range (Rat.cast : ℚ → ℝ) ↔
      IsSquare (x^2+y^2) := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    have he := rational_complex_norm_sq x y
    rw [←ha] at he
    have he' : a^2=x^2+y^2 := by exact_mod_cast he
    nlinarith [he']
  · rintro ⟨a,ha⟩
    refine ⟨|a|,?_⟩
    have he := rational_complex_norm_sq x y
    rw [ha] at he
    push_cast at he ⊢
    have hsq : |(a : ℝ)|^2=‖(x : ℂ)+(y : ℂ)*Complex.I‖^2 := by
      nlinarith [sq_abs (a : ℝ)]
    exact (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq

def body (t s e f : ℚ) : ℚ :=
  (1+e*vx t+f*vx s)^2+(e*vy t+f*vy s)^2

/-- Each of the four body-diagonal conditions is precisely one square
condition, taking e,f independently from {1,-1}. -/
lemma body_norm_iff (t s e f : ℚ) :
    ‖1+(e : ℂ)*point t+(f : ℂ)*point s‖ ∈ Set.range (Rat.cast : ℚ → ℝ) ↔
      IsSquare (body t s e f) := by
  have he : 1+(e : ℂ)*point t+(f : ℂ)*point s =
      ((1+e*vx t+f*vx s : ℚ) : ℂ)+((e*vy t+f*vy s : ℚ) : ℂ)*Complex.I := by
    unfold point
    push_cast
    ring
  rw [he,norm_rational_iff]
  rfl

lemma original_control_not_all_body_squares : ¬ IsSquare (body (1/2) (2/3) 1 1) := by
  norm_num [body,vx,vy,Rat.isSquare_iff]

#print axioms characteristic_square
#print axioms unit_identity
#print axioms all_faces_square
#print axioms complete_normal_form
#print axioms complete_up_to_sign
#print axioms body_norm_iff
#print axioms original_control_not_all_body_squares
end
end Erdos213.UnitCubeNormalForm
