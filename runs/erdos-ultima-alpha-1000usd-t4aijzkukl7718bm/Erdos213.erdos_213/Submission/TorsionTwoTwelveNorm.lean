import Submission.OrthogonalCurve

/-! Exact arithmetic for a quadratic-field 2-by-12 torsion family.
These are restricted construction obstructions, not a settlement of Erdos 213.
The parameter range v>1 gives an imaginary quadratic coordinate field. -/
namespace Erdos213.TorsionTwoTwelve

set_option maxHeartbeats 2000000

def characteristic (v : ℚ) : ℚ := (v^2-1)*(3*v^2+1)
def normClass (v : ℚ) : ℚ := (v^4-1)*(9*v^4-1)
def crossClass (v : ℚ) : ℚ := (v^2+1)*(3*v^2-1)

lemma class_product (v : ℚ) :
    normClass v = characteristic v * crossClass v := by
  dsimp [normClass,characteristic,crossClass]
  ring

lemma parameter_sq_gt_one {v : ℚ} (hv : 1<v) : 1<v^2 := by
  nlinarith

lemma characteristic_pos {v : ℚ} (hv : 1<v) : 0<characteristic v := by
  have h : 0<v^2-1 := by have := parameter_sq_gt_one hv; linarith
  dsimp [characteristic]
  positivity

lemma normClass_not_square {v : ℚ} (hv : 1<v) : ¬ IsSquare (normClass v) := by
  rintro ⟨w,hw⟩
  have h4 : 1<v^4 := by
    have h2 := parameter_sq_gt_one hv
    nlinarith [sq_nonneg (v^2-1)]
  have he : (9*v^2*w)^2=(9*v^4)*(9*v^4-1)*(9*v^4-9) := by
    dsimp [normClass] at hw
    linear_combination -81*v^4*hw
  obtain ⟨hx,-⟩ := (OrthogonalCurve.isogenous_affine_points_iff _ _).mp he
  rcases hx with hx | hx | hx <;> nlinarith

lemma crossClass_not_square {v : ℚ} (hv : 1<v) : ¬ IsSquare (crossClass v) := by
  rintro ⟨w,hw⟩
  have h2 := parameter_sq_gt_one hv
  have he : (3*v*w)^2=(3*v^2-1)*((3*v^2-1)+1)*((3*v^2-1)+4) := by
    dsimp [crossClass] at hw
    linear_combination -9*v^2*hw
  rcases (OrthogonalCurve.affine_points_iff _ _).mp he with h | h | h | h | h
  all_goals nlinarith [h.1]

/-- The coefficients below are 32*v^8 times the three nonreal y representatives.
Their full orbits are obtained by negation and conjugation. -/
def realPart (v : ℚ) : Fin 3 → ℚ :=
  ![-2*v^2*(v^2-1)^3*(3*v^2+1),
    (v-1)*(v+1)^5*(3*v^2+1)*(v^2+1),
    (v+1)*(v-1)^5*(3*v^2+1)*(v^2+1)]

def imagCoeff (v : ℚ) : Fin 3 → ℚ :=
  ![8*v^5*(v^2-1),
    -(v+1)^2*(v^2+1)*(3*v^4-2*v^3-2*v^2-2*v-1),
    (v-1)^2*(v^2+1)*(3*v^4+2*v^3-2*v^2+2*v-1)]

def normFactor (v : ℚ) : Fin 3 → ℚ :=
  ![2*v^2*(v^4-1), 2*v^2*(v+1)^2*(v^2+1), 2*v^2*(v-1)^2*(v^2+1)]

def ordinateNorm (v : ℚ) (i : Fin 3) : ℚ :=
  realPart v i ^ 2 + characteristic v * imagCoeff v i ^ 2

lemma ordinateNorm_factor (v : ℚ) (i : Fin 3) :
    ordinateNorm v i = normFactor v i ^ 2 * normClass v := by
  fin_cases i <;> norm_num [ordinateNorm,realPart,imagCoeff,normFactor,
    characteristic,normClass,Matrix.cons_val_two] <;> ring

lemma normFactor_ne_zero {v : ℚ} (hv : 1<v) (i : Fin 3) : normFactor v i ≠ 0 := by
  have h0 : 0<v := by linarith
  have hm : 0<v-1 := by linarith
  have h4 : 0<v^4-1 := by
    have h2 := parameter_sq_gt_one hv
    nlinarith [sq_nonneg (v^2-1)]
  apply ne_of_gt
  fin_cases i
  · change 0 < 2*v^2*(v^4-1)
    positivity
  · change 0 < 2*v^2*(v+1)^2*(v^2+1)
    positivity
  · change 0 < 2*v^2*(v-1)^2*(v^2+1)
    positivity

lemma realPart_ne_zero {v : ℚ} (hv : 1<v) (i : Fin 3) : realPart v i ≠ 0 := by
  have h0 : v≠0 := by linarith
  have hm : v-1≠0 := by linarith
  have hp : v+1≠0 := by linarith
  have hs : v^2-1≠0 := by have := parameter_sq_gt_one hv; linarith
  have h3 : 3*v^2+1≠0 := ne_of_gt (by positivity)
  have h2 : v^2+1≠0 := ne_of_gt (by positivity)
  fin_cases i <;> simp [realPart,Matrix.cons_val_two,h0,hm,hp,hs,h3,h2]

lemma ordinateNorm_not_square {v : ℚ} (hv : 1<v) (i : Fin 3) :
    ¬ IsSquare (ordinateNorm v i) := by
  intro hs
  have hf := normFactor_ne_zero hv i
  have hh := hs.div (IsSquare.sq (normFactor v i))
  rw [ordinateNorm_factor] at hh
  have he : normFactor v i ^ 2 * normClass v / normFactor v i ^ 2 = normClass v := by
    field_simp
  rw [he] at hh
  exact normClass_not_square hv hh

/-- In particular the ordinate norm and the characteristic lie in distinct
rational square classes. The statement includes a zero-coordinate control. -/
lemma norm_characteristic_separated {v : ℚ} (hv : 1<v) (i : Fin 3)
    {r s : ℚ} (hr : r≠0)
    (h : ordinateNorm v i * r^2 = characteristic v * s^2) : False := by
  have hD := ne_of_gt (characteristic_pos hv)
  have hf := normFactor_ne_zero hv i
  apply crossClass_not_square hv
  refine ⟨s/(normFactor v i*r), ?_⟩
  rw [ordinateNorm_factor,class_product] at h
  field_simp
  have he : normFactor v i^2 * crossClass v * r^2=s^2 := by
    apply mul_left_cancel₀ hD
    linear_combination h
  nlinarith only [he]

#print axioms normClass_not_square
#print axioms crossClass_not_square
#print axioms ordinateNorm_not_square
#print axioms norm_characteristic_separated
end Erdos213.TorsionTwoTwelve
