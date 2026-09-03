import Submission.GaussianQuarticObstruction

/-! A finite interpolation obstruction for homogeneous quadratic output maps
on one explicit five-variable pencil. This does not estimate unrestricted
integer representation counts. -/
namespace Erdos322Research.JointQuadraticGaussianInterpolation

noncomputable section
open Finset QuadraticMap
set_option Elab.async false
set_option maxHeartbeats 0

abbrev K := GaussianQuartic.GaussianRational
abbrev V := Fin 5 → K

def imag : K := algebraMap GaussianInt K Zsqrtd.sqrtd

lemma imag_sq : imag ^ 2 = -1 := by
  have h : (Zsqrtd.sqrtd : GaussianInt) ^ 2 = -1 := by
    simp [pow_two, Zsqrtd.dmuld]
  simpa [imag] using congrArg (algebraMap GaussianInt K) h

lemma imag_ne_zero : imag ≠ 0 := by
  intro h
  have hh := imag_sq
  rw [h] at hh
  norm_num at hh

def weights : Fin 5 → K := ![1,17,26,2,3]
def label₁ (x : V) : K := ∑ i, x i ^ 2
def label₂ (x : V) : K := ∑ i, weights i * x i ^ 2
private def axis (i : Fin 5) : V := Pi.single i 1
private def flip (i : Fin 5) (x : V) : V := x - (2 * x i) • axis i

private lemma flip_sq (i j : Fin 5) (x : V) : flip i x j ^ 2 = x j ^ 2 := by
  by_cases h : j = i
  · subst j
    simp [flip,axis]
    ring
  · simp [flip,axis,h]

private lemma flip_labels (i : Fin 5) (x : V) :
    label₁ (flip i x) = label₁ x ∧ label₂ (flip i x) = label₂ x := by
  constructor <;> simp only [label₁,label₂,flip_sq]

private lemma form_expansion (P : QuadraticForm K V) (x : V) :
    P x = ∑ i, ∑ j, P.associated (axis i) (axis j) * x i * x j := by
  have hx : (∑ i, x i • axis i) = x := by
    funext j
    simp [axis,Pi.single_apply]
  rw [← associated_eq_self_apply K P x, ← hx]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [hx]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [associated_isSymm K P (axis j) (axis i)]
  ring

private lemma mixed_difference (P : QuadraticForm K V) (x : V)
    (i j : Fin 5) (hij : i ≠ j) :
    P x - P (flip i x) - P (flip j x) + P (flip i (flip j x)) =
      8 * x i * x j * P.associated (axis i) (axis j) := by
  have hf : flip j x i = x i := by
    simp [flip,axis,hij]
  rw [show flip i (flip j x) = flip j x - (2*x i) • axis i by rw [flip,hf]]
  simp only [← associated_eq_self_apply K P,flip,
    map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [associated_isSymm K P (axis j) (axis i)]
  ring

def point₀ : V := ![3,5*imag,4,0,0]
def point₁ : V := ![3,imag,-1,3*imag,0]
def point₂ : V := ![29,101*imag,80,52,16]

lemma points_on_cone :
    (label₁ point₀ = 0 ∧ label₂ point₀ = 0) ∧
    (label₁ point₁ = 0 ∧ label₂ point₁ = 0) ∧
    (label₁ point₂ = 0 ∧ label₂ point₂ = 0) := by
  norm_num [label₁,label₂,point₀,point₁,point₂,weights,
    Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,mul_pow,imag_sq]

lemma point₂_nonzero (i : Fin 5) : point₂ i ≠ 0 := by
  fin_cases i <;> norm_num [point₂,imag_ne_zero]

private lemma off_diagonal_zero (P : QuadraticForm K V)
    (h : ∀ x, label₁ x = 0 → label₂ x = 0 → P x = 0)
    (i j : Fin 5) (hij : i ≠ j) : P.associated (axis i) (axis j) = 0 := by
  have hv := points_on_cone.2.2
  have hi := flip_labels i point₂
  have hj := flip_labels j point₂
  have hij' := flip_labels i (flip j point₂)
  have hm := mixed_difference P point₂ i j hij
  rw [h _ hv.1 hv.2,h _ (hi.1.trans hv.1) (hi.2.trans hv.2),
    h _ (hj.1.trans hv.1) (hj.2.trans hv.2),
    h _ (hij'.1.trans (hj.1.trans hv.1)) (hij'.2.trans (hj.2.trans hv.2))] at hm
  have hprod : (8 * point₂ i * point₂ j) * P.associated (axis i) (axis j) = 0 := by
    simpa using hm.symm
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (point₂_nonzero i)) (point₂_nonzero j))

private lemma diagonal_expansion (P : QuadraticForm K V)
    (h : ∀ x, label₁ x = 0 → label₂ x = 0 → P x = 0) (x : V) :
    P x = ∑ i, P (axis i) * x i ^ 2 := by
  rw [form_expansion]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · rw [associated_eq_self_apply]
    ring
  · intro j _ hji
    rw [off_diagonal_zero P h i j hji.symm]
    ring
  · simp

/-- Every quadratic form vanishing on the common Gaussian cone belongs to
this pencil. All mixed-parity homogeneous quadratic forms are allowed. -/
theorem cone_quadratic_span (P : QuadraticForm K V)
    (h : ∀ x, label₁ x = 0 → label₂ x = 0 → P x = 0) :
    ∃ α β : K, ∀ x, P x = α * label₁ x + β * label₂ x := by
  let a : Fin 5 → K := fun i ↦ P (axis i)
  have h₀ := h point₀ points_on_cone.1.1 points_on_cone.1.2
  have h₁ := h point₁ points_on_cone.2.1.1 points_on_cone.2.1.2
  have h₂ := h point₂ points_on_cone.2.2.1 points_on_cone.2.2.2
  rw [diagonal_expansion P h] at h₀ h₁ h₂
  change (∑ i, a i * point₀ i ^ 2) = 0 at h₀
  change (∑ i, a i * point₁ i ^ 2) = 0 at h₁
  change (∑ i, a i * point₂ i ^ 2) = 0 at h₂
  norm_num [point₀,point₁,point₂,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,mul_pow,imag_sq] at h₀ h₁ h₂
  change a 0 * 9 + (-(a 1 * 25) + a 2 * 16) = 0 at h₀
  change a 0 * 9 + (-a 1 + (a 2 + -(a 3 * 9))) = 0 at h₁
  change a 0 * 841 + (-(a 1 * 10201) + (a 2 * 6400 + (a 3 * 2704 + a 4 * 256))) = 0 at h₂
  refine ⟨(17*a 0-a 1)/16,(a 1-a 0)/16,?_⟩
  intro x
  rw [diagonal_expansion P h]
  change (∑ i, a i * x i ^ 2) = _
  have ha : ∀ i, a i = (17*a 0-a 1)/16 + (a 1-a 0)/16 * weights i := by
    intro i
    fin_cases i <;> norm_num [weights]
    · ring
    · ring
    · change a 2 = _
      linear_combination h₀ / 16
    · change a 3 = _
      linear_combination h₁ / (-9) + h₀ / 144
    · change a 4 = _
      linear_combination h₂ / 256 + h₁ * (169/144 : K) - h₀ * (3769/2304 : K)
  simp only [label₁,label₂,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [ha i]
  ring

/-- No nonzero linear form vanishes on the whole common cone. -/
theorem cone_linear_zero (L : V →ₗ[K] K)
    (h : ∀ x, label₁ x = 0 → label₂ x = 0 → L x = 0) : ∀ x, L x = 0 := by
  have hv := points_on_cone.2.2
  have ha (i : Fin 5) : L (axis i) = 0 := by
    have hf := flip_labels i point₂
    have he := h (flip i point₂) (hf.1.trans hv.1) (hf.2.trans hv.2)
    simp only [flip,map_sub,map_smul,h _ hv.1 hv.2,smul_eq_mul,zero_sub,neg_eq_zero]
      at he
    exact (mul_eq_zero.mp he).resolve_left
      (mul_ne_zero (by norm_num) (point₂_nonzero i))
  intro x
  have hx : (∑ i, x i • axis i) = x := by
    funext j
    simp [axis,Pi.single_apply]
  rw [←hx,map_sum]
  simp [ha]

/-- A quartic norm identity whose target vanishes at the origin forces each
homogeneous quadratic output to lie in the pencil. The identity here is on
Gaussian inputs, not just rational inputs. -/
theorem quartic_identity_outputs_in_pencil (P : Fin 4 → QuadraticForm K V)
    (H : K → K → K) (hH : H 0 0 = 0)
    (h : ∀ x, ∑ i, P i x ^ 4 = H (label₁ x) (label₂ x)) :
    ∀ i, ∃ α β : K, ∀ x, P i x = α * label₁ x + β * label₂ x := by
  intro i
  apply cone_quadratic_span
  intro x hx hy
  apply GaussianQuartic.gaussian_rational_fourth_sum_zero (fun i ↦ P i x) _ i
  rw [h,hx,hy,hH]

theorem quartic_identity_constant_on_joint_fibers (P : Fin 4 → QuadraticForm K V)
    (H : K → K → K) (hH : H 0 0 = 0)
    (h : ∀ x, ∑ i, P i x ^ 4 = H (label₁ x) (label₂ x))
    (x y : V) (hx : label₁ x = label₁ y) (hy : label₂ x = label₂ y) :
    ∀ i, P i x = P i y := by
  intro i
  obtain ⟨α,β,hp⟩ := quartic_identity_outputs_in_pencil P H hH h i
  rw [hp,hp,hx,hy]

end
end Erdos322Research.JointQuadraticGaussianInterpolation
