import Submission.UnitCubeNormalForm
import Submission.BiquadraticSquares

/-! Function-field square-class obstructions for the unit-cube body cover.
These do not classify rational specializations or arbitrary point sets. -/
namespace Erdos213.UnitCubeBodyCover
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

local notation "cj" => starRingEnd ℂ

def branch (a : ℂ) : ℂ[X] :=
  C (a+1)*(1-X^2)+C (2*Complex.I*(1-a))*X

private lemma I_sq : (C Complex.I : ℂ[X])^2= -1 := by
  rw [←map_pow,Complex.I_sq]
  simp

lemma branch_bezout (a b : ℂ) :
    (-C (b+1)*X+C (2*Complex.I*(1-b)))*branch a+
    (C (a+1)*X+C (2*Complex.I*(a-1)))*branch b =
      C (4*Complex.I*(a-b)) := by
  simp only [branch,map_add,map_sub,map_mul,map_ofNat,map_one]
  ring

lemma branch_coprime {a b : ℂ} (h : a ≠ b) : IsCoprime (branch a) (branch b) := by
  have hc : 4*Complex.I*(a-b) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (sub_ne_zero.mpr h)
  refine ⟨C ((4*Complex.I*(a-b))⁻¹)*(-C (b+1)*X+C (2*Complex.I*(1-b))),
    C ((4*Complex.I*(a-b))⁻¹)*(C (a+1)*X+C (2*Complex.I*(a-1))),?_⟩
  calc
    _=C ((4*Complex.I*(a-b))⁻¹)*
      ((-C (b+1)*X+C (2*Complex.I*(1-b)))*branch a+
      (C (a+1)*X+C (2*Complex.I*(a-1)))*branch b) := by ring
    _=1 := by rw [branch_bezout,←map_mul,inv_mul_cancel₀ hc,map_one]

lemma branch_derivative_bezout (a : ℂ) :
    (-4*C (a+1))*branch a+
    (2*C (a+1)*X-C (2*Complex.I*(1-a)))*(branch a).derivative = C (-16*a) := by
  simp only [branch]
  simp only [derivative_add,derivative_C_mul,derivative_sub,derivative_one,
    derivative_X_pow,derivative_X]
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one,map_neg,zero_sub]
  norm_num only [Nat.cast_ofNat]
  simp only [map_ofNat]
  ring_nf
  rw [I_sq]
  ring

lemma branch_squarefree {a : ℂ} (ha : a ≠ 0) : Squarefree (branch a) := by
  have hc : -16*a ≠ 0 := mul_ne_zero (by norm_num) ha
  apply Polynomial.Separable.squarefree
  rw [separable_def']
  refine ⟨C ((-16*a)⁻¹)*(-4*C (a+1)),
    C ((-16*a)⁻¹)*(2*C (a+1)*X-C (2*Complex.I*(1-a))),?_⟩
  calc
    _=C ((-16*a)⁻¹)*((-4*C (a+1))*branch a+
      (2*C (a+1)*X-C (2*Complex.I*(1-a)))*(branch a).derivative) := by ring
    _=1 := by rw [branch_derivative_bezout,←map_mul,inv_mul_cancel₀ hc,map_one]

lemma branch_degree {a : ℂ} (ha : a ≠ -1) : (branch a).natDegree=2 := by
  have hc : a+1 ≠ 0 := by intro h; apply ha; linear_combination h
  have h : branch a=C (-(a+1))*X^2+C (2*Complex.I*(1-a))*X+C (a+1) := by
    simp [branch]
    ring
  rw [h]
  compute_degree!
  intro hz
  apply hc
  norm_num at hz
  linear_combination -hz

/-- The product is the squared norm of the complex quadratic along the real
parameter line. Its two branch parameters are a and 1/conj(a). -/
def normBranch (a : ℂ) : ℂ[X] := branch a*(branch a).map cj

lemma conjugate_branch (a : ℂ) (ha : a ≠ 0) :
    (branch a).map cj=C (cj a)*branch ((cj a)⁻¹) := by
  have hac : cj a ≠ 0 := by simpa using ha
  simp only [branch]
  simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,Polynomial.map_one]
  simp only [map_add,map_sub,map_mul,map_one,map_ofNat,Complex.conj_I]
  have hi : C (cj a)*C ((cj a)⁻¹)=(1 : ℂ[X]) := by
    rw [←map_mul,mul_inv_cancel₀ hac,map_one]
  simp only [map_neg]
  linear_combination -(1-X^2-2*C Complex.I*X)*hi

lemma normBranch_factor (a : ℂ) (ha : a ≠ 0) :
    normBranch a=C (cj a)*(branch a*branch ((cj a)⁻¹)) := by
  rw [normBranch,conjugate_branch a ha]
  ring

private lemma conj_nonzero {a : ℂ} (ha : a ≠ 0) : cj a ≠ 0 := by simpa using ha

lemma normBranch_squarefree {a : ℂ} (ha : a ≠ 0) (hn : a*cj a ≠ 1) :
    Squarefree (normBranch a) := by
  have hca := conj_nonzero ha
  have hi : a ≠ (cj a)⁻¹ := by
    intro h
    apply hn
    calc
      a*cj a=(cj a)⁻¹*cj a := congrArg (fun z => z*cj a) h
      _=1 := inv_mul_cancel₀ hca
  have hu : IsUnit (C (cj a)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hca)
  rw [normBranch_factor a ha,squarefree_mul_iff]
  refine ⟨hu.isRelPrime_left,hu.squarefree,?_⟩
  exact squarefree_mul_iff.mpr ⟨(branch_coprime hi).isRelPrime,
    branch_squarefree ha,branch_squarefree (inv_ne_zero hca)⟩

lemma normBranch_coprime {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hinv : a*cj b ≠ 1) :
    IsCoprime (normBranch a) (normBranch b) := by
  have hca := conj_nonzero ha
  have hcb := conj_nonzero hb
  have hi : a ≠ (cj b)⁻¹ := by
    intro h
    apply hinv
    rw [h,inv_mul_cancel₀ hcb]
  have hj : (cj a)⁻¹ ≠ b := by
    intro h
    apply hinv
    rw [←h]
    simp [ha]
  have hk : (cj a)⁻¹ ≠ (cj b)⁻¹ := by
    intro h
    have hh := congrArg (fun z : ℂ => cj (z⁻¹)) h
    exact hab (by simpa using hh)
  have hua : IsUnit (C (cj a)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hca)
  have hub : IsUnit (C (cj b)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcb)
  rw [normBranch_factor a ha,normBranch_factor b hb,
    isCoprime_mul_units_left hua hub]
  exact ((branch_coprime hab).mul_right (branch_coprime hi)).mul_left
    ((branch_coprime hj).mul_right (branch_coprime hk))

lemma normBranch_degree {a : ℂ} (ha : a ≠ 0) (h1 : a ≠ -1) :
    (normBranch a).natDegree=4 := by
  have h0 := (branch_squarefree ha).ne_zero
  have hm : (branch a).map cj ≠ 0 := by simpa using h0
  rw [normBranch,natDegree_mul h0 hm,natDegree_map,branch_degree h1]

lemma branch_eval_identity (a : ℂ) (s : ℚ) :
    (branch a).eval (s : ℂ) =
      (1-(s : ℂ)*Complex.I)^2*(a+UnitCubeNormalForm.point s) := by
  have hd : 1+(s : ℂ)^2 ≠ 0 := by
    have h : (1 : ℚ)+s^2 ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast h
  simp only [branch,eval_add,eval_mul,eval_C,eval_sub,eval_one,eval_pow,eval_X,
    UnitCubeNormalForm.point,UnitCubeNormalForm.vx,UnitCubeNormalForm.vy]
  push_cast
  field_simp
  ring_nf
  norm_num [Complex.I_sq]
  ring

lemma normBranch_eval (a : ℂ) (s : ℚ) :
    (normBranch a).eval (s : ℂ) =
      (((1+s^2)^2 : ℚ) : ℂ)*((‖a+UnitCubeNormalForm.point s‖^2 : ℝ) : ℂ) := by
  have hc : cj (s : ℂ)=(s : ℂ) := by simp
  have he : ((branch a).map cj).eval (s : ℂ)=cj ((branch a).eval (s : ℂ)) := by
    conv_lhs => rw [←hc]
    exact eval_map_apply cj _
  rw [normBranch,eval_mul,he,Complex.mul_conj,←Complex.sq_norm,branch_eval_identity,
    norm_mul,mul_pow,norm_pow]
  have hn : ‖1-(s : ℂ)*Complex.I‖^2=1+(s : ℝ)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  rw [hn]
  push_cast
  ring

def parameter (x y : ℚ) : Fin 4 → ℂ :=
  ![1+((x : ℂ)+(y : ℂ)*Complex.I), -(1+((x : ℂ)+(y : ℂ)*Complex.I)),
    1-((x : ℂ)+(y : ℂ)*Complex.I), -(1-((x : ℂ)+(y : ℂ)*Complex.I))]

def bodyPolynomial (x y : ℚ) (i : Fin 4) : ℂ[X] := normBranch (parameter x y i)

lemma parameter_nonzero {x y : ℚ} (hy : y ≠ 0) (i : Fin 4) : parameter x y i ≠ 0 := by
  intro he
  have h := congrArg Complex.im he
  fin_cases i <;> simp [parameter] at h <;> exact hy h

lemma parameter_not_neg_one {x y : ℚ} (hy : y ≠ 0) (i : Fin 4) :
    parameter x y i ≠ -1 := by
  intro he
  have h := congrArg Complex.im he
  fin_cases i <;> simp [parameter] at h <;> exact hy h

lemma parameter_norm_not_one {x y : ℚ} (hu : x^2+y^2=1) (i : Fin 4) :
    parameter x y i*cj (parameter x y i) ≠ 1 := by
  intro he
  have hr := congrArg Complex.re he
  have hu' : (x : ℝ)^2+(y : ℝ)^2=1 := by exact_mod_cast hu
  have hs : (2*y)^2=(3 : ℚ) := by
    have hs' : (2*(y : ℝ))^2=3 := by
      fin_cases i <;> simp [parameter] at hr <;> nlinarith [hu']
    exact_mod_cast hs'
  have hbad : IsSquare (3 : ℚ) := ⟨2*y,by nlinarith [hs]⟩
  norm_num at hbad

lemma parameter_injective {x y : ℚ} (hy : y ≠ 0) : Function.Injective (parameter x y) := by
  intro i j he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  fin_cases i <;> fin_cases j <;> simp [parameter] at hre him ⊢
  all_goals exfalso
  all_goals exact hy' (by linarith)

lemma parameter_cross_not_one {x y : ℚ} (hu : x^2+y^2=1)
    (i j : Fin 4) (hij : i ≠ j) :
    parameter x y i*cj (parameter x y j) ≠ 1 := by
  intro he
  have hr := congrArg Complex.re he
  have hu' : (x : ℝ)^2+(y : ℝ)^2=1 := by exact_mod_cast hu
  fin_cases i <;> fin_cases j <;> simp [parameter] at hij hr
  all_goals nlinarith [hu',sq_nonneg (y : ℝ),sq_nonneg (1+(x : ℝ)),sq_nonneg (1-(x : ℝ))]

lemma bodies_squarefree {x y : ℚ} (hu : x^2+y^2=1) (hy : y ≠ 0) (i : Fin 4) :
    Squarefree (bodyPolynomial x y i) :=
  normBranch_squarefree (parameter_nonzero hy i) (parameter_norm_not_one hu i)

lemma bodies_coprime {x y : ℚ} (hu : x^2+y^2=1) (hy : y ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) :
    IsCoprime (bodyPolynomial x y i) (bodyPolynomial x y j) :=
  normBranch_coprime (parameter_nonzero hy i) (parameter_nonzero hy j)
    (fun h => hij (parameter_injective hy h)) (parameter_cross_not_one hu i j hij)

lemma bodies_degree {x y : ℚ} (hy : y ≠ 0) (i : Fin 4) :
    (bodyPolynomial x y i).natDegree=4 :=
  normBranch_degree (parameter_nonzero hy i) (parameter_not_neg_one hy i)

/-- Every nonempty product of distinct body polynomials is nonsquare.
This is independence of their function-field square classes, not of their
values at a rational specialization. -/
theorem nonempty_product_not_square {x y : ℚ} (hu : x^2+y^2=1) (hy : y ≠ 0)
    (S : Finset (Fin 4)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, bodyPolynomial x y i) := by
  classical
  have hsf : Squarefree (∏ i ∈ S, bodyPolynomial x y i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (bodies_coprime hu hy i j hij).isRelPrime
    · intro i hi
      exact bodies_squarefree hu hy i
  have hd : (∏ i ∈ S, bodyPolynomial x y i).natDegree=4*S.card := by
    rw [natDegree_prod S (bodyPolynomial x y) (fun i _ => (bodies_squarefree hu hy i).ne_zero)]
    simp [bodies_degree hy,mul_comm]
  rintro ⟨p,hp⟩
  have hup : IsUnit p := hsf p (by rw [hp])
  have huall : IsUnit (∏ i ∈ S, bodyPolynomial x y i) := hp ▸ hup.mul hup
  have hz := natDegree_eq_zero_of_isUnit huall
  have hc := Finset.card_pos.mpr hS
  omega

private lemma square_ratFunc_iff (p : ℂ[X]) :
    IsSquare (algebraMap ℂ[X] (RatFunc ℂ) p) ↔ IsSquare p := by
  constructor
  · rintro ⟨r,hr⟩
    have hint : IsIntegral ℂ[X] (r^2) := by
      rw [pow_two,←hr]
      exact isIntegral_algebraMap
    obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := ℂ[X]) (K := RatFunc ℂ) (by norm_num : 0 < (2 : ℕ)) hint
    refine ⟨q,?_⟩
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    simpa [map_mul,hq] using hr
  · rintro ⟨q,hq⟩
    exact ⟨algebraMap ℂ[X] (RatFunc ℂ) q,by simp [hq]⟩

theorem nonempty_product_not_square_ratFunc {x y : ℚ} (hu : x^2+y^2=1) (hy : y ≠ 0)
    (S : Finset (Fin 4)) (hS : S.Nonempty) :
    ¬ IsSquare (algebraMap ℂ[X] (RatFunc ℂ) (∏ i ∈ S, bodyPolynomial x y i)) := by
  rw [square_ratFunc_iff]
  exact nonempty_product_not_square hu hy S hS

abbrev QOne {K : Type*} [Field K] (F : Fin 4 → K) := QuadraticAlgebra K (F 0) 0
abbrev QTwo {K : Type*} [Field K] (F : Fin 4 → K) :=
  QuadraticAlgebra (QOne F) (algebraMap K (QOne F) (F 1)) 0

def liftTwo {K : Type*} [Field K] (F : Fin 4 → K) (d : K) : QTwo F :=
  algebraMap (QOne F) (QTwo F) (algebraMap K (QOne F) d)

abbrev QThree {K : Type*} [Field K] (F : Fin 4 → K) :=
  QuadraticAlgebra (QTwo F) (liftTwo F (F 2)) 0

def liftThree {K : Type*} [Field K] (F : Fin 4 → K) (d : K) : QThree F :=
  algebraMap (QTwo F) (QThree F) (liftTwo F d)

/-- Square-class independence excludes automatic completion even after the
first three square roots have been adjoined. -/
lemma independent_fourth_not_square {K : Type*} [Field K] [CharZero K]
    (F : Fin 4 → K)
    (h : ∀ S : Finset (Fin 4), S.Nonempty → ¬ IsSquare (∏ i ∈ S, F i)) :
    ¬ IsSquare (liftThree F (F 3)) := by
  have h0 : ¬ IsSquare (F 0) := by simpa using h {0} (by simp)
  have h1 : ¬ IsSquare (F 1) := by simpa using h {1} (by simp)
  have h2 : ¬ IsSquare (F 2) := by simpa using h {2} (by simp)
  have h01 : ¬ IsSquare (F 0*F 1) := by simpa using h {0,1} (by simp)
  have ha0 : F 0 ≠ 0 := by intro he; exact h0 (he ▸ IsSquare.zero)
  have hb0 : F 1 ≠ 0 := by intro he; exact h1 (he ▸ IsSquare.zero)
  have hc0 : F 2 ≠ 0 := by intro he; exact h2 (he ▸ IsSquare.zero)
  letI : Fact (∀ r : K, r^2 ≠ F 0+0*r) := ⟨by
    intro r hr
    apply h0
    exact ⟨r,by simpa [pow_two] using hr.symm⟩⟩
  have hb : ¬ IsSquare (algebraMap K (QOne F) (F 1)) := by
    rw [BiquadraticSquares.quadratic_square_iff _ _ ha0]
    exact not_or.mpr ⟨h1,h01⟩
  letI : Fact (∀ r : QOne F, r^2 ≠ algebraMap K (QOne F) (F 1)+0*r) := ⟨by
    intro r hr
    apply hb
    exact ⟨r,by simpa [pow_two] using hr.symm⟩⟩
  have hc : liftTwo F (F 2) ≠ 0 := by
    intro he
    have hh := congrArg QuadraticAlgebra.re (congrArg QuadraticAlgebra.re he)
    exact hc0 (by simpa [liftTwo] using hh)
  have h3 : ¬ IsSquare (F 3) := by simpa using h {3} (by simp)
  have h03 : ¬ IsSquare (F 0*F 3) := by simpa using h {0,3} (by simp)
  have h13 : ¬ IsSquare (F 1*F 3) := by simpa using h {1,3} (by simp)
  have h013 : ¬ IsSquare (F 0*(F 1*F 3)) := by simpa using h {0,1,3} (by simp)
  have h23 : ¬ IsSquare (F 2*F 3) := by simpa using h {2,3} (by simp)
  have h023 : ¬ IsSquare (F 0*(F 2*F 3)) := by simpa using h {0,2,3} (by simp)
  have h123 : ¬ IsSquare (F 1*(F 2*F 3)) := by simpa using h {1,2,3} (by simp)
  have h0123 : ¬ IsSquare (F 0*(F 1*(F 2*F 3))) := by
    simpa using h {0,1,2,3} (by simp)
  have hm : liftTwo F (F 2)*liftTwo F (F 3)=liftTwo F (F 2*F 3) := by
    simp only [liftTwo,map_mul]
  unfold liftThree
  rw [BiquadraticSquares.quadratic_square_iff _ _ hc,hm]
  simp only [liftTwo,BiquadraticSquares.biquadratic_square_iff (F 0) (F 1) _ h0 hb0]
  tauto

def bodyFunction (x y : ℚ) (i : Fin 4) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (bodyPolynomial x y i)

theorem no_automatic_fourth {x y : ℚ} (hu : x^2+y^2=1) (hy : y ≠ 0) :
    ¬ IsSquare (liftThree (bodyFunction x y) (bodyFunction x y 3)) := by
  apply independent_fourth_not_square
  intro S hS
  simpa only [bodyFunction,map_prod] using nonempty_product_not_square_ratFunc hu hy S hS

theorem no_automatic_fourth_parameter {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1) :
    ¬ IsSquare (liftThree
      (bodyFunction (UnitCubeNormalForm.vx t) (UnitCubeNormalForm.vy t))
      (bodyFunction (UnitCubeNormalForm.vx t) (UnitCubeNormalForm.vy t) 3)) := by
  have hpos : 0 < UnitCubeNormalForm.vy t := by
    have h : 0 < 1-t^2 := by nlinarith [sq_nonneg t]
    unfold UnitCubeNormalForm.vy
    positivity
  exact no_automatic_fourth (UnitCubeNormalForm.unit_identity t) (ne_of_gt hpos)

#print axioms branch_bezout
#print axioms branch_coprime
#print axioms branch_squarefree
#print axioms branch_degree
#print axioms normBranch_factor
#print axioms normBranch_eval
#print axioms normBranch_squarefree
#print axioms normBranch_coprime
#print axioms normBranch_degree
#print axioms bodies_squarefree
#print axioms bodies_coprime
#print axioms bodies_degree
#print axioms nonempty_product_not_square_ratFunc
#print axioms no_automatic_fourth
#print axioms no_automatic_fourth_parameter
end
end Erdos213.UnitCubeBodyCover
