import Submission.GaussianQuarticObstruction

/-! Polynomial rotation rigidity for maps to four-coordinate quartic spheres.
These are construction obstructions, not bounds on the representation count. -/
namespace Erdos322Research.SpherePolynomialRigidity

noncomputable section
open Polynomial
open Erdos322Research.GaussianQuartic

abbrev CircleAlgebra := Localization.Away circlePolynomialRat

private abbrev polyMap : Polynomial ℚ →+* CircleAlgebra :=
  algebraMap (Polynomial ℚ) CircleAlgebra

private abbrev ratMap : ℚ →+* CircleAlgebra := polyMap.comp Polynomial.C

private lemma circle_ne_zero : circlePolynomialRat ≠ 0 := by
  apply Polynomial.Monic.ne_zero
  simpa [circlePolynomialRat] using
    (Polynomial.monic_X_pow_add_C (1 : ℚ) (by decide : 2 ≠ 0))

private lemma polyMap_injective : Function.Injective polyMap := by
  intro p q h
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq circlePolynomialRat h
  exact mul_left_cancel₀ (pow_ne_zero m circle_ne_zero) hm

/-- Every four-coordinate quartic sphere over the Gaussian circle algebra
has only constant points. -/
theorem circle_algebra_rigidity (f : Fin 4 → CircleAlgebra) (a : ℚ)
    (h : ∑ i, f i ^ 4 = ratMap a) :
    ∃ b : Fin 4 → ℚ, ∀ i, f i = ratMap (b i) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers circlePolynomialRat) f
  choose P hP using hd
  obtain ⟨m, hm⟩ := d.property
  have hd' : (d : Polynomial ℚ) = circlePolynomialRat ^ m := hm.symm
  have hPm (i : Fin 4) : polyMap (P i) = polyMap (circlePolynomialRat ^ m) * f i := by
    simpa only [Algebra.smul_def, hd'] using hP i
  have hp : ∑ i, P i ^ 4 = C a * circlePolynomialRat ^ (4*m) := by
    apply polyMap_injective
    simp only [map_sum, map_pow, map_mul, hPm, mul_pow]
    rw [← Finset.mul_sum, h]
    change (polyMap circlePolynomialRat ^ m) ^ 4 * ratMap a =
      ratMap a * polyMap circlePolynomialRat ^ (4*m)
    rw [← pow_mul, mul_comm m 4, mul_comm]
  obtain ⟨b, hb⟩ := circle_denominator_rigidity_rat P a m hp
  refine ⟨b, fun i ↦ ?_⟩
  have hi := hPm i
  rw [hb i, map_mul] at hi
  have hu : IsUnit (polyMap (circlePolynomialRat ^ m)) := by
    simpa only [map_pow] using
      (IsLocalization.Away.algebraMap_pow_isUnit circlePolynomialRat (S := CircleAlgebra) m)
  apply hu.mul_left_cancel
  change polyMap (circlePolynomialRat ^ m) * f i =
    polyMap (circlePolynomialRat ^ m) * polyMap (C (b i))
  simpa only [mul_comm] using hi.symm

private def atParameter (t : ℚ) : CircleAlgebra →+* ℚ :=
  IsLocalization.Away.lift circlePolynomialRat
    (g := Polynomial.evalRingHom t) (isUnit_iff_ne_zero.mpr (by
      change circlePolynomialRat.eval t ≠ 0
      simp only [circlePolynomialRat, eval_add, eval_pow, eval_X, eval_one]
      positivity))

@[simp] private lemma atParameter_poly (t : ℚ) (P : Polynomial ℚ) :
    atParameter t (polyMap P) = P.eval t := by
  exact IsLocalization.Away.lift_eq _ _ _

@[simp] private lemma atParameter_rat (t a : ℚ) : atParameter t (ratMap a) = a := by
  change atParameter t (polyMap (C a)) = a
  simp

/-- Any two rational evaluations of a constant-quartic-norm point in this
circle algebra agree coordinatewise. -/
theorem circle_algebra_evaluation_constant (f : Fin 4 → CircleAlgebra) (a : ℚ)
    (h : ∑ i, f i ^ 4 = ratMap a) (i : Fin 4) (s t : ℚ) :
    atParameter s (f i) = atParameter t (f i) := by
  obtain ⟨b, hb⟩ := circle_algebra_rigidity f a h
  rw [hb i]
  simp

private def circleInv : CircleAlgebra :=
  IsLocalization.Away.invSelf circlePolynomialRat

private def circleCos : CircleAlgebra := polyMap (1-X^2) * circleInv
private def circleSin : CircleAlgebra := polyMap (2*X) * circleInv

private lemma circle_unit : circleCos^2 + circleSin^2 = 1 := by
  calc
    _ = (polyMap circlePolynomialRat * circleInv)^2 := by
      simp only [circleCos, circleSin, circlePolynomialRat, map_sub, map_add,
        map_one, map_pow, map_mul, map_ofNat]
      ring
    _ = 1 := by
      change (algebraMap (Polynomial ℚ) CircleAlgebra circlePolynomialRat *
        IsLocalization.Away.invSelf circlePolynomialRat)^2=1
      rw [IsLocalization.Away.mul_invSelf]; simp

private lemma atParameter_inv (t : ℚ) :
    atParameter t circleInv = 1/(t^2+1) := by
  have ht : t^2+1 ≠ 0 := by positivity
  apply (eq_div_iff ht).mpr
  have he := congrArg (atParameter t)
    (IsLocalization.Away.mul_invSelf circlePolynomialRat (S := CircleAlgebra))
  simpa [circleInv, circlePolynomialRat, mul_comm] using he

@[simp] private lemma atParameter_cos (t : ℚ) :
    atParameter t circleCos = (1-t^2)/(1+t^2) := by
  simp [circleCos, atParameter_inv, div_eq_mul_inv, add_comm]

@[simp] private lemma atParameter_sin (t : ℚ) :
    atParameter t circleSin = 2*t/(1+t^2) := by
  simp [circleSin, atParameter_inv, div_eq_mul_inv, add_comm]

/-- Rotate two coordinates and leave all others fixed. -/
def planeRotate {σ R : Type*} [DecidableEq σ] [CommRing R]
    (x : σ → R) (i j : σ) (c s : R) : σ → R := fun l ↦
  if l=i then c*x i-s*x j else if l=j then s*x i+c*x j else x l

private lemma planeRotate_sum_sq {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (x : σ → R) (i j : σ) (hij : i ≠ j) (c s : R)
    (hcs : c^2+s^2=1) :
    ∑ l, (planeRotate x i j c s l)^2 = ∑ l, (x l)^2 := by
  have he (l : σ) : (planeRotate x i j c s l)^2 =
      (x l)^2 + (if l=i then (c*x i-s*x j)^2-(x i)^2 else 0) +
        (if l=j then (s*x i+c*x j)^2-(x j)^2 else 0) := by
    by_cases hi : l=i
    · subst l; simp [planeRotate, hij]
    · by_cases hj : l=j
      · subst l; simp [planeRotate, hij.symm]
      · simp [planeRotate, hi, hj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination ((x i)^2+(x j)^2)*hcs

@[simp] private lemma parameter_rotate {σ : Type*} [DecidableEq σ]
    (x : σ → ℚ) (i j l : σ) (t : ℚ) :
    atParameter t (planeRotate (fun l ↦ ratMap (x l)) i j circleCos circleSin l) =
      planeRotate x i j ((1-t^2)/(1+t^2)) (2*t/(1+t^2)) l := by
  by_cases hi : l=i
  · simp [planeRotate, hi]
  · by_cases hj : l=j
    · subst l; simp [planeRotate, hi]
    · simp [planeRotate, hi, hj]

private lemma parameter_mv_eval {σ : Type*} (P : MvPolynomial σ ℚ)
    (x : σ → CircleAlgebra) (t : ℚ) :
    atParameter t (MvPolynomial.eval₂Hom ratMap x P) =
      MvPolynomial.eval (fun l ↦ atParameter t (x l)) P := by
  rw [MvPolynomial.map_eval₂Hom]
  have he : (atParameter t).comp ratMap = RingHom.id ℚ := by
    ext a
    simp
  rw [he]
  rfl

/-- A rational polynomial map whose quartic norm is a function of the
ordinary squared norm is invariant under every rational plane rotation. -/
theorem polynomial_map_rotation_invariant {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Fin 4 → MvPolynomial σ ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x : σ → ℚ) (i j : σ) (hij : i ≠ j) (t : ℚ) (l : Fin 4) :
    MvPolynomial.eval (planeRotate x i j ((1-t^2)/(1+t^2)) (2*t/(1+t^2))) (P l) =
      MvPolynomial.eval x (P l) := by
  let y := planeRotate (fun j ↦ ratMap (x j)) i j circleCos circleSin
  let f : Fin 4 → CircleAlgebra := fun l ↦ MvPolynomial.eval₂Hom ratMap y (P l)
  have hy : ∑ j, y j ^ 2 = ratMap (∑ j, x j ^ 2) := by
    rw [planeRotate_sum_sq _ i j hij circleCos circleSin circle_unit]
    simp only [map_sum, map_pow]
  have hf : ∑ l, f l ^ 4 = ratMap (H.eval (∑ j, x j ^ 2)) := by
    have he := congrArg (MvPolynomial.eval₂Hom ratMap y) h
    rw [Polynomial.hom_eval₂] at he
    have hm : (MvPolynomial.eval₂Hom ratMap y).comp MvPolynomial.C = ratMap := by
      ext a
      simp
    simp only [map_sum, map_pow, MvPolynomial.eval₂Hom_X', hm] at he
    rw [hy, Polynomial.eval₂_at_apply] at he
    exact he
  have hc := circle_algebra_evaluation_constant f _ hf l t 0
  dsimp only [f] at hc
  simp only [parameter_mv_eval] at hc
  dsimp only [y] at hc
  simp only [parameter_rotate] at hc
  have hz : planeRotate x i j ((1-(0:ℚ)^2)/(1+0^2)) (2*0/(1+0^2)) = x := by
    funext k
    by_cases hi : k=i
    · simp [planeRotate, hi]
    · by_cases hj : k=j
      · subst k; simp [planeRotate, hij.symm]
      · simp [planeRotate, hi, hj]
  simpa only [hz] using hc

/-- Evaluate a rational multivariate polynomial at real coordinates. -/
def realEval {σ : Type*} (P : MvPolynomial σ ℚ) (x : σ → ℝ) : ℝ :=
  MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P)

private lemma realEval_cast {σ : Type*} (P : MvPolynomial σ ℚ) (x : σ → ℚ) :
    realEval P (fun j ↦ (x j : ℝ)) = (MvPolynomial.eval x P : ℝ) := by
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℚ) x (Rat.castHom ℝ) P
  rw [realEval, ← MvPolynomial.eval₂_eq_eval_map]
  simpa only [RingHom.comp_id, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_id] using he.symm

private lemma rotate_cast {σ : Type*} [DecidableEq σ] (x : σ → ℚ)
    (i j : σ) (c s : ℚ) :
    planeRotate (fun k ↦ (x k : ℝ)) i j (c : ℝ) (s : ℝ) =
      fun k ↦ ((planeRotate (R := ℚ) x i j c s k : ℚ) : ℝ) := by
  funext k
  by_cases hi : k=i
  · simp [planeRotate, hi]
  · by_cases hj : k=j
    · subst k; simp [planeRotate, hi]
    · simp [planeRotate, hi, hj]

private theorem real_parameter_rotation_invariant {σ : Type*}
    [Fintype σ] [DecidableEq σ]
    (P : Fin 4 → MvPolynomial σ ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x : σ → ℝ) (i j : σ) (hij : i ≠ j) (t : ℝ) (l : Fin 4) :
    realEval (P l) (planeRotate x i j ((1-t^2)/(1+t^2)) (2*t/(1+t^2))) =
      realEval (P l) x := by
  let F : ((σ → ℝ) × ℝ) → ℝ := fun z ↦ realEval (P l)
    (planeRotate z.1 i j ((1-z.2^2)/(1+z.2^2)) (2*z.2/(1+z.2^2)))
  let G : ((σ → ℝ) × ℝ) → ℝ := fun z ↦ realEval (P l) z.1
  have hF : Continuous F := by
    apply (MvPolynomial.continuous_eval (MvPolynomial.map (Rat.castHom ℝ) (P l))).comp
    apply continuous_pi
    intro k
    by_cases hi : k=i
    · simp only [planeRotate, hi, if_true]
      fun_prop (disch := intro z; positivity)
    · by_cases hj : k=j
      · subst k
        simp only [planeRotate, hi, if_false, if_true]
        fun_prop (disch := intro z; positivity)
      · simp only [planeRotate, hi, hj, if_false]
        fun_prop
  have hG : Continuous G :=
    (MvPolynomial.continuous_eval (MvPolynomial.map (Rat.castHom ℝ) (P l))).comp continuous_fst
  have hd : DenseRange (fun z : (σ → ℚ) × ℚ ↦
      ((fun k ↦ (z.1 k : ℝ)), (z.2 : ℝ))) :=
    (DenseRange.piMap (fun _ : σ ↦ (Rat.denseRange_cast : DenseRange (Rat.cast : ℚ → ℝ)))).prodMap
      Rat.denseRange_cast
  have he : F=G := hd.equalizer hF hG (by
    funext z
    rcases z with ⟨a,b⟩
    dsimp only [Function.comp_def, F, G]
    have hr := congrArg (Rat.cast : ℚ → ℝ)
      (polynomial_map_rotation_invariant P H h a i j hij b l)
    have hc : (1-(b:ℝ)^2)/(1+(b:ℝ)^2) = (((1-b^2)/(1+b^2) : ℚ) : ℝ) := by norm_cast
    have hs : 2*(b:ℝ)/(1+(b:ℝ)^2) = ((2*b/(1+b^2) : ℚ) : ℝ) := by norm_cast
    rw [hc, hs, rotate_cast, realEval_cast, realEval_cast]
    exact hr)
  exact congrFun he (x,t)

private lemma double_quarter_turn {σ R : Type*} [DecidableEq σ] [CommRing R]
    (x : σ → R) (i j : σ) (hij : i ≠ j) :
    planeRotate (planeRotate x i j 0 1) i j 0 1 = planeRotate x i j (-1) 0 := by
  funext k
  by_cases hi : k=i
  · subst k; simp [planeRotate, hij.symm]
  · by_cases hj : k=j
    · subst k; simp [planeRotate, hij.symm]
    · simp [planeRotate, hi, hj]

/-- Rotation invariance holds on all real points, although the polynomial
coefficients in the hypothesis must be rational. -/
theorem real_rotation_invariant {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Fin 4 → MvPolynomial σ ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x : σ → ℝ) (i j : σ) (hij : i ≠ j) (c s : ℝ) (hcs : c^2+s^2=1)
    (l : Fin 4) : realEval (P l) (planeRotate x i j c s) = realEval (P l) x := by
  by_cases hc : c = -1
  · have hs : s=0 := by rw [hc] at hcs; nlinarith [sq_nonneg s]
    subst c; subst s
    have h1 := real_parameter_rotation_invariant P H h x i j hij 1 l
    have h2 := real_parameter_rotation_invariant P H h (planeRotate x i j 0 1) i j hij 1 l
    norm_num at h1 h2
    rw [double_quarter_turn x i j hij] at h2
    exact h2.trans h1
  · let t := s/(1+c)
    have hd : 1+c ≠ 0 := by intro he; apply hc; linarith
    have hdt : 1+t^2 ≠ 0 := by positivity
    have htC : (1-t^2)/(1+t^2)=c := by
      apply (div_eq_iff hdt).mpr
      dsimp [t]
      field_simp
      nlinarith [sq_nonneg c, sq_nonneg s]
    have htS : 2*t/(1+t^2)=s := by
      apply (div_eq_iff hdt).mpr
      dsimp [t]
      field_simp
      linear_combination -s*hcs
    simpa only [htC, htS] using real_parameter_rotation_invariant P H h x i j hij t l

private lemma unit_rotation_to_axis (a b : ℝ) :
    ∃ c s : ℝ, c^2+s^2=1 ∧ c*a-s*b=Real.sqrt (a^2+b^2) ∧ s*a+c*b=0 := by
  let r := Real.sqrt (a^2+b^2)
  have hrs : r^2=a^2+b^2 := Real.sq_sqrt (by positivity)
  by_cases hr : r=0
  · have ha : a=0 := by nlinarith [sq_nonneg b]
    have hb : b=0 := by nlinarith [sq_nonneg a]
    exact ⟨1,0,by norm_num,by simp [ha,hb],by simp [hb]⟩
  · refine ⟨a/r,-b/r,?_,?_,?_⟩
    · field_simp
      exact hrs.symm
    · change a/r*a-(-b/r)*b=r
      field_simp
      nlinarith [hrs]
    · ring

private theorem coordinate_elimination {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Fin 4 → MvPolynomial σ ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x : σ → ℝ) (i j : σ) (hij : i ≠ j) (l : Fin 4) :
    realEval (P l) (Function.update
      (Function.update x i (Real.sqrt ((x i)^2+(x j)^2))) j 0) = realEval (P l) x := by
  obtain ⟨c,s,hcs,ha,hb⟩ := unit_rotation_to_axis (x i) (x j)
  have he : planeRotate x i j c s = Function.update
      (Function.update x i (Real.sqrt ((x i)^2+(x j)^2))) j 0 := by
    funext k
    by_cases hi : k=i
    · subst k; simpa [planeRotate, hij] using ha
    · by_cases hj : k=j
      · subst k; simpa [planeRotate, hij.symm] using hb
      · simp [planeRotate, hi, hj]
  rw [←he]
  exact real_rotation_invariant P H h x i j hij c s hcs l

private theorem axis_reduction
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x : Fin 4 → ℝ) (l : Fin 4) :
    realEval (P l) ![Real.sqrt (∑ j, (x j)^2),0,0,0] = realEval (P l) x := by
  let r₁ := Real.sqrt ((x 0)^2+(x 1)^2)
  let r₂ := Real.sqrt (r₁^2+(x 2)^2)
  let r₃ := Real.sqrt (r₂^2+(x 3)^2)
  let y₁ : Fin 4 → ℝ := ![r₁,0,x 2,x 3]
  let y₂ : Fin 4 → ℝ := ![r₂,0,0,x 3]
  let y₃ : Fin 4 → ℝ := ![r₃,0,0,0]
  have he₁ : Function.update (Function.update x 0 (Real.sqrt ((x 0)^2+(x 1)^2))) 1 0 = y₁ := by
    funext k; fin_cases k <;> simp [y₁,r₁]
  have he₂ : Function.update (Function.update y₁ 0 (Real.sqrt ((y₁ 0)^2+(y₁ 2)^2))) 2 0 = y₂ := by
    funext k; fin_cases k <;> simp [y₁,y₂,r₂]
  have he₃ : Function.update (Function.update y₂ 0 (Real.sqrt ((y₂ 0)^2+(y₂ 3)^2))) 3 0 = y₃ := by
    funext k; fin_cases k <;> simp [y₂,y₃,r₃]
  have h₁ := coordinate_elimination P H h x 0 1 (by decide) l
  have h₂ := coordinate_elimination P H h y₁ 0 2 (by decide) l
  have h₃ := coordinate_elimination P H h y₂ 0 3 (by decide) l
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃] at h₃
  have hr₁ : r₁^2=(x 0)^2+(x 1)^2 := Real.sq_sqrt (by positivity)
  have hr₂ : r₂^2=r₁^2+(x 2)^2 := Real.sq_sqrt (by positivity)
  have hr₃ : r₃=Real.sqrt (∑ j, (x j)^2) := by
    dsimp only [r₃]
    rw [hr₂,hr₁,Fin.sum_univ_four]
  simpa only [y₃,hr₃] using h₃.trans (h₂.trans h₁)

/-- A rational polynomial map from ordinary four-dimensional spheres to
four-coordinate quartic spheres is constant on each sphere. In particular,
ordinary-sphere multiplicity cannot be transferred by such a polynomial map. -/
theorem constant_on_real_spheres
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x y : Fin 4 → ℝ) (hxy : ∑ j, (x j)^2 = ∑ j, (y j)^2) (l : Fin 4) :
    realEval (P l) x = realEval (P l) y := by
  rw [←axis_reduction P H h x l, ←axis_reduction P H h y l, hxy]

/-- Rational-point version of the same rigidity theorem. -/
theorem constant_on_rational_spheres
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i ^ 4 = H.eval₂ MvPolynomial.C (∑ j, MvPolynomial.X j ^ 2))
    (x y : Fin 4 → ℚ) (hxy : ∑ j, (x j)^2 = ∑ j, (y j)^2) (l : Fin 4) :
    MvPolynomial.eval x (P l) = MvPolynomial.eval y (P l) := by
  have he := constant_on_real_spheres P H h (fun j ↦ (x j : ℝ))
    (fun j ↦ (y j : ℝ)) (by simp only; exact_mod_cast hxy) l
  rw [realEval_cast,realEval_cast] at he
  exact_mod_cast he

end
end Erdos322Research.SpherePolynomialRigidity
