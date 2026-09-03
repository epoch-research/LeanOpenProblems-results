import Submission.JointQuadraticFiberNorm
import Submission.JointQuadraticConeIdeal

/-! Arbitrary-degree polynomial quartic norms on the explicit joint
quadratic fibers. These theorems concern polynomial constructions only. -/
namespace Erdos322Research.JointQuadraticCone
noncomputable section
open MvPolynomial QuadraticSpecializationAnisotropy
set_option Elab.async false
set_option maxHeartbeats 0

private def fiberCoords (u v : K) : Fin 5 → FiberRing u v :=
  ![QuadraticAlgebra.omega,
    algebraMap (FiberFirst v) (FiberRing u v) QuadraticAlgebra.omega,
    fiberBase u v (X 0),fiberBase u v (X 1),fiberBase u v (X 2)]

def fiberEval (u v : K) : Source →+* FiberRing u v :=
  MvPolynomial.eval₂Hom ((fiberBase u v).comp MvPolynomial.C) (fiberCoords u v)

private lemma fiberEval_X (u v : K) (j : Fin 5) :
    fiberEval u v (X j) = fiberCoords u v j := by simp [fiberEval]
private lemma fiberEval_C (u v c : K) :
    fiberEval u v (C c) = fiberBase u v (C c) := by simp [fiberEval]

private lemma fiberEval_tail (u v : K) (P : Base) :
    fiberEval u v (tailEmbed P) = fiberBase u v P := by
  have he : (fiberEval u v).comp tailEmbed = fiberBase u v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [tailEmbed,fiberEval]
    · intro j
      fin_cases j <;> simp [tailEmbed,fiberEval,fiberCoords]
      all_goals rfl
  exact congrArg (fun f : Base →+* FiberRing u v ↦ f P) he

lemma fiberEval_equation₀ (u v : K) : fiberEval u v equation₀ = fiberBase u v (C u) := by
  simp only [equation₀,map_sub,map_pow,fiberEval_tail,fiberEval_X]
  change (QuadraticAlgebra.omega : FiberRing u v)^2-fiberBase u v radicand₀ = fiberBase u v (C u)
  have he : (QuadraticAlgebra.omega : FiberRing u v)^2 = fiberBase u v (radicand₀+C u) := by
    simp [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk,fiberBase,QuadraticAlgebra.algebraMap_eq]
  rw [he]
  simp only [map_add,add_sub_cancel_left]

lemma fiberEval_equation₁ (u v : K) : fiberEval u v equation₁ = fiberBase u v (C v) := by
  simp only [equation₁,map_sub,map_pow,fiberEval_tail,fiberEval_X]
  change (algebraMap (FiberFirst v) (FiberRing u v) QuadraticAlgebra.omega)^2-
    fiberBase u v radicand₁ = fiberBase u v (C v)
  rw [←map_pow]
  have he : (QuadraticAlgebra.omega : FiberFirst v)^2 =
      algebraMap Base (FiberFirst v) (radicand₁+C v) := by
    simp [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk,QuadraticAlgebra.algebraMap_eq]
  rw [he]
  change fiberBase u v (radicand₁+C v)-fiberBase u v radicand₁ = fiberBase u v (C v)
  simp only [map_add,add_sub_cancel_left]

def fiberIdeal (u v : K) : Ideal Source := Ideal.span {equation₀-C u,equation₁-C v}

lemma fiberEval_zero_of_mem (u v : K) (P : Source) (h : P ∈ fiberIdeal u v) :
    fiberEval u v P = 0 := by
  obtain ⟨a,b,he⟩ := Ideal.mem_span_pair.mp h
  rw [←he,map_add,map_mul,map_mul,map_sub,map_sub,
    fiberEval_equation₀,fiberEval_equation₁,fiberEval_C,fiberEval_C]
  simp

private def pointTail (x : Fin 5 → K) : Base →+* K := MvPolynomial.eval ![x 2,x 3,x 4]

private lemma eval_tail (x : Fin 5 → K) (P : Base) :
    MvPolynomial.eval x (tailEmbed P) = pointTail x P := by
  have he : (MvPolynomial.eval x).comp tailEmbed = pointTail x := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [tailEmbed,pointTail]
    · intro j
      fin_cases j <;> simp [tailEmbed,pointTail,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
      all_goals rfl
  exact congrArg (fun f : Base →+* K ↦ f P) he

private def pointFirst (v : K) (x : Fin 5 → K) (hx : MvPolynomial.eval x equation₁ = v) :
    FiberFirst v →+* K :=
  quadraticEval (radicand₁+C v) (pointTail x) (x 1) (by
    have hh : x 1^2-pointTail x radicand₁ = v := by simpa [equation₁,eval_tail] using hx
    have ht : pointTail x (C v) = v := by simp [pointTail]
    rw [map_add,ht]
    linear_combination hh)

private def pointFiber (u v : K) (x : Fin 5 → K)
    (hx : MvPolynomial.eval x equation₀ = u) (hy : MvPolynomial.eval x equation₁ = v) :
    FiberRing u v →+* K :=
  quadraticEval (algebraMap Base (FiberFirst v) (radicand₀+C u)) (pointFirst v x hy) (x 0) (by
    have hh : x 0^2-pointTail x radicand₀ = u := by simpa [equation₀,eval_tail] using hx
    have hroot : x 0^2 = pointTail x (radicand₀+C u) := by
      have ht : pointTail x (C u) = u := by simp [pointTail]
      rw [map_add,ht]
      linear_combination hh
    simpa [pointFirst,quadraticEval_apply] using hroot)


private lemma pointFiber_base (u v : K) (x : Fin 5 → K)
    (hx : MvPolynomial.eval x equation₀ = u) (hy : MvPolynomial.eval x equation₁ = v) (P : Base) :
    pointFiber u v x hx hy (fiberBase u v P) = pointTail x P := by
  simp [pointFiber,pointFirst,fiberBase,quadraticEval_apply]

private lemma pointFiber_eval (u v : K) (x : Fin 5 → K)
    (hx : MvPolynomial.eval x equation₀ = u) (hy : MvPolynomial.eval x equation₁ = v) (P : Source) :
    pointFiber u v x hx hy (fiberEval u v P) = MvPolynomial.eval x P := by
  have he : (pointFiber u v x hx hy).comp (fiberEval u v) = MvPolynomial.eval x := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,fiberEval_C,pointFiber_base,pointTail,MvPolynomial.eval_C]
    · intro j
      simp only [RingHom.comp_apply,fiberEval_X]
      rw [MvPolynomial.eval_X]
      fin_cases j <;> simp [fiberCoords,pointFiber,pointFirst,fiberBase,quadraticEval_apply,
        pointTail,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  exact congrArg (fun f : Source →+* K ↦ f P) he

/-- A constant fourth-power norm modulo a joint-fiber ideal forces each
output to take one constant value on that fiber. No degree bound is used. -/
theorem polynomial_constant_norm_on_fiber (u v c : K) (P : Fin 4 → Source)
    (h : ((∑ i, P i^4)-C c) ∈ fiberIdeal u v) :
    ∃ d : Fin 4 → K, ∀ x : Fin 5 → K,
      MvPolynomial.eval x equation₀ = u → MvPolynomial.eval x equation₁ = v →
      ∀ i, MvPolynomial.eval x (P i) = d i := by
  have hh := fiberEval_zero_of_mem u v _ h
  simp only [map_sub,map_sum,map_pow,fiberEval_C,sub_eq_zero] at hh
  have hc := fiber_constant_norm u v (fun i ↦ fiberEval u v (P i)) c hh
  refine ⟨fun i ↦ coeff 0 (fiberEval u v (P i)).re.re,?_⟩
  intro x hx hy i
  have he := congrArg (pointFiber u v x hx hy) (hc i)
  simpa only [pointFiber_eval,pointFiber_base,pointTail,MvPolynomial.eval_C] using he

/-- The two quadratic labels as polynomials. -/
def pencil₁ : Source := ∑ j, X j^2
def pencil₂ : Source := ∑ j, C (JointQuadraticGaussianInterpolation.weights j)*X j^2

lemma eval_pencil₁ (x : Fin 5 → K) :
    MvPolynomial.eval x pencil₁ = JointQuadraticGaussianInterpolation.label₁ x := by
  simp [pencil₁,JointQuadraticGaussianInterpolation.label₁]

lemma eval_pencil₂ (x : Fin 5 → K) :
    MvPolynomial.eval x pencil₂ = JointQuadraticGaussianInterpolation.label₂ x := by
  simp [pencil₂,JointQuadraticGaussianInterpolation.label₂]

lemma pencil₁_equations : pencil₁ = equation₀+equation₁ := by
  apply MvPolynomial.funext
  intro x
  simp only [pencil₁,equation₀,equation₁,map_add,map_sub,map_sum,map_pow,eval_X,eval_tail]
  simp only [radicand₀,radicand₁,pointTail,map_sub,map_mul,map_neg,map_pow,eval_C,eval_X,
    Fin.sum_univ_five,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  ring

lemma pencil₂_equations : pencil₂ = equation₀+17*equation₁ := by
  apply MvPolynomial.funext
  intro x
  simp only [pencil₂,equation₀,equation₁,map_add,map_sub,map_sum,map_pow,map_mul,map_ofNat,
    eval_C,eval_X,eval_tail]
  simp only [radicand₀,radicand₁,pointTail,map_sub,map_mul,map_neg,map_pow,eval_C,eval_X,
    Fin.sum_univ_five,JointQuadraticGaussianInterpolation.weights,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  ring

/-- Substitution of the two labels into a bivariate polynomial target. -/
def pencilTarget : MvPolynomial (Fin 2) K →+* Source :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![pencil₁,pencil₂]

private lemma fiberEval_pencilTarget (u v : K) (H : MvPolynomial (Fin 2) K) :
    fiberEval u v (pencilTarget H) = fiberBase u v (C (MvPolynomial.eval ![u+v,u+17*v] H)) := by
  have he : (fiberEval u v).comp pencilTarget =
      (fiberBase u v).comp (MvPolynomial.C.comp (MvPolynomial.eval ![u+v,u+17*v])) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [pencilTarget,fiberEval_C]
    · intro j
      simp only [RingHom.comp_apply,pencilTarget,eval₂Hom_X',eval_X]
      fin_cases j
      · change fiberEval u v pencil₁ = fiberBase u v (C (u+v))
        simp only [pencil₁_equations,(fiberEval u v).map_add,fiberEval_equation₀,fiberEval_equation₁,
          (MvPolynomial.C : K →+* Base).map_add,(fiberBase u v).map_add]
      · change fiberEval u v pencil₂ = fiberBase u v (C (u+17*v))
        simp only [pencil₂_equations,(fiberEval u v).map_add,(fiberEval u v).map_mul,
          map_ofNat (fiberEval u v),fiberEval_equation₀,fiberEval_equation₁,
          (MvPolynomial.C : K →+* Base).map_add,(MvPolynomial.C : K →+* Base).map_mul,
          map_ofNat (MvPolynomial.C : K →+* Base),(fiberBase u v).map_add,
          (fiberBase u v).map_mul,map_ofNat (fiberBase u v)]

  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* FiberRing u v ↦ f H) he

/-- Arbitrary-degree polynomial outputs of a norm identity depending on the
explicit two labels are constant on every joint fiber. -/
theorem polynomial_quartic_identity_constant_on_joint_fibers
    (P : Fin 4 → Source) (H : MvPolynomial (Fin 2) K)
    (h : (∑ i, P i^4) = pencilTarget H) (x y : Fin 5 → K)
    (hx : JointQuadraticGaussianInterpolation.label₁ x = JointQuadraticGaussianInterpolation.label₁ y)
    (hy : JointQuadraticGaussianInterpolation.label₂ x = JointQuadraticGaussianInterpolation.label₂ y) :
    ∀ i, MvPolynomial.eval x (P i) = MvPolynomial.eval y (P i) := by
  let u := MvPolynomial.eval x equation₀
  let v := MvPolynomial.eval x equation₁
  have h₁ : MvPolynomial.eval y equation₀+MvPolynomial.eval y equation₁ = u+v := by
    rw [←map_add,←pencil₁_equations,eval_pencil₁,←hx,←eval_pencil₁,pencil₁_equations,map_add]
  have h₂ : MvPolynomial.eval y equation₀+17*MvPolynomial.eval y equation₁ = u+17*v := by
    have he : MvPolynomial.eval y pencil₂ = MvPolynomial.eval x pencil₂ :=
      (eval_pencil₂ y).trans (hy.symm.trans (eval_pencil₂ x).symm)
    simpa only [pencil₂_equations,map_add,map_mul,map_ofNat] using he

  have hu : MvPolynomial.eval y equation₀ = u := by linear_combination (17*h₁-h₂)/16
  have hv : MvPolynomial.eval y equation₁ = v := by linear_combination (h₂-h₁)/16
  have hh := congrArg (fiberEval u v) h
  simp only [map_sum,map_pow,fiberEval_pencilTarget] at hh
  have hc := fiber_constant_norm u v (fun i ↦ fiberEval u v (P i)) _ hh
  intro i
  have hxi := congrArg (pointFiber u v x rfl rfl) (hc i)
  have hyi := congrArg (pointFiber u v y hu hv) (hc i)
  simp only [pointFiber_eval,pointFiber_base,pointTail,MvPolynomial.eval_C] at hxi hyi
  exact hxi.trans hyi.symm

end
end Erdos322Research.JointQuadraticCone
