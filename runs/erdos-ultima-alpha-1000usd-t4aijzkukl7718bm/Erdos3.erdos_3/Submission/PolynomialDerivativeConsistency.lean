import Submission.HigherPolynomialSeparation

/-! Accurate polynomial approximations to derivatives satisfy an exact
normalized cocycle identity on every good triple of directions. -/
namespace Erdos3PolynomialDerivativeConsistency
open Finset Erdos3HigherPolynomialSeparation Erdos3HigherUniformityPerturbation
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma meanDistance_symm (f g : G → ℂ) : meanDistance f g = meanDistance g f := by
  unfold meanDistance
  apply expect_congr rfl
  intro x _
  exact norm_sub_rev _ _

lemma meanDistance_triangle (f g h : G → ℂ) :
    meanDistance f h ≤ meanDistance f g+meanDistance g h := by
  unfold meanDistance
  rw [← expect_add_distrib]
  exact expect_le_expect (fun x _ ↦ norm_sub_le_norm_sub_add_norm_sub _ _ _)

lemma meanDistance_shift (f g : G → ℂ) (a : G) :
    meanDistance (fun x ↦ f (x+a)) (fun x ↦ g (x+a)) = meanDistance f g :=
  Fintype.expect_equiv (Equiv.addRight a) _ _ (fun _ ↦ rfl)

lemma phase_add_distance (a b c d : Additive Circle) :
    ‖phase (a+b)-phase (c+d)‖ ≤ ‖phase a-phase c‖+‖phase b-phase d‖ := by
  rw [phase_add,phase_add]
  calc
    _ = ‖(phase a-phase c)*phase b+phase c*(phase b-phase d)‖ := by congr 1; ring
    _ ≤ ‖(phase a-phase c)*phase b‖+‖phase c*(phase b-phase d)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul,phase_norm,phase_norm,mul_one,one_mul]

lemma meanDistance_phase_add (a b c d : G → Additive Circle) :
    meanDistance (fun x ↦ phase (a x+b x)) (fun x ↦ phase (c x+d x)) ≤
      meanDistance (fun x ↦ phase (a x)) (fun x ↦ phase (c x))+
      meanDistance (fun x ↦ phase (b x)) (fun x ↦ phase (d x)) := by
  unfold meanDistance
  rw [← expect_add_distrib]
  exact expect_le_expect (fun x _ ↦ phase_add_distance _ _ _ _)

lemma cubeDifference_add (n : ℕ) (q p : G → Additive Circle)
    (h : Fin n → G) (x : G) :
    cubeDifference n (fun y ↦ q y+p y) h x =
      cubeDifference n q h x+cubeDifference n p h x := by
  induction n generalizing q p with
  | zero => rfl
  | succ n ih =>
    have he : fwdDiff (h 0) (fun y ↦ q y+p y) =
        fun y ↦ fwdDiff (h 0) q y+fwdDiff (h 0) p y := fwdDiff_add _ _ _
    rw [cubeDifference,he,ih]
    rfl

lemma cubeDifference_shift (n : ℕ) (q : G → Additive Circle)
    (a : G) (h : Fin n → G) (x : G) :
    cubeDifference n (fun y ↦ q (y+a)) h x = cubeDifference n q h (x+a) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have he : fwdDiff (h 0) (fun y ↦ q (y+a)) =
        fun y ↦ fwdDiff (h 0) q (y+a) := by
      funext y
      simp only [fwdDiff]
      rw [add_right_comm y (h 0) a]
    rw [cubeDifference,he,ih]
    rfl

lemma global_polynomial_add (n : ℕ) (q p : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q)
    (hp : IsLocallyPolynomial Set.univ n p) :
    IsLocallyPolynomial Set.univ n (fun x ↦ q x+p x) := by
  intro x h hR
  rw [cubeDifference_add,hq x h hR,hp x h hR,add_zero]

lemma global_polynomial_shift (n : ℕ) (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q) (a : G) :
    IsLocallyPolynomial Set.univ n (fun x ↦ q (x+a)) := by
  intro x h _
  rw [cubeDifference_shift]
  exact hq (x+a) h (fun _ ↦ Set.mem_univ _)

lemma additive_derivative_cocycle (q : G → Additive Circle) (h k x : G) :
    fwdDiff (h+k) q x = fwdDiff h q (x+k)+fwdDiff k q x := by
  simp only [fwdDiff]
  rw [show x+(h+k) = (x+k)+h by abel]
  abel

noncomputable def normalize (q : G → Additive Circle) (x : G) : Additive Circle := q x-q 0

/-- This implication is exact: the approximation errors disappear after
normalization, because distinct polynomial classes have a uniform gap. -/
theorem derivative_polynomial_cocycle (n : ℕ) (q : G → Additive Circle)
    (P : G → G → Additive Circle) (h k : G) {η : ℝ}
    (hη : 3*η < polynomialGap n/2)
    (hPh : IsLocallyPolynomial Set.univ n (P h))
    (hPk : IsLocallyPolynomial Set.univ n (P k))
    (hPhk : IsLocallyPolynomial Set.univ n (P (h+k)))
    (hDh : meanDistance (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P h x)) ≤ η)
    (hDk : meanDistance (fun x ↦ phase (fwdDiff k q x)) (fun x ↦ phase (P k x)) ≤ η)
    (hDhk : meanDistance (fun x ↦ phase (fwdDiff (h+k) q x)) (fun x ↦ phase (P (h+k) x)) ≤ η) :
    ∀ x, normalize (P (h+k)) x =
      normalize (P h) (x+k)-normalize (P h) k+normalize (P k) x := by
  let R : G → Additive Circle := fun x ↦ P h (x+k)+P k x
  have hR : IsLocallyPolynomial Set.univ n R :=
    global_polynomial_add n _ _ (global_polynomial_shift n _ hPh k) hPk
  have hD : meanDistance (fun x ↦ phase (fwdDiff (h+k) q x)) (fun x ↦ phase (R x)) ≤ 2*η := by
    have he : (fun x ↦ phase (fwdDiff (h+k) q x)) =
        fun x ↦ phase (fwdDiff h q (x+k)+fwdDiff k q x) := by
      funext x
      rw [additive_derivative_cocycle]
    rw [he]
    have hh := meanDistance_phase_add (fun x ↦ fwdDiff h q (x+k)) (fwdDiff k q)
      (fun x ↦ P h (x+k)) (P k)
    rw [meanDistance_shift (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P h x)) k] at hh
    exact hh.trans (by linarith only [hDh,hDk])
  have hclose : meanDistance (fun x ↦ phase (P (h+k) x)) (fun x ↦ phase (R x)) < polynomialGap n/2 := by
    have ht := meanDistance_triangle (fun x ↦ phase (P (h+k) x))
      (fun x ↦ phase (fwdDiff (h+k) q x)) (fun x ↦ phase (R x))
    rw [meanDistance_symm (fun x ↦ phase (P (h+k) x))
      (fun x ↦ phase (fwdDiff (h+k) q x))] at ht
    linarith only [ht,hDhk,hD,hη]
  have hc := close_polynomials_constant_difference n (P (h+k)) R hPhk hR hclose
  intro x
  have he := sub_eq_iff_eq_add.mp (hc x)
  dsimp only [normalize]
  rw [he]
  dsimp only [R]
  rw [zero_add]
  abel

#print axioms derivative_polynomial_cocycle
end Erdos3PolynomialDerivativeConsistency
