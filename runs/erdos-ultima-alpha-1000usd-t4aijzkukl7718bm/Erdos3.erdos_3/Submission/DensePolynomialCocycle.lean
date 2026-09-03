import Submission.DensePartialHomomorphism
import Submission.PolynomialDerivativeConsistency

/-! A semidirect group of normalized phase functions, and extension of dense
partial polynomial cocycles. These are exact structural results, not a general
positive-uniformity inverse theorem. -/
namespace Erdos3DensePolynomialCocycle
open Finset Erdos3DensePartialHomomorphism Erdos3PolynomialDerivativeConsistency
  Erdos3HigherPolynomialSeparation Erdos3HigherUniformityDefect
  Erdos3HigherLocalPolynomialProgressions Erdos3HigherPhaseDifferences Erdos3FiniteUniformity
open scoped BigOperators Classical
set_option maxHeartbeats 3000000
noncomputable section

/-- Translation together with a circle-valued coefficient, modulo constants. -/
structure PhaseAction (G : Type*) [AddCommGroup G] where
  dir : G
  coeff : G → Additive Circle
  coeff_zero : coeff 0 = 0

namespace PhaseAction
variable {G : Type*} [AddCommGroup G]

@[ext] lemma ext {p q : PhaseAction G} (hd : p.dir = q.dir) (hc : p.coeff = q.coeff) : p = q := by
  cases p
  cases q
  cases hd
  cases hc
  rfl

instance : One (PhaseAction G) := ⟨⟨0,fun _ ↦ 0,rfl⟩⟩
instance : Mul (PhaseAction G) := ⟨fun p q ↦
  ⟨p.dir+q.dir,fun x ↦ p.coeff x+q.coeff (x+p.dir)-q.coeff p.dir,by
    dsimp only
    rw [p.coeff_zero,zero_add,zero_add,sub_self]⟩⟩
instance : Inv (PhaseAction G) := ⟨fun p ↦
  ⟨-p.dir,fun x ↦ -p.coeff (x-p.dir)+p.coeff (-p.dir),by
    dsimp only
    rw [zero_sub,neg_add_cancel]⟩⟩

@[simp] lemma one_dir : (1 : PhaseAction G).dir = 0 := rfl
@[simp] lemma one_coeff (x : G) : (1 : PhaseAction G).coeff x = 0 := rfl
@[simp] lemma mul_dir (p q : PhaseAction G) : (p*q).dir = p.dir+q.dir := rfl
@[simp] lemma mul_coeff (p q : PhaseAction G) (x : G) :
    (p*q).coeff x = p.coeff x+q.coeff (x+p.dir)-q.coeff p.dir := rfl
@[simp] lemma inv_dir (p : PhaseAction G) : p⁻¹.dir = -p.dir := rfl
@[simp] lemma inv_coeff (p : PhaseAction G) (x : G) :
    p⁻¹.coeff x = -p.coeff (x-p.dir)+p.coeff (-p.dir) := rfl

instance : Group (PhaseAction G) where
  mul_assoc p q r := by
    apply ext
    · exact add_assoc _ _ _
    · funext x
      simp only [mul_coeff,mul_dir,add_assoc]
      abel
  one_mul p := by
    apply ext
    · exact zero_add _
    · funext x
      simp only [mul_coeff,one_coeff,one_dir,add_zero,p.coeff_zero,zero_add,sub_zero]
  mul_one p := by
    apply ext
    · exact add_zero _
    · funext x
      simp only [mul_coeff,one_coeff,add_zero,sub_zero]
  inv_mul_cancel p := by
    apply ext
    · exact neg_add_cancel _
    · funext x
      simp only [mul_coeff,inv_coeff,inv_dir,one_coeff,sub_eq_add_neg]
      abel

end PhaseAction

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def phaseAction (P : G → G → Additive Circle) (h : G) : PhaseAction G :=
  ⟨h,normalize (P h),sub_self _⟩

lemma global_polynomial_const (n : ℕ) (c : Additive Circle) :
    IsLocallyPolynomial (Set.univ : Set G) n (fun _ ↦ c) :=
  (uniformity_eq_one_iff_polynomial n (fun _ ↦ c)).mp
    (uniformityPower_unit_const n (phase_norm c))

lemma global_polynomial_normalize (n : ℕ) (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q) :
    IsLocallyPolynomial Set.univ n (normalize q) :=
  global_polynomial_sub n q (fun _ ↦ q 0) hq (global_polynomial_const n (q 0))

/-- Extend a normalized partial polynomial cocycle from density greater than 3/4.
The polynomial degree is preserved on every direction, including new ones. -/
theorem dense_polynomial_cocycle (n : ℕ) (S : Finset G)
    (hS : 4*(Fintype.card G-S.card) < Fintype.card G) (P : G → G → Additive Circle)
    (hpoly : ∀ h ∈ S, IsLocallyPolynomial Set.univ n (P h))
    (hcocycle : ∀ h ∈ S, ∀ k ∈ S, h+k ∈ S → ∀ x,
      normalize (P (h+k)) x = normalize (P h) x+
        normalize (P k) (x+h)-normalize (P k) h) :
    ∃ Q : G → G → Additive Circle,
      (∀ h, Q h 0 = 0) ∧
      (∀ h ∈ S, Q h = normalize (P h)) ∧
      (∀ h, IsLocallyPolynomial Set.univ n (Q h)) ∧
      ∀ h k x, Q (h+k) x = Q h x+Q k (x+h)-Q k h := by
  let S' : Finset (Multiplicative G) := S
  have hS' : 4*(Fintype.card (Multiplicative G)-S'.card) < Fintype.card (Multiplicative G) := by
    simpa only [Fintype.card_multiplicative,S'] using hS
  let f : Multiplicative G → PhaseAction G := fun h ↦ phaseAction P h.toAdd
  have hf : ∀ a ∈ S', ∀ b ∈ S', a*b ∈ S' → f (a*b) = f a*f b := by
    intro a ha b hb hab
    apply PhaseAction.ext
    · rfl
    · funext x
      exact hcocycle a.toAdd ha b.toAdd hb hab x
  obtain ⟨φ,hφ,_⟩ := dense_partial_homomorphism S' hS' f hf
  have hagree (h : G) (hh : h ∈ S) : φ (Multiplicative.ofAdd h) = phaseAction P h := hφ _ hh
  have hdir (h : G) : (φ (Multiplicative.ofAdd h)).dir = h := by
    obtain ⟨b,hb,hhb,_,_⟩ := exists_four_good S hS (Equiv.refl G) (Equiv.addLeft h)
      (Equiv.refl G) (Equiv.refl G)
    change h+b ∈ S at hhb
    have hm := congrArg PhaseAction.dir (φ.map_mul (Multiplicative.ofAdd h) (Multiplicative.ofAdd b))
    change (φ (Multiplicative.ofAdd (h+b))).dir =
      (φ (Multiplicative.ofAdd h)).dir+(φ (Multiplicative.ofAdd b)).dir at hm
    rw [hagree (h+b) hhb,hagree b hb] at hm
    exact (add_right_cancel hm).symm
  let Q : G → G → Additive Circle := fun h ↦ (φ (Multiplicative.ofAdd h)).coeff
  have hQ (h : G) (hh : h ∈ S) : Q h = normalize (P h) := by
    exact congrArg PhaseAction.coeff (hagree h hh)
  have hc (h k x : G) : Q (h+k) x = Q h x+Q k (x+h)-Q k h := by
    have hm := congrArg (fun p : PhaseAction G ↦ p.coeff x)
      (φ.map_mul (Multiplicative.ofAdd h) (Multiplicative.ofAdd k))
    change Q (h+k) x = Q h x+Q k (x+(φ (Multiplicative.ofAdd h)).dir)-
      Q k (φ (Multiplicative.ofAdd h)).dir at hm
    simpa only [hdir] using hm
  refine ⟨Q,fun h ↦ (φ (Multiplicative.ofAdd h)).coeff_zero,hQ,?_,hc⟩
  intro h
  obtain ⟨b,hb,hhb,_,_⟩ := exists_four_good S hS (Equiv.refl G) (Equiv.addLeft h)
    (Equiv.refl G) (Equiv.refl G)
  change h+b ∈ S at hhb
  have he : Q h = fun x ↦ normalize (P (h+b)) x-normalize (P b) (x+h)+normalize (P b) h := by
    funext x
    have hh := hc h b x
    rw [hQ (h+b) hhb,hQ b hb] at hh
    rw [hh]
    abel
  rw [he]
  exact global_polynomial_add n _ _
    (global_polynomial_sub n _ _ (global_polynomial_normalize n _ (hpoly (h+b) hhb))
      (global_polynomial_shift n _ (global_polynomial_normalize n _ (hpoly b hb)) h))
    (global_polynomial_const n _)

/-- Dense, sufficiently accurate polynomial approximations to derivatives
produce a global normalized polynomial cocycle. -/
theorem dense_derivative_polynomial_cocycle (n : ℕ) (S : Finset G)
    (hS : 4*(Fintype.card G-S.card) < Fintype.card G)
    (q : G → Additive Circle) (P : G → G → Additive Circle) {η : ℝ}
    (hη : 3*η < polynomialGap n/2)
    (hpoly : ∀ h ∈ S, IsLocallyPolynomial Set.univ n (P h))
    (happrox : ∀ h ∈ S, Erdos3HigherUniformityPerturbation.meanDistance
      (fun x ↦ phase (fwdDiff h q x)) (fun x ↦ phase (P h x)) ≤ η) :
    ∃ Q : G → G → Additive Circle,
      (∀ h, Q h 0 = 0) ∧
      (∀ h ∈ S, Q h = normalize (P h)) ∧
      (∀ h, IsLocallyPolynomial Set.univ n (Q h)) ∧
      ∀ h k x, Q (h+k) x = Q h x+Q k (x+h)-Q k h := by
  apply dense_polynomial_cocycle n S hS P hpoly
  intro h hh k hk hhk x
  have hkh : k+h ∈ S := by simpa only [add_comm k h] using hhk
  have he := derivative_polynomial_cocycle n q P k h hη
    (hpoly k hk) (hpoly h hh) (hpoly (k+h) hkh)
    (happrox k hk) (happrox h hh) (happrox (k+h) hkh) x
  rw [add_comm k h] at he
  rw [he]
  abel

#print axioms dense_polynomial_cocycle
#print axioms dense_derivative_polynomial_cocycle
end
end Erdos3DensePolynomialCocycle
