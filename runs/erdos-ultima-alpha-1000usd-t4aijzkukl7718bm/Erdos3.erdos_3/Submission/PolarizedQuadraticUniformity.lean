import Submission.UniformFactorDistribution

/-! Exact lower-order uniformity of global quadratic maps in terms of the
radical of their polarized characters. No rank or equidistribution assertion
is made about the merely local phases produced by strong regularity. -/
namespace Erdos3PolarizedQuadraticUniformity
open Finset Erdos3UniformFactorDistribution Erdos3FiniteUniformity
  Erdos3FiniteFourier Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {H G : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup G] [Fintype G]

/-- The character radical: shifts for which the bilinear phase is trivial. -/
noncomputable def characterRadical (B : H →+ H →+ G) (χ : AddChar G ℂ) : Finset H :=
  univ.filter (fun h ↦ χ.compAddMonoidHom (B h) = 1)

lemma quadratic_character_derivative (q : H → G) (B : H →+ H →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x)
    (χ : AddChar G ℂ) (h x : H) :
    derivative (fun x ↦ χ (q x)) h x =
      χ (q h-q 0)*(χ.compAddMonoidHom (B h)) x := by
  unfold derivative
  rw [← char_sub]
  change χ (q (x+h)-q x) = χ (q h-q 0)*χ (B h x)
  rw [← χ.map_add_eq_mul]
  congr 1
  rw [add_comm x h,hq h x]
  abel

/-- The fourth power of U2 is exactly the relative size of the character
radical. This is valid for arbitrary finite abelian domain and target groups. -/
theorem quadratic_character_U2 (q : H → G) (B : H →+ H →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x)
    (χ : AddChar G ℂ) :
    uniformityPower 1 (fun x ↦ χ (q x)) = density (characterRadical B χ) := by
  change (𝔼 h : H, ‖𝔼 x : H, derivative (fun x ↦ χ (q x)) h x‖^2) = _
  rw [← expect_indicator]
  apply expect_congr rfl
  intro h _
  simp only [quadratic_character_derivative q B hq χ,← mul_expect,
    norm_mul,χ.norm_apply,one_mul]
  by_cases hh : χ.compAddMonoidHom (B h) = 1
  · simp [hh,indicator,characterRadical]
  · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr hh]
    simp [hh,indicator,characterRadical]

/-- Quadratic character phases have maximal U3, even though their U2 is small
when their polarization radical is small. -/
theorem quadratic_character_U3 (q : H → G) (B : H →+ H →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x)
    (χ : AddChar G ℂ) : uniformityPower 2 (fun x ↦ χ (q x)) = 1 := by
  change (𝔼 h : H, uniformityPower 1 (derivative (fun x ↦ χ (q x)) h)) = 1
  have he (h : H) : derivative (fun x ↦ χ (q x)) h =
      fun x ↦ χ (q h-q 0)*(χ.compAddMonoidHom (B h)) x := by
    funext x
    exact quadratic_character_derivative q B hq χ h x
  simp only [he,uniformityPower_unit_scale _ _ (χ.norm_apply _),
    character_uniformity,Fintype.expect_const]

/-- The exact third-difference relation follows from biadditivity, without a
finite-field modeling or distribution assumption. -/
theorem quadratic_fourth_relation (q : H → G) (B : H →+ H →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x) (x d : H) :
    q (x+3 • d) = q x-3 • q (x+d)+3 • q (x+2 • d) := by
  have h₁ := hq x d
  have h₂ := hq (x+d) d
  have h₃ := hq (x+2 • d) d
  have hs₂ : x+d+d = x+2 • d := by module
  have hs₃ : x+2 • d+d = x+3 • d := by module
  rw [hs₂] at h₂
  rw [hs₃] at h₃
  simp only [map_add,map_nsmul,AddMonoidHom.add_apply,AddMonoidHom.nsmul_apply] at h₂ h₃
  rw [h₃,h₂,h₁]
  module

variable {F : Type*} [Field F] [Fintype F]

/-- Actual triple character discrepancy from an explicit radical-size bound. -/
theorem triple_discrepancy_of_radical (v : Fin 3 → F)
    (hv : Function.Injective v) (q : F → G) (B : F →+ F →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrad : ∀ χ : AddChar G ℂ, χ ≠ 1 → density (characterRadical B χ) ≤ ε^4)
    (χ₀ χ₁ χ₂ : AddChar G ℂ) :
    ‖(𝔼 x : F, 𝔼 d : F,
        χ₀ (q (x+v 0*d))*χ₁ (q (x+v 1*d))*χ₂ (q (x+v 2*d)))-
      (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε := by
  apply triple_character_discrepancy v hv q hε ?_ χ₀ χ₁ χ₂
  intro χ hχ
  rw [quadratic_character_U2 q B hq χ]
  exact hrad χ hχ

/-- A four-term progression criterion with the distribution hypothesis fully
replaced by the polarized-character radical bound. -/
theorem exists_fourAP_of_radical
    (hv : Function.Injective (fun i : Fin 4 ↦ (i.val : F)))
    (A : Finset F) (q : F → G) (B : F →+ F →+ G)
    (hq : ∀ h x, q (h+x) = q h+q x-q 0+B h x)
    (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hrad : ∀ χ : AddChar G ℂ, χ ≠ 1 → density (characterRadical B χ) ≤ ε^4)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-Φ (q x) : ℝ) : ℂ)) ≤ η^8)
    (hnum : ε*(Fintype.card G : ℝ)^2+4*η+density A/(Fintype.card F : ℝ) <
      (𝔼 y : G, Φ y)^4) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin 4, x+(i.val : F)*d ∈ A := by
  apply exists_pattern_of_character_uniform_factor (fun i : Fin 4 ↦ (i.val : F)) hv
    A q Φ hΦ ?_ hε hη ?_ hU hnum
  · intro x d
    simpa only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,
      Nat.cast_one,Nat.cast_ofNat,zero_mul,add_zero,one_mul,nsmul_eq_mul] using
      quadratic_fourth_relation q B hq x d
  · intro χ hχ
    rw [quadratic_character_U2 q B hq χ]
    exact hrad χ hχ

#print axioms quadratic_character_U2
#print axioms quadratic_fourth_relation
#print axioms exists_fourAP_of_radical
end Erdos3PolarizedQuadraticUniformity
