import Submission.QuadraticModelTransfer
import Submission.MaskedUniformityCounting

/-! Four-term counting from a well-distributed quadratic factor plus a small
uniformity error. The structural and discrepancy assumptions are explicit.
This does not produce such a factor for an arbitrary progression-free set. -/
namespace Erdos3QuadraticFactorCounting
open Finset Erdos3QuadraticModelTransfer Erdos3MaskedUniformityCounting
  Erdos3UniformityCounting Erdos3LinearFormsUniformity Erdos3FiniteUniformity
  Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]

noncomputable def fourRealAverage (v : Fin 4 → F) (f : F → ℝ) : ℝ :=
  𝔼 x : F, 𝔼 d : F, ∏ i : Fin 4, f (x+v i*d)

lemma fourRealAverage_coe (v : Fin 4 → F) (f : F → ℝ) :
    (fourRealAverage v f : ℂ) = linearAverage v (fun _ x ↦ (f x : ℂ)) := by
  simp only [fourRealAverage,linearAverage,Complex.ofReal_expect,Complex.ofReal_prod]

lemma fourRealAverage_difference (v : Fin 4 → F) (hv : Function.Injective v)
    (f g : F → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower 2 (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^8) :
    |fourRealAverage v f-fourRealAverage v g| ≤ 4*η := by
  have hfc (x : F) : ‖(f x : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hf x).1] using (hf x).2
  have hgc (x : F) : ‖(g x : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hg x).1] using (hg x).2
  have hfg (x : F) : ‖(f x : ℂ)-(g x : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hf x).2,(hg x).1]⟩
  have h := counting_difference 2 v hv (fun x ↦ (f x : ℂ)) (fun x ↦ (g x : ℂ))
    hfc hgc hfg hη (by simpa using hU)
  rw [← fourRealAverage_coe,← fourRealAverage_coe,← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h

lemma fourRealAverage_factor_lower (v : Fin 4 → F) (q : F → G)
    (Φ : G → ℝ) (hΦ : ∀ y, |Φ y| ≤ 1)
    (hrel : ∀ x d : F, q (x+v 3*d) = q (x+v 0*d)-3 • q (x+v 1*d)+3 • q (x+v 2*d))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 x : F, 𝔼 d : F, χ₀ (q (x+v 0*d))*χ₁ (q (x+v 1*d))*χ₂ (q (x+v 2*d)))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : G, Φ y)^4-ε*(Fintype.card G : ℝ)^2 ≤ fourRealAverage v (fun x ↦ Φ (q x)) := by
  let a (i : Fin 4) (p : F × F) : G := q (p.1+v i*p.2)
  have ht := quadratic_model_lower_bounded Φ hΦ (a 0) (a 1) (a 2) (a 3)
    (fun p ↦ hrel p.1 p.2) hε (fun χ₀ χ₁ χ₂ ↦ by
      dsimp only [a]
      rw [show (𝔼 p : F × F, χ₀ (q (p.1+v 0*p.2))*χ₁ (q (p.1+v 1*p.2))*χ₂ (q (p.1+v 2*p.2))) =
        𝔼 x : F, 𝔼 d : F, χ₀ (q (x+v 0*d))*χ₁ (q (x+v 1*d))*χ₂ (q (x+v 2*d)) from expect_product _ _ _]
      exact hdisc χ₀ χ₁ χ₂)
  convert ht using 1
  unfold fourRealAverage
  simp only [Fin.prod_univ_four]
  exact (expect_product (univ : Finset F) (univ : Finset F)
    (fun p : F × F ↦ Φ (q (p.1+v 0*p.2))*Φ (q (p.1+v 1*p.2))*
      Φ (q (p.1+v 2*p.2))*Φ (q (p.1+v 3*p.2)))).symm

/-- An explicit sufficient criterion for an actual nontrivial four-point
configuration, after accounting for the diagonal contribution. -/
theorem exists_pattern_of_quadratic_factor (v : Fin 4 → F) (hv : Function.Injective v)
    (A : Finset F) (q : F → G) (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hrel : ∀ x d : F, q (x+v 3*d) = q (x+v 0*d)-3 • q (x+v 1*d)+3 • q (x+v 2*d))
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 x : F, 𝔼 d : F, χ₀ (q (x+v 0*d))*χ₁ (q (x+v 1*d))*χ₂ (q (x+v 2*d)))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-Φ (q x) : ℝ) : ℂ)) ≤ η^8)
    (hnum : ε*(Fintype.card G : ℝ)^2+4*η+density A/(Fintype.card F : ℝ) < (𝔼 y : G, Φ y)^4) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin 4, x+v i*d ∈ A := by
  have hc := fourRealAverage_factor_lower v q Φ
    (fun y ↦ by simpa only [abs_of_nonneg (hΦ y).1] using (hΦ y).2) hrel hε hdisc
  have hd := (abs_le.mp (fourRealAverage_difference v hv (indicator A) (fun x ↦ Φ (q x))
    (indicator_norm_bounds A) (fun x ↦ hΦ (q x)) hη hU)).1
  by_contra! hno
  have hdiag : ∀ x d : F, (∀ i : Fin 4, x+v i*d ∈ A) → d = 0 := by
    intro x d hm
    by_contra hdz
    obtain ⟨i,hi⟩ := hno x d hdz
    exact hi (hm i)
  have he := indicator_diagonal_average (by decide : 0 < 4) v A hdiag
  rw [← fourRealAverage_coe,← Complex.ofReal_natCast,← Complex.ofReal_div] at he
  have heR := Complex.ofReal_injective he
  linarith

#print axioms fourRealAverage_difference
#print axioms exists_pattern_of_quadratic_factor
end Erdos3QuadraticFactorCounting
