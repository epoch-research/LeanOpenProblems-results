import Submission.EvenPolynomialModelTransfer
import Submission.MaskedUniformityCounting

/-! Conditional all-even-length counting criterion: an appropriate polynomial
factor, equidistributed free coordinates, and small higher-order uniformity
error imply an actual nontrivial arithmetic progression. No existence theorem
for the factor or its equidistribution is assumed without an explicit hypothesis. -/
namespace Erdos3EvenPolynomialFactorCounting
open Finset Erdos3EvenPolynomialModelTransfer Erdos3EvenPolynomialCoordinates
  Erdos3HigherPhaseDifferences Erdos3MaskedUniformityCounting Erdos3UniformityCounting
  Erdos3LinearFormsUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]

noncomputable def realLinearAverage {k : ℕ} (v : Fin k → F) (f : F → ℝ) : ℝ :=
  𝔼 x : F, 𝔼 d : F, ∏ i : Fin k, f (x+v i*d)

lemma realLinearAverage_coe {k : ℕ} (v : Fin k → F) (f : F → ℝ) :
    (realLinearAverage v f : ℂ) = linearAverage v (fun _ x ↦ (f x : ℂ)) := by
  simp only [realLinearAverage,linearAverage,Complex.ofReal_expect,Complex.ofReal_prod]

lemma realLinearAverage_difference (n : ℕ) (v : Fin (n+2) → F) (hv : Function.Injective v)
    (f g : F → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower n (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ η^(2^(n+1))) :
    |realLinearAverage v f-realLinearAverage v g| ≤ (n+2 : ℕ)*η := by
  have hfc (x : F) : ‖(f x : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hf x).1] using (hf x).2
  have hgc (x : F) : ‖(g x : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg (hg x).1] using (hg x).2
  have hfg (x : F) : ‖(f x : ℂ)-(g x : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hf x).2,(hg x).1]⟩
  have h := counting_difference n v hv (fun x ↦ (f x : ℂ)) (fun x ↦ (g x : ℂ))
    hfc hgc hfg hη (by simpa only [Complex.ofReal_sub] using hU)
  rw [← realLinearAverage_coe,← realLinearAverage_coe,← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h

/-- The pure polynomial model supplies a count along actual field APs when its
free coordinate distribution satisfies the stated discrepancy hypothesis. -/
lemma realLinearAverage_factor_lower (m : ℕ) (q : F → G)
    (Φ : G → ℝ) (hΦ : ∀ y, |Φ y| ≤ 1)
    (hq : ∀ x d : F, diffIter (2*m+1) (fun j : ℕ ↦ q (x+(j : F)*d)) 0 = 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ : AddChar (G × (Fin m → G) × (Fin m → G)) ℂ,
      ‖(𝔼 x : F, 𝔼 d : F, χ (polynomialCoordinates m (fun j : ℕ ↦ q (x+(j : F)*d))))-
        (𝔼 p : G × (Fin m → G) × (Fin m → G), χ p)‖ ≤ ε) :
    (𝔼 y : G, Φ y)^(2*m+2)-ε*(Fintype.card G : ℝ)^(m+1) ≤
      realLinearAverage (fun i : Fin (2*m+2) ↦ (i.val : F)) (fun x ↦ Φ (q x)) := by
  let Q (p : F × F) (j : ℕ) : G := q (p.1+(j : F)*p.2)
  have ht := even_polynomial_transfer_bounded m Φ hΦ Q (fun p ↦ hq p.1 p.2) hε
    (fun χ ↦ by
      change ‖(𝔼 p : F × F, χ (polynomialCoordinates m (fun j : ℕ ↦ q (p.1+(j : F)*p.2))))-_‖ ≤ ε
      rw [show (𝔼 p : F × F, χ (polynomialCoordinates m (fun j : ℕ ↦ q (p.1+(j : F)*p.2)))) =
        𝔼 x : F, 𝔼 d : F, χ (polynomialCoordinates m (fun j : ℕ ↦ q (x+(j : F)*d))) from expect_product _ _ _]
      exact hdisc χ)
  convert ht using 1
  unfold realLinearAverage
  symm
  exact expect_product _ _ _

/-- Accounts for the diagonal count and produces a nonzero common difference.
This is a sufficient criterion, not an unconditional existence of the factor. -/
theorem exists_AP_of_even_polynomial_factor (m : ℕ)
    (hv : Function.Injective (fun i : Fin (2*m+2) ↦ (i.val : F)))
    (A : Finset F) (q : F → G) (Φ : G → ℝ) (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hq : ∀ x d : F, diffIter (2*m+1) (fun j : ℕ ↦ q (x+(j : F)*d)) 0 = 0)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdisc : ∀ χ : AddChar (G × (Fin m → G) × (Fin m → G)) ℂ,
      ‖(𝔼 x : F, 𝔼 d : F, χ (polynomialCoordinates m (fun j : ℕ ↦ q (x+(j : F)*d))))-
        (𝔼 p : G × (Fin m → G) × (Fin m → G), χ p)‖ ≤ ε)
    (hU : uniformityPower (2*m) (fun x ↦ ((indicator A x-Φ (q x) : ℝ) : ℂ)) ≤ η^(2^(2*m+1)))
    (hnum : ε*(Fintype.card G : ℝ)^(m+1)+(2*m+2 : ℕ)*η+density A/(Fintype.card F : ℝ) <
      (𝔼 y : G, Φ y)^(2*m+2)) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin (2*m+2), x+(i.val : F)*d ∈ A := by
  have hc := realLinearAverage_factor_lower m q Φ
    (fun y ↦ by simpa only [abs_of_nonneg (hΦ y).1] using (hΦ y).2) hq hε hdisc
  have hd := (abs_le.mp (realLinearAverage_difference (2*m) _ hv (indicator A) (fun x ↦ Φ (q x))
    (indicator_norm_bounds A) (fun x ↦ hΦ (q x)) hη hU)).1
  by_contra! hno
  have hdiag : ∀ x d : F, (∀ i : Fin (2*m+2), x+(i.val : F)*d ∈ A) → d = 0 := by
    intro x d hm
    by_contra hdz
    obtain ⟨i,hi⟩ := hno x d hdz
    exact hi (hm i)
  have he := indicator_diagonal_average (by omega : 0 < 2*m+2) _ A hdiag
  rw [← realLinearAverage_coe,← Complex.ofReal_natCast,← Complex.ofReal_div] at he
  have heR := Complex.ofReal_injective he
  linarith

#print axioms realLinearAverage_difference
#print axioms exists_AP_of_even_polynomial_factor
end Erdos3EvenPolynomialFactorCounting
