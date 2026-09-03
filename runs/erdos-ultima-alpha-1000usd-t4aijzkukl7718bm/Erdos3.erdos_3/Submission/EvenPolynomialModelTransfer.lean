import Submission.EvenPolynomialCoordinates

/-! All-even polynomial model transfer from character discrepancy of the free
coordinates. The supplied polynomial windows may be local; no inverse theorem
or equidistribution conclusion for arbitrary sets is assumed. -/
namespace Erdos3EvenPolynomialModelTransfer
open Finset Erdos3FourierMultilinearTransfer Erdos3EvenPolynomialModel
  Erdos3EvenPolynomialCoordinates Erdos3HigherPhaseDifferences
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G X : Type*} [AddCommGroup G] [Fintype G] [Fintype X]

/-- Only character discrepancy on the 2m+1 free coordinates is needed. -/
theorem even_polynomial_transfer (m : ℕ) (f : G → ℝ) (q : X → ℕ → G)
    (hq : ∀ x, diffIter (2*m+1) (q x) 0 = 0) {ε : ℝ}
    (hdisc : ∀ χ : AddChar (G × (Fin m → G) × (Fin m → G)) ℂ,
      ‖(𝔼 x : X, χ (polynomialCoordinates m (q x)))-
        (𝔼 p : G × (Fin m → G) × (Fin m → G), χ p)‖ ≤ ε) :
    (𝔼 y : G, f y)^(2*m+2)-ε*fourierMass (fun y ↦ (f y : ℂ))^(2*m+2) ≤
      𝔼 x : X, ∏ j : Fin (2*m+2), f (q x j.val) := by
  have hd (χ : Fin (2*m+2) → AddChar G ℂ) :
      ‖(𝔼 x : X, ∏ j : Fin (2*m+2), χ j (q x j.val))-
        (𝔼 p : G × (Fin m → G) × (Fin m → G), ∏ j : Fin (2*m+2), χ j (evenPolynomial m p j.val))‖ ≤ ε := by
    have he (x : X) (j : Fin (2*m+2)) : evenPolynomial m (polynomialCoordinates m (q x)) j.val = q x j.val :=
      evenPolynomial_reconstruct m (q x) (hq x) j
    simpa only [modelCharacter_apply,he] using hdisc (modelCharacter m χ)
  have ht := multilinear_transfer_real (fun _ : Fin (2*m+2) ↦ f)
    (fun x j ↦ q x j.val) (fun p j ↦ evenPolynomial m p j.val) hd
  simp only [prod_const,card_univ,Fintype.card_fin] at ht
  have hl := even_polynomial_model_lower m f
  have he := (abs_le.mp ht).1
  linarith

lemma fourierMass_even_bound (m : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    fourierMass f^(2*m+2) ≤ (Fintype.card G : ℝ)^(m+1) := by
  have henergy : (𝔼 x : G, ‖f x‖^2) ≤ 1 := by
    calc
      _ ≤ 𝔼 _x : G, (1 : ℝ)^2 :=
        expect_le_expect (fun x _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
      _ = _ := by simp
  have hs := (fourierMass_sq_le f).trans
    (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg (Fintype.card G)))
  rw [mul_one] at hs
  rw [show 2*m+2 = 2*(m+1) by omega,pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hs (m+1)

theorem even_polynomial_transfer_bounded (m : ℕ) (f : G → ℝ) (hf : ∀ y, |f y| ≤ 1)
    (q : X → ℕ → G) (hq : ∀ x, diffIter (2*m+1) (q x) 0 = 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ : AddChar (G × (Fin m → G) × (Fin m → G)) ℂ,
      ‖(𝔼 x : X, χ (polynomialCoordinates m (q x)))-
        (𝔼 p : G × (Fin m → G) × (Fin m → G), χ p)‖ ≤ ε) :
    (𝔼 y : G, f y)^(2*m+2)-ε*(Fintype.card G : ℝ)^(m+1) ≤
      𝔼 x : X, ∏ j : Fin (2*m+2), f (q x j.val) := by
  have ht := even_polynomial_transfer m f q hq hdisc
  have hm := fourierMass_even_bound m (fun y ↦ (f y : ℂ)) (fun y ↦ by simpa using hf y)
  have he := mul_le_mul_of_nonneg_left hm hε
  linarith

#print axioms even_polynomial_transfer
#print axioms even_polynomial_transfer_bounded
end Erdos3EvenPolynomialModelTransfer
