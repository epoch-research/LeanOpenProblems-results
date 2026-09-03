import Submission.FourierMultilinearTransfer
import Submission.QuadraticModelCounting

/-! Transfers the positive pure-quadratic model under an explicit character
discrepancy hypothesis for the first three values. This is a conditional
counting theorem, not an inverse theorem for arbitrary sets. -/
namespace Erdos3QuadraticModelTransfer
open Finset Erdos3FourierMultilinearTransfer Erdos3QuadraticModelCounting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {X : Type*} [Fintype X]

lemma four_characters_relation (χ : Fin 4 → AddChar G ℂ) (a b c : G) :
    χ 0 a*χ 1 b*χ 2 c*χ 3 (a-3 • b+3 • c) =
      (χ 0*χ 3) a*(χ 1/(χ 3)^3) b*(χ 2*(χ 3)^3) c := by
  simp only [AddChar.mul_apply,AddChar.div_apply,AddChar.inv_apply,AddChar.pow_apply,
    AddChar.map_add_eq_mul,AddChar.map_sub_eq_div,AddChar.map_nsmul_eq_pow,
    AddChar.map_neg_eq_inv,inv_pow,div_eq_mul_inv]
  ring

/-- The only discrepancy input concerns the joint distribution of the first
three values. The fourth is forced by the vanishing third difference. -/
theorem quadratic_model_transfer (f : G → ℝ) (a b c d : X → G)
    (hrel : ∀ x, d x = a x-3 • b x+3 • c x) {ε : ℝ}
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 x : X, χ₀ (a x)*χ₁ (b x)*χ₂ (c x))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    |(𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x))-quadraticModelCount f| ≤
      ε*fourierMass (fun y ↦ (f y : ℂ))^4 := by
  let v : X → Fin 4 → G := fun x ↦ ![a x,b x,c x,d x]
  let w : G × G × G → Fin 4 → G := fun p ↦ ![p.1,p.2.1,p.2.2,p.1-3 • p.2.1+3 • p.2.2]
  have hd (χ : Fin 4 → AddChar G ℂ) :
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 p : G × G × G, ∏ i, χ i (w p i))‖ ≤ ε := by
    have hv (x : X) : (∏ i : Fin 4, χ i (v x i)) =
        (χ 0*χ 3) (a x)*(χ 1/(χ 3)^3) (b x)*(χ 2*(χ 3)^3) (c x) := by
      rw [Fin.prod_univ_four]
      change χ 0 (a x)*χ 1 (b x)*χ 2 (c x)*χ 3 (d x) = _
      rw [hrel x]
      exact four_characters_relation χ (a x) (b x) (c x)
    have hw (p : G × G × G) : (∏ i : Fin 4, χ i (w p i)) =
        (χ 0*χ 3) p.1*(χ 1/(χ 3)^3) p.2.1*(χ 2*(χ 3)^3) p.2.2 := by
      rw [Fin.prod_univ_four]
      exact four_characters_relation χ p.1 p.2.1 p.2.2
    simp only [hv,hw]
    exact hdisc (χ 0*χ 3) (χ 1/(χ 3)^3) (χ 2*(χ 3)^3)
  have h := multilinear_transfer_real (I := Fin 4) (fun _ ↦ f) v w hd
  have hw : (𝔼 p : G × G × G, ∏ i : Fin 4, f (w p i)) = quadraticModelCount f := by
    simp only [Fin.prod_univ_four,w,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,expect_triple]
    exact (quadraticModelCount_eq_balanced f).symm
  rw [hw] at h
  simpa only [Fin.prod_univ_four,v,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,prod_const,card_univ,Fintype.card_fin] using h

theorem quadratic_model_lower (f : G → ℝ) (a b c d : X → G)
    (hrel : ∀ x, d x = a x-3 • b x+3 • c x) {ε : ℝ}
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 x : X, χ₀ (a x)*χ₁ (b x)*χ₂ (c x))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : G, f y)^4-ε*fourierMass (fun y ↦ (f y : ℂ))^4 ≤
      𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x) := by
  have h := (abs_le.mp (quadratic_model_transfer f a b c d hrel hdisc)).1
  have hl := quadraticModelCount_lower f
  linarith

/-- A coarser bound removes the Fourier mass for any unit-bounded observable. -/
theorem quadratic_model_lower_bounded (f : G → ℝ) (hf : ∀ y, |f y| ≤ 1)
    (a b c d : X → G) (hrel : ∀ x, d x = a x-3 • b x+3 • c x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : ∀ χ₀ χ₁ χ₂ : AddChar G ℂ,
      ‖(𝔼 x : X, χ₀ (a x)*χ₁ (b x)*χ₂ (c x))-
        (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε) :
    (𝔼 y : G, f y)^4-ε*(Fintype.card G : ℝ)^2 ≤
      𝔼 x : X, f (a x)*f (b x)*f (c x)*f (d x) := by
  have hm := fourierMass_four_le (fun y ↦ (f y : ℂ)) (fun y ↦ by simpa using hf y)
  have ht := quadratic_model_lower f a b c d hrel hdisc
  have he := mul_le_mul_of_nonneg_left hm hε
  linarith

#print axioms quadratic_model_transfer
#print axioms quadratic_model_lower_bounded
end Erdos3QuadraticModelTransfer
