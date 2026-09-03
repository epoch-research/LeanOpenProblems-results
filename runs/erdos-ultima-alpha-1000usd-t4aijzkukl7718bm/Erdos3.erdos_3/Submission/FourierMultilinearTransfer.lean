import Submission.FiniteFourier

/-! Transfer of finite multilinear averages from character discrepancy. All
comparison-distribution hypotheses are explicit; no equidistribution of an
arbitrary polynomial factor is asserted. -/
namespace Erdos3FourierMultilinearTransfer
open Finset Erdos3FiniteFourier
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]

noncomputable def fourierMass (f : G → ℂ) : ℝ := ∑ χ : AddChar G ℂ, ‖hat f χ‖

lemma fourierMass_nonneg (f : G → ℂ) : 0 ≤ fourierMass f :=
  sum_nonneg (fun _ _ ↦ norm_nonneg _)

lemma fourierMass_sq_le (f : G → ℂ) :
    fourierMass f^2 ≤ (Fintype.card G : ℝ)*(𝔼 x : G, ‖f x‖^2) := by
  calc
    _ = (∑ χ : AddChar G ℂ, 1*‖hat f χ‖)^2 := by simp only [one_mul,fourierMass]
    _ ≤ (∑ _χ : AddChar G ℂ, (1 : ℝ)^2)*(∑ χ : AddChar G ℂ, ‖hat f χ‖^2) :=
      sum_mul_sq_le_sq_mul_sq ..
    _ = _ := by rw [parseval]; simp only [one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,AddChar.card_eq]

lemma fourierMass_four_le (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    fourierMass f^4 ≤ (Fintype.card G : ℝ)^2 := by
  have henergy : (𝔼 x : G, ‖f x‖^2) ≤ 1 := by
    calc
      _ ≤ 𝔼 _x : G, (1 : ℝ)^2 :=
        expect_le_expect (fun x _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
      _ = _ := by simp
  have hs := (fourierMass_sq_le f).trans
    (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg (Fintype.card G)))
  rw [mul_one] at hs
  simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg (fourierMass f)) hs 2

lemma product_expansion (f : I → G → ℂ) (v : I → G) :
    (∏ i, f i (v i)) = ∑ χ : I → AddChar G ℂ,
      (∏ i, hat (f i) (χ i))*(∏ i, χ i (v i)) := by
  calc
    _ = ∏ i, ∑ χ : AddChar G ℂ, hat (f i) χ*χ (v i) := by
      apply prod_congr rfl
      intro i _
      exact inversion (f i) (v i)
    _ = _ := by rw [Fintype.prod_sum]; simp only [prod_mul_distrib]

lemma multilinear_expansion (f : I → G → ℂ) (v : X → I → G) :
    (𝔼 x : X, ∏ i, f i (v x i)) = ∑ χ : I → AddChar G ℂ,
      (∏ i, hat (f i) (χ i))*(𝔼 x : X, ∏ i, χ i (v x i)) := by
  calc
    _ = 𝔼 x : X, ∑ χ : I → AddChar G ℂ,
        (∏ i, hat (f i) (χ i))*(∏ i, χ i (v x i)) := by
      apply expect_congr rfl
      intro x _
      exact product_expansion f (v x)
    _ = _ := by rw [expect_sum_comm]; simp only [← mul_expect]

/-- Character discrepancy transfers to products of arbitrary functions, with
loss equal to the product of their Fourier l1 masses. -/
theorem multilinear_transfer (f : I → G → ℂ) (v : X → I → G) (w : Y → I → G)
    {ε : ℝ}
    (hdisc : ∀ χ : I → AddChar G ℂ,
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i))‖ ≤ ε) :
    ‖(𝔼 x : X, ∏ i, f i (v x i))-(𝔼 y : Y, ∏ i, f i (w y i))‖ ≤
      ε*∏ i, fourierMass (f i) := by
  rw [multilinear_expansion,multilinear_expansion,← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ χ : I → AddChar G ℂ,
        ‖(∏ i, hat (f i) (χ i))*
          ((𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ χ : I → AddChar G ℂ, (∏ i, ‖hat (f i) (χ i)‖)*ε := by
      apply sum_le_sum
      intro χ _
      rw [norm_mul,norm_prod]
      exact mul_le_mul_of_nonneg_left (hdisc χ) (prod_nonneg (fun _ _ ↦ norm_nonneg _))
    _ = ε*∏ i, fourierMass (f i) := by
      rw [← sum_mul,← Fintype.prod_sum (fun i (χ : AddChar G ℂ) ↦ ‖hat (f i) χ‖)]
      exact mul_comm _ _

/-- The same comparison for real products. -/
theorem multilinear_transfer_real (f : I → G → ℝ) (v : X → I → G) (w : Y → I → G)
    {ε : ℝ}
    (hdisc : ∀ χ : I → AddChar G ℂ,
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-(𝔼 y : Y, ∏ i, χ i (w y i))‖ ≤ ε) :
    |(𝔼 x : X, ∏ i, f i (v x i))-(𝔼 y : Y, ∏ i, f i (w y i))| ≤
      ε*∏ i, fourierMass (fun a ↦ (f i a : ℂ)) := by
  have h := multilinear_transfer (fun i a ↦ (f i a : ℂ)) v w hdisc
  simpa only [← Complex.ofReal_prod,← Complex.ofReal_expect,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

#print axioms multilinear_transfer
#print axioms multilinear_transfer_real
end Erdos3FourierMultilinearTransfer
