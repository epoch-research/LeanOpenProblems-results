import Submission.CorrelationMoments
import Submission.Unbalancing

/-! Correlation-weighted moment positivity and unbalancing for localization.
These are auxiliary analytic identities, not the original conjecture. -/
namespace Erdos3WeightedCorrelation
open Finset Erdos3CorrelationMoments Erdos3FiniteSampling Erdos3Unbalancing
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma gram_product {I X Y Z : Type*} [Fintype I] [Fintype X] [Fintype Y] [Fintype Z]
    (f : I → X → Z → ℝ) (g : I → Y → Z → ℝ) :
    (𝔼 x : X, 𝔼 y : Y, ∏ i, 𝔼 z : Z, f i x z*g i y z) =
      𝔼 v : I → Z, (𝔼 x : X, ∏ i, f i x (v i))*(𝔼 y : Y, ∏ i, g i y (v i)) := by
  have he (x : X) (y : Y) : (∏ i, 𝔼 z : Z, f i x z*g i y z) =
      𝔼 v : I → Z, ∏ i, f i x (v i)*g i y (v i) :=
    (expect_pi_prod (fun i z ↦ f i x z*g i y z)).symm
  simp_rw [he, prod_mul_distrib]
  calc
    _ = 𝔼 x : X, 𝔼 v : I → Z, 𝔼 y : Y,
        (∏ i, f i x (v i))*(∏ i, g i y (v i)) := by
      apply expect_congr rfl
      intro x _
      exact expect_comm _ _ _
    _ = 𝔼 v : I → Z, 𝔼 x : X, 𝔼 y : Y,
        (∏ i, f i x (v i))*(∏ i, g i y (v i)) := expect_comm _ _ _
    _ = _ := by simp_rw [← Fintype.expect_mul_expect]

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def familyTensor {I : Type*} [Fintype I] (g : I → G → ℝ) (v : I → G) : ℝ :=
  𝔼 x : G, ∏ i, g i (x+v i)

lemma corr_product_gram {I : Type*} [Fintype I] (g : I → G → ℝ) :
    (𝔼 t : G, ∏ i, corr (g i) t) = 𝔼 v : I → G, (familyTensor g v)^2 := by
  have ht (x : G) : (𝔼 y : G, ∏ i, corr (g i) (y-x)) = 𝔼 t : G, ∏ i, corr (g i) t := by
    simpa only [sub_eq_add_neg] using expect_translate (fun t ↦ ∏ i, corr (g i) t) (-x)
  calc
    _ = 𝔼 x : G, 𝔼 y : G, ∏ i, corr (g i) (y-x) := by
      simp_rw [ht]
      exact (Fintype.expect_const _).symm
    _ = _ := by
      simp_rw [corr_gram]
      rw [gram_product]
      simp only [familyTensor, sq]

lemma conv_product_gram {I : Type*} [Fintype I] (g : I → G → ℝ) :
    (𝔼 t : G, ∏ i, conv (g i) t) =
      𝔼 v : I → G, familyTensor g v*familyTensor g (-v) := by
  have ht (x : G) : (𝔼 y : G, ∏ i, conv (g i) (x+y)) = 𝔼 t : G, ∏ i, conv (g i) t := by
    simpa only [add_comm] using expect_translate (fun t ↦ ∏ i, conv (g i) t) x
  calc
    _ = 𝔼 x : G, 𝔼 y : G, ∏ i, conv (g i) (x+y) := by
      simp_rw [ht]
      exact (Fintype.expect_const _).symm
    _ = _ := by
      simp_rw [conv_gram]
      rw [gram_product]
      simp only [familyTensor, Pi.neg_apply, sub_eq_add_neg]

lemma corr_product_nonneg {I : Type*} [Fintype I] (g : I → G → ℝ) :
    0 ≤ 𝔼 t : G, ∏ i, corr (g i) t := by
  rw [corr_product_gram]
  positivity

lemma abs_conv_product_le_corr {I : Type*} [Fintype I] (g : I → G → ℝ) :
    |𝔼 t : G, ∏ i, conv (g i) t| ≤ 𝔼 t : G, ∏ i, corr (g i) t := by
  rw [conv_product_gram, corr_product_gram]
  have h := expect_mul_sq_le_sq_mul_sq univ (fun v : I → G ↦ familyTensor g v)
    (fun v ↦ familyTensor g (-v))
  have hn : (𝔼 v : I → G, (familyTensor g (-v))^2) = 𝔼 v : I → G, (familyTensor g v)^2 :=
    Fintype.expect_equiv (Equiv.neg (I → G)) _ _ (fun _ ↦ rfl)
  rw [hn, ← sq] at h
  exact abs_le_of_sq_le_sq h (by positivity)

/-- All integer moments of a correlation remain nonnegative under a correlation weight. -/
theorem weighted_corr_moment_nonneg (g h : G → ℝ) (p : ℕ) :
    0 ≤ 𝔼 t : G, corr h t*(corr g t)^p := by
  let f : Option (Fin p) → G → ℝ := fun i ↦ i.elim h (fun _ ↦ g)
  simpa only [Fintype.prod_option, f, Option.elim_none, Option.elim_some, prod_const,
    card_univ, Fintype.card_fin] using corr_product_nonneg f

theorem abs_weighted_conv_moment_le (g h : G → ℝ) (p : ℕ) :
    |𝔼 t : G, conv h t*(conv g t)^p| ≤ 𝔼 t : G, corr h t*(corr g t)^p := by
  let f : Option (Fin p) → G → ℝ := fun i ↦ i.elim h (fun _ ↦ g)
  simpa only [Fintype.prod_option, f, Option.elim_none, Option.elim_some, prod_const,
    card_univ, Fintype.card_fin] using abs_conv_product_le_corr f

lemma conv_eq_corr_of_even (h : G → ℝ) (hh : ∀ x, h (-x) = h x) (t : G) :
    conv h t = corr h t := by
  calc
    _ = 𝔼 y : G, h (-y)*h (t+y) :=
      Fintype.expect_equiv (Equiv.neg G) _ _ (fun y ↦ by simp [sub_eq_add_neg])
    _ = _ := by
      unfold corr
      simp only [hh, add_comm]

lemma weighted_comparison_of_even (g h : G → ℝ) (hh : ∀ x, h (-x) = h x) (p : ℕ) :
    |𝔼 t : G, corr h t*(conv g t)^p| ≤ 𝔼 t : G, corr h t*(corr g t)^p := by
  simpa only [conv_eq_corr_of_even h hh] using abs_weighted_conv_moment_le g h p

lemma mean_corr (h : G → ℝ) : (𝔼 t : G, corr h t) = (𝔼 x : G, h x)^2 := by
  unfold corr
  rw [expect_comm]
  have ht (y : G) : (𝔼 x : G, h (y+x)) = 𝔼 x : G, h x := by
    simpa only [add_comm] using expect_translate h y
  simp_rw [← mul_expect, ht]
  rw [← expect_mul, sq]

/-- Weighted unbalancing only needs positivity of the weighted moments. -/
lemma weighted_unbalance {X : Type*} [Fintype X] (w g : X → ℝ)
    {p r : ℕ} (hr : 0 < r) {e M : ℝ} (he : 0 ≤ e) (hM : 0 ≤ M)
    (hp : M*e^p ≤ 𝔼 x, w x*(g x)^p)
    (hg : ∀ j ≤ r*p, 0 ≤ 𝔼 x, w x*(g x)^j) :
    M*((r : ℝ)*e)^p ≤ 𝔼 x, w x*(1+g x)^(r*p) := by
  have hpr : p ≤ r*p := by nlinarith
  have hchoose : (r : ℝ)^p ≤ ((r*p).choose p : ℝ) := by exact_mod_cast pow_le_choose_mul r p
  have hexpand : (𝔼 x, w x*(1+g x)^(r*p)) =
      ∑ j ∈ range (r*p+1), (𝔼 x, w x*(g x)^j)*((r*p).choose j : ℝ) := by
    simp_rw [add_comm (1 : ℝ), add_pow, one_pow, mul_one, mul_sum, ← mul_assoc]
    rw [expect_sum_comm]
    simp_rw [← expect_mul]
  rw [hexpand]
  calc
    M*((r : ℝ)*e)^p = (r : ℝ)^p*(M*e^p) := by rw [mul_pow]; ring
    _ ≤ ((r*p).choose p : ℝ)*(𝔼 x, w x*(g x)^p) :=
      mul_le_mul hchoose hp (mul_nonneg hM (pow_nonneg he _)) (Nat.cast_nonneg _)
    _ = (𝔼 x, w x*(g x)^p)*((r*p).choose p : ℝ) := mul_comm _ _
    _ ≤ _ := single_le_sum (fun j hj ↦ mul_nonneg (hg j (by simpa using hj))
      (Nat.cast_nonneg _)) (mem_range.mpr (by omega))

lemma weighted_unbalance_half {X : Type*} [Fintype X] (w g : X → ℝ) {p : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hp : M*(1/2 : ℝ)^p ≤ 𝔼 x, w x*(g x)^p)
    (hg : ∀ j ≤ 8*p, 0 ≤ 𝔼 x, w x*(g x)^j) :
    M*(9/8 : ℝ)^(8*p) ≤ 𝔼 x, w x*(1+g x)^(8*p) := by
  have h := weighted_unbalance w g (r := 8) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1/2) hM hp hg
  norm_num only [Nat.cast_ofNat, show (8 : ℝ)*(1/2) = 4 by norm_num] at h
  calc
    _ = M*((9/8 : ℝ)^8)^p := by rw [pow_mul]
    _ ≤ M*(4 : ℝ)^p := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by norm_num) _) hM
    _ ≤ _ := h

#print axioms weighted_corr_moment_nonneg
#print axioms weighted_comparison_of_even
#print axioms weighted_unbalance_half
end Erdos3WeightedCorrelation
