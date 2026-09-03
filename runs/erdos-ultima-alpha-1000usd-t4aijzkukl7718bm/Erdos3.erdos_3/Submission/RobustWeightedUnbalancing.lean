import Submission.WeightedCorrelation

/-! Robust weighted unbalancing: small local centering errors preserve a moment gain.
This is an auxiliary result, not the conjecture's conclusion. -/
namespace Erdos3RobustWeightedUnbalancing
open Finset Erdos3CorrelationMoments Erdos3WeightedCorrelation
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma robust_even_power_bound {u v : ℝ} (hv : 0 ≤ v) (huv : |u-v| ≤ 1/256)
    {q : ℕ} (hq : Even q) :
    u^q ≤ (65/64 : ℝ)^q*v^q+(65/256 : ℝ)^q := by
  have habs : |u| ≤ v+1/256 := by
    rcases abs_le.mp huv with ⟨hl,hu⟩
    apply abs_le.mpr
    constructor <;> linarith
  rw [← hq.pow_abs]
  by_cases hlarge : (1/4 : ℝ) ≤ v
  · have h : |u| ≤ (65/64 : ℝ)*v := by linarith
    calc
      _ ≤ ((65/64 : ℝ)*v)^q := pow_le_pow_left₀ (abs_nonneg _) h _
      _ = (65/64 : ℝ)^q*v^q := mul_pow _ _ _
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have h : |u| ≤ (65/256 : ℝ) := by linarith
    calc
      _ ≤ (65/256 : ℝ)^q := pow_le_pow_left₀ (abs_nonneg _) h _
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma robust_power_gap {q : ℕ} (hq : 2 ≤ q) :
    (65/64 : ℝ)^q*(17/16 : ℝ)^q+(65/256 : ℝ)^q ≤ (9/8 : ℝ)^q := by
  let a : ℝ := (65/64)*(17/16)
  let b : ℝ := 65/256
  let c : ℝ := 9/8
  have ha0 : 0 ≤ a/c := by norm_num [a,c]
  have ha1 : a/c ≤ 1 := by norm_num [a,c]
  have hb0 : 0 ≤ b/c := by norm_num [b,c]
  have hb1 : b/c ≤ 1 := by norm_num [b,c]
  have hsq : (a/c)^2+(b/c)^2 ≤ 1 := by norm_num [a,b,c]
  have hpow : (a/c)^q+(b/c)^q ≤ 1 := by
    have h₁ := pow_le_pow_of_le_one ha0 ha1 hq
    have h₂ := pow_le_pow_of_le_one hb0 hb1 hq
    linarith
  rw [div_pow a c, div_pow b c, ← add_div, div_le_one (pow_pos (by norm_num [c]) _)] at hpow
  simpa only [a,b,c,mul_pow] using hpow

/-- Under a probability weight, a 1/256 pointwise error on the support still leaves
a 17/16 moment gain after a 9/8 gain for an even moment. -/
theorem weighted_moment_transfer {X : Type*} [Fintype X]
    (w u v : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hmean : (𝔼 x, w x) = 1)
    (hv : ∀ x, 0 ≤ v x) (hclose : ∀ x, w x ≠ 0 → |u x-v x| ≤ 1/256)
    {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hu : (9/8 : ℝ)^q ≤ 𝔼 x, w x*(u x)^q) :
    (17/16 : ℝ)^q ≤ 𝔼 x, w x*(v x)^q := by
  have hbound : (𝔼 x, w x*(u x)^q) ≤
      (65/64 : ℝ)^q*(𝔼 x, w x*(v x)^q)+(65/256 : ℝ)^q := by
    calc
      _ ≤ 𝔼 x, ((65/64 : ℝ)^q*(w x*(v x)^q)+(65/256 : ℝ)^q*w x) := by
        apply expect_le_expect
        intro x _
        by_cases hx : w x = 0
        · simp [hx]
        · have h := mul_le_mul_of_nonneg_left (robust_even_power_bound (hv x) (hclose x hx) hq) (hw x)
          convert h using 1 <;> ring
      _ = _ := by rw [expect_add_distrib, ← mul_expect, ← mul_expect, hmean, mul_one]
  have hgap := robust_power_gap hq2
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (65/64 : ℝ)^q)).mp
  linarith [hu.trans hbound]

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma weighted_comparison_div (g h : G → ℝ) (hh : ∀ x, h (-x) = h x)
    {β : ℝ} (hβ : 0 < β) (p : ℕ) :
    |𝔼 t : G, corr h t*(conv g t/β)^p| ≤ 𝔼 t : G, corr h t*(corr g t/β)^p := by
  simp_rw [div_pow, ← mul_div_assoc, ← expect_div]
  rw [abs_div, abs_of_pos (pow_pos hβ _)]
  exact div_le_div_of_nonneg_right (weighted_comparison_of_even g h hh p) (pow_pos hβ _).le

lemma weighted_corr_div_moment_nonneg (g h : G → ℝ) {β : ℝ} (hβ : 0 < β) (p : ℕ) :
    0 ≤ 𝔼 t : G, corr h t*(corr g t/β)^p := by
  simp_rw [div_pow, ← mul_div_assoc, ← expect_div]
  exact div_nonneg (weighted_corr_moment_nonneg g h p) (pow_pos hβ _).le

/-- A weighted centered-convolution deficit produces a large local correlation moment,
provided the local centering error is at most β/256 on the weight's support. -/
theorem local_weighted_unbalance (f g h : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hh : ∀ x, 0 ≤ h x) (hme : (𝔼 x : G, h x) = 1)
    (heven : ∀ x, h (-x) = h x) {β : ℝ} (hβ : 0 < β) {p : ℕ} (hp : 0 < p)
    (hdeficit : (1/2 : ℝ)^p ≤ |𝔼 t : G, corr h t*(conv g t/β)^p|)
    (hcenter : ∀ t, corr h t ≠ 0 → |corr g t-(corr f t-β)| ≤ β/256) :
    (17/16 : ℝ)^(8*p) ≤ 𝔼 t : G, corr h t*(corr f t/β)^(8*p) := by
  have hpos (t : G) : 0 ≤ corr h t := expect_nonneg (fun x _ ↦ mul_nonneg (hh x) (hh _))
  have hmeanw : (𝔼 t : G, corr h t) = 1 := by rw [mean_corr, hme]; norm_num
  have hmoment := hdeficit.trans (weighted_comparison_div g h heven hβ p)
  have hu : (9/8 : ℝ)^(8*p) ≤ 𝔼 t : G, corr h t*(1+corr g t/β)^(8*p) := by
    have h := weighted_unbalance_half (fun t ↦ corr h t) (fun t ↦ corr g t/β)
      (M := 1) (by norm_num) (by simpa only [one_mul] using hmoment)
      (fun j _ ↦ weighted_corr_div_moment_nonneg g h hβ j)
    simpa only [one_mul] using h
  apply weighted_moment_transfer (fun t ↦ corr h t) (fun t ↦ 1+corr g t/β)
    (fun t ↦ corr f t/β) hpos hmeanw
    (fun t ↦ div_nonneg (expect_nonneg (fun x _ ↦ mul_nonneg (hf x) (hf _))) hβ.le)
    _ (show Even (8*p) from ⟨4*p, by omega⟩) (by omega) hu
  intro t ht
  have heq : 1+corr g t/β-corr f t/β = (corr g t-(corr f t-β))/β := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hβ]
  apply (div_le_iff₀ hβ).mpr
  nlinarith [hcenter t ht]

#print axioms weighted_moment_transfer
#print axioms local_weighted_unbalance
end Erdos3RobustWeightedUnbalancing
