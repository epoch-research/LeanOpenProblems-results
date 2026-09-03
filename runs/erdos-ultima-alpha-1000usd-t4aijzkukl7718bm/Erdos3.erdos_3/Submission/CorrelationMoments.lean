import Submission.FiniteSampling

/-! Finite Gram identities for convolution and autocorrelation moments.
These are auxiliary results, not a settlement of Erdős Problem 3. -/
namespace Erdos3CorrelationMoments
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

lemma expect_pow_eq {Z : Type*} [Fintype Z] (f : Z → ℝ) (p : ℕ) :
    (𝔼 z, f z)^p = 𝔼 v : Fin p → Z, ∏ i, f (v i) := by
  simpa using expect_pow (univ : Finset Z) f p

lemma gram_moment {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (f : X → Z → ℝ) (g : Y → Z → ℝ) (p : ℕ) :
    (𝔼 x, 𝔼 y, (𝔼 z, f x z * g y z)^p) =
      𝔼 v : Fin p → Z, (𝔼 x, ∏ i, f x (v i)) * (𝔼 y, ∏ i, g y (v i)) := by
  simp_rw [expect_pow_eq, prod_mul_distrib]
  calc
    _ = 𝔼 x : X, 𝔼 v : Fin p → Z, 𝔼 y : Y,
          (∏ i, f x (v i)) * ∏ i, g y (v i) := by
      apply expect_congr rfl
      intro x _
      exact expect_comm _ _ _
    _ = 𝔼 v : Fin p → Z, 𝔼 x : X, 𝔼 y : Y,
          (∏ i, f x (v i)) * ∏ i, g y (v i) := expect_comm _ _ _
    _ = _ := by simp_rw [← Fintype.expect_mul_expect]

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def corr (g : G → ℝ) (x : G) : ℝ := 𝔼 y : G, g y * g (y+x)
noncomputable def conv (g : G → ℝ) (x : G) : ℝ := 𝔼 y : G, g y * g (x-y)
noncomputable def tensorMean {I : Type*} [Fintype I] (g : G → ℝ) (v : I → G) : ℝ :=
  𝔼 x : G, ∏ i, g (x+v i)

lemma expect_translate (g : G → ℝ) (s : G) : (𝔼 x, g (x+s)) = 𝔼 x, g x :=
  Fintype.expect_equiv (Equiv.addRight s) (fun x ↦ g (x+s)) g (fun _ ↦ rfl)

lemma corr_gram (g : G → ℝ) (x y : G) :
    corr g (y-x) = 𝔼 z, g (x+z)*g (y+z) := by
  unfold corr
  rw [← expect_translate (fun z ↦ g z * g (z+(y-x))) x]
  apply expect_congr rfl
  intro z _
  congr 2 <;> abel

lemma conv_gram (g : G → ℝ) (x y : G) :
    conv g (x+y) = 𝔼 z, g (x+z)*g (y-z) := by
  unfold conv
  rw [← expect_translate (fun z ↦ g z * g (x+y-z)) x]
  apply expect_congr rfl
  intro z _
  congr 2 <;> abel

lemma corr_moment_gram (g : G → ℝ) (p : ℕ) :
    (𝔼 x, (corr g x)^p) = 𝔼 v : Fin p → G, (tensorMean g v)^2 := by
  calc
    _ = 𝔼 x : G, 𝔼 y : G, (corr g (y-x))^p := by
      have ht (x : G) : (𝔼 y : G, (corr g (y-x))^p) = 𝔼 y, (corr g y)^p :=
        by simpa only [sub_eq_add_neg] using expect_translate (fun y ↦ (corr g y)^p) (-x)
      simp_rw [ht]
      exact (Fintype.expect_const _).symm
    _ = 𝔼 x : G, 𝔼 y : G, (𝔼 z : G, g (x+z)*g (y+z))^p := by
      simp_rw [corr_gram]
    _ = _ := by
      rw [gram_moment]
      simp only [tensorMean, sq]

lemma conv_moment_gram (g : G → ℝ) (p : ℕ) :
    (𝔼 x, (conv g x)^p) =
      𝔼 v : Fin p → G, tensorMean g v * tensorMean g (-v) := by
  calc
    _ = 𝔼 x : G, 𝔼 y : G, (conv g (x+y))^p := by
      have ht (x : G) : (𝔼 y : G, (conv g (x+y))^p) = 𝔼 y, (conv g y)^p := by
        simpa only [add_comm] using expect_translate (fun y ↦ (conv g y)^p) x
      simp_rw [ht]
      exact (Fintype.expect_const _).symm
    _ = 𝔼 x : G, 𝔼 y : G, (𝔼 z : G, g (x+z)*g (y-z))^p := by
      simp_rw [conv_gram]
    _ = _ := by
      rw [gram_moment]
      simp only [tensorMean, sub_eq_add_neg, Pi.neg_apply]

lemma corr_moment_nonneg (g : G → ℝ) (p : ℕ) : 0 ≤ 𝔼 x, (corr g x)^p := by
  rw [corr_moment_gram]
  positivity

lemma abs_conv_moment_le_corr (g : G → ℝ) (p : ℕ) :
    |𝔼 x, (conv g x)^p| ≤ 𝔼 x, (corr g x)^p := by
  rw [conv_moment_gram, corr_moment_gram]
  have h := expect_mul_sq_le_sq_mul_sq univ
    (fun v : Fin p → G ↦ tensorMean g v) (fun v ↦ tensorMean g (-v))
  have hneg : (𝔼 v : Fin p → G, (tensorMean g (-v))^2) =
      𝔼 v : Fin p → G, (tensorMean g v)^2 :=
    Fintype.expect_equiv (Equiv.neg (Fin p → G)) _ _ (fun _ ↦ rfl)
  rw [hneg, ← sq] at h
  exact (abs_le_of_sq_le_sq h (by positivity))

lemma corr_center (g : G → ℝ) (c : ℝ) (x : G) :
    corr (fun y ↦ g y-c) x = corr g x - 2*c*(𝔼 y, g y) + c^2 := by
  have h (y : G) : (g y-c)*(g (y+x)-c) =
      g y*g (y+x) - c*g y - c*g (y+x) + c^2 := by ring
  unfold corr
  simp_rw [h]
  rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib,
    ← mul_expect, ← mul_expect, expect_translate, Fintype.expect_const]
  ring

lemma conv_center (g : G → ℝ) (c : ℝ) (x : G) :
    conv (fun y ↦ g y-c) x = conv g x - 2*c*(𝔼 y, g y) + c^2 := by
  have h (y : G) : (g y-c)*(g (x-y)-c) =
      g y*g (x-y) - c*g y - c*g (x-y) + c^2 := by ring
  have ht : (𝔼 y, g (x-y)) = 𝔼 y, g y :=
    Fintype.expect_equiv (Equiv.subLeft x) _ _ (fun _ ↦ rfl)
  unfold conv
  simp_rw [h]
  rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib,
    ← mul_expect, ← mul_expect, ht, Fintype.expect_const]
  ring

lemma corr_center_one (g : G → ℝ) (hg : (𝔼 y, g y) = 1) (x : G) :
    corr (fun y ↦ g y-1) x = corr g x - 1 := by rw [corr_center, hg]; ring

lemma conv_center_one (g : G → ℝ) (hg : (𝔼 y, g y) = 1) (x : G) :
    conv (fun y ↦ g y-1) x = conv g x - 1 := by rw [conv_center, hg]; ring

lemma corr_center_moment_nonneg (g : G → ℝ) (hg : (𝔼 y, g y) = 1) (p : ℕ) :
    0 ≤ 𝔼 x, (corr g x - 1)^p := by
  simpa only [corr_center_one g hg] using corr_moment_nonneg (fun y ↦ g y-1) p

lemma abs_conv_center_moment_le_corr (g : G → ℝ) (hg : (𝔼 y, g y) = 1) (p : ℕ) :
    |𝔼 x, (conv g x - 1)^p| ≤ 𝔼 x, (corr g x - 1)^p := by
  simpa only [corr_center_one g hg, conv_center_one g hg] using
    abs_conv_moment_le_corr (fun y ↦ g y-1) p

#print axioms corr_moment_nonneg
#print axioms abs_conv_moment_le_corr
#print axioms corr_center_moment_nonneg
#print axioms abs_conv_center_moment_le_corr
end Erdos3CorrelationMoments
