import Submission.CorrelationSifting
import Submission.Unbalancing

/-! From a three-term-progression-free set to a sifted set of popular differences.
This is an auxiliary finite-group step, not a proof of Erdős Problem 3. -/
namespace Erdos3ThreeAPSifting
open Finset Erdos3CorrelationMoments Erdos3CorrelationSifting Erdos3Unbalancing
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma conv_indicator_double (A : Finset G) (hfree : ThreeAPFree (A : Set G))
    {a : G} (ha : a ∈ A) : conv (indicator A) (a+a) = 1 / (Fintype.card G : ℝ) := by
  have hp (y : G) : indicator A y * indicator A (a+a-y) =
      if y = a then (1 : ℝ) else 0 := by
    by_cases hya : y = a
    · subst y
      simp [indicator, ha]
    · by_cases hy : y ∈ A
      · have hn : a+a-y ∉ A := by
          intro hc
          exact hya (hfree hy ha hc (by abel))
        simp [indicator, hya, hn]
      · simp [indicator, hy, hya]
  unfold conv
  simp_rw [hp]
  rw [Fintype.expect_eq_sum_div_card]
  simp

omit [Fintype G] in
lemma double_injOn (A : Finset G) (hfree : ThreeAPFree (A : Set G)) :
    (A : Set G).InjOn (fun x ↦ x+x) := by
  intro x hx y hy hxy
  exact hfree hx hy hx hxy

lemma density_mul_le_expect (A : Finset G) (hfree : ThreeAPFree (A : Set G))
    (f : G → ℝ) {c : ℝ} (hf : ∀ x, 0 ≤ f x) (hc : ∀ a ∈ A, c ≤ f (a+a)) :
    density A*c ≤ 𝔼 x : G, f x := by
  have hsum : (A.card : ℝ)*c ≤ ∑ x : G, f x := by
    calc
      _ = ∑ _a ∈ A, c := by simp
      _ ≤ ∑ a ∈ A, f (a+a) := sum_le_sum hc
      _ = ∑ x ∈ A.image (fun a ↦ a+a), f x := by
        rw [sum_image (double_injOn A hfree)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ ↦ hf x)
  rw [Fintype.expect_eq_sum_div_card]
  calc
    density A*c = ((A.card : ℝ)*c)/(Fintype.card G : ℝ) := by unfold density; ring
    _ ≤ _ := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

lemma conv_normalized_double_le (A : Finset G) (hfree : ThreeAPFree (A : Set G))
    (hsize : 4 ≤ (Fintype.card G : ℝ)*(density A)^2) {a : G} (ha : a ∈ A) :
    conv (normalized A) (a+a) ≤ 1/4 := by
  rw [conv_normalized, conv_indicator_double A hfree ha, div_div]
  exact one_div_le_one_div_of_le (by norm_num) hsize

/-- When the set is large enough, the normalized convolution is at most 1/4 at its doubles.
An even centered moment then detects a deficit of at least 3/4 there. -/
lemma centered_moment_lower (A : Finset G) (hfree : ThreeAPFree (A : Set G))
    (hsize : 4 ≤ (Fintype.card G : ℝ)*(density A)^2)
    {p : ℕ} (hp : Even p) :
    density A*(3/4 : ℝ)^p ≤ 𝔼 x : G, (conv (normalized A) x - 1)^p := by
  apply density_mul_le_expect A hfree _ (fun x ↦ hp.pow_nonneg _) _
  intro a ha
  have h := conv_normalized_double_le A hfree hsize ha
  have heq : (conv (normalized A) (a+a)-1)^p =
      (1-conv (normalized A) (a+a))^p := by
    rw [show conv (normalized A) (a+a)-1 = -(1-conv (normalized A) (a+a)) by ring,
      hp.neg_pow]
  rw [heq]
  exact pow_le_pow_left₀ (by norm_num) (by linarith) p

lemma large_corr_moment (A : Finset G) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set G))
    (hsize : 4 ≤ (Fintype.card G : ℝ)*(density A)^2)
    {p : ℕ} (hp : Even p) (hdensity : (2/3 : ℝ)^p ≤ density A) :
    (9/8 : ℝ)^(8*p) ≤ 𝔼 x : G, (corr (normalized A) x)^(8*p) := by
  apply corr_moment_of_conv_center (normalized A) (expect_normalized A hA)
  calc
    (1/2 : ℝ)^p = (2/3 : ℝ)^p*(3/4 : ℝ)^p := by rw [← mul_pow]; norm_num
    _ ≤ density A*(3/4 : ℝ)^p := mul_le_mul_of_nonneg_right hdensity (by positivity)
    _ ≤ 𝔼 x : G, (conv (normalized A) x - 1)^p := centered_moment_lower A hfree hsize hp
    _ ≤ _ := le_abs_self _

/-- Sifting a sufficiently large 3AP-free set produces an intersection B of 8p translates,
with density at least α^(8p)/2. All but at most 2(17/18)^(8p) of its ordered pairs have
normalized autocorrelation greater than 17/16 at their difference. -/
theorem sift_threeAPFree (A : Finset G) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set G))
    (hsize : 4 ≤ (Fintype.card G : ℝ)*(density A)^2)
    {p : ℕ} (hp : Even p) (hdensity : (2/3 : ℝ)^p ≤ density A) :
    ∃ v : Fin (8*p) → G,
      (common A v).Nonempty ∧
      (density A)^(8*p) ≤ 2*density (common A v) ∧
      pairDensity (common A v) (fun t ↦ if corr (normalized A) t ≤ 17/16 then 1 else 0) ≤
        2*(17/18 : ℝ)^(8*p)*(density (common A v))^2 := by
  obtain ⟨v,hvne,hvs,hvb⟩ := exists_normalized_sifted_intersection A hA (8*p)
    (L := 17/16) (H := 9/8) (by norm_num) (by norm_num)
    (large_corr_moment A hA hfree hsize hp hdensity)
  refine ⟨v,hvne,?_,?_⟩
  · have hsq : ((density A)^(8*p))^2 ≤ 2*(density (common A v))^2 := by
      calc
        _ = (density A)^(2*(8*p)) := by rw [← pow_mul]; congr 1; omega
        _ ≤ (density A)^(2*(8*p))*(9/8 : ℝ)^(8*p) :=
          le_mul_of_one_le_right (pow_nonneg (density_nonneg A) _)
            (one_le_pow₀ (by norm_num))
        _ ≤ _ := hvs
    apply (pow_le_pow_iff_left₀ (pow_nonneg (density_nonneg A) _)
      (mul_nonneg (by norm_num) (density_nonneg _)) (by decide : 2 ≠ 0)).mp
    nlinarith [sq_nonneg (density (common A v))]
  · norm_num only [show (17/16 : ℝ)/(9/8) = 17/18 by norm_num] at hvb
    exact hvb

#print axioms centered_moment_lower
#print axioms large_corr_moment
#print axioms sift_threeAPFree
end Erdos3ThreeAPSifting
