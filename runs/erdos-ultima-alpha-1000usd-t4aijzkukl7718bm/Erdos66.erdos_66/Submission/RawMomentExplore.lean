import Submission.MomentExplore

/-!
# A finite self-convolution cannot converge in moments to the uniform interval law

An auxiliary obstruction to a flat-prefix construction, not a disproof of Erdős 66.
-/

namespace Erdos66RawMoment
open Filter Erdos66Moment
open scoped Topology

variable {X : Type*}

noncomputable def avg (A : Finset X) (f : X → ℝ) : ℝ := (∑ a ∈ A, f a) / A.card

lemma avg_add (A : Finset X) (f g : X → ℝ) :
    avg A (fun a ↦ f a + g a) = avg A f + avg A g := by
  simp only [avg, Finset.sum_add_distrib, add_div]

lemma avg_sub (A : Finset X) (f g : X → ℝ) :
    avg A (fun a ↦ f a - g a) = avg A f - avg A g := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

lemma avg_const_mul (A : Finset X) (c : ℝ) (f : X → ℝ) :
    avg A (fun a ↦ c * f a) = c * avg A f := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

lemma avg_const (A : Finset X) (hA : A.Nonempty) (c : ℝ) : avg A (fun _ ↦ c) = c := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  simp only [avg, Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard]

lemma avg_center_sq (A : Finset X) (hA : A.Nonempty) (f : X → ℝ) :
    avg A (fun a ↦ (f a - avg A f) ^ 2) = avg A (fun a ↦ (f a) ^ 2) - (avg A f) ^ 2 := by
  have hp (a : X) : (f a - avg A f) ^ 2 =
      (f a) ^ 2 - (2 * avg A f) * f a + (avg A f) ^ 2 := by ring
  simp only [hp, avg_add, avg_sub, avg_const_mul, avg_const A hA]
  ring

lemma avg_center_fourth (A : Finset X) (hA : A.Nonempty) (f : X → ℝ) :
    avg A (fun a ↦ (f a - avg A f) ^ 4) =
      avg A (fun a ↦ (f a) ^ 4) - 4 * avg A f * avg A (fun a ↦ (f a) ^ 3) +
      6 * (avg A f) ^ 2 * avg A (fun a ↦ (f a) ^ 2) - 3 * (avg A f) ^ 4 := by
  have hp (a : X) : (f a - avg A f) ^ 4 =
      (f a) ^ 4 - (4 * avg A f) * (f a) ^ 3 +
      (6 * (avg A f) ^ 2) * (f a) ^ 2 - (4 * (avg A f) ^ 3) * f a + (avg A f) ^ 4 := by ring
  simp only [hp, avg_add, avg_sub, avg_const_mul, avg_const A hA]
  ring

noncomputable def pairMoment (A : Finset X) (x : X → ℝ) (k : ℕ) : ℝ :=
  avg (A ×ˢ A) (fun ab ↦ (x ab.1 + x ab.2) ^ k)

lemma pair_first (A : Finset X) (hA : A.Nonempty) (x : X → ℝ) :
    avg (A ×ˢ A) (fun ab ↦ x ab.1 + x ab.2) = 2 * avg A x := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  simp only [avg, Finset.sum_product, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, Finset.card_product, Nat.cast_mul]
  field_simp
  ring

lemma pair_normalized_kurtosis (A : Finset X) (hA : A.Nonempty) (x : X → ℝ) :
    2 * (avg (A ×ˢ A) (fun ab ↦ (x ab.1 + x ab.2 - 2 * avg A x) ^ 2)) ^ 2 ≤
      avg (A ×ˢ A) (fun ab ↦ (x ab.1 + x ab.2 - 2 * avg A x) ^ 4) := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  have halg (u v m : ℝ) (hm : m ≠ 0) (h : 2 * u ^ 2 ≤ m ^ 2 * v) :
      2 * (u / m ^ 2) ^ 2 ≤ v / m ^ 2 := by
    have hh := div_le_div_of_nonneg_right h (sq_nonneg (m ^ 2))
    convert hh using 1 <;> field_simp <;> ring
  have hh := halg _ _ _ hcard (centered_pair_kurtosis_bound A x)
  simpa only [avg, Finset.sum_product, Finset.card_product, Nat.cast_mul,
    ← mul_div_assoc, ← pow_two, Nat.cast_pow] using hh

lemma pair_raw_moment_inequality (A : Finset X) (hA : A.Nonempty) (x : X → ℝ) :
    0 ≤ pairMoment A x 4 - 4 * pairMoment A x 1 * pairMoment A x 3 +
      10 * (pairMoment A x 1) ^ 2 * pairMoment A x 2 -
      5 * (pairMoment A x 1) ^ 4 - 2 * (pairMoment A x 2) ^ 2 := by
  have h := pair_normalized_kurtosis A hA x
  rw [← pair_first A hA x, avg_center_sq _ (hA.product hA), avg_center_fourth _ (hA.product hA)] at h
  simp only [pairMoment, pow_one]
  nlinarith [h]

/-- The first four moments of these self-convolutions cannot converge to those of `[0,1]`. -/
lemma not_uniform_moment_limits (A : ℕ → Finset X) (hA : ∀ n, (A n).Nonempty)
    (x : ℕ → X → ℝ)
    (h1 : Tendsto (fun n ↦ pairMoment (A n) (x n) 1) atTop (𝓝 (1 / 2)))
    (h2 : Tendsto (fun n ↦ pairMoment (A n) (x n) 2) atTop (𝓝 (1 / 3)))
    (h3 : Tendsto (fun n ↦ pairMoment (A n) (x n) 3) atTop (𝓝 (1 / 4)))
    (h4 : Tendsto (fun n ↦ pairMoment (A n) (x n) 4) atTop (𝓝 (1 / 5))) : False := by
  have hh := (((h4.sub ((h1.const_mul 4).mul h3)).add
    (((h1.pow 2).const_mul 10).mul h2)).sub ((h1.pow 4).const_mul 5)).sub
      ((h2.pow 2).const_mul 2)
  norm_num at hh
  have hnon := ge_of_tendsto hh (Filter.Eventually.of_forall
    (fun n ↦ pair_raw_moment_inequality (A n) (hA n) (x n)))
  norm_num at hnon

lemma pair_raw_moment_inequality_all (A : Finset X) (x : X → ℝ) :
    0 ≤ pairMoment A x 4 - 4 * pairMoment A x 1 * pairMoment A x 3 +
      10 * (pairMoment A x 1) ^ 2 * pairMoment A x 2 -
      5 * (pairMoment A x 1) ^ 4 - 2 * (pairMoment A x 2) ^ 2 := by
  by_cases hA : A.Nonempty
  · exact pair_raw_moment_inequality A hA x
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp [pairMoment, avg]

lemma not_uniform_moment_limits_any (A : ℕ → Finset X) (x : ℕ → X → ℝ)
    (h1 : Tendsto (fun n ↦ pairMoment (A n) (x n) 1) atTop (𝓝 (1 / 2)))
    (h2 : Tendsto (fun n ↦ pairMoment (A n) (x n) 2) atTop (𝓝 (1 / 3)))
    (h3 : Tendsto (fun n ↦ pairMoment (A n) (x n) 3) atTop (𝓝 (1 / 4)))
    (h4 : Tendsto (fun n ↦ pairMoment (A n) (x n) 4) atTop (𝓝 (1 / 5))) : False := by
  have hh := (((h4.sub ((h1.const_mul 4).mul h3)).add
    (((h1.pow 2).const_mul 10).mul h2)).sub ((h1.pow 4).const_mul 5)).sub
      ((h2.pow 2).const_mul 2)
  norm_num at hh
  have hnon := ge_of_tendsto hh (Filter.Eventually.of_forall
    (fun n ↦ pair_raw_moment_inequality_all (A n) (x n)))
  norm_num at hnon

end Erdos66RawMoment
