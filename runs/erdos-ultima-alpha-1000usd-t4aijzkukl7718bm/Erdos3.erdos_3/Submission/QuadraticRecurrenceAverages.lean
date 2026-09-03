import Submission.LinearFormsUniformity

/-! Elementary finite averaging estimates for quantitative single-phase
quadratic recurrence. These lemmas do not assert the Erdős conjecture. -/
namespace Erdos3QuadraticRecurrenceAverages
open Finset Erdos3FiniteFourier Erdos3FiniteSamplingMoments
  Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

lemma norm_mean_sq_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℂ) :
    ‖𝔼 i, f i‖^2 ≤ 𝔼 i, ‖f i‖^2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_expect_le (K := ℂ)) 2).trans
    (expect_even_pow_le (by decide : Even 2) _)

lemma norm_mean_sq_pair {I : Type*} [Fintype I] (f : I → ℂ) :
    ‖𝔼 i, f i‖^2 = 𝔼 i, 𝔼 j, (f i*conj (f j)).re := by
  have h : (𝔼 i, 𝔼 j, f i*conj (f j)) = ((‖𝔼 i, f i‖^2 : ℝ) : ℂ) := by
    simp_rw [← mul_expect]
    rw [← expect_mul, ← expect_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hh := congrArg Complex.re h
  simpa only [expect_re, Complex.ofReal_re] using hh.symm

lemma mean_diagonal {I : Type*} [Fintype I] [Nonempty I] :
    (𝔼 i : I, 𝔼 j : I, (if i = j then (1 : ℝ) else 0)) =
      1/(Fintype.card I : ℝ) := by
  have h (i : I) : (𝔼 j : I, (if i = j then (1 : ℝ) else 0)) =
      1/(Fintype.card I : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  simp_rw [h]
  exact Fintype.expect_const _

lemma pair_energy_bounds {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [Nonempty X] (f : X → I → ℂ)
    (hf : ∀ x i, ‖f x i‖ = 1) {η : ℝ} (hη : 0 ≤ η)
    (hpair : ∀ i j, i ≠ j → ‖𝔼 x, f x i*conj (f x j)‖ ≤ η) :
    1/(Fintype.card I : ℝ)-η ≤ (𝔼 x, ‖𝔼 i, f x i‖^2) ∧
    (𝔼 x, ‖𝔼 i, f x i‖^2) ≤ 1/(Fintype.card I : ℝ)+η := by
  have he : (𝔼 x, ‖𝔼 i, f x i‖^2) =
      𝔼 i, 𝔼 j, (𝔼 x, f x i*conj (f x j)).re := by
    simp_rw [norm_mean_sq_pair, expect_re]
    rw [expect_comm]
    apply expect_congr rfl
    intro i _
    exact expect_comm _ _ _
  have hdiag (i : I) : (𝔼 x, f x i*conj (f x i)).re = 1 := by
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, hf, one_pow,
      Complex.ofReal_one, Fintype.expect_const, Complex.one_re]
  have hlow (i j : I) : (if i = j then (1 : ℝ) else 0)-η ≤
      (𝔼 x, f x i*conj (f x j)).re := by
    split_ifs with h
    · subst j; rw [hdiag]; linarith
    · have hn := Complex.abs_re_le_norm (𝔼 x, f x i*conj (f x j))
      have hp := hpair i j h
      have ha := neg_abs_le (𝔼 x, f x i*conj (f x j)).re
      linarith
  have hupp (i j : I) : (𝔼 x, f x i*conj (f x j)).re ≤
      (if i = j then (1 : ℝ) else 0)+η := by
    split_ifs with h
    · subst j; rw [hdiag]; linarith
    · exact (Complex.re_le_norm _).trans (by simpa using hpair i j h)
  rw [he]
  constructor
  · calc
      _ = 𝔼 i, 𝔼 j, ((if i = j then (1 : ℝ) else 0)-η) := by
        simp only [expect_sub_distrib, Fintype.expect_const, mean_diagonal]
      _ ≤ _ := expect_le_expect (fun i _ ↦ expect_le_expect (fun j _ ↦ hlow i j))
  · calc
      _ ≤ 𝔼 i, 𝔼 j, ((if i = j then (1 : ℝ) else 0)+η) :=
        expect_le_expect (fun i _ ↦ expect_le_expect (fun j _ ↦ hupp i j))
      _ = _ := by simp only [expect_add_distrib, Fintype.expect_const, mean_diagonal]

lemma geometric_sum_norm (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ) :
    ‖∑ j ∈ range K, z^j‖*‖z-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖z^K‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

lemma geometric_mean_norm (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ) :
    ‖𝔼 j : Fin K, z^j.val‖*‖z-1‖ ≤ 2/(K : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, norm_div,
    Complex.norm_natCast, Fin.sum_univ_eq_sum_range]
  calc
    _ = (‖∑ j ∈ range K, z^j‖*‖z-1‖)/(K : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (geometric_sum_norm z hz K) (Nat.cast_nonneg K)

noncomputable def intervalMean (N : ℕ) (f : ℕ → ℂ) : ℂ :=
  𝔼 n : Fin N, f n.val

lemma intervalMean_eq (N : ℕ) (f : ℕ → ℂ) :
    intervalMean N f = (∑ n ∈ range N, f n)/(N : ℂ) := by
  rw [intervalMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range]

lemma shifted_sum_sub (f : ℕ → ℂ) (N h : ℕ) :
    (∑ n ∈ range N, f (n+h))-(∑ n ∈ range N, f n) =
      (∑ n ∈ range h, f (n+N))-(∑ n ∈ range h, f n) := by
  have h1 := sum_range_add f N h
  have h2 := sum_range_add f h N
  rw [Nat.add_comm h N] at h2
  have hs1 : (∑ x ∈ range h, f (N+x)) = ∑ x ∈ range h, f (x+N) := by
    apply sum_congr rfl
    intro x _
    rw [Nat.add_comm]
  have hs2 : (∑ x ∈ range N, f (h+x)) = ∑ x ∈ range N, f (x+h) := by
    apply sum_congr rfl
    intro x _
    rw [Nat.add_comm]
  rw [hs1] at h1
  rw [hs2] at h2
  linear_combination h1-h2

lemma interval_shift_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N h : ℕ) :
    ‖intervalMean N (fun n ↦ f (n+h))-intervalMean N f‖ ≤ 2*(h : ℝ)/(N : ℝ) := by
  rw [intervalMean_eq, intervalMean_eq, ← sub_div, shifted_sum_sub,
    norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ ‖∑ n ∈ range h, f (n+N)‖+‖∑ n ∈ range h, f n‖ := norm_sub_le _ _
    _ ≤ (∑ _n ∈ range h, (1 : ℝ))+(∑ _n ∈ range h, (1 : ℝ)) := by
      apply add_le_add
      · exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ ↦ hf (n+N)))
      · exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ ↦ hf n))
    _ = _ := by simp; ring

lemma averaged_shift_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (N H : ℕ) (hH : 0 < H) :
    ‖(𝔼 h : Fin H, intervalMean N (fun n ↦ f (n+h.val)))-intervalMean N f‖ ≤
      2*(H : ℝ)/(N : ℝ) := by
  letI : NeZero H := ⟨by omega⟩
  rw [← Fintype.expect_const (ι := Fin H) (intervalMean N f), ← expect_sub_distrib]
  calc
    _ ≤ 𝔼 h : Fin H, ‖intervalMean N (fun n ↦ f (n+h.val))-intervalMean N f‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 2*(H : ℝ)/(N : ℝ) := by
      apply expect_le univ_nonempty
      intro h _
      apply (interval_shift_bound f hf N h.val).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h.isLt.le) (by norm_num)

#print axioms pair_energy_bounds
#print axioms averaged_shift_bound
end Erdos3QuadraticRecurrenceAverages
