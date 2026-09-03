import Submission.SquarefreeDivisorExpansion
import Submission.PrimeSmoothDivisorEstimate

/-! Square-divisor expansion with an injective output map. These finite
support estimates retain their large-square tails. -/
namespace Erdos972MappedSquarefreeDivisorExpansion

open Finset ArithmeticFunction
open Erdos972SquarefreeDivisorExpansion Erdos972WeightedDivisorAmplification
open Erdos972SelbergLowerTest

set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma mapped_row_le_cap (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {M d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 ≤ L)
    (hg : Set.InjOn g (↑S : Set ℕ)) (hgM : ∀ n ∈ S, g n ∈ Ioc 0 M)
    (ha : ∀ n ∈ S, a n ≤ L) :
    row S a g d ≤ L*(M : ℝ)/d := by
  classical
  calc
    _ ≤ ∑ n ∈ S, if d ∣ g n then L else 0 := by
      unfold row
      apply sum_le_sum
      intro n hn
      split_ifs
      · exact ha n hn
      · exact le_rfl
    _ = ∑ m ∈ S.image g, if d ∣ m then L else 0 := by rw [sum_image hg]
    _ ≤ divisorRow (Ioc 0 M) (fun _ => L) d := by
      unfold divisorRow
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact hgM n hn
      · intro m hm hnot
        split_ifs <;> first | exact hL | exact le_rfl
    _ ≤ _ := divisorRow_le_cap (fun _ => L) hL M d hd (fun _ _ => le_rfl)

lemma mapped_squarefree_tail (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) {L : ℝ} (hL : 0 ≤ L)
    (hg : Set.InjOn g (↑S : Set ℕ)) (hgM : ∀ n ∈ S, g n ∈ Ioc 0 M)
    (ha0 : ∀ n ∈ S, 0 ≤ a n) (haL : ∀ n ∈ S, a n ≤ L) :
    |(∑ n ∈ S, a n*|(moebius (g n) : ℝ)|) -
      ∑ n ∈ S, a n*squarefreeTruncation D (g n)| ≤ L*(M : ℝ)/D := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, |a n*|(moebius (g n) : ℝ)| - a n*squarefreeTruncation D (g n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, a n*(∑ d ∈ Ioc D M, if d^2 ∣ g n then (1 : ℝ) else 0) := by
      apply sum_le_sum
      intro n hn
      rw [← mul_sub, abs_mul, abs_of_nonneg (ha0 n hn)]
      exact mul_le_mul_of_nonneg_left
        (squarefreeTruncation_tail_bound (mem_Ioc.mp (hgM n hn)).1
          (mem_Ioc.mp (hgM n hn)).2 hDM) (ha0 n hn)
    _ = ∑ d ∈ Ioc D M, row S a g (d^2) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      unfold row
      apply sum_congr rfl
      intro n hn
      by_cases hdn : d^2 ∣ g n <;> simp [hdn]
    _ ≤ ∑ d ∈ Ioc D M, L*(M : ℝ)/(d^2 : ℕ) := by
      apply sum_le_sum
      intro d hd
      exact mapped_row_le_cap S a g (pow_pos (hD.trans (mem_Ioc.mp hd).1) 2)
        hL hg hgM haL
    _ = L*(M : ℝ)*(∑ d ∈ Ioc D M, ((d : ℝ)^2)⁻¹) := by
      simp only [Nat.cast_pow, div_eq_mul_inv, mul_sum]
    _ ≤ L*(M : ℝ)*((D : ℝ)⁻¹-(M : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub hD.ne' hDM) (by positivity)
    _ ≤ L*(M : ℝ)/D := by
      rw [mul_sub, ← div_eq_mul_inv]
      have hh : 0 ≤ L*(M : ℝ)*(M : ℝ)⁻¹ := by positivity
      linarith only [hh]

lemma mapped_squarefreeTruncation (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (D : ℕ) :
    (∑ n ∈ S, a n*squarefreeTruncation D (g n)) =
      ∑ d ∈ Ioc 0 D, (moebius d : ℝ)*row S a g (d^2) := by
  simp only [squarefreeTruncation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  simp only [row, mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hdn : d^2 ∣ g n <;> simp [hdn, mul_comm]

lemma mapped_squarefreeTruncation_error (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (D : ℕ) {X E : ℝ}
    (hrows : ∀ d ∈ Ioc 0 D, |row S a g (d^2)-X/(d^2 : ℕ)| ≤ E) :
    |(∑ n ∈ S, a n*squarefreeTruncation D (g n))-X*squarefreeMeanTruncation D| ≤ D*E := by
  rw [mapped_squarefreeTruncation, squarefreeMeanTruncation, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, E := by
      apply sum_le_sum
      intro d hd
      have he : (moebius d : ℝ)*row S a g (d^2)-X*((moebius d : ℝ)/(d : ℝ)^2) =
          (moebius d : ℝ)*(row S a g (d^2)-X/(d^2 : ℕ)) := by push_cast; ring
      rw [he, abs_mul]
      have hmu : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans (by simpa using hrows d hd)
    _ = _ := by simp

/-- All hypotheses refer to the actual mapped rows. -/
theorem mapped_squarefree_mean_error (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) {L : ℝ} (hL : 0 ≤ L)
    (hg : Set.InjOn g (↑S : Set ℕ)) (hgM : ∀ n ∈ S, g n ∈ Ioc 0 M)
    (ha0 : ∀ n ∈ S, 0 ≤ a n) (haL : ∀ n ∈ S, a n ≤ L) {X E : ℝ}
    (hrows : ∀ d ∈ Ioc 0 D, |row S a g (d^2)-X/(d^2 : ℕ)| ≤ E) :
    |(∑ n ∈ S, a n*|(moebius (g n) : ℝ)|)-X*squarefreeMeanTruncation D| ≤
      L*(M : ℝ)/D+D*E := by
  exact (abs_sub_le _ (∑ n ∈ S, a n*squarefreeTruncation D (g n)) _).trans
    (add_le_add (mapped_squarefree_tail S a g hD hDM hL hg hgM ha0 haL)
      (mapped_squarefreeTruncation_error S a g D hrows))

#print axioms mapped_squarefree_mean_error
end Erdos972MappedSquarefreeDivisorExpansion
