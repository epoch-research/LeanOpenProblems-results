import Submission.UniformPrimeFactorError

/-! Sparse first-moment bounds for the original and prime-restricted
Vaughan remainders. These control mean corrections, not signed correlations. -/
namespace Erdos972SparseSingleDivisorMoment
open Finset Classical
open Erdos972DivisorEnergy Erdos972PrimePowerError
open Erdos972DoubleVaughan Erdos972PrimeFactorRemainder
open Erdos972UniformPrimeFactorError Erdos972LargeSquareDivisors
open Erdos972MellinRemainderEnergy
set_option maxHeartbeats 1000000
set_option autoImplicit false

lemma sparse_single_sum_square {M : ℕ} {L C : ℝ}
    (s : Finset ℕ) (hs : s ⊆ Ioc 0 M) (hL : 1+Real.log M ≤ L)
    (f : ℕ → ℝ) (hf : ∀ n ∈ s, |f n| ≤ C*(n.divisors.card : ℝ)) :
    (∑ n ∈ s, f n)^2 ≤ C^2*(s.card : ℝ)*(M : ℝ)*L^3 := by
  have hL0 : 0 ≤ L := by linarith [Real.log_natCast_nonneg M]
  have hsum : |∑ n ∈ s, f n| ≤ C*∑ n ∈ s, (n.divisors.card : ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    exact sum_le_sum hf
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun n => (n.divisors.card : ℝ))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  have hm : (∑ n ∈ s, (n.divisors.card : ℝ)^2) ≤ (M : ℝ)*L^3 := by
    apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    exact (sum_card_divisors_square_le_log M).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (by positivity [Real.log_natCast_nonneg M]) hL 3) (Nat.cast_nonneg _))
  have hh := pow_le_pow_left₀ (abs_nonneg _) hsum 2
  rw [sq_abs, mul_pow] at hh
  apply hh.trans
  calc
    _ ≤ C^2*((s.card : ℝ)*(∑ n ∈ s, (n.divisors.card : ℝ)^2)) := by
      exact mul_le_mul_of_nonneg_left hcs (sq_nonneg C)
    _ ≤ C^2*((s.card : ℝ)*((M : ℝ)*L^3)) := by gcongr
    _ = _ := by ring

lemma divisor_log_sum_square {M : ℕ} {L : ℝ}
    (s : Finset ℕ) (hs : s ⊆ Ioc 0 M) (hL : 1+Real.log M ≤ L)
    (f : ℕ → ℝ) (hf : ∀ n ∈ s, |f n| ≤ (n.divisors.card : ℝ)*Real.log n) :
    (∑ n ∈ s, f n)^2 ≤ (M : ℝ)^2*L^5 := by
  have hL0 : 0 ≤ L := by linarith [Real.log_natCast_nonneg M]
  have hpoint : ∀ n ∈ s, |f n| ≤ L*(n.divisors.card : ℝ) := by
    intro n hn
    have hl := (log_input_le (hs hn)).trans (show Real.log M ≤ L by linarith)
    exact ((hf n hn).trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))).trans_eq (by ring)
  have hh := sparse_single_sum_square s hs hL f hpoint
  have hc : (s.card : ℝ) ≤ M := by
    exact_mod_cast (card_le_card hs).trans_eq (by simp)
  apply hh.trans
  calc
    _ ≤ L^2*(M : ℝ)*(M : ℝ)*L^3 := by gcongr
    _ = _ := by ring

lemma remainder_difference_sum_square {U V Z M : ℕ} {L : ℝ}
    (hZ : 0 < Z) (hV : Z^3 ≤ V) (s : Finset ℕ) (hs : s ⊆ Ioc 0 M)
    (hL : 1+Real.log M ≤ L) :
    (∑ n ∈ s, (typeIIPart U V n-primeTypeIIPart U V n))^2 ≤
      4*(M : ℝ)^2*L^5/(Z : ℝ) := by
  have hL0 : 0 ≤ L := by linarith [Real.log_natCast_nonneg M]
  let t := s ∩ largeSquareSet Z M
  have ht : t ⊆ Ioc 0 M := (inter_subset_left).trans hs
  have he : (∑ n ∈ s, (typeIIPart U V n-primeTypeIIPart U V n)) =
      ∑ n ∈ t, (typeIIPart U V n-primeTypeIIPart U V n) := by
    symm
    apply sum_subset inter_subset_left
    intro n hn hnot
    have hne : n ∉ largeSquareSet Z M := fun hh => hnot (mem_inter.mpr ⟨hn, hh⟩)
    rw [prime_remainder_eq_of_no_large_square_general hV (hs hn) hne, sub_self]
  rw [he]
  have hp : ∀ n ∈ t, |typeIIPart U V n-primeTypeIIPart U V n| ≤
      (2*L)*(n.divisors.card : ℝ) := by
    intro n hn
    have hl := (log_input_le (ht hn)).trans (show Real.log M ≤ L by linarith)
    apply (abs_sub _ _).trans
    have hb := add_le_add (remainder_abs_bound U V n) (prime_remainder_abs_bound U V n)
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) n.divisors.card)
    nlinarith only [hm]
  have hh := sparse_single_sum_square t ht hL _ hp
  have hc : (t.card : ℝ) ≤ (M : ℝ)/Z :=
    (Nat.cast_le.mpr (card_le_card inter_subset_right)).trans (largeSquareSet_card_le hZ M)
  apply hh.trans
  calc
    _ ≤ (2*L)^2*((M : ℝ)/Z)*(M : ℝ)*L^3 := by gcongr
    _ = _ := by ring

lemma floor_image_subset {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (Ioc 0 N).image (floorMul α) ⊆ Ioc 0 (floorMul α N) := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
  exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
    (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩

lemma sum_floor_eq_image {α : ℝ} (hα : 1 ≤ α) (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, f (floorMul α n)) = ∑ q ∈ (Ioc 0 N).image (floorMul α), f q := by
  rw [sum_image]
  exact (floorMul_strictMono hα).injective.injOn

#print axioms sparse_single_sum_square
#print axioms divisor_log_sum_square
#print axioms remainder_difference_sum_square
end Erdos972SparseSingleDivisorMoment
