import Submission.DivisorFourthMoment
import Submission.PrimePowerError

/-! Hölder bounds for divisor products on sparse subsets of a Beatty graph.
No cancellation or prime-pair lower bound is asserted. -/
namespace Erdos972SparseDivisorMoment

open Finset
open Erdos972PrimePowerError Erdos972DivisorFourthMoment
set_option maxHeartbeats 1000000

lemma sum_product_fourth_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ n ∈ s, f n*g n)^4 ≤
      (s.card : ℝ)^2*(∑ n ∈ s, f n^4)*(∑ n ∈ s, g n^4) := by
  have h1 := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun n => f n*g n)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h1
  have h2 := sum_mul_sq_le_sq_mul_sq s (fun n => f n^2) (fun n => g n^2)
  have he : (∑ n ∈ s, (f n*g n)^2) = ∑ n ∈ s, f n^2*g n^2 := by simp_rw [mul_pow]
  rw [he] at h1
  have he4 (f : ι → ℝ) : (∑ n ∈ s, (f n^2)^2) = ∑ n ∈ s, f n^4 := by
    simp_rw [← pow_mul]
  rw [he4, he4] at h2
  have h1sq := pow_le_pow_left₀ (sq_nonneg _) h1 2
  have h2mul := mul_le_mul_of_nonneg_left h2 (sq_nonneg (s.card : ℝ))
  calc
    _ = ((∑ n ∈ s, f n*g n)^2)^2 := by ring
    _ ≤ ((s.card : ℝ)*(∑ n ∈ s, f n^2*g n^2))^2 := h1sq
    _ = (s.card : ℝ)^2*(∑ n ∈ s, f n^2*g n^2)^2 := mul_pow _ _ _
    _ ≤ _ := h2mul.trans_eq (by ring)

lemma output_divisor_fourth_moment {α : ℝ} (hα : 1 ≤ α) {N : ℕ}
    (s : Finset ℕ) (hs : s ⊆ Ioc 0 N) :
    (∑ n ∈ s, ((floorMul α n).divisors.card : ℝ)^4) ≤
      (floorMul α N : ℝ)*(1+Real.log (floorMul α N))^15 := by
  classical
  have hsub : s.image (floorMul α) ⊆ Ioc 0 (floorMul α N) := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
    exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp (hs hn)).1,
      (floorMul_strictMono hα).monotone (mem_Ioc.mp (hs hn)).2⟩
  have hi : (∑ n ∈ s, ((floorMul α n).divisors.card : ℝ)^4) =
      ∑ q ∈ s.image (floorMul α), (q.divisors.card : ℝ)^4 := by
    rw [sum_image]
    exact (floorMul_strictMono hα).injective.injOn
  rw [hi]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
    (sum_card_divisors_fourth_le_log (floorMul α N))

lemma divisor_product_fourth_bound {α L : ℝ} (hα : 1 ≤ α) {N : ℕ}
    (s : Finset ℕ) (hs : s ⊆ Ioc 0 N)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L) :
    (∑ n ∈ s, (n.divisors.card : ℝ)*(floorMul α n).divisors.card)^4 ≤
      (s.card : ℝ)^2*(N : ℝ)*(floorMul α N : ℝ)*L^30 := by
  have hL : 0 ≤ L := by linarith [Real.log_natCast_nonneg N]
  have hi : (∑ n ∈ s, (n.divisors.card : ℝ)^4) ≤ (N : ℝ)*L^15 := by
    apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    exact (sum_card_divisors_fourth_le_log N).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (by positivity [Real.log_natCast_nonneg N]) hiL 15) (Nat.cast_nonneg _))
  have ho : (∑ n ∈ s, ((floorMul α n).divisors.card : ℝ)^4) ≤ (floorMul α N : ℝ)*L^15 :=
    (output_divisor_fourth_moment hα s hs).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (by positivity [Real.log_natCast_nonneg (floorMul α N)]) hoL 15) (Nat.cast_nonneg _))
  apply (sum_product_fourth_le s (fun n => (n.divisors.card : ℝ))
    (fun n => ((floorMul α n).divisors.card : ℝ))).trans
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul hi ho (sum_nonneg fun _ _ => by positivity) (by positivity))
    (sq_nonneg (s.card : ℝ))
  convert hh using 1 <;> ring

lemma sparse_sum_fourth_bound {α L C : ℝ} (hα : 1 ≤ α) {N : ℕ}
    (s : Finset ℕ) (hs : s ⊆ Ioc 0 N)
    (hiL : 1+Real.log N ≤ L) (hoL : 1+Real.log (floorMul α N) ≤ L)
    (f : ℕ → ℝ) (hf : ∀ n ∈ s,
      |f n| ≤ C*(n.divisors.card : ℝ)*(floorMul α n).divisors.card) :
    |∑ n ∈ s, f n|^4 ≤ C^4*(s.card : ℝ)^2*(N : ℝ)*(floorMul α N : ℝ)*L^30 := by
  have hsum : |∑ n ∈ s, f n| ≤ C*∑ n ∈ s,
      (n.divisors.card : ℝ)*(floorMul α n).divisors.card := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    exact sum_le_sum fun n hn => (hf n hn).trans_eq (by ring)
  have hh := pow_le_pow_left₀ (abs_nonneg _) hsum 4
  rw [mul_pow] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (divisor_product_fourth_bound hα s hs hiL hoL) (by positivity)).trans_eq (by ring))

#print axioms sum_product_fourth_le
#print axioms sparse_sum_fourth_bound
end Erdos972SparseDivisorMoment
