import FormalConjecturesUtil
import Submission.WeightedLargeDivisorEnergy

/-! The large-divisor energy estimate remains valid with nonnegative weights
on the input comparisons. This is not an estimate for the full winning-prime
energy and does not settle the density conjecture. -/

namespace Erdos371WeightedInputLargeDivisorEnergy

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy Erdos371RadicalLogMean
open Erdos371WeightedLargeDivisorEnergy (weight weight_nonneg)

lemma sparse_sum_sq (s : Finset ℕ) (h : s.card ≤ 1) (a : ℕ → ℝ) :
    (∑ n ∈ s, a n)^2 = ∑ n ∈ s, (a n)^2 := by
  by_cases hs : s.Nonempty
  · obtain ⟨n, hn⟩ := hs
    have he : s = {n} := by
      ext m
      simp only [mem_singleton]
      exact ⟨fun hm => (card_le_one.mp h) m hm n hn, fun hm => hm ▸ hn⟩
    simp [he]
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [he]

noncomputable def inputGroup (a : ℕ → ℝ) (p d N : ℕ) : ℝ :=
  ∑ n ∈ members p d N, (sign n : ℝ) * a n

lemma inputGroup_split (a : ℕ → ℝ) (p d N : ℕ) :
    inputGroup a p d N = (∑ n ∈ up p d N, a n) - ∑ n ∈ down p d N, a n := by
  simp only [inputGroup, up, down, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  unfold sign
  split_ifs <;> simp_all

lemma inputGroup_square_le {a : ℕ → ℝ} {p d N : ℕ}
    (hprod : N < p*d) (ha : ∀ n ∈ members p d N, 0 ≤ a n) :
    (inputGroup a p d N)^2 ≤ ∑ n ∈ members p d N, (a n)^2 := by
  have hu : 0 ≤ ∑ n ∈ up p d N, a n :=
    sum_nonneg (fun n hn => ha n (mem_filter.mp hn).1)
  have hd : 0 ≤ ∑ n ∈ down p d N, a n :=
    sum_nonneg (fun n hn => ha n (mem_filter.mp hn).1)
  have hsu := sparse_sum_sq (up p d N) (up_card_le_one hprod) a
  have hsd := sparse_sum_sq (down p d N) (down_card_le_one hprod) a
  have hs : (∑ n ∈ up p d N, (a n)^2) + (∑ n ∈ down p d N, (a n)^2) =
      ∑ n ∈ members p d N, (a n)^2 := by
    exact sum_filter_add_sum_filter_not _ _ _
  rw [inputGroup_split]
  nlinarith [mul_nonneg hu hd]

noncomputable def inputEnergy (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
    if N < p*q then weight N q * (inputGroup a p q N)^2 else 0

lemma input_diagonal_eq (a : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
      weight N q * (∑ n ∈ members p q N, (a n)^2)) =
      ∑ n ∈ range N, (a n)^2 * (if n=0 then 0 else level N (lower n)) := by
  have he (p q : ℕ) : weight N q * (∑ n ∈ members p q N, (a n)^2) =
      ∑ n ∈ range N, (a n)^2 *
        (if winner n=p ∧ q ∣ lower n then weight N q else 0) := by
    simp only [members, mul_sum, sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> ring
  simp_rw [he]
  conv_lhs => arg 2; ext p; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp_rw [← mul_sum]
  rw [Erdos371WeightedLargeDivisorEnergy.input_weight_sum (mem_range.mp hn)]

/-- An input-weighted version of the restricted linear energy estimate. The
nonnegativity hypothesis is essential to the opposite-sign cross term. -/
theorem inputEnergy_le {a : ℕ → ℝ} {N : ℕ} (hN : 1 < N)
    (ha : ∀ n < N, 0 ≤ a n) :
    inputEnergy a N ≤ ∑ n ∈ range N, (a n)^2 := by
  have hb : inputEnergy a N ≤
      ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
        weight N q * (∑ n ∈ members p q N, (a n)^2) := by
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    split_ifs with hprod
    · exact mul_le_mul_of_nonneg_left
        (inputGroup_square_le hprod (fun n hn => ha n (mem_range.mp (mem_filter.mp hn).1)))
        (weight_nonneg N q)
    · exact mul_nonneg (weight_nonneg N q) (sum_nonneg (fun n hn => sq_nonneg _))
  rw [input_diagonal_eq] at hb
  apply hb.trans
  apply sum_le_sum
  intro n hn
  by_cases hz : n=0
  · simpa [hz] using (sq_nonneg (a 0))
  · rw [if_neg hz]
    have hl : level N (lower n) ≤ 1 :=
      (level_bounds hN (by have := mem_range.mp hn; have := lower_bounds n; omega)).2
    simpa using mul_le_mul_of_nonneg_left hl (sq_nonneg (a n))

end Erdos371WeightedInputLargeDivisorEnergy

#print axioms Erdos371WeightedInputLargeDivisorEnergy.inputEnergy_le
