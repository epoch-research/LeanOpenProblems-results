import FormalConjecturesUtil
import Submission.PrimeEnergy

/-! An exact expansion of the winning-prime energy. The off-diagonal
cancellation inequality is not assumed or asserted unconditionally. -/

namespace Erdos371OffDiagonalEnergy

open Erdos371PrimeDiscrepancy Erdos371PrimeEnergy

noncomputable def correlation (n m : ℕ) : ℝ :=
  if 0 < n ∧ 0 < m ∧ winner n = winner m then (sign n : ℝ) * (sign m : ℝ) else 0

noncomputable def offDiagonal (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, correlation n m

lemma correlation_symm (n m : ℕ) : correlation n m = correlation m n := by
  simp only [correlation]
  by_cases hn : 0 < n <;> by_cases hm : 0 < m <;>
    by_cases hw : winner n = winner m <;> simp_all [mul_comm, eq_comm]

lemma winner_zero : winner 0 = 1 := by decide +kernel

lemma winner_mem_iff {n N : ℕ} (hn : n < N) :
    winner n ∈ (N+1).primesBelow ↔ 0 < n := by
  constructor
  · intro h
    by_contra h0
    have he : n = 0 := by omega
    subst n
    simp [winner_zero, Nat.mem_primesBelow] at h
  · intro h
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_of_le (winner_le hn), winner_prime h⟩

lemma group_cast (p N : ℕ) : (group p N : ℝ) =
    ∑ n ∈ Finset.range N, if winner n = p then (sign n : ℝ) else 0 := by
  simp [group]

lemma energy_eq_double_sum (N : ℕ) :
    energy N = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, correlation n m := by
  unfold energy
  simp_rw [group_cast, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hwn := winner_mem_iff (Finset.mem_range.mp hn)
  have hwm := winner_mem_iff (Finset.mem_range.mp hm)
  by_cases he : winner n = winner m
  · have hpos : 0 < n ↔ 0 < m := by rw [← hwn, ← hwm, he]
    simp only [he, ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq,
      correlation, and_true]
    by_cases h : 0 < m <;> simp_all
  · have hh (p : ℕ) :
        (if winner n = p then (sign n : ℝ) else 0) *
          (if winner m = p then (sign m : ℝ) else 0) = 0 := by
      split_ifs <;> simp_all
    simp [hh, correlation, he]

lemma sum_square_eq_diagonal_add_twice_triangle (f : ℕ → ℕ → ℝ)
    (hf : ∀ n m, f n m = f m n) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, f n m) =
      (∑ n ∈ Finset.range N, f n n) +
        2 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range m, f n m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih]
    have he : (∑ m ∈ Finset.range N, f N m) = ∑ m ∈ Finset.range N, f m N :=
      Finset.sum_congr rfl (fun m _ => hf N m)
    rw [he]
    ring

lemma correlation_self (n : ℕ) : correlation n n = if n = 0 then 0 else 1 := by
  by_cases h : n = 0
  · simp [correlation, h]
  · have hn : 0 < n := by omega
    simp only [correlation, hn, and_self, if_true]
    unfold sign
    split_ifs <;> norm_num [h]

lemma diagonal_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, correlation n n) = (N-1 : ℕ) := by
  simp_rw [correlation_self]
  cases N with
  | zero => simp
  | succ N =>
    rw [Finset.sum_range_succ']
    simp

/-- The diagonal contributes exactly `N-1`; all further difficulty is in the
signed correlation of two distinct comparisons with the same winning prime. -/
theorem energy_expansion (N : ℕ) :
    energy N = (N-1 : ℕ) + 2 * offDiagonal N := by
  rw [energy_eq_double_sum,
    sum_square_eq_diagonal_add_twice_triangle correlation correlation_symm, diagonal_sum]
  rfl

/-- Unordered pairs of comparisons with equal winner and equal signs. -/
def sameCount (N : ℕ) : ℕ :=
  ∑ m ∈ Finset.range N,
    ((Finset.range m).filter fun n =>
      0 < n ∧ winner n = winner m ∧ sign n = sign m).card

/-- Unordered pairs of comparisons with equal winner and opposite signs. -/
def oppositeCount (N : ℕ) : ℕ :=
  ∑ m ∈ Finset.range N,
    ((Finset.range m).filter fun n =>
      0 < n ∧ winner n = winner m ∧ sign n ≠ sign m).card

lemma sign_product (n m : ℕ) :
    (sign n : ℝ) * (sign m : ℝ) = if sign n = sign m then 1 else -1 := by
  unfold sign
  split_ifs <;> norm_num at *

lemma correlation_eq_count_difference {n m : ℕ} (hnm : n < m) :
    correlation n m =
      (if 0 < n ∧ winner n = winner m ∧ sign n = sign m then (1 : ℝ) else 0) -
      (if 0 < n ∧ winner n = winner m ∧ sign n ≠ sign m then (1 : ℝ) else 0) := by
  have hm : 0 < m := by omega
  simp only [correlation, hm, true_and, sign_product]
  by_cases hn : 0 < n <;> by_cases hw : winner n = winner m <;>
    by_cases hs : sign n = sign m <;> simp [hn, hw, hs]

lemma offDiagonal_eq_counts (N : ℕ) :
    offDiagonal N = (sameCount N : ℝ) - oppositeCount N := by
  unfold offDiagonal sameCount oppositeCount
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact correlation_eq_count_difference (Finset.mem_range.mp hn)

/-- A purely finite identity, not a cancellation estimate. -/
theorem energy_eq_pair_counts (N : ℕ) :
    energy N = (N-1 : ℕ) + 2 * ((sameCount N : ℝ) - oppositeCount N) := by
  rw [energy_expansion, offDiagonal_eq_counts]

lemma energy_le_diagonal_iff (N : ℕ) :
    energy N ≤ (N-1 : ℕ) ↔ sameCount N ≤ oppositeCount N := by
  rw [energy_eq_pair_counts]
  have he : (sameCount N : ℝ) ≤ oppositeCount N ↔ sameCount N ≤ oppositeCount N :=
    Nat.cast_le
  constructor
  · intro h
    exact he.mp (by linarith)
  · intro h
    have hh := he.mpr h
    linarith

end Erdos371OffDiagonalEnergy

#print axioms Erdos371OffDiagonalEnergy.energy_expansion
#print axioms Erdos371OffDiagonalEnergy.energy_eq_pair_counts
#print axioms Erdos371OffDiagonalEnergy.energy_le_diagonal_iff
