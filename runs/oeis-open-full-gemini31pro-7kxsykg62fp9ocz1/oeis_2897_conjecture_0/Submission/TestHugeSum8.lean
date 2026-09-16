import FormalConjectures.Util.ProblemImports
import Submission.TestHugeSum2
open Finset Nat MvPolynomial Finsupp

def a_local (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

lemma small_sum2_eq_a (n : ℕ)
  (small_sum2_simplified : my_small_sum2 n =
    ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
      ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ))
  (drop_filter_sum : ∀ j, ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) =
                          ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v))
  (inner_sum_eval : ∀ j, ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) =
                         (n.choose j : ℤ) * (-1 : ℤ) ^ j)
  (sum_choose_square : ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 = ((2 * n).choose n : ℤ)) :
  my_small_sum2 n = (a_local n : ℤ) := by
  unfold a_local
  rw [small_sum2_simplified]
  have h_inner : ∀ j, ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ) =
    ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 := by
    intro j
    calc ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
          ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) )
      _ = ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
          ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j * ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) ) := by
        apply sum_congr rfl
        intro v _
        rw [pow_add]
        ring
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) := by
        rw [← Finset.mul_sum]
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) := by
        rw [drop_filter_sum j]
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ((n.choose j : ℤ) * (-1 : ℤ) ^ j) := by
        rw [inner_sum_eval j]
      _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 * ((-1 : ℤ) ^ j) ^ 2 := by
        ring
      _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 := by
        have h_even : ((-1 : ℤ) ^ j) ^ 2 = 1 := by
          rw [← pow_mul]
          have h_mul : j * 2 = 2 * j := by ring
          rw [h_mul, pow_mul]
          simp
        rw [h_even, mul_one]
  have h_sum : ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ) =
    ∑ j ∈ range (n + 1), (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2) := sum_congr rfl (fun j _ => h_inner j)
  rw [h_sum]
  rw [← Finset.mul_sum]
  rw [sum_choose_square]
  push_cast
  ring
