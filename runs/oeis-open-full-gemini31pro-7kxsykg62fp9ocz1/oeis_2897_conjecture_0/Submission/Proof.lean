import FormalConjectures.Util.ProblemImports
import Submission.TestCommRing
import Submission.TestHugeSum2
import Submission.TestHugeSum3
import Submission.TestHugeSum6
import Submission.TestHugeSum7
import Submission.TestHugeSum8
import Submission.TestHugeSum9
import Submission.TestHugeSum12
import Submission.TestHugeSum14
import Submission.TestIfEquiv

open MvPolynomial Finset Nat

local notation "P" => MvPolynomial Vars_local ℤ
noncomputable def P_n_local (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

lemma P_n_eq (n : ℕ) :
  P_n_local n = ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ( ( (2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j ) *
    ( (1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j) ) := by
  unfold P_n_local
  have h := comm_ring_id (1 + X 0 : MvPolynomial Vars_local ℤ) (X 1 + X 2) (X 1 - X 2) n
  have hB : (1 + X 0 : MvPolynomial Vars_local ℤ) + (X 1 + X 2) = 1 + X 0 + X 1 + X 2 := by ring
  have hC1 : (1 + X 0 : MvPolynomial Vars_local ℤ) + (X 1 - X 2) = 1 + X 0 + X 1 - X 2 := by ring
  have hC2 : (1 + X 0 : MvPolynomial Vars_local ℤ) - (X 1 - X 2) = 1 + X 0 - X 1 + X 2 := by ring
  rw [hB, hC1, hC2] at h
  exact h

lemma coeff_P_n (n : ℕ) :
  coeff (xyz_pow_n_local n) (P_n_local n) =
  ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
      ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
      ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
      (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
  rw [P_n_eq]
  rw [coeff_sum]
  apply sum_congr rfl
  intro i hi
  rw [coeff_sum]
  apply sum_congr rfl
  intro j hj
  have hc : coeff (xyz_pow_n_local n) ((((2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j) * ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j))) =
            (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
            coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) := by
    have h_C : (((2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j) =
               C (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) := by
      simp
    rw [h_C, coeff_C_mul]
  rw [hc]
  have hc_pij : coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) =
                ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
    exact coeff_P_ij n i j (4 * n - i - 2 * j)
  rw [hc_pij]
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  ring
