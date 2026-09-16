import FormalConjectures.Util.ProblemImports
import Submission.Proof2
import Submission.TestHugeSum8
import Submission.TestHugeSum2
import Submission.TestHugeSum3
import Submission.TestHugeSum6
import Submission.TestHugeSum7

open Nat MvPolynomial

def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3
abbrev Vars := Fin 3
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)
local notation "P" => MvPolynomial Vars ℤ
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by
  have ha : a n = a_local n := rfl
  have hP : P_n n = P_n_local n := rfl
  have hx : xyz_pow_n n = xyz_pow_n_local n := rfl
  have h1 := small_sum2_eq_a n (small_sum2_simplified n) (drop_filter_sum n) (inner_sum_eval n) (sum_choose_square n)
  have h2 := my_small_sum2_eq_coeff_full n
  rw [ha, hP, hx]
  rw [← h1, h2]

theorem oeis_2897_conjecture_0.disproof : ¬ (type_of% @oeis_2897_conjecture_0) := sorry
