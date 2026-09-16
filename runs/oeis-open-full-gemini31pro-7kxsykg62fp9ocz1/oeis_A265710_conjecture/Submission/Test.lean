import Submission.Spec
open Nat Finset

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

lemma a_45994 : a 45994 = 2 := by
  dsimp [a]
  have : Nat.divisors 45994 = {45994, 22997, 3538, 1769, 1586, 793, 754, 377, 122, 61, 58, 29, 26, 13, 2, 1} := by decide
  rw [this]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have h1 : ArithmeticFunction.sigma 1 45994 = 78120 := by rfl
  have h2 : ArithmeticFunction.sigma 1 22997 = 26040 := by rfl
  have h3 : ArithmeticFunction.sigma 1 3538 = 5580 := by rfl
  have h4 : ArithmeticFunction.sigma 1 1769 = 1860 := by rfl
  have h5 : ArithmeticFunction.sigma 1 1586 = 2604 := by rfl
  have h6 : ArithmeticFunction.sigma 1 793 = 868 := by rfl
  have h7 : ArithmeticFunction.sigma 1 754 = 1260 := by rfl
  have h8 : ArithmeticFunction.sigma 1 377 = 420 := by rfl
  have h9 : ArithmeticFunction.sigma 1 122 = 186 := by rfl
  have h10 : ArithmeticFunction.sigma 1 61 = 62 := by rfl
  have h11 : ArithmeticFunction.sigma 1 58 = 90 := by rfl
  have h12 : ArithmeticFunction.sigma 1 29 = 30 := by rfl
  have h13 : ArithmeticFunction.sigma 1 26 = 42 := by rfl
  have h14 : ArithmeticFunction.sigma 1 13 = 14 := by rfl
  have h15 : ArithmeticFunction.sigma 1 2 = 3 := by rfl
  have h16 : ArithmeticFunction.sigma 1 1 = 1 := by rfl
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  norm_num
