import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k
def term (a b k : ℕ) : ℤ := (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)
def S_def (a b : ℕ) : ℤ := ∑ k ∈ Ico a b, term a b k

lemma comb_correct (a m b : ℕ) (ha : a ≤ m) (hm : m ≤ b) (p1 p2 : ℕ) (f1 f2 : ℤ)
  (h1 : P_def a m = p1 ∧ S_def a m = f1)
  (h2 : P_def m b = p2 ∧ S_def m b = f2) :
  P_def a b = p1 * p2 ∧ S_def a b = f1 * (p2 : ℤ) + (p1 : ℤ) * f2 := sorry

lemma chunk_0 : P_def 2 5 = 24 ∧ S_def 2 5 = 10 := sorry
lemma chunk_1 : P_def 5 8 = 210 ∧ S_def 5 8 = -62 := sorry

lemma comb_0_1 : P_def 2 8 = 5040 ∧ S_def 2 8 = 574 := by
  have H := comb_correct 2 5 8 (by decide) (by decide) 24 210 10 (-62) chunk_0 chunk_1
  have H2 : 24 * 210 = 5040 ∧ 10 * (210 : ℤ) + (24 : ℤ) * (-62) = 574 := by decide
  rw [H2.1, H2.2] at H
  exact H
