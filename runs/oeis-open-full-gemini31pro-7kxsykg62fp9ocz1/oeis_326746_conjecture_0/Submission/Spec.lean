import Submission.Helper12
import FormalConjectures.Util.ProblemImports

open Nat List Filter Real

/--
A326746: $a(n) = (\text{sum of digits of } n) \bmod (\text{sum of digits of } n+1)$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum % (Nat.digits 10 (n + 1)).sum

/-- The count of non-negative integers $n < N$ such that $a(n) = m$. -/
def count_a_eq (N m : ℕ) : ℕ :=
  (List.range N).countP fun n => a n = m

/--
oeis_326746_conjecture_0:
The frequency of occurrence for the values of a(n) for large values of n has an interesting distribution - it is a bell-shaped curve but with large increases for a(n) = 8, and a smaller increase for a(n) = 17. The value a(n) = 8 is likely the most common value as every time n increases by 100 the value of a(n) goes through ten smaller cycles, and 8 appears to be the only value that is present in all ten cycles. The reason a(n) = 17 also appears more often is not clear, although the distribution for n up to 10^10 also shows a slight increase in the number of occurrences for a(n) = 26, suggesting that a(n) values of the form a(n) = 8 + 9 * k, where k >= 0, occur more frequently than one would predicted from the surrounding bell-curve distribution.

We formalize the core claim that 8 is the most common value by asserting that its asymptotic frequency is at least that of any other value $m$.
The asymptotic frequency is captured by the $\limsup$ of the proportion of occurrences up to $N$.
-/
theorem oeis_326746_conjecture_0 :
  ∀ m : ℕ,
    Filter.limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop
    ≥
    Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop
    := by
  intro m
  by_cases hm : m = 8
  · rw [hm]
  · have h1 : limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop ≤ 1 / 100 := limsup_m_le m hm
    have h2 : 9 / 100 ≤ limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop := limsup_8_ge
    linarith

theorem oeis_326746_conjecture_0.disproof : ¬ (type_of% @oeis_326746_conjecture_0) := sorry
