import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The term $C(6k,3k)C(3k,k)$ appearing in the sum. -/
def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

/--
A189286: $a(n):=\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
We define the sequence as an integer sequence, handling $n=0$ explicitly and relying on exact division for $n>0$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if h : n = 0 then
    (-1 : ℤ) -- Explicitly defined a(0)
  else
    let numerator_nat : ℕ := Finset.sum (range (n + 1)) fun k => T_term k * T_term (n - k)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    (numerator_nat : ℤ) / denominator

theorem oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int :=
by sorry

theorem oeis_a189286_conjecture_0.disproof : ¬ (type_of% @oeis_a189286_conjecture_0) := sorry
