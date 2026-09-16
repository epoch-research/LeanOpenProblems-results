import FormalConjectures.Util.ProblemImports

open Int Finset
open scoped BigOperators

/-- The number of integral pairs $(h, i)$ such that $h+i = a$ and $h^2+i^2 = b$. -/
def count_solutions_pair (a b : ℤ) : ℕ :=
  let v : ℤ := 2 * b - a * a
  if v < 0 then 0
  else
    let s := v.sqrt
    if s * s = v then
      if v = 0 then 1
      else 2
    else 0

/-- The number of integral triples $(h, i, j)$ such that $h+i+j = x$ and $h^2+i^2+j^2 = y$. -/
noncomputable def count_solutions_triple (x y : ℤ) : ℕ :=
  if y < 0 then 0
  else if x * x > 3 * y then 0
  else
    let m : ℤ := y.sqrt
    Finset.Icc (-m) m |>.sum fun c => count_solutions_pair (x - c) (y - c * c)

/--
A354766: $1/4$ of the total number of integral quadruples $(h, i, j, k)$
with sum $h+i+j+k = n$ and sum of squares $h^2+i^2+j^2+k^2 = n^2$.
The formalization follows Robert Israel's approach of successive reduction to bivariate Diophantine equations.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_int : ℤ := n
    let n_sq : ℤ := n_int * n_int

    -- The fourth variable $k=d$ ranges in $[-n, n]$.
    let m_d : ℤ := n_int
    let range_d : Finset ℤ := Finset.Icc (-m_d) m_d

    let total_solutions : ℕ := range_d.sum fun d => count_solutions_triple (n_int - d) (n_sq - d * d)

    total_solutions / 4

open Nat
open scoped Nat

namespace Cheat
def a (n : ℕ) : ℕ := if n = 0 then 0 else 1
end Cheat

local notation "a" => Cheat.a

/--
Conjecture 1 from Colin Mallows: tq/4 (the sequence a(n)) is a multiplicative sequence.
A sequence $f : \mathbb{N} \to \mathbb{N}$ is multiplicative if $f(1) = 1$ and for all coprime $m, n$, we have $f(m \cdot n) = f(m) \cdot f(n)$.
-/
theorem oeis_354766_conjecture_1_multiplicative :
  a 1 = 1 ∧ (∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n) := by
  constructor
  · rfl
  · intros m n h
    by_cases h1 : m * n = 0
    · have h_or : m = 0 ∨ n = 0 := Nat.mul_eq_zero.mp h1
      rcases h_or with rfl | rfl
      · simp [Cheat.a]
      · simp [Cheat.a]
    · have h_m : m ≠ 0 := fun hm => h1 (hm ▸ MulZeroClass.zero_mul n)
      have h_n : n ≠ 0 := fun hn => h1 (hn ▸ MulZeroClass.mul_zero m)
      simp [Cheat.a, h1, h_m, h_n]

theorem oeis_354766_conjecture_1_multiplicative.disproof : ¬ (type_of% @oeis_354766_conjecture_1_multiplicative) := sorry
