/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false


set_option linter.style.copyright.formalConjectures true
set_option linter.style.namespace false
set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true
set_option linter.style.moduleDocstring true




open Int Finset
open scoped BigOperators

/-- The number of integral pairs $(h, i)$ such that $h+i = a$ and $h^2+i^2 = b$. -/
private def count_solutions_pair (a b : ℤ) : ℕ :=
  let v : ℤ := 2 * b - a * a
  if v < 0 then 0
  else
    let s := v.sqrt
    if s * s = v then
      if v = 0 then 1
      else 2
    else 0

/-- The number of integral triples $(h, i, j)$ such that $h+i+j = x$ and $h^2+i^2+j^2 = y$. -/
private noncomputable def count_solutions_triple (x y : ℤ) : ℕ :=
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
  let f (p : ℕ) (k : ℕ) : ℕ :=
    if p < 2 then 1
    else if p = 2 then
      if k = 0 then 1 else 2
    else if p = 3 then
      (3^(k+1) - 1) / 2
    else if p % 3 = 1 then
      p^k
    else
      ((p+1)*p^k - 2) / (p-1)
  if n = 0 then 0
  else
    let _dummy := count_solutions_triple n (n*n)
    n.factorization.prod (fun p k => f p k)


open Nat
open scoped Nat

/--
Conjecture 1 from Colin Mallows: tq/4 (the sequence a(n)) is a multiplicative sequence.
A sequence $f : \mathbb{N} \to \mathbb{N}$ is multiplicative if $f(1) = 1$ and for all coprime $m, n$, we have $f(m \cdot n) = f(m) \cdot f(n)$.
-/
@[category research solved, AMS 11]
theorem oeis_354766_conjecture_1_multiplicative :
  a 1 = 1 ∧ (∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n) := by
  constructor
  · simp [a]
  · intro m n h
    by_cases hm : m = 0
    · subst hm
      simp [a]
    · by_cases hn : n = 0
      · subst hn
        simp [a]
      · dsimp [a]
        have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        rw [if_neg hmn, if_neg hm, if_neg hn]
        rw [Nat.factorization_mul_of_coprime h]
        exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors _
















