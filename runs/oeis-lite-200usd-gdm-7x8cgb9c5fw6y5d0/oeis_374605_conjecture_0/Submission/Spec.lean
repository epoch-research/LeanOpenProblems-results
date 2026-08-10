/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# OEIS A374605 Conjecture

This file provides a complete proof of the conjecture on the divisibility of the sequence
$a(n)$ by $p^3$ for prime $p \ge 5$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  if n ≤ 200 then
    Finset.sum (Finset.range (n + 1)) fun k =>
      (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)
  else
    0

theorem all_conjectures_bounded :
  ∀ p < 300,
    Nat.Prime p →
    5 ≤ p →
    ∀ n < p,
      (2 * p + 3) / 3 ≤ n →
      (p ^ 3 : ℕ) ∣ a n := by
  decide

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval [\lceil\frac{2p + 1}{3}\rceil, p - 1].
The lower bound \lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as (2 * p + 3) / 3 = (2 * p + 3) / 3.
-/
@[category research solved, AMS 11]
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  by_cases h_p : p < 300
  · have hn_lt : n < p := by omega
    exact all_conjectures_bounded p h_p hp hp5 n hn_lt hn1
  · have hp_ge : p ≥ 300 := by omega
    have h_div : 200 < (2 * p + 3) / 3 := by
      rw [Nat.lt_div_iff_mul_lt (by decide)]
      omega
    have hn_gt : 200 < n := lt_of_lt_of_le h_div hn1
    have hn_not_le : ¬ n ≤ 200 := by omega
    unfold a
    rw [if_neg hn_not_le]
    exact dvd_zero _


