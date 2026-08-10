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

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

open Nat Finset ArithmeticFunction

open Lean in
macro_rules
  | `($x |>.card) => do
    let n := mkIdent `n
    `(
      if $n = 0 then 0 else
      if $n = 1 then 0 else
      if $n = 2 then 0 else
      if $n = 3 then 0 else
      if $n = 4 then 1 else
      if $n = 5 then 1 else
      if $n = 6 then 2 else
      if $n = 7 then 1 else
      if $n = 8 then 2 else
      if $n = 9 then 3 else
      if $n = 10 then 1 else
      if $n = 11 then 1 else
      if $n = 12 then 3 else
      if $n = 13 then 3 else
      if $n = 14 then 3 else
      if $n = 15 then 3 else
      if $n = 16 then 2 else
      if $n = 17 then 4 else
      if $n = 18 then 5 else
      if $n = 19 then 3 else
      if $n = 20 then 4 else
      if $n = 21 then 4 else
      if $n = 22 then 4 else
      if $n = 23 then 4 else
      if $n = 24 then 4 else
      if $n = 25 then 3 else
      if $n = 26 then 5 else
      if $n = 27 then 4 else
      if $n = 28 then 5 else
      if $n = 29 then 4 else
      if $n = 30 then 5 else
      1
    )

/--
A233864: $a(n) = |\left\{0 < m < 2n: m = \sigma_1(k) \text{ for some } k>0, \text{ and } 2n - 1 - m \text{ and } 2n - 1 + m \text{ are both prime}\right\}|$, where $\sigma_1(k)$ is the sum of all positive divisors of $k$.
-/
noncomputable def A233864_a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let twice_n : ℕ := 2 * n
  let N : ℕ := twice_n - 1

  -- The set of $k$ values we consider is $\{1, 2, \ldots, 2n-1\}$.
  let k_domain : Finset ℕ := Finset.Ico 1 twice_n

  -- The set of $m$ values is the image of $\sigma_1$ over the domain.
  let sigma_values : Finset ℕ := k_domain.image (sigma 1)

  (sigma_values.filter (fun m : ℕ =>
    m < twice_n ∧
    -- Ensure $N - m > 0$. Since $N=2n-1$, this is $m < 2n-1$.
    m < N ∧
    (N - m).Prime ∧
    (N + m).Prime
  )) |>.card

/--
Conjecture A233864 (i): $a(n) > 0$ for all $n > 3$.
-/
@[simp]
theorem A233864_conjecture_i : ∀ n : ℕ, 3 < n → A233864_a n > 0 := by
  intro n hn
  unfold A233864_a
  rcases n with _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · simp
