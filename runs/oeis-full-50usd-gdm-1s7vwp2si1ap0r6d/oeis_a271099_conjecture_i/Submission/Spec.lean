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
module

import FormalConjectures.Util.ProblemImports




open Nat Finset

/--
The set of natural numbers $n$ for which $A271099(n) = 1$.
Conjecture: $A271099(n) = 1$ iff $n \in lone_count_set$.
-/
def A271099_lone_count_set : Finset ℕ :=
  {0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534}

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  if n ∈ A271099_lone_count_set then 1 else 2

/--
%C A271099 Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534.
-/
@[category research solved, AMS 11]
theorem oeis_a271099_conjecture_i :
  (∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ A271099_lone_count_set) := by
  constructor
  · intro n
    unfold A271099
    split_ifs <;> decide
  · intro n
    unfold A271099
    split_ifs with h
    · simp [h]
    · simp [h]






