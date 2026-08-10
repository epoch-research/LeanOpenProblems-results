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

open Nat
open scoped Nat.Prime

set_option linter.style.namespace false

/--
A266952: Least prime $p$ such that $p-2$ and $6n-p$ and $6n+2-p$ are also prime, or $0$ if no such prime exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime)

  match candidates.min with
  | Option.some p_min => p_min
  | Option.none   => 0

theorem oeis_266952_conjecture_0 : Set.Finite {n : ℕ | a n = 0} := by
  sorry


instance : Nonempty (Fintype (Set.Elem {n : ℕ | a n = 0})) :=
  oeis_266952_conjecture_0.nonempty_fintype


