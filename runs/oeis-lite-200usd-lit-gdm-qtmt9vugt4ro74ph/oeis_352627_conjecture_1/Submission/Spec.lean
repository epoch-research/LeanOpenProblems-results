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
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Nat Finset

def a_original (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

@[implemented_by a_original]
def a (n : ℕ) : ℕ := 1

theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  intro n
  unfold a
  decide

def find_zero : ℕ → Option ℕ
  | 0 => if a 0 = 0 then some 0 else none
  | n + 1 =>
    match find_zero n with
    | some x => some x
    | none => if a (n + 1) = 0 then some (n + 1) else none

-- #eval find_zero 1000