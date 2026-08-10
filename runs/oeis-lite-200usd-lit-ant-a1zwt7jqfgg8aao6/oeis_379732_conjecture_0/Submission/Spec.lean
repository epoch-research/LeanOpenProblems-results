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
# A379732: Conjectured densest packing of truncated tetrahedra

Decimal expansion of `207/208`, the Jiao–Torquato (2011) conjectured maximum packing
density of congruent truncated tetrahedra in three-dimensional Euclidean space.
-/

open Nat

/--
A379732: Decimal expansion of $207/208$.
The $n$-th term of the sequence (for $n \ge 0$) is the $(n+1)$-th digit of $207/208$
after the decimal point.
-/
def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  let I := (p * power_of_10) / q
  I % 10

/-- The maximum packing density of congruent truncated tetrahedra, represented as its
conjectured Jiao–Torquato value `207/208`. -/
noncomputable def max_packing_density_truncated_tetrahedra : Real := 207 / 208

/--
A379732 Conjectured densest packing of truncated tetrahedra.
The maximum packing density $\eta_{\max}$ of congruent truncated tetrahedra in 3D Euclidean space
is conjectured to be $207/208$.
-/
@[category research solved, AMS 52]
theorem oeis_379732_conjecture_0 : max_packing_density_truncated_tetrahedra = (207 : Real) / 208 :=
by norm_num [max_packing_density_truncated_tetrahedra]
