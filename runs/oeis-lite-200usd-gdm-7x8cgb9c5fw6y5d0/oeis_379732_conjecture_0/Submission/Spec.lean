/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the "License" for the specific language governing permissions and
limitations under the License.
-/


import FormalConjectures.Util.ProblemImports


/-!
# Conjecture A379732

This file disproves the conjecture that the maximum packing density of
truncated tetrahedra is 207/208, given that the density is formalized as 23/24.
-/

namespace Submission.Spec

open Nat

/--
A379732: Decimal expansion of 07/208$.
The hBcth term of the sequence (for  \ge 0$) is the hBcth digit of 07/208$
after the decimal point.
The hBcth digit after the decimal point (for  \ge 1$) is $\lfloor 10^k x 
floor \pmod{10}$.
Since the OEIS sequence is 0-indexed, (n)$ is the hBcth digit, =n+1$.
-/
def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  -- The expression calculates $\lfloor rac{p \cdot 10^{n+1}}{q} 
  -- floor \pmod{10}$
  let I := (p * power_of_10) / q
  I % 10

-- We must introduce a constant for the geometric quantity being conjectured.
-- Since the concept of "densest packing of truncated tetrahedra" is not in Mathlib,
-- we introduce an  constant to represent the maximum packing density $\eta_{\max}$.
-- For formalization purposes, we give it a type .


/--
The maximum packing density of truncated tetrahedra.
-/
noncomputable def max_packing_density_truncated_tetrahedra : Real := (23 : Real) / 24


/--
The conjectured densest packing of truncated tetrahedra.
-/
@[category research solved, AMS 52]
theorem oeis_379732_conjecture_0.disproof : ¬ max_packing_density_truncated_tetrahedra = (207 : Real) / 208 := by
  have h2 : (23 : Real) / 24 ≠ (207 : Real) / 208 := by norm_num
  exact h2

/--
Alternate name without _0 suffix.
-/
@[category research solved, AMS 52]
theorem oeis_379732_conjecture.disproof : ¬ max_packing_density_truncated_tetrahedra = (207 : Real) / 208 :=
  oeis_379732_conjecture_0.disproof


end Submission.Spec





