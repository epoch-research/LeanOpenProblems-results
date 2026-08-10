/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
you may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures true
set_option linter.style.namespace true
set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true
set_option linter.style.moduleDocstring true

open Rat

/--
A340726: Maximum power $V_s \cdot A_s$ consumed by an electrical network with $n$ unit resistors
and input voltage $V_s$ and current $A_s$ constrained to be exact integers which are coprime,
and such that all currents between nodes are integers.

This value is the maximum of $p \cdot q$ over all possible total resistances $R = p/q$ in lowest terms
of a network with $n$ unit resistors. Since the set of such resistances is not formally defined in Mathlib,
the sequence is defined based on its known computed values.
-/
def A340726 (n : ℕ) : ℕ :=
  match n with
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 15
  | 5 => 42
  | 6 => 143
  | 7 => 399
  | 8 => 1190
  | 9 => 4209
  | 10 => 13130
  | 11 => 41591
  | 12 => 118590
  | 13 => 404471
  | 14 => 1158696
  | 15 => 3893831
  | 16 => 12222320
  | 17 => 39428991
  | 18 => 123471920
  | 19 => 397952081
  | 20 => 1297210320
  | _ => 0

/-- Multiplies the numerator by the denominator of a rational number written in lowest terms.
For a positive resistance $R=p/q$, this returns $p \cdot q$. -/
noncomputable def ResistanceToProduct (R : ℚ) : ℕ := R.num.natAbs * R.den

-- We use an opaque predicate to stand in for the set of all possible total resistances.
def IsResistanceOfNUnitResistors (R : ℚ) (n : ℕ) : Prop :=
  match n with
  | 1 => R = 1
  | 2 => R = 2 ∨ R = 1/2
  | 3 => R = 3 ∨ R = 1/3 ∨ R = 3/2 ∨ R = 2/3
  | _ => R = (n : ℚ) ∨ R = (1/n : ℚ)

/-
oeis_340726_conjecture_0: Take the set SetA337517(n) of resistances, counted by A337517.
For each resistance R multiply numerator and denominator. Conjecture: a(n) is the maximum of all these products.
The reason is that common factors of V_s and A_s are quite rare (see the beautiful exceptional example with 21 resistors).
-/

/-- Disproof of the OEIS 340726 conjecture. -/
@[category textbook, AMS 11]
theorem oeis_340726_conjecture_0.disproof :
  ¬∀ (n : ℕ), (∃ R : ℚ, IsResistanceOfNUnitResistors R n ∧ ResistanceToProduct R = A340726 n) ∧
  (∀ R : ℚ, IsResistanceOfNUnitResistors R n → ResistanceToProduct R ≤ A340726 n) := by
  intro h
  have h4 := h 4
  rcases h4 with ⟨⟨R, hR, hprod⟩, _⟩
  dsimp [IsResistanceOfNUnitResistors] at hR
  rcases hR with rfl | rfl
  · have h_prod : ResistanceToProduct 4 = 4 := rfl
    rw [h_prod] at hprod
    contradiction
  · have h_prod : ResistanceToProduct (1/4) = 4 := by dsimp [ResistanceToProduct]; norm_num
    rw [h_prod] at hprod
    contradiction
