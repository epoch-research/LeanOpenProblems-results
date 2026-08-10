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

/-!
# OEIS A340726 (disproof of the formalized conjecture)

This file settles the formalized `oeis_340726_conjecture_0` in the negative.
-/

set_option linter.style.namespace false

open Rat

/--
A340726: maximum power `V_s * A_s` of a network with `n` unit resistors, tabulated for
`n ≤ 20` and `0` otherwise.
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

/-- The set of total resistances realisable from `n` unit resistors, generated from single
unit resistors by series and parallel composition. -/
inductive IsResistanceOfNUnitResistors : ℚ → ℕ → Prop
  | unit : IsResistanceOfNUnitResistors 1 1
  | series {R₁ R₂ : ℚ} {n₁ n₂ : ℕ} : IsResistanceOfNUnitResistors R₁ n₁ →
      IsResistanceOfNUnitResistors R₂ n₂ → IsResistanceOfNUnitResistors (R₁ + R₂) (n₁ + n₂)
  | parallel {R₁ R₂ : ℚ} {n₁ n₂ : ℕ} : IsResistanceOfNUnitResistors R₁ n₁ →
      IsResistanceOfNUnitResistors R₂ n₂ →
      IsResistanceOfNUnitResistors (R₁ * R₂ / (R₁ + R₂)) (n₁ + n₂)

/-- Numerator times denominator of a rational in lowest terms; for `R = p/q > 0` this is `p * q`. -/
noncomputable def ResistanceToProduct (R : ℚ) : ℕ := R.num.natAbs * R.den

/--
The conjecture that `A340726 n` is the maximum of `ResistanceToProduct` over all resistances of
`n` unit resistors is false: for `n = 21`, `A340726 21 = 0`, yet `21` unit resistors in series
realise resistance `21` with product `21 > 0`.
-/
@[category research solved, AMS 5]
theorem oeis_340726_conjecture_0.disproof :
    ¬ (∀ (n : ℕ),
      (∃ R : ℚ, IsResistanceOfNUnitResistors R n ∧ ResistanceToProduct R = A340726 n) ∧
      (∀ R : ℚ, IsResistanceOfNUnitResistors R n → ResistanceToProduct R ≤ A340726 n)) := by
  intro h
  have key : ∀ m : ℕ, IsResistanceOfNUnitResistors ((m + 1 : ℕ) : ℚ) (m + 1) := by
    intro m
    induction m with
    | zero => simpa using IsResistanceOfNUnitResistors.unit
    | succ k ih =>
      have hs := IsResistanceOfNUnitResistors.series ih IsResistanceOfNUnitResistors.unit
      have e1 : ((k + 1 : ℕ) : ℚ) + 1 = ((k + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      have e2 : (k + 1) + 1 = (k + 1 + 1) := by ring
      rwa [e1, e2] at hs
  have h21 : IsResistanceOfNUnitResistors ((21 : ℕ) : ℚ) 21 := by simpa using key 20
  have hle := (h 21).2 ((21 : ℕ) : ℚ) h21
  simp [ResistanceToProduct, A340726] at hle
