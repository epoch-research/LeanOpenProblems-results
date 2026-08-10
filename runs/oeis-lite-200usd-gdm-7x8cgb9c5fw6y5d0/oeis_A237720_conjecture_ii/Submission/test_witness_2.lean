import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

def P_witness (n p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime ∧ p ≤ 16 * (sqrt (n + p)) + 1 ∧
    (p ≤ 11 ∧ n ≤ 182 → sqrt (n + p) ≤ 7) ∧
    (p = 2 ∧ sqrt (n + p) ≤ 16 → n ≤ 193) ∧ (p = 3 ∧ sqrt (n + p) ≤ 16 → n ≤ 192) ∧
    (p = 5 ∧ sqrt (n + p) ≤ 16 → n ≤ 191) ∧ (p = 7 ∧ sqrt (n + p) ≤ 16 → n ≤ 190) ∧ (p = 11 ∧ sqrt (n + p) ≤ 16 → n ≤ 189) ∧
    (p = 13 ∧ sqrt (n + p) ≤ 16 → n ≤ 188) ∧ (p = 17 ∧ sqrt (n + p) ≤ 16 → n ≤ 187) ∧ (p = 19 ∧ sqrt (n + p) ≤ 16 → n ≤ 186) ∧
    (p = 23 ∧ sqrt (n + p) ≤ 16 → n ≤ 185) ∧ (p = 29 ∧ sqrt (n + p) ≤ 16 → n ≤ 184) ∧ (p = 31 ∧ sqrt (n + p) ≤ 16 → n ≤ 183) ∧
    (p = 37 ∧ sqrt (n + p) ≤ 16 → n ≤ 182) ∧
    (p ≤ 3 ∧ n + p = sqrt (n + p) * sqrt (n + p) → sqrt (n + p) ≤ 16) ∧
    (sqrt (n + p) ≥ 18 → p ≤ 4 * (sqrt (n + p)) - 2)

set_option allowUnsafeReducibility true
attribute [local reducible] P_witness

#eval decide (P_witness 321 2)
