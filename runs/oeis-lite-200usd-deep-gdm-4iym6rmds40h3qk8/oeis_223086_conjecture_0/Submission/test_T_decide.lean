import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000

def T : ℕ → ℕ
  | 0 => 65
  | i + 1 => (4 * T i + 3) / 3

def V_1100 : ℕ := 114366393100376302897582038760792701

lemma test : V_1100 ≥ T 89 := by decide
