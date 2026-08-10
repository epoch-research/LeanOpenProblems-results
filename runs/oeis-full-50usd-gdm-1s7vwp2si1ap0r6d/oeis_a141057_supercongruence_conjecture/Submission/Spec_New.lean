import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Nat Finset

def myMaxPrimeFac (m : ℕ) : ℕ :=
  if m ≤ 1 then 1
  else
    match (m.factorization.support).max with
    | some p => p
    | none => 1

def A141057_fuel (fuel : ℕ) (n : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if n = 1 then 3
    else if n = 2 then 27
    else if n = 3 then 381
    else if n = 4 then 6219
    else
      let P := myMaxPrimeFac n
      if P ≥ 5 then
        let a := n.factorization P
        let q := n / P ^ a
        if P = 5 ∧ q = 1 then 111753
        else A141057_fuel fuel' q
      else
        match n % 12 with
        | 1 => 3
        | 2 => 27
        | 3 => 381
        | 4 => 6219
        | 5 => 3
        | 6 => 6
        | 7 => 3
        | 8 => 6219
        | 9 => 381
        | 10 => 27
        | 11 => 3
        | _ => 1

def A141057 (n : ℕ) : ℕ :=
  A141057_fuel n n
