import Lean
open Lean

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def in_hull (F C : Int) : Bool :=
  0 * F + 1 * C + -128 ≤ 0 ∧
  -3 * F + 5 * C + 2 ≤ 0 ∧
  -20 * F + 31 * C + 235 ≤ 0 ∧
  -48 * F + 37 * C + 3369 ≤ 0 ∧
  -1 * F + 0 * C + 91 ≤ 0 ∧
  -7 * F + -15 * C + 82 ≤ 0 ∧
  -5 * F + -11 * C + 46 ≤ 0 ∧
  0 * F + -1 * C + -64 ≤ 0 ∧
  32 * F + -11 * C + -9728 ≤ 0 ∧
  3 * F + -1 * C + -911 ≤ 0 ∧
  64 * F + -21 * C + -19456 ≤ 0

def check_one (F C : Int) : Bool :=
  if in_hull F C then
    let F1 := F - C
    let C1 := -2 * C
    let ok1 :=
      if F1 ≥ 91 ∧ 3 * F1 ≥ 5 * C1 ∧ 3 * F1 ≥ -7 * C1 then
        in_hull F1 C1
      else true
    let ok2 :=
      if F % 2 ≠ 0 then
        let F2 := F - C
        let C2 := F - 2 * C
        if F2 ≥ 91 ∧ 3 * F2 ≥ 5 * C2 ∧ 3 * F2 ≥ -7 * C2 then
          in_hull F2 C2
        else true
      else true
    ok1 ∧ ok2
  else true

def loopC (F : Int) (C_val : Nat) : Option (Int × Int) :=
  match C_val with
  | 0 => none
  | c' + 1 =>
    let C := (c' : Int) - 64
    if ¬ check_one F C then some (F, C)
    else loopC F c'

def loopF (F_val : Nat) : Option (Int × Int) :=
  match F_val with
  | 0 => none
  | f' + 1 =>
    let F := (f' : Int) + 91
    match loopC F 193 with
    | some p => some p
    | none => loopF f'

#eval loopF 215
