import Submission.S303

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def cmp_state (F1 : Nat) (C1 : Int) (F2 : Nat) (C2 : Int) : Ordering :=
  match compare F1 F2 with
  | Ordering.eq => compare C1 C2
  | ord => ord

def in_S303 : StateTree → Nat → Int → Bool
| StateTree.leaf, _, _ => false
| StateTree.node F C left right, kF, kC =>
  match cmp_state kF kC F C with
  | Ordering.eq => true
  | Ordering.lt => in_S303 left kF kC
  | Ordering.gt => in_S303 right kF kC

def check_list : List (Nat × Int) → Bool
| [] => true
| (F, C) :: rest =>
  let F1 := (F : Int) - C
  let C1 := -2 * C
  let ok1 :=
    if F1 ≥ 91 ∧ 3 * F1 ≥ 5 * C1 ∧ 3 * F1 ≥ -7 * C1 then
      in_S303 S303_tree F1.toNat C1
    else true
  let ok2 :=
    if F % 2 ≠ 0 then
      let F2 := (F : Int) - C
      let C2 := (F : Int) - 2 * C
      if F2 ≥ 91 ∧ 3 * F2 ≥ 5 * C2 ∧ 3 * F2 ≥ -7 * C2 then
        in_S303 S303_tree F2.toNat C2
      else true
    else true
  if ok1 ∧ ok2 then check_list rest else false

def initial_check : Bool :=
  let ok1 := ¬ in_S303 S303_tree 137 46
  let ok2 := check_list S303_list
  ok1 ∧ ok2

theorem S303_is_closed : initial_check = true := by decide
