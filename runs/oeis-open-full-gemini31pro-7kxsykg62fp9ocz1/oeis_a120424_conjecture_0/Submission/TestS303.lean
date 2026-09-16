import Submission.S303

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

def cmp_state (a b : Nat × Int) : Ordering :=
  match compare a.1 b.1 with
  | Ordering.eq => compare a.2 b.2
  | ord => ord

def binSearch (fuel : Nat) (arr : Array (Nat × Int)) (k : Nat × Int) (low high : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if low > high then false
    else
      let mid := (low + high) / 2
      if h : mid < arr.size then
        let midVal := arr[mid]
        match cmp_state k midVal with
        | Ordering.eq => true
        | Ordering.lt => 
          if mid == 0 then false else binSearch fuel' arr k low (mid - 1)
        | Ordering.gt => binSearch fuel' arr k (mid + 1) high
      else false

def in_S303 (F : Nat) (C : Int) : Bool :=
  binSearch 30 S303 (F, C) 0 (S303.size - 1)

def check_closure : Bool :=
  Id.run do
    for (F, C) in S303 do
      let F1 := (F : Int) - C
      let C1 := -2 * C
      if F1 ≥ 91 ∧ 3 * F1 ≥ 5 * C1 ∧ 3 * F1 ≥ -7 * C1 then
        if ¬ in_S303 F1.toNat C1 then return false
      if F % 2 ≠ 0 then
        let F2 := (F : Int) - C
        let C2 := (F : Int) - 2 * C
        if F2 ≥ 91 ∧ 3 * F2 ≥ 5 * C2 ∧ 3 * F2 ≥ -7 * C2 then
          if ¬ in_S303 F2.toNat C2 then return false
    return true

theorem S303_is_closed : check_closure = true := by decide
