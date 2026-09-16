import Submission.Spec

def check_all (n : ℕ) : Bool :=
  let c1 := if n ≥ 2 then A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0 else true
  let c2 := if n ≥ 6 then A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0 else true
  let odd_part :=
    let rec go (x : ℕ) : ℕ := if x = 0 then 0 else if x % 2 == 0 then go (x / 2) else x
    go n
  let c3 :=
    if n > 0 ∧ odd_part % 4 == 1 ∧ n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804 then
      A274274 n ≠ 0
    else true
  c1 ∧ c2 ∧ c3

def find_ce (fuel : ℕ) (n : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | f + 1 => if !check_all n then some n else find_ce f (n + 1)

#eval find_ce 100 0
