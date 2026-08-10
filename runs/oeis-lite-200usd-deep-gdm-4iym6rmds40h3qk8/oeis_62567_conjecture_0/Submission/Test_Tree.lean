import FormalConjectures.Util.ProblemImports

open Nat

def fast_rev (n : Nat) : Nat :=
  let rec loop (fuel : Nat) (n : Nat) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if n = 0 then acc
      else loop fuel' (n / 10) (acc * 10 + n % 10)
  loop n n 0

def search_tree (n : Nat) (k : Nat) (d : Nat) : Bool :=
  match d with
  | 0 =>
    if k > 0 ∧ k < 12345679 then
      (fast_rev (k * n)) % n == 0
    else
      false
  | d' + 1 =>
    search_tree n k d' || search_tree n (k + 2^d') d'

theorem test_decide : search_tree 81 1 12 = false := by decide
