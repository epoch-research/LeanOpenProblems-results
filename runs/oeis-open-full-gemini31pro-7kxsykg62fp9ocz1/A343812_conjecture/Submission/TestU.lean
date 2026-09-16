import Submission.Spec

open Nat Finset

def p_list : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

def p_lean (i : ℕ) : ℕ := p_list.getD i 0

def S_lean (n : ℕ) : ℕ := (range n).sum p_lean

def a_lean (n : ℕ) : ℕ := (range n).sum (fun i => S_lean n % p_lean i)

#eval (List.range 15).map a_lean
