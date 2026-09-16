import FormalConjectures.Util.ProblemImports
open Nat

def rev_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

def check_k (n k : ℕ) : Bool :=
  (rev_nat (k * n)) % n == 0

def check_all_k (n max_k : ℕ) : Bool :=
  let rec loop (k : ℕ) : Bool :=
    if k >= max_k then false
    else if check_k n k then true
    else loop (k + 1)
  loop 1

#eval! check_all_k 81 100000
