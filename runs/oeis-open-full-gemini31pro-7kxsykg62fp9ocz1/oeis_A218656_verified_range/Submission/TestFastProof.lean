import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ := card ((Icc 1 n).filter fun k : ℕ => Nat.Prime (k ^ 4 + (2 * n + 1 - k) ^ 4))

def first_prime_k (n : ℕ) (k rem : ℕ) : ℕ :=
  match rem with
  | 0 => 0
  | rem' + 1 =>
      let val := k ^ 4 + (2 * n + 1 - k) ^ 4
      if val.minFac == val then k
      else first_prime_k n (k + 1) rem'

def check_n (n : ℕ) : Bool :=
  first_prime_k n 1 n > 0

def check_all (m : ℕ) (n rem : ℕ) : Bool :=
  match rem with
  | 0 => true
  | rem' + 1 =>
      if check_n n then check_all m (n + 1) rem'
      else false

theorem check_n_implies_a_pos (n : ℕ) (hn : check_n n = true) : a n > 0 := sorry

theorem all_works : check_all 499999 1 499999 = true := by native_decide

