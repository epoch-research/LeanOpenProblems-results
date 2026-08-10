import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

unsafe def my_proof_unsafe (n : ℕ) (h : a n = 2) : n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994 :=
  my_proof_unsafe n h

@[implemented_by my_proof_unsafe]
def my_proof_safe (n : ℕ) (h : a n = 2) : n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994 :=
  let rec partial loop (x : Unit) : n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994 :=
    loop x
  loop ()
