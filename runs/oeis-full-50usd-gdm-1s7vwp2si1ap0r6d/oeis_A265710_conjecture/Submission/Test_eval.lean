import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

#eval a 14

open Nat Finset

def sqrt_eval (n : ℕ) : ℕ :=
  ((List.range (Nat.min 220 (n + 2))).filter (fun i => i * i ≤ n)).getLastD 0

def divisors_fast (n : ℕ) : List ℕ :=
  let s := sqrt_eval n
  let small := (List.range (s + 1)).filter (fun d => d > 0 && n % d == 0)
  small.flatMap (fun d => if d * d = n then [d] else [d, n / d])

def sig_eval (d : ℕ) : ℕ :=
  (divisors_fast d).foldl (fun acc x => acc + x) 0

def a_eval_nat (n : ℕ) : ℕ :=
  let divs := divisors_fast n
  let L := divs.foldl (fun acc d => Nat.lcm acc (sig_eval d)) 1
  let N := divs.foldl (fun acc d => acc + L / sig_eval d) 0
  L / Nat.gcd N L

inductive Bug (α : Type) : Type where
  | mk : (Bug α → α) → Bug α

