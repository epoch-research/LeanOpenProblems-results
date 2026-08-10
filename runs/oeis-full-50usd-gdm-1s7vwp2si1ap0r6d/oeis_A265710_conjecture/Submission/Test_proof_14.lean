import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

-- Bounded list-based square root for fast kernel evaluation (for n <= 45994)
def sqrt_eval (n : ℕ) : ℕ :=
  ((List.range (Nat.min 220 (n + 2))).filter (fun i => i * i ≤ n)).getLastD 0

-- Bounded fast list of divisors
def divisors_fast (n : ℕ) : List ℕ :=
  let s := sqrt_eval n
  let small := (List.range (s + 1)).filter (fun d => d > 0 && n % d == 0)
  small.flatMap (fun d => if d * d = n then [d] else [d, n / d])

-- Sum of divisors in Nat
def sig_eval (d : ℕ) : ℕ :=
  (divisors_fast d).foldl (fun acc x => acc + x) 0

-- Fast kernel evaluator for the A265710 function
def a_eval_nat (n : ℕ) : ℕ :=
  let divs := divisors_fast n
  let L := divs.foldl (fun acc d => Nat.lcm acc (sig_eval d)) 1
  let N := divs.foldl (fun acc d => acc + L / sig_eval d) 0
  L / Nat.gcd N L

theorem a_eval_14 : a_eval_nat 14 = 2 := by decide
theorem a_eval_244 : a_eval_nat 244 = 2 := by decide
theorem a_eval_494 : a_eval_nat 494 = 2 := by decide
theorem a_eval_45994 : a_eval_nat 45994 = 2 := by decide
theorem test_norm_num : (1/1 : Rat) + 1/3 + 1/8 + 1/24 = 3/2 := by norm_num
