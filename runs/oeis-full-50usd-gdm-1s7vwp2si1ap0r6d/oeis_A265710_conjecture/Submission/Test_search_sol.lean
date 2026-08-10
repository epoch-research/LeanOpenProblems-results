import FormalConjectures.Util.ProblemImports

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

def search_sol (n : ℕ) (limit : ℕ) (h_bound : n < limit) : n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994 ∨ a_eval_nat n ≠ 2 :=
  match limit with
  | 0 => by contradiction
  | l + 1 =>
    if h_eq : n = l then
      h_eq ▸ (by decide)
    else
      search_sol n l (by omega)
