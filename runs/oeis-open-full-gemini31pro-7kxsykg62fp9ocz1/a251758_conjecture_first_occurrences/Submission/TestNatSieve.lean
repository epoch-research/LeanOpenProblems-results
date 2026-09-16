import Mathlib

def mark_mults_tree (start step len f : ℕ) : ℕ :=
  match f with
  | 0 => 0
  | f' + 1 =>
    if len == 0 then 0
    else if len == 1 then (1 <<< start)
    else
      let half := len / 2
      mark_mults_tree start step half f' ||| mark_mults_tree (start + half * step) step (len - half) f'

def build_sieve (limit : ℕ) : ℕ :=
  let p_limit := 2584
  let rec loop (p f : ℕ) (acc : ℕ) : ℕ :=
    match f with
    | 0 => acc
    | f' + 1 =>
      if p > p_limit then acc
      else if (acc &&& (1 <<< p)) == 0 then
        let num_mults := (limit - p * p) / p + 1
        let mask := mark_mults_tree (p * p) p num_mults 200
        loop (p + 1) f' (acc ||| mask)
      else
        loop (p + 1) f' acc
  loop 2 p_limit 0

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : (build_sieve 1000000 &&& (1 <<< 999983)) == 0 := by decide
