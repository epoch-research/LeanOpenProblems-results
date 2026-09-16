import Mathlib
def a_comp (n : ℕ) : ℕ :=
  let divs := n.divisors
  let tau_n := divs.card
  let sum_d := divs.sum (fun d => d * (Nat.divisors d).card)
  sum_d - n * tau_n
def check_range (start stop : ℕ) : Bool :=
  (List.range (stop - start)).all (fun i => let n := start + i; if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)
def main : IO Unit := do
  let start ← IO.monoMsNow
  let res := check_range 30000 40000
  let stop ← IO.monoMsNow
  IO.println s!"Result: {res}, Time: {stop - start} ms"
