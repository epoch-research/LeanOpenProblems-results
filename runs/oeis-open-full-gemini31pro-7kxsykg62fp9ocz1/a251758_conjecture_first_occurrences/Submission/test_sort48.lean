import Mathlib

def list_divisors_chunked (n : ℕ) : List ℕ :=
  let rec loop (start fuel : ℕ) : List ℕ :=
    match fuel with
    | 0 => []
    | f + 1 =>
      let c := (List.range 10000).map (· + start) |>.filter (fun x => if h : x > 0 then n % x == 0 else false)
      c ++ loop (start + 10000) f
  loop 0 (n / 10000 + 1)

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t1 : (list_divisors_chunked 6678671).length = 32 := by decide
