import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def divPairs (n : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | d, (fuel+1) =>
    if n < d*d then 0
    else (if n % d == 0 then (if d*d == n then 1 else 2) else 0) + divPairs n (d+1) fuel

def tauFast (n : ℕ) : ℕ := if n == 0 then 0 else divPairs n 1 (n+1)

def stepOne (c4 c2 a : ℕ) : ℕ × ℕ × Bool :=
  let t := tauFast a
  let ok := if t == 2 && Nat.ble 37 a then Nat.ble (c2+1) c4 else true
  (c4 + (if t == 4 then 1 else 0), c2 + (if t == 2 then 1 else 0), ok)

def goTree : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × Bool
  | 0, c4, c2, _a, _b => (c4, c2, true)
  | (depth+1), c4, c2, a, b =>
    if b ≤ a then (c4, c2, true)
    else if a + 1 == b then stepOne c4 c2 a
    else
      match goTree depth c4 c2 a ((a + b) / 2) with
      | (c4', c2', ok1) =>
        match goTree depth c4' c2' ((a + b) / 2) b with
        | (c4'', c2'', ok2) => (c4'', c2'', ok1 && ok2)

def treeCheck (N : ℕ) : Bool := (goTree 20 0 0 0 N).2.2

example : treeCheck 11000 = true := by decide
