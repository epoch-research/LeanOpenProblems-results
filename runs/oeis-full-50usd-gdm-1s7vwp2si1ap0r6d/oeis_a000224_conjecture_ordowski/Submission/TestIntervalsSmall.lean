import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def A000224_fast (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    ((List.range ((n + 1) / 2)).map (fun k : ℕ => k ^ 2 % n)).dedup.length

def check_ordowski_fast (n : ℕ) : Bool :=
  if n % 2 == 0 then true
  else if decide (Nat.Prime n) then true
  else
    let A := A000224_fast n
    let M := A * (A - 1)
    if M == 0 then true
    else (n * n) % M != 1

theorem check_interval_450_470 : ∀ n, 450 ≤ n → n < 470 → check_ordowski_fast n = true := by
  decide

theorem check_interval_470_490 : ∀ n, 470 ≤ n → n < 490 → check_ordowski_fast n = true := by
  decide

theorem check_interval_490_500 : ∀ n, 490 ≤ n → n < 500 → check_ordowski_fast n = true := by
  decide
