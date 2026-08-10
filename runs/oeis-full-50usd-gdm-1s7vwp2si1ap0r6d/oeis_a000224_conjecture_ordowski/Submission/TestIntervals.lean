import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

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

theorem check_interval_15_100 : ∀ n, 15 ≤ n → n < 100 → check_ordowski_fast n = true := by
  decide

theorem check_interval_100_150 : ∀ n, 100 ≤ n → n < 150 → check_ordowski_fast n = true := by
  decide

theorem check_interval_150_200 : ∀ n, 150 ≤ n → n < 200 → check_ordowski_fast n = true := by
  decide

theorem check_interval_200_250 : ∀ n, 200 ≤ n → n < 250 → check_ordowski_fast n = true := by
  decide

theorem check_interval_250_300 : ∀ n, 250 ≤ n → n < 300 → check_ordowski_fast n = true := by
  decide

theorem check_interval_300_350 : ∀ n, 300 ≤ n → n < 350 → check_ordowski_fast n = true := by
  decide

theorem check_interval_350_370 : ∀ n, 350 ≤ n → n < 370 → check_ordowski_fast n = true := by
  decide

theorem check_interval_370_390 : ∀ n, 370 ≤ n → n < 390 → check_ordowski_fast n = true := by
  decide

theorem check_interval_390_410 : ∀ n, 390 ≤ n → n < 410 → check_ordowski_fast n = true := by
  decide

theorem check_interval_410_430 : ∀ n, 410 ≤ n → n < 430 → check_ordowski_fast n = true := by
  decide

theorem check_interval_430_450 : ∀ n, 430 ≤ n → n < 450 → check_ordowski_fast n = true := by
  decide

theorem check_interval_450_460 : ∀ n, 450 ≤ n → n < 460 → check_ordowski_fast n = true := by
  decide

theorem check_interval_460_470 : ∀ n, 460 ≤ n → n < 470 → check_ordowski_fast n = true := by
  decide

theorem check_interval_470_480 : ∀ n, 470 ≤ n → n < 480 → check_ordowski_fast n = true := by
  decide

theorem check_interval_480_490 : ∀ n, 480 ≤ n → n < 490 → check_ordowski_fast n = true := by
  decide

theorem check_interval_490_500 : ∀ n, 490 ≤ n → n < 500 → check_ordowski_fast n = true := by
  decide
