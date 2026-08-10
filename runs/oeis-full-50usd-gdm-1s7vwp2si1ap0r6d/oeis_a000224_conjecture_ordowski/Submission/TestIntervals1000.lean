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

theorem check_interval_15_100 : ∀ n, 15 ≤ n → n < 100 → check_ordowski_fast n = true := by decide

theorem check_interval_100_150 : ∀ n, 100 ≤ n → n < 150 → check_ordowski_fast n = true := by decide

theorem check_interval_150_200 : ∀ n, 150 ≤ n → n < 200 → check_ordowski_fast n = true := by decide

theorem check_interval_200_250 : ∀ n, 200 ≤ n → n < 250 → check_ordowski_fast n = true := by decide

theorem check_interval_250_300 : ∀ n, 250 ≤ n → n < 300 → check_ordowski_fast n = true := by decide

theorem check_interval_300_350 : ∀ n, 300 ≤ n → n < 350 → check_ordowski_fast n = true := by decide

theorem check_interval_350_400 : ∀ n, 350 ≤ n → n < 400 → check_ordowski_fast n = true := by decide

theorem check_interval_400_450 : ∀ n, 400 ≤ n → n < 450 → check_ordowski_fast n = true := by decide

theorem check_interval_450_500 : ∀ n, 450 ≤ n → n < 500 → check_ordowski_fast n = true := by decide

theorem check_interval_500_520 : ∀ n, 500 ≤ n → n < 520 → check_ordowski_fast n = true := by decide

theorem check_interval_520_540 : ∀ n, 520 ≤ n → n < 540 → check_ordowski_fast n = true := by decide

theorem check_interval_540_560 : ∀ n, 540 ≤ n → n < 560 → check_ordowski_fast n = true := by decide

theorem check_interval_560_580 : ∀ n, 560 ≤ n → n < 580 → check_ordowski_fast n = true := by decide

theorem check_interval_580_600 : ∀ n, 580 ≤ n → n < 600 → check_ordowski_fast n = true := by decide

theorem check_interval_600_620 : ∀ n, 600 ≤ n → n < 620 → check_ordowski_fast n = true := by decide

theorem check_interval_620_640 : ∀ n, 620 ≤ n → n < 640 → check_ordowski_fast n = true := by decide

theorem check_interval_640_660 : ∀ n, 640 ≤ n → n < 660 → check_ordowski_fast n = true := by decide

theorem check_interval_660_680 : ∀ n, 660 ≤ n → n < 680 → check_ordowski_fast n = true := by decide

theorem check_interval_680_700 : ∀ n, 680 ≤ n → n < 700 → check_ordowski_fast n = true := by decide

theorem check_interval_700_720 : ∀ n, 700 ≤ n → n < 720 → check_ordowski_fast n = true := by decide

theorem check_interval_720_740 : ∀ n, 720 ≤ n → n < 740 → check_ordowski_fast n = true := by decide

theorem check_interval_740_760 : ∀ n, 740 ≤ n → n < 760 → check_ordowski_fast n = true := by decide

theorem check_interval_760_780 : ∀ n, 760 ≤ n → n < 780 → check_ordowski_fast n = true := by decide

theorem check_interval_780_800 : ∀ n, 780 ≤ n → n < 800 → check_ordowski_fast n = true := by decide

theorem check_interval_800_820 : ∀ n, 800 ≤ n → n < 820 → check_ordowski_fast n = true := by decide

theorem check_interval_820_840 : ∀ n, 820 ≤ n → n < 840 → check_ordowski_fast n = true := by decide

theorem check_interval_840_860 : ∀ n, 840 ≤ n → n < 860 → check_ordowski_fast n = true := by decide

theorem check_interval_860_880 : ∀ n, 860 ≤ n → n < 880 → check_ordowski_fast n = true := by decide

theorem check_interval_880_900 : ∀ n, 880 ≤ n → n < 900 → check_ordowski_fast n = true := by decide

theorem check_interval_900_920 : ∀ n, 900 ≤ n → n < 920 → check_ordowski_fast n = true := by decide

theorem check_interval_920_940 : ∀ n, 920 ≤ n → n < 940 → check_ordowski_fast n = true := by decide

theorem check_interval_940_960 : ∀ n, 940 ≤ n → n < 960 → check_ordowski_fast n = true := by decide

theorem check_interval_960_980 : ∀ n, 960 ≤ n → n < 980 → check_ordowski_fast n = true := by decide

theorem check_interval_980_1000 : ∀ n, 980 ≤ n → n < 1000 → check_ordowski_fast n = true := by decide