import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
open Nat List

def bits_fuel : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2 == 1) :: bits_fuel fuel (n / 2)

def is_evil_fast (k : ℕ) : Bool :=
  (bits_fuel k k).count true % 2 == 0

def find_min_m_fuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
    if m > n then 0
    else if is_evil_fast (n.choose m) then m
    else find_min_m_fuel n fuel (m + 1)

def a_fast (n : ℕ) : ℕ :=
  find_min_m_fuel n n 1

lemma chunk_1 : ∀ n < 500, a_fast n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by decide
lemma chunk_2 : ∀ n < 1000, n ≥ 500 → a_fast n ≠ 0 := by decide
lemma chunk_3 : ∀ n < 1500, n ≥ 1000 → a_fast n ≠ 0 := by decide
lemma chunk_4 : ∀ n < 2000, n ≥ 1500 → a_fast n ≠ 0 := by decide
lemma chunk_5 : ∀ n < 2500, n ≥ 2000 → a_fast n ≠ 0 := by decide
lemma chunk_6 : ∀ n < 3000, n ≥ 2500 → a_fast n ≠ 0 := by decide
