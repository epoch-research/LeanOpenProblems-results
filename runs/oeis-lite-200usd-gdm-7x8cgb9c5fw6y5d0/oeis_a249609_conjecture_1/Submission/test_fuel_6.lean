import FormalConjectures.Util.ProblemImports

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

lemma find_min_m_fuel_ge_of_exists (n : ℕ) (fuel : ℕ) (m k : ℕ)
    (hmk : m ≤ k) (hkn : k ≤ n) (hfuel : n + 1 - m ≤ fuel)
    (hevil : is_evil_fast (n.choose k) = true) :
    find_min_m_fuel n fuel m ≥ m := by
  induction fuel generalizing m with
  | zero =>
    have : n + 1 - m = 0 := by omega
    have : n + 1 ≤ m := by omega
    omega
  | succ f ih =>
    dsimp [find_min_m_fuel]
    by_cases hmn : m > n
    · omega
    · simp only [hmn, ↓reduceIte]
      by_cases he : is_evil_fast (n.choose m) = true
      · simp [he]
      · have he_false : is_evil_fast (n.choose m) = false := by
          cases h : is_evil_fast (n.choose m)
          · rfl
          · contradiction
        simp [he_false]
        have h_mk_ne : m ≠ k := by
          intro h_eq
          subst h_eq
          rw [hevil] at he_false
          contradiction
        have h_m1_k : m + 1 ≤ k := by omega
        have h_fuel : n + 1 - (m + 1) ≤ f := by omega
        have ih_val := ih (m + 1) h_m1_k h_fuel
        omega
