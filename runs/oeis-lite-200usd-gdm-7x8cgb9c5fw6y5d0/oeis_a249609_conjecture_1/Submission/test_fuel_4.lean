import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

def is_evil_fn (k : ℕ) : Bool := (k.bits.count true % 2) = 0

def bits_fuel : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2 == 1) :: bits_fuel fuel (n / 2)

lemma bits_eq_fuel (fuel : ℕ) (n : ℕ) (hfuel : n ≤ fuel) :
    n.bits = bits_fuel fuel n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    exact Nat.zero_bits
  | succ f ih =>
    dsimp [bits_fuel]
    by_cases hn : n = 0
    · subst hn
      exact Nat.zero_bits
    · rw [if_neg hn]
      have h_div : n / 2 ≤ f := by
        have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        omega
      by_cases hmod : n % 2 = 1
      · have hn_eq : n = 2 * (n / 2) + 1 := by
          rw [← Nat.div_add_mod n 2]
          omega
        have h_bits_eq : n.bits = true :: (n / 2).bits := by
          conv => lhs; rw [hn_eq]
          rw [Nat.bit1_bits]
        rw [h_bits_eq]
        rw [hmod]
        rw [← ih (n / 2) h_div]
        rfl
      · have hmod_zero : n % 2 = 0 := by omega
        have hn_eq : n = 2 * (n / 2) := by
          rw [← Nat.div_add_mod n 2]
          omega
        have h_div_ne : n / 2 ≠ 0 := by omega
        have h_bits_eq : n.bits = false :: (n / 2).bits := by
          conv => lhs; rw [hn_eq]
          rw [Nat.bit0_bits _ h_div_ne]
        rw [h_bits_eq]
        rw [hmod_zero]
        rw [← ih (n / 2) h_div]
        rfl

def is_evil_fast (k : ℕ) : Bool :=
  (bits_fuel k k).count true % 2 == 0

lemma is_evil_fn_eq_fast (k : ℕ) : is_evil_fn k = is_evil_fast k := by
  dsimp [is_evil_fn, is_evil_fast]
  have h_eq : k.bits = bits_fuel k k := bits_eq_fuel k k (by omega)
  rw [h_eq]

def find_min_m_fuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
    if m > n then 0
    else if is_evil_fast (n.choose m) then m
    else find_min_m_fuel n fuel (m + 1)

lemma find_min_m_eq_fuel (n : ℕ) (m : ℕ) (fuel : ℕ) (hfuel : n + 1 - m ≤ fuel) :
    a.find_min_m n (fun k => decide ((k.bits.count true % 2) = 0)) m = find_min_m_fuel n fuel m := by
  induction fuel generalizing m with
  | zero =>
    have hmn : m > n := by omega
    rw [a.find_min_m.eq_1]
    simp [hmn]
    rfl
  | succ f ih =>
    rw [a.find_min_m.eq_1]
    dsimp [find_min_m_fuel]
    by_cases hmn : m > n
    · simp [hmn]
    · simp [hmn]
      have h_evil_eq : (decide (List.count true (n.choose m).bits % 2 = 0)) = is_evil_fast (n.choose m) := by
        exact is_evil_fn_eq_fast (n.choose m)
      rw [h_evil_eq]
      by_cases heven : is_evil_fast (n.choose m)
      · simp [heven]
      · simp [heven]
        have h_fuel : n + 1 - (m + 1) ≤ f := by omega
        exact ih (m + 1) h_fuel

def a_fast (n : ℕ) : ℕ :=
  find_min_m_fuel n n 1

lemma a_eq_a_fast (n : ℕ) : a n = a_fast n := by
  dsimp [a, a_fast]
  have hfuel : n + 1 - 1 ≤ n := by omega
  exact find_min_m_eq_fuel n 1 n hfuel

lemma small_cases_fast : ∀ n < 15, a_fast n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  decide
