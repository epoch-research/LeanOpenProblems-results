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

def find_min_m_fuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
    if m > n then 0
    else if is_evil_fn (n.choose m) then m
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
      by_cases hevil : (List.count true (n.choose m).bits % 2 = 0)
      · have hevil_bool : (decide (List.count true (n.choose m).bits % 2 = 0)) = true := decide_eq_true hevil
        simp [is_evil_fn, hevil]
      · have hevil_bool : (decide (List.count true (n.choose m).bits % 2 = 0)) = false := decide_eq_false hevil
        simp [is_evil_fn, hevil]
        have h_fuel : n + 1 - (m + 1) ≤ f := by omega
        exact ih (m + 1) h_fuel

def a_fast (n : ℕ) : ℕ :=
  find_min_m_fuel n n 1

lemma a_eq_a_fast (n : ℕ) : a n = a_fast n := by
  dsimp [a, a_fast]
  have hfuel : n + 1 - 1 ≤ n := by omega
  exact find_min_m_eq_fuel n 1 n hfuel

lemma small_cases_fast : ∀ n < 30, a_fast n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  decide

lemma small_cases : ∀ n < 30, a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  intro n hn
  rw [a_eq_a_fast]
  exact small_cases_fast n hn
