import FormalConjectures.Util.ProblemImports

import FormalConjectures.Util.ProblemImports

noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

def check_digits_01_fuel (fuel : Nat) (n : Nat) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if n = 0 then true
    else
      let d := n % 10
      (d == 0 || d == 1) && check_digits_01_fuel f (n / 10)

lemma digits_step (n : ℕ) (hn : n ≠ 0) : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) := by
  have h_div_stmt : n % 10 + 10 * (n / 10) = n := Nat.mod_add_div n 10
  nth_rw 1 [← h_div_stmt]
  apply Nat.digits_add 10 (by norm_num) (n % 10) (n / 10) (Nat.mod_lt _ (by norm_num))
  by_cases h_div : n / 10 = 0
  · left
    have h_or : 10 = 0 ∨ n < 10 := Nat.div_eq_zero_iff.mp h_div
    have h_lt : n < 10 := by omega
    have h_mod : n % 10 = n := Nat.mod_eq_of_lt h_lt
    rw [h_mod]
    exact hn
  · right
    exact h_div

theorem check_digits_01_fuel_ok : ∀ (fuel : Nat) (n : Nat),
    check_digits_01_fuel fuel n = true → (Nat.digits 10 n).length ≤ fuel → ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1
  | 0, n, _, h_len => by
    have : (Nat.digits 10 n).length = 0 := by omega
    have : Nat.digits 10 n = [] := List.eq_nil_of_length_eq_zero this
    rw [this]
    intro d hd; contradiction
  | f + 1, n, h, h_len => by
    by_cases hn : n = 0
    · subst hn
      intro d hd
      simp [Nat.digits_zero] at hd
    · unfold check_digits_01_fuel at h
      simp [hn] at h
      have h_digits := digits_step n hn
      rw [h_digits]
      intro d hd
      cases hd with
      | head => exact h.1
      | tail _ h_mem =>
        have h_len_arg := h_len
        have h_len' : (Nat.digits 10 (n / 10)).length ≤ f := by
          rw [h_digits] at h_len_arg
          simp only [List.length_cons] at h_len_arg
          omega
        exact check_digits_01_fuel_ok f (n / 10) h.2 h_len' d h_mem

lemma digits_len_le_of_lt (w : Nat) (h : w < 10^30) : (Nat.digits 10 w).length ≤ 30 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 30 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

def witness_fast (n : Nat) : Nat :=
  match n with
  | 17 => 11101
  | 18 => 1111111110
  | 19 => 11001
  | 20 => 100
  | 21 => 10101
  | 22 => 110
  | 23 => 110101
  | 24 => 111000
  | 25 => 100
  | _ => 1

def verify_witness_fast (n : Nat) : Bool :=
  let w := witness_fast n
  (0 < w) && (w % n == 0) && check_digits_01_fuel 30 w && (w ≤ (10^27 - 1) / 9)

theorem verify_witness_ok (n : Nat) (h : verify_witness_fast n = true) : A004290 n ≤ (10^27 - 1) / 9 := by
  unfold verify_witness_fast at h
  simp at h
  have h_pos : 0 < witness_fast n := h.1.1.1
  have h_div : n ∣ witness_fast n := Nat.dvd_of_mod_eq_zero h.1.1.2
  have h_fuel : check_digits_01_fuel 30 (witness_fast n) = true := h.1.2
  have h_bound : witness_fast n ≤ (10^27 - 1) / 9 := h.2
  have h_digits : ∀ d ∈ Nat.digits 10 (witness_fast n), d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 30 (witness_fast n) h_fuel
    have h_lt : witness_fast n < 10^30 := by
      calc witness_fast n ≤ (10^27 - 1) / 9 := h_bound
        _ < 10^27 := by
          apply Nat.div_lt_of_lt_mul
          have : 9 * 10^27 > 10^27 - 1 := by omega
          omega
        _ < 10^30 := by
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
    exact digits_len_le_of_lt (witness_fast n) h_lt
  have h_mem : witness_fast n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  exact le_trans h_le h_bound

def check_range (start : Nat) (count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 => verify_witness_fast start && check_range (start + 1) c

theorem check_range_ok : ∀ (count : Nat) (start : Nat), check_range start count = true →
  ∀ (n : Nat), start ≤ n → n < start + count → verify_witness_fast n = true
  | 0, start, h, n, h_ge, h_lt => by
    omega
  | c + 1, start, h, n, h_ge, h_lt => by
    unfold check_range at h
    rw [Bool.and_eq_true] at h
    have h_start := h.1
    have h_rest := h.2
    by_cases hn : n = start
    · subst hn; exact h_start
    · have h_ge' : start + 1 ≤ n := by omega
      have h_lt' : n < (start + 1) + c := by omega
      exact check_range_ok c (start + 1) h_rest n h_ge' h_lt'

theorem test_range_17_25 : check_range 17 9 = true := by decide

theorem test_large_helper (n : ℕ) (hn : n < 26) (hn17 : n ≥ 17) : A004290 n ≤ (10^27 - 1) / 9 := by
  have h_fast : verify_witness_fast n = true := by
    apply check_range_ok 9 17 test_range_17_25 n hn17 hn
  exact verify_witness_ok n h_fast

