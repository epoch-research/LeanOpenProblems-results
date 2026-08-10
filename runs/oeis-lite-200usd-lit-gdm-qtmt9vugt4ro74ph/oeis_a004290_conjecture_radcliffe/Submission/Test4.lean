import FormalConjectures.Util.ProblemImports

open Nat Set

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

lemma digits_len_le_of_lt_46 (w : Nat) (h : w < 10^46) : (Nat.digits 10 w).length ≤ 46 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 46 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

lemma A004290_76923_lt : A004290 76923 < (10^45 - 1)/9 := by
  let W : ℕ := 1000001010001010101110101110111110111111111
  have h_pos : 0 < W := by decide
  have h_div : 76923 ∣ W := by
    use 13000026130039261353692668124112555557
  have h_fuel : check_digits_01_fuel 46 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 46 W h_fuel
    have h_lt : W < 10^46 := by decide
    exact digits_len_le_of_lt_46 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 76923 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^45 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound


lemma digits_len_le_of_lt_37 (w : Nat) (h : w < 10^37) : (Nat.digits 10 w).length ≤ 37 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 37 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

lemma A004290_10989_lt : A004290 10989 < (10^37 - 1)/9 := by
  let W : ℕ := 1010101010101010101110111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 10989 ∣ W := by
    use 91919283838475757676777787888899
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 10989 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_29997_lt : A004290 29997 < (10^37 - 1)/9 := by
  let W : ℕ := 1111111101111111111111111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 29997 ∣ W := by
    use 37040740777781481851888892592963
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 29997 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_32967_lt : A004290 32967 < (10^37 - 1)/9 := by
  let W : ℕ := 1010101010101010101111111111111110111
  have h_pos : 0 < W := by decide
  have h_div : 32967 ∣ W := by
    use 30639761279491919225622929326633
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 32967 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

axiom A004290_le_ten_pow_mul (n k : ℕ) (d : ℕ) (hd : d ∣ 10^k) (hu : d ∣ n) (hn : n > 0) :
    A004290 n ≤ 10^k * A004290 (n / d)

axiom dvd_pow_ten_sub_one (n : ℕ) : 9 ∣ 10^n - 1

axiom test_large_k5 (n : ℕ) (hn : n < 10000) (hn17 : n ≥ 17) : A004290 (n / Nat.gcd n 100) < (10^30 - 1) / 9


def check_range_k5_5digit_fast (start count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 =>
    if start == 10989 || start == 29997 || start == 32967 || start == 69993 || start == 76923 || start == 89991 then
      check_range_k5_5digit_fast (start + 1) c
    else if Nat.gcd start 100 == 1 then
      verify_witness_fast_k5 start && check_range_k5_5digit_fast (start + 1) c
    else
      check_range_k5_5digit_fast (start + 1) c

theorem test_range_5digit_1 : check_range_k5_5digit_fast 10000 1000 = true := by decide

theorem test_compile (n k d3 : ℕ) (hn_pos : n > 0) (hu3_pos : n / d3 > 0)
    (hd3 : d3 ∣ 10^(k-3)) (hu3 : d3 ∣ n) (hn : n < 10^k - 1)
    (hu3_ge : n / d3 ≥ 10000) (hu3_76923 : n / d3 ≠ 76923) (hk : k ≥ 5) :
    A004290 n < (10^(9 * k) - 1) / 9 := by
  let u3 := n / d3
  by_cases hu3_cases : u3 = 10989 ∨ u3 = 21978
  · rcases hu3_cases with rfl | rfl
    · -- u3 = 10989
      have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
        have h_pow : 8 * k - 3 ≥ 37 := by omega
        have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
          apply Nat.div_le_div_right
          have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
          omega
        exact lt_of_lt_of_le A004290_10989_lt h_le
      have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
      have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
        have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
        have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
        have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
          rw [h_eqB]
          calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
            _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
              apply Nat.mul_lt_mul_of_pos_left
              · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                rw [h_eqA] at this
                exact this
              · exact Nat.pow_pos (by norm_num)
            _ = 10^(9 * k - 6) - 10^(k-3) := by
              rw [Nat.mul_sub_left_distrib, mul_one]
              have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                rw [← pow_add]
                congr 1
                omega
              rw [h_pow]
            _ < 10^(9 * k) - 1 := by
              have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                have : 9 * k = (9 * k - 6) + 6 := by omega
                nth_rw 2 [this]
                rw [pow_add]
                have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                  apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                omega
              have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
              have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
        exact Nat.lt_of_mul_lt_mul_left h_mul_lt
      exact lt_of_le_of_lt h_le_M3 h_lt_M3
    · -- u3 = 21978
      have h_lt_u3_geom : A004290 10989 < (10^(8 * k - 3) - 1) / 9 := by
        have h_pow : 8 * k - 3 ≥ 37 := by omega
        have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
          apply Nat.div_le_div_right
          have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
          omega
        exact lt_of_lt_of_le A004290_10989_lt h_le
      have h_le_u3_10989 : A004290 21978 ≤ 10 * A004290 10989 := by
        have h_div2 : 2 ∣ 10^1 := by use 5
        have h_div_n : 2 ∣ 21978 := by use 10989
        have h_pos : 21978 > 0 := by norm_num
        have h_le := A004290_le_ten_pow_mul 21978 1 2 h_div2 h_div_n h_pos
        have h_eq : 21978 / 2 = 10989 := rfl
        rw [h_eq] at h_le
        exact h_le
      have h_le_M3 : A004290 n ≤ 10^(k-2) * A004290 10989 := by
        have h_le_M3' : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
        calc A004290 n ≤ 10^(k-3) * A004290 21978 := h_le_M3'
          _ ≤ 10^(k-3) * (10 * A004290 10989) := Nat.mul_le_mul_left (10^(k-3)) h_le_u3_10989
          _ = 10^(k-2) * A004290 10989 := by
            have : 10^(k-3) * 10 = 10^(k-2) := by
              rw [← pow_add]
              congr 1
              omega
            rw [this, mul_assoc]
      have h_lt_M3 : 10^(k-2) * A004290 10989 < (10^(9 * k) - 1) / 9 := by
        have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
        have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
        have h_mul_lt : 9 * (10^(k-2) * A004290 10989) < 9 * ((10^(9 * k) - 1) / 9) := by
          rw [h_eqB]
          calc 9 * (10^(k-2) * A004290 10989) = 10^(k-2) * (9 * A004290 10989) := by ring
            _ < 10^(k-2) * (10^(8 * k - 3) - 1) := by
              apply Nat.mul_lt_mul_of_pos_left
              · have : 9 * A004290 10989 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                rw [h_eqA] at this
                exact this
              · exact Nat.pow_pos (by norm_num)
            _ = 10^(9 * k - 5) - 10^(k-2) := by
              rw [Nat.mul_sub_left_distrib, mul_one]
              have h_pow : 10^(k-2) * 10^(8 * k - 3) = 10^(9 * k - 5) := by
                rw [← pow_add]
                congr 1
                omega
              rw [h_pow]
            _ < 10^(9 * k) - 1 := by
              have h_pow_lt : 10^(9 * k - 5) < 10^(9 * k) := by
                have : 9 * k = (9 * k - 5) + 5 := by omega
                nth_rw 2 [this]
                rw [pow_add]
                have : 10^(9 * k - 5) * 10^5 > 10^(9 * k - 5) * 1 := by
                  apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                omega
              have h_pow_k : 10^(k-2) ≥ 1 := Nat.one_le_pow (k-2) 10 (by norm_num)
              have h_pow_le : 10^(k-2) ≤ 10^(9 * k - 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
        exact Nat.lt_of_mul_lt_mul_left h_mul_lt
      exact lt_of_le_of_lt h_le_M3 h_lt_M3
  · sorry
