import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 250000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 2000

open Finset ZMod Nat Classical

def pow_fast_go (b : ZMod 550172) (e : ℕ) (acc : ZMod 550172) (fuel : ℕ) : ZMod 550172 :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if e = 0 then acc
    else if e % 2 = 1 then
      pow_fast_go (b * b) (e / 2) (acc * b) fuel
    else
      pow_fast_go (b * b) (e / 2) acc fuel

def pow_fast (base : ZMod 550172) (exp : ℕ) : ZMod 550172 :=
  pow_fast_go base exp 1 40

lemma pow_fast_go_eq (fuel : ℕ) : ∀ (e : ℕ) (b acc : ZMod 550172), e < 2 ^ fuel →
    pow_fast_go b e acc fuel = acc * b ^ e := by
  induction fuel with
  | zero =>
    intro e b acc h
    have : e = 0 := by omega
    subst this
    simp [pow_fast_go]
  | succ fuel ih =>
    intro e b acc h
    unfold pow_fast_go
    by_cases he : e = 0
    · simp [he]
    · simp [he]
      by_cases ho : e % 2 = 1
      · simp [ho]
        have h_fuel : e / 2 < 2 ^ fuel := by omega
        rw [ih (e / 2) (b * b) (acc * b) h_fuel]
        have h_pow : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
          rw [mul_pow, ← pow_add]
          congr 2
          omega
        rw [h_pow]
        have h_odd : e = 2 * (e / 2) + 1 := by omega
        nth_rw 2 [h_odd]
        rw [pow_succ]
        ring
      · simp [ho]
        have h_fuel : e / 2 < 2 ^ fuel := by omega
        rw [ih (e / 2) (b * b) acc h_fuel]
        have h_pow : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
          rw [mul_pow, ← pow_add]
          congr 2
          omega
        rw [h_pow]
        have h_even : e = 2 * (e / 2) := by omega
        congr 2
        omega

lemma pow_fast_eq (exp : ℕ) (base : ZMod 550172) (h : exp < 2 ^ 40) :
    pow_fast base exp = base ^ exp := by
  unfold pow_fast
  rw [pow_fast_go_eq 40 exp base 1 h]
  ring

lemma pow_two_zmod_four (k : ℕ) (hk : 2 ≤ k) : (2 : ZMod 4) ^ k = 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rfl
  | succ k hk ih =>
    rw [pow_succ, ih, zero_mul]

lemma ne_of_mod_four (k : ℕ) (hk : 2 ≤ k) (hk4 : k % 4 ≠ 3) : (2 ^ k - k : ZMod 550172) ≠ 13573 := by
  intro h_eq
  have h_dvd : 4 ∣ 550172 := by decide
  let f := ZMod.castHom h_dvd (ZMod 4)
  have h_eq_4 := RingHom.congr_arg f h_eq
  simp [f] at h_eq_4
  change (2 : ZMod 4) ^ k - (k : ZMod 4) = (13573 : ZMod 4) at h_eq_4
  rw [pow_two_zmod_four k hk] at h_eq_4
  have h_sub : ∀ x : ZMod 4, 0 - x = 13573 → x = 3 := by decide
  have h_k_eq : (k : ZMod 4) = 3 := h_sub (k : ZMod 4) h_eq_4
  change (k : ZMod 4) = (Nat.cast 3 : ZMod 4) at h_k_eq
  rw [ZMod.natCast_eq_natCast_iff'] at h_k_eq
  simp at h_k_eq
  exact hk4 h_k_eq

lemma pow_two_zmod_343 (k : ℕ) : (2 : ZMod 343) ^ k = (2 : ZMod 343) ^ (k % 1029) := by
  have h_div : k = 1029 * (k / 1029) + k % 1029 := by omega
  nth_rw 1 [h_div]
  rw [pow_add, pow_mul]
  have h_pow1029 : (2 : ZMod 343) ^ 1029 = 1 := by decide
  rw [h_pow1029, one_pow, one_mul]

lemma k_zmod_343 (k : ℕ) : (k : ZMod 343) = (Nat.cast (k % 1029) : ZMod 343) := by
  have h_div : k = 1029 * (k / 1029) + k % 1029 := by omega
  nth_rw 1 [h_div]
  push_cast
  have h_1029 : (1029 : ZMod 343) = 0 := by decide
  rw [h_1029, zero_mul, zero_add]

lemma ne_of_mod_343 (k : ℕ) (hk36 : k % 1029 ≠ 36) (hk284 : k % 1029 ≠ 284) (hk1003 : k % 1029 ≠ 1003) :
    (2 ^ k - k : ZMod 550172) ≠ 13573 := by
  intro h_eq
  have h_dvd : 343 ∣ 550172 := by decide
  let f := ZMod.castHom h_dvd (ZMod 343)
  have h_eq_343 := RingHom.congr_arg f h_eq
  have h_f2 : f 2 = 2 := rfl
  have h_f13573 : f 13573 = 13573 := rfl
  rw [map_sub, map_pow, h_f2, h_f13573, map_natCast] at h_eq_343
  rw [pow_two_zmod_343 k, k_zmod_343 k] at h_eq_343
  change (2 : ZMod 343) ^ (k % 1029) - (Nat.cast (k % 1029) : ZMod 343) = (Nat.cast 13573 : ZMod 343) at h_eq_343
  have h_sub : ∀ x < 1029, (2 : ZMod 343) ^ x - (Nat.cast x : ZMod 343) = (Nat.cast 13573 : ZMod 343) → x = 36 ∨ x = 284 ∨ x = 1003 := by decide
  have h_cases := h_sub (k % 1029) (by omega) h_eq_343
  rcases h_cases with h1 | h2 | h3
  · exact hk36 h1
  · exact hk284 h2
  · exact hk1003 h3

def pow_fast_401_go (b : ZMod 401) (e : ℕ) (acc : ZMod 401) (fuel : ℕ) : ZMod 401 :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if e = 0 then acc
    else if e % 2 = 1 then
      pow_fast_401_go (b * b) (e / 2) (acc * b) fuel
    else
      pow_fast_401_go (b * b) (e / 2) acc fuel

def pow_fast_401 (base : ZMod 401) (exp : ℕ) : ZMod 401 :=
  pow_fast_401_go base exp 1 17

lemma pow_fast_401_go_eq (fuel : ℕ) : ∀ (e : ℕ) (b acc : ZMod 401), e < 2 ^ fuel →
    pow_fast_401_go b e acc fuel = acc * b ^ e := by
  induction fuel with
  | zero =>
    intro e b acc h
    have : e = 0 := by omega
    subst this
    simp [pow_fast_401_go]
  | succ fuel ih =>
    intro e b acc h
    unfold pow_fast_401_go
    by_cases he : e = 0
    · simp [he]
    · simp [he]
      by_cases ho : e % 2 = 1
      · simp [ho]
        have h_fuel : e / 2 < 2 ^ fuel := by omega
        rw [ih (e / 2) (b * b) (acc * b) h_fuel]
        have h_pow : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
          rw [mul_pow, ← pow_add]
          congr 2
          omega
        rw [h_pow]
        have h_odd : e = 2 * (e / 2) + 1 := by omega
        nth_rw 2 [h_odd]
        rw [pow_succ]
        ring
      · simp [ho]
        have h_fuel : e / 2 < 2 ^ fuel := by omega
        rw [ih (e / 2) (b * b) acc h_fuel]
        have h_pow : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
          rw [mul_pow, ← pow_add]
          congr 2
          omega
        rw [h_pow]
        have h_even : e = 2 * (e / 2) := by omega
        congr 2
        omega

lemma pow_fast_401_eq (exp : ℕ) (base : ZMod 401) (h : exp < 2 ^ 17) :
    pow_fast_401 base exp = base ^ exp := by
  unfold pow_fast_401
  rw [pow_fast_401_go_eq 17 exp base 1 h]
  ring

lemma pow_two_zmod_401 (k : ℕ) : (2 : ZMod 401) ^ k = (2 : ZMod 401) ^ (k % 80200) := by
  have h_div : k = 80200 * (k / 80200) + k % 80200 := by omega
  nth_rw 1 [h_div]
  rw [pow_add, pow_mul]
  have h_pow80200 : (2 : ZMod 401) ^ 80200 = 1 := by
    rw [← pow_fast_401_eq 80200 2 (by decide)]
    decide
  rw [h_pow80200, one_pow, one_mul]

lemma k_zmod_401 (k : ℕ) : (k : ZMod 401) = (Nat.cast (k % 80200) : ZMod 401) := by
  have h_div : k = 80200 * (k / 80200) + k % 80200 := by omega
  nth_rw 1 [h_div]
  push_cast
  have h_80200 : (80200 : ZMod 401) = 0 := by decide
  rw [h_80200, zero_mul, zero_add]

lemma ne_of_mod_401 (k : ℕ) (h_fast : (pow_fast_401 2 (k % 80200) - (Nat.cast (k % 80200) : ZMod 401) != (13573 : ZMod 401)) = true) :
    (2 ^ k - k : ZMod 550172) ≠ 13573 := by
  intro h_eq
  have h_dvd : 401 ∣ 550172 := by decide
  let f := ZMod.castHom h_dvd (ZMod 401)
  have h_eq_401 := RingHom.congr_arg f h_eq
  simp [f] at h_eq_401
  change (2 : ZMod 401) ^ k - (k : ZMod 401) = (13573 : ZMod 401) at h_eq_401
  rw [pow_two_zmod_401 k, k_zmod_401 k] at h_eq_401
  have h_pow_eq : pow_fast_401 2 (k % 80200) = (2 : ZMod 401) ^ (k % 80200) := by
    apply pow_fast_401_eq
    omega
  rw [← h_pow_eq] at h_eq_401
  change (pow_fast_401 2 (k % 80200) - (Nat.cast (k % 80200) : ZMod 401) = (13573 : ZMod 401)) at h_eq_401
  rw [h_eq_401] at h_fast
  simp at h_fast

lemma ne_to_bool_ne {α : Type _} [DecidableEq α] (x y : α) (h : x ≠ y) : (x != y) = true := by
  have : (x == y) = false := decide_eq_false h
  unfold bne
  rw [this]
  rfl

def check_at_step (i : ℕ) : Bool :=
  let k1 := 4116 * i + 1003
  let k2 := 4116 * i + 3123
  let k3 := 4116 * i + 3371
  (k1 > 16331503 || (pow_fast_401 2 (k1 % 80200) - (Nat.cast (k1 % 80200) : ZMod 401)) != (13573 : ZMod 401)) &&
  (k2 > 16331503 || (pow_fast_401 2 (k2 % 80200) - (Nat.cast (k2 % 80200) : ZMod 401)) != (13573 : ZMod 401)) &&
  (k3 > 16331503 || (pow_fast_401 2 (k3 % 80200) - (Nat.cast (k3 % 80200) : ZMod 401)) != (13573 : ZMod 401))

def check_all_steps (len : ℕ) : Bool :=
  match len with
  | 0 => true
  | len + 1 => check_at_step len && check_all_steps len

theorem sieve_fast : check_all_steps 3968 = true := by decide

lemma check_all_steps_spec (len : ℕ) : ∀ (h : check_all_steps len = true) (q : ℕ) (hq : q < len), check_at_step q = true := by
  induction len with
  | zero =>
    intro _ q hq
    omega
  | succ len ih =>
    intro h q hq
    unfold check_all_steps at h
    rw [Bool.and_eq_true] at h
    have h_last := h.1
    have h_rest := h.2
    by_cases hq_len : q = len
    · subst hq_len; exact h_last
    · have : q < len := by omega
      exact ih h_rest q this

lemma ne_of_check_at_step (q : ℕ) (h_step : check_at_step q = true) (k : ℕ) (hk_le : k ≤ 16331503)
    (hk_cases : k = 4116 * q + 1003 ∨ k = 4116 * q + 3123 ∨ k = 4116 * q + 3371) :
    pow_fast_401 2 (k % 80200) - (Nat.cast (k % 80200) : ZMod 401) ≠ 13573 := by
  unfold check_at_step at h_step
  rw [Bool.and_eq_true] at h_step
  have h_k3 := h_step.2
  have h_step12 := h_step.1
  rw [Bool.and_eq_true] at h_step12
  have h_k1 := h_step12.1
  have h_k2 := h_step12.2
  rw [Bool.or_eq_true] at h_k1 h_k2 h_k3
  rcases hk_cases with rfl | rfl | rfl
  · rcases h_k1 with h_gt | h_ne
    · rw [decide_eq_true_iff] at h_gt; omega
    · intro h_eq; rw [h_eq] at h_ne; revert h_ne; decide
  · rcases h_k2 with h_gt | h_ne
    · rw [decide_eq_true_iff] at h_gt; omega
    · intro h_eq; rw [h_eq] at h_ne; revert h_ne; decide
  · rcases h_k3 with h_gt | h_ne
    · rw [decide_eq_true_iff] at h_gt; omega
    · intro h_eq; rw [h_eq] at h_ne; revert h_ne; decide

lemma k_not_covered (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 16331503) : (2 ^ k - k : ZMod 550172) ≠ 13573 := by
  by_cases hk_lt : k < 2
  · have : k = 1 := by omega
    subst this
    decide
  · have hk_ge : 2 ≤ k := by omega
    by_cases hk4 : k % 4 = 3
    · by_cases hk343 : (k % 1029 = 36 ∨ k % 1029 = 284 ∨ k % 1029 = 1003)
      · have h_mod : k % 4116 = 1003 ∨ k % 4116 = 3123 ∨ k % 4116 = 3371 := by
          omega
        let q := k / 4116
        have h_div : k = 4116 * q + k % 4116 := by omega
        have hq : q < 3968 := by
          omega
        have h_step : check_at_step q = true := by
          have h_all : check_all_steps 3968 = true := sieve_fast
          exact check_all_steps_spec 3968 h_all q hq
        have h_cases : k = 4116 * q + 1003 ∨ k = 4116 * q + 3123 ∨ k = 4116 * q + 3371 := by
          rcases h_mod with h1 | h2 | h3
          · left; omega
          · right; left; omega
          · right; right; omega
        have h_ne : pow_fast_401 2 (k % 80200) - (Nat.cast (k % 80200) : ZMod 401) ≠ 13573 := by
          apply ne_of_check_at_step q h_step k hk2 h_cases
        apply ne_of_mod_401 k (ne_to_bool_ne _ _ h_ne)
      · apply ne_of_mod_343 k
        · intro hc; exact hk343 (Or.inl hc)
        · intro hc; exact hk343 (Or.inr (Or.inl hc))
        · intro hc; exact hk343 (Or.inr (Or.inr hc))
    · apply ne_of_mod_four k hk_ge hk4

lemma pow_period_step (r : ℕ) (hr : 2 ≤ r) : (2 : ZMod 550172) ^ 29400 * 2 ^ r = 2 ^ r := by
  have h_base : (pow_fast 2 29400) * 2 ^ 2 = 2 ^ 2 := by decide
  have h_pow_eq : pow_fast 2 29400 = (2 : ZMod 550172) ^ 29400 := by
    apply pow_fast_eq
    decide
  rw [h_pow_eq] at h_base
  have h_div : r = 2 + (r - 2) := by omega
  nth_rw 1 [h_div]
  nth_rw 2 [h_div]
  rw [pow_add]
  rw [← mul_assoc, h_base]

lemma pow_period (q : ℕ) (r : ℕ) (hr : 2 ≤ r) : (2 : ZMod 550172) ^ (29400 * q + r) = 2 ^ r := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h_add : 29400 * (q + 1) + r = 29400 + (29400 * q + r) := by omega
    rw [h_add, pow_add]
    rw [pow_period_step (29400 * q + r) (by omega), ih]

lemma zmod_mul_eq_mul (A B : ℕ) :
    (196 * A : ZMod 550172) = (196 * B : ZMod 550172) ↔ (A : ZMod 2807) = (B : ZMod 2807) := by
  have h_mul1 : (196 * A : ZMod 550172) = (((196 * A : ℕ) : ZMod 550172)) := by push_cast; rfl
  have h_mul2 : (196 * B : ZMod 550172) = (((196 * B : ℕ) : ZMod 550172)) := by push_cast; rfl
  rw [h_mul1, h_mul2]
  have h_eq : 550172 = 196 * 2807 := by decide
  rw [h_eq]
  rw [ZMod.natCast_eq_natCast_iff', ZMod.natCast_eq_natCast_iff']
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  constructor
  · intro h
    have : 0 < 196 := Nat.zero_lt_succ 195
    exact Nat.mul_left_cancel this h
  · intro h
    rw [h]

lemma r_bound (r : ℕ) (hr : 20 ≤ r) : r + 550172 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [pow_succ]
    omega

lemma preimage_formula_correct (y : ZMod 550172) (r : ℕ) (hr : y.val % 196 = (2 ^ r - r) % 196) (hr_gt : 20 ≤ r) :
    (2 : ZMod 550172) ^ (29400 * ((131 * (((2 : ℕ) ^ r - r - y.val) / 196)) % 2807) + r) -
    (Nat.cast (29400 * ((131 * (((2 : ℕ) ^ r - r - y.val) / 196)) % 2807) + r) : ZMod 550172) = y := by
  have h_period : (2 : ZMod 550172) ^ (29400 * ((131 * (((2 : ℕ) ^ r - r - y.val) / 196)) % 2807) + r) = 2 ^ r := by
    apply pow_period
    omega
  rw [h_period]
  have h_le : y.val ≤ 2 ^ r - r := by
    have h_bound := r_bound r hr_gt
    have h_val : y.val < 550172 := y.val_lt
    omega
  let K := ((2 : ℕ) ^ r - r - y.val) / 196
  have h_mul_div : 196 * K = 2 ^ r - r - y.val := by
    rw [Nat.mul_comm]
    apply Nat.div_mul_cancel
    have h_mod : (2 ^ r - r - y.val) % 196 = 0 := by
      have h_eq_zmod : ((2 ^ r - r : ℕ) : ZMod 196) = ((y.val : ℕ) : ZMod 196) := by
        rw [ZMod.natCast_eq_natCast_iff']
        exact hr.symm
      have h_dvd : 196 ∣ 2 ^ r - r - y.val := by
        have h_sub : ((2 ^ r - r - y.val : ℕ) : ZMod 196) = 0 := by
          rw [Nat.cast_sub h_le]
          rw [h_eq_zmod]
          rw [sub_self]
        rw [ZMod.natCast_eq_zero_iff] at h_sub
        exact h_sub
      exact Nat.mod_eq_zero_of_dvd h_dvd
    exact Nat.dvd_of_mod_eq_zero h_mod
  have h_sub_eq : 2 ^ r - (Nat.cast (29400 * ((131 * K) % 2807) + r) : ZMod 550172) = y ↔
      (2 : ZMod 550172) ^ r - r - y = (Nat.cast (29400 * ((131 * K) % 2807)) : ZMod 550172) := by
    constructor
    · intro h
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      push_cast
      ring
    · intro h
      rw [sub_eq_iff_eq_add]
      have h_add : (2 : ZMod 550172) ^ r - r - y + r + y = (Nat.cast (29400 * ((131 * K) % 2807)) : ZMod 550172) + r + y := by rw [h]
      have h_simp : (2 : ZMod 550172) ^ r - r - y + r + y = 2 ^ r := by ring
      rw [h_simp] at h_add
      rw [h_add]
      push_cast
      ring
  rw [h_sub_eq]
  have h_lhs_eval : ((2 ^ r - r - y.val : ℕ) : ZMod 550172) = (196 * K : ZMod 550172) := by
    rw [← h_mul_div]
    push_cast
    rfl
  have h_lhs : (2 : ZMod 550172) ^ r - r - y = (196 * K : ZMod 550172) := by
    have h_y : y = (y.val : ZMod 550172) := by simp
    rw [h_y]
    have h_r_le : r ≤ 2 ^ r := by
      have h_bound := r_bound r hr_gt
      omega
    have h_sub : (2 : ZMod 550172) ^ r - r - (y.val : ZMod 550172) = ((2 ^ r - r - y.val : ℕ) : ZMod 550172) := by
      rw [Nat.cast_sub h_le]
      rw [Nat.cast_sub h_r_le]
      push_cast
      rfl
    rw [h_sub, h_lhs_eval]
  rw [h_lhs]
  have h_rhs_eval : ((29400 * ((131 * K) % 2807) : ℕ) : ZMod 550172) = (((196 * (150 * ((131 * K) % 2807)) : ℕ) : ZMod 550172)) := by
    congr 1
    ring
  rw [h_rhs_eval]
  rw [Nat.cast_mul]
  change (196 : ZMod 550172) * ↑K = (196 : ZMod 550172) * ↑(150 * (131 * K % 2807))
  rw [zmod_mul_eq_mul]
  push_cast
  rw [ZMod.natCast_mod]
  push_cast
  have h_inv : (150 : ZMod 2807) * 131 = 1 := by decide
  have h_goal : (K : ZMod 2807) = 150 * (131 * (K : ZMod 2807)) := by
    rw [← mul_assoc, h_inv, one_mul]
  rw [← h_goal]

def r_table : List ℕ := [36, 143, 2, 349, 308, 3, 26, 225, 332, 191, 50, 81, 4, 31, 58, 85, 48, 139, 98, 193, 220, 15, 122, 237, 328, 287, 146, 5, 204, 311, 170, 29, 60, 171, 10, 37, 64, 27, 118, 77, 172, 199, 226, 101, 216, 307, 266, 125, 72, 183, 290, 149, 8, 39, 150, 173, 16, 43, 6, 97, 56, 151, 178, 205, 80, 195, 286, 245, 104, 51, 162, 269, 128, 475, 18, 129, 152, 11, 22, 49, 76, 35, 130, 157, 184, 59, 174, 265, 224, 83, 30, 141, 248, 107, 454, 413, 108, 131, 330, 437, 28, 55, 14, 109, 136, 163, 38, 153, 244, 203, 62, 9, 120, 227, 86, 433, 392, 87, 110, 309, 416, 7, 34, 61, 88, 115, 142, 17, 132, 223, 182, 41, 304, 99, 206, 65, 412, 371, 66, 89, 288, 395, 254, 13, 40, 67, 94, 121, 148, 111, 202, 161, 20, 283, 78, 185, 44, 391, 350, 45, 68, 267, 374, 233, 12, 19, 46, 73, 100, 127, 90, 181, 140, 235, 262, 57, 164, 23, 370, 329, 24, 47, 246, 353, 212, 71, 102, 25, 52, 79, 106, 69, 160, 119, 214, 241]

def get_r (m : ℕ) : ℕ := r_table.getD m 2 + 588

lemma get_r_ge_20 (m : ℕ) : 20 ≤ get_r m := by
  unfold get_r
  omega

lemma get_r_property (m : ℕ) (hm : m < 196) : (2 ^ (get_r m) - get_r m) % 196 = m := by
  revert m hm
  decide

lemma two_pow_pos (k : ℕ) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    omega

lemma k_le_pow_two (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    have := two_pow_pos k
    omega

lemma preimage_exists (y : ZMod 550172) : ∃ k : ℕ, 1 ≤ k ∧ (2 ^ k - k : ZMod 550172) = y := by
  let m := y.val % 196
  have hm : m < 196 := Nat.mod_lt _ (by decide)
  let r := get_r m
  have hr_gt : 20 ≤ r := get_r_ge_20 m
  have hr : y.val % 196 = (2 ^ r - r) % 196 := by
    have h_prop := get_r_property m hm
    dsimp [r]
    rw [h_prop]
  refine ⟨29400 * ((131 * (((2 : ℕ) ^ r - r - y.val) / 196)) % 2807) + r, ?_, ?_⟩
  · generalize 29400 * ((131 * (((2 : ℕ) ^ r - r - y.val) / 196)) % 2807) = X
    omega
  · exact preimage_formula_correct y r hr hr_gt

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S

theorem A232616_prop_one : A232616_prop 1 1 := by
  ext x
  constructor
  · intro _
    rw [Finset.mem_image]
    use 1
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; decide
    · apply Subsingleton.elim
  · intro _
    exact mem_univ x

theorem A232616_prop_zero_neg_one : ¬ A232616_prop 1 0 := by
  intro h
  have h2 : (0 : ZMod 1) ∈ (univ : Finset (ZMod 1)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, _⟩
  rw [Finset.mem_Icc] at hk
  omega

theorem A232616_one : A232616 1 = 1 := by
  have h1 : 1 ≠ 0 := by decide
  rw [A232616, dif_neg h1]
  have h_nonempty : {m : ℕ | A232616_prop 1 m}.Nonempty := ⟨1, A232616_prop_one⟩
  rw [Nat.sInf_def h_nonempty]
  rw [Nat.find_eq_iff]
  refine ⟨A232616_prop_one, fun k hk ↦ ?_⟩
  interval_cases k
  · exact A232616_prop_zero_neg_one

theorem A232616_prop_two : A232616_prop 2 2 := by
  ext x
  constructor
  · intro _
    fin_cases x
    · rw [Finset.mem_image]
      use 2
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]; decide
      · rfl
    · rw [Finset.mem_image]
      use 1
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]; decide
      · rfl
  · intro _
    exact mem_univ x

theorem A232616_prop_one_neg : ¬ A232616_prop 2 1 := by
  intro h
  have h2 : (0 : ZMod 2) ∈ (univ : Finset (ZMod 2)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, hk2⟩
  rw [Finset.mem_Icc] at hk
  have : k = 1 := by omega
  subst this
  revert hk2
  decide

theorem A232616_prop_zero_neg : ¬ A232616_prop 2 0 := by
  intro h
  have h2 : (0 : ZMod 2) ∈ (univ : Finset (ZMod 2)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, _⟩
  rw [Finset.mem_Icc] at hk
  omega

theorem A232616_two : A232616 2 = 2 := by
  have h2 : 2 ≠ 0 := by decide
  rw [A232616, dif_neg h2]
  have h_nonempty : {m : ℕ | A232616_prop 2 m}.Nonempty := ⟨2, A232616_prop_two⟩
  rw [Nat.sInf_def h_nonempty]
  rw [Nat.find_eq_iff]
  refine ⟨A232616_prop_two, fun k hk ↦ ?_⟩
  interval_cases k
  · exact A232616_prop_zero_neg
  · exact A232616_prop_one_neg

theorem sInf_eq_zero_or_mem (s : Set ℕ) : sInf s = 0 ∨ sInf s ∈ s := by
  have h_inf : sInf s = if h : ∃ n, n ∈ s then Nat.find h else 0 := rfl
  by_cases h : ∃ n, n ∈ s
  · right
    rw [h_inf, dif_pos h]
    exact Nat.find_spec h
  · left
    rw [h_inf, dif_neg h]

theorem le_nth_self (p : ℕ → Prop) (hf : (setOf p).Infinite) (n : ℕ) : n ≤ Nat.nth p n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 : Nat.nth p n < Nat.nth p (n + 1) := by
      rw [Nat.nth_lt_nth hf]
      omega
    omega

theorem prime_three_le (n : ℕ) : 5 ≤ Nat.nth Nat.Prime (n + 2) := by
  have h_le : 2 ≤ n + 2 := by omega
  have h_mono := (Nat.nth_le_nth Nat.infinite_setOf_prime).mpr h_le
  rw [Nat.nth_prime_two_eq_five] at h_mono
  exact h_mono

theorem prime_bound_pos (n : ℕ) : 0 < 2 * (Nat.nth Nat.Prime (n + 2) - 1) := by
  have h := prime_three_le n
  omega

theorem A232616_prop_mono (n : ℕ) [NeZero n] (m1 m2 : ℕ) (h : m1 ≤ m2) (hm1 : A232616_prop n m1) : A232616_prop n m2 := by
  unfold A232616_prop at *
  ext x
  refine ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ x⟩
  have hx : x ∈ (Finset.Icc 1 m1).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := by
    rw [← hm1]
    exact Finset.mem_univ x
  rw [Finset.mem_image] at hx ⊢
  rcases hx with ⟨k, hk, rfl⟩
  use k
  rw [Finset.mem_Icc] at hk ⊢
  refine ⟨⟨hk.1, hk.2.trans h⟩, rfl⟩

def noFactorsGo (p : ℕ) (m : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    if m * m > p then true
    else if p % m = 0 then false
    else noFactorsGo p (m + 2) fuel

lemma odd_of_dvd_odd {p k : ℕ} (hp : p % 2 = 1) (hk : k ∣ p) : k % 2 = 1 := by
  by_contra h
  have : k % 2 = 0 := by omega
  have : 2 ∣ k := Nat.dvd_of_mod_eq_zero this
  have : 2 ∣ p := dvd_trans this hk
  have : p % 2 = 0 := Nat.mod_eq_zero_of_dvd this
  omega

lemma noFactorsGo_spec (fuel : ℕ) (p : ℕ) (hp_odd : p % 2 = 1) :
    ∀ (m : ℕ) (hm_odd : m % 2 = 1) (h_fuel : sqrt p + 1 - m ≤ fuel),
    noFactorsGo p m fuel = true ↔ ∀ k, m ≤ k → k * k ≤ p → ¬ k ∣ p := by
  induction fuel with
  | zero =>
    intro m hm_odd h_fuel
    have : sqrt p < m := by omega
    simp [noFactorsGo]
    intro k hk hk_sq
    have h_k_le : k ≤ sqrt p := le_sqrt.mpr hk_sq
    omega
  | succ fuel ih =>
    intro m hm_odd h_fuel
    unfold noFactorsGo
    by_cases h_gt : m * m > p
    · rw [if_pos h_gt]
      simp
      intro k hk hk_sq
      have : m * m ≤ k * k := mul_self_le_mul_self hk
      omega
    · rw [if_neg h_gt]
      by_cases h_dvd : m ∣ p
      · have h_mod_eq : p % m = 0 := dvd_iff_mod_eq_zero.mp h_dvd
        rw [if_pos h_mod_eq]
        simp
        use m
        refine ⟨by omega, ?_⟩
        have : m * m ≤ p := by omega
        exact ⟨this, h_dvd⟩
      · have h_mod_ne : p % m ≠ 0 := by
          intro h_zero
          have : m ∣ p := dvd_iff_mod_eq_zero.mpr h_zero
          exact h_dvd this
        rw [if_neg h_mod_ne]
        have hm2_odd : (m + 2) % 2 = 1 := by omega
        have h_fuel' : sqrt p + 1 - (m + 2) ≤ fuel := by omega
        rw [ih (m + 2) hm2_odd h_fuel']
        constructor
        · intro h_all k hk hk_sq kdvd
          have k_odd : k % 2 = 1 := odd_of_dvd_odd hp_odd kdvd
          by_cases hk_m : k = m
          · subst hk_m; exact h_dvd kdvd
          · have : m + 1 ≤ k := by omega
            have : m + 2 ≤ k := by omega
            exact h_all k this hk_sq kdvd
        · intro h_all k hk hk_sq kdvd
          exact h_all k (by omega) hk_sq kdvd

def isPrimeFast (p : ℕ) : Bool :=
  if p < 2 then false
  else if p = 2 then true
  else if p % 2 = 0 then false
  else noFactorsGo p 3 3000

lemma isPrimeFast_spec (p : ℕ) (hp : p < 9000000) : isPrimeFast p = true ↔ Nat.Prime p := by
  unfold isPrimeFast
  by_cases h_lt : p < 2
  · rw [if_pos h_lt]
    simp
    intro hc
    have : 2 ≤ p := hc.two_le
    omega
  · rw [if_neg h_lt]
    by_cases h_eq : p = 2
    · rw [if_pos h_eq]
      subst h_eq
      simp [Nat.prime_two]
    · rw [if_neg h_eq]
      by_cases h_even : p % 2 = 0
      · rw [if_pos h_even]
        simp
        intro hc
        have hp2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero h_even
        have hp2_eq : p = 2 := ((hc.eq_one_or_self_of_dvd 2 hp2).resolve_left (by decide)).symm
        contradiction
      · rw [if_neg h_even]
        have h_fuel_le : sqrt p + 1 - 3 ≤ 3000 := by
          have h_sqrt : sqrt p < 3000 := by
            rw [sqrt_lt]
            exact hp
          omega
        have hp_odd : p % 2 = 1 := by omega
        rw [noFactorsGo_spec 3000 p hp_odd 3 (by decide) h_fuel_le]
        rw [prime_def_le_sqrt]
        have hp_ge : 2 ≤ p := by omega
        simp [hp_ge]
        constructor
        · intro h_all m hm1 hm2 mdvd
          by_cases hm_even : m % 2 = 0
          · have : 2 ∣ m := dvd_of_mod_eq_zero hm_even
            have : 2 ∣ p := dvd_trans this mdvd
            have : p % 2 = 0 := Nat.mod_eq_zero_of_dvd this
            contradiction
          · have hm_ge : 3 ≤ m := by
              have : m ≠ 2 := by
                intro hc
                subst hc
                contradiction
              omega
            have hm_sq : m * m ≤ p := le_sqrt.mp hm2
            exact h_all m hm_ge hm_sq mdvd
        · intro h_all m hm_ge hm_sq mdvd
          have hm_le_sqrt : m ≤ sqrt p := le_sqrt.mpr hm_sq
          have hm_ge_2 : 2 ≤ m := by omega
          exact h_all m hm_ge_2 hm_le_sqrt mdvd

instance (priority := high) decidablePrimeFast (p : ℕ) : Decidable (Nat.Prime p) :=
  if h : p < 9000000 then
    decidable_of_iff _ (isPrimeFast_spec p h)
  else
    Nat.decidablePrime p

def countPrimesRange (start len : ℕ) : ℕ :=
  let rec go (i : ℕ) (acc : ℕ) : ℕ :=
    match i with
    | 0 => acc
    | i + 1 => go i (if decide (Nat.Prime (start + i + 1)) then acc + 1 else acc)
  go len 0

lemma countPrimesRange_go_eq (start len acc : ℕ) :
    countPrimesRange.go start len acc = acc + (Finset.filter Nat.Prime (Finset.Ioc start (start + len))).card := by
  induction len generalizing acc with
  | zero =>
    simp [countPrimesRange.go]
  | succ len ih =>
    have h_split : Finset.Ioc start (start + len + 1) = Finset.Ioc start (start + len) ∪ {start + len + 1} := by
      ext x
      rw [mem_union, mem_Ioc, mem_Ioc, mem_singleton]
      omega
    have h_disj : Disjoint (Finset.Ioc start (start + len)) {start + len + 1} := by
      rw [disjoint_singleton_right, mem_Ioc]
      omega
    have h_add : start + (len + 1) = start + len + 1 := by omega
    unfold countPrimesRange.go
    rw [ih]
    rw [h_add]
    rw [h_split, filter_union, card_union_of_disjoint]
    · by_cases h_pr : Nat.Prime (start + len + 1)
      · have h_dec : decide (Nat.Prime (start + len + 1)) = true := decide_eq_true h_pr
        rw [h_dec]
        simp only [if_true]
        have h_sub : filter Nat.Prime {start + len + 1} = {start + len + 1} := by
          ext x
          simp only [mem_filter, mem_singleton]
          constructor
          · rintro ⟨rfl, _⟩; rfl
          · rintro rfl; exact ⟨rfl, h_pr⟩
        rw [h_sub, card_singleton]
        omega
      · have h_dec : decide (Nat.Prime (start + len + 1)) = false := decide_eq_false h_pr
        rw [h_dec]
        have h_empty : filter Nat.Prime {start + len + 1} = ∅ := by
          ext x
          simp
          intro hx
          subst hx
          exact h_pr
        rw [h_empty, card_empty]
        simp
    · apply disjoint_filter_filter
      exact h_disj

lemma countPrimesRange_eq (start len : ℕ) :
    countPrimesRange start len = (Finset.filter Nat.Prime (Finset.Ioc start (start + len))).card := by
  unfold countPrimesRange
  rw [countPrimesRange_go_eq]
  omega

lemma nth_le_step (i : ℕ) (A B C : ℕ) (h_nth : Nat.nth Nat.Prime i ≤ A)
    (h_count : countPrimesRange A (B - A) = C) (h_le : A ≤ B) :
    Nat.nth Nat.Prime (i + C) ≤ B := by
  have h_range_eq : countPrimesRange A (B - A) = (Finset.filter Nat.Prime (Finset.Ioc A (A + (B - A)))).card := countPrimesRange_eq A (B - A)
  have h_sub_add : A + (B - A) = B := by omega
  rw [h_sub_add] at h_range_eq
  rw [h_range_eq] at h_count
  have h_union : Finset.filter Nat.Prime (range (B + 1)) = Finset.filter Nat.Prime (range (A + 1)) ∪ Finset.filter Nat.Prime (Finset.Ioc A B) := by
    rw [← filter_union]
    congr 1
    ext x
    rw [mem_union, mem_range, mem_Ioc, mem_range]
    omega
  have h_disj : Disjoint (Finset.filter Nat.Prime (range (A + 1))) (Finset.filter Nat.Prime (Finset.Ioc A B)) := by
    apply disjoint_filter_filter
    rw [disjoint_right]
    intro x hx
    rw [mem_Ioc] at hx
    rw [mem_range]
    omega
  have h_card_all : (Finset.filter Nat.Prime (range (B + 1))).card = (Finset.filter Nat.Prime (range (A + 1))).card + (Finset.filter Nat.Prime (Finset.Ioc A B)).card := by
    rw [h_union, card_union_of_disjoint h_disj]
  have h_card_S1 : count Nat.Prime (A + 1) = (Finset.filter Nat.Prime (range (A + 1))).card := by
    rw [count_eq_card_filter_range]
  have h_lt_S1 : i < (Finset.filter Nat.Prime (range (A + 1))).card := by
    rw [← h_card_S1]
    by_contra! h_le_i
    rw [count_le_iff_le_nth (infinite_setOf_prime)] at h_le_i
    change A + 1 ≤ Nat.nth Nat.Prime i at h_le_i
    omega
  have h_lt_all : i + C < (Finset.filter Nat.Prime (range (B + 1))).card := by
    omega
  have h_card_all2 : count Nat.Prime (B + 1) = (Finset.filter Nat.Prime (range (B + 1))).card := by
    rw [count_eq_card_filter_range]
  rw [← h_card_all2] at h_lt_all
  by_contra! h_gt_B
  have h_le_all : count Nat.Prime (B + 1) ≤ i + C := by
    rw [count_le_iff_le_nth (infinite_setOf_prime)]
    exact h_gt_B
  omega

def sum_counts : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, count) :: rest => count + sum_counts rest

def last_A (default_A : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => default_A
  | (B, _) :: rest => last_A B rest

def checkIntervals : List (ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | (B, count) :: rest, A =>
    (A <= B) && (countPrimesRange A (B - A) == count) && checkIntervals rest B

lemma checkIntervals_spec : ∀ (intervals : List (ℕ × ℕ)) (A : ℕ) (curr_idx : ℕ),
    checkIntervals intervals A = true → Nat.nth Nat.Prime curr_idx ≤ A →
    Nat.nth Nat.Prime (curr_idx + sum_counts intervals) ≤ last_A A intervals := by
  intro intervals
  induction intervals with
  | nil =>
    intro A curr_idx h_check h_nth
    simp [sum_counts, last_A]
    exact h_nth
  | cons head rest ih =>
    rintro A curr_idx h_check h_nth
    obtain ⟨B, count⟩ := head
    unfold checkIntervals at h_check
    rw [Bool.and_eq_true] at h_check
    rcases h_check with ⟨h_check_first, h_rest⟩
    rw [Bool.and_eq_true] at h_check_first
    rcases h_check_first with ⟨h_le, h_eq⟩
    have h_le_prop : A ≤ B := by
      rw [decide_eq_true_iff] at h_le
      exact h_le
    have h_count : countPrimesRange A (B - A) = count := by
      rw [beq_iff_eq] at h_eq
      exact h_eq
    have h_le_B : Nat.nth Nat.Prime (curr_idx + count) ≤ B := by
      apply nth_le_step curr_idx A B count h_nth h_count h_le_prop
    have h_ih := ih B (curr_idx + count) h_rest h_le_B
    simp [sum_counts, last_A]
    have h_assoc : curr_idx + (count + sum_counts rest) = curr_idx + count + sum_counts rest := by omega
    rw [h_assoc]
    exact h_ih

theorem prime_bound_0 : Nat.nth Nat.Prime 0 ≤ 2 := Nat.nth_prime_zero_eq_two.le

def sieve_intervals : List (ℕ × ℕ) := [(10002, 1228), (20002, 1033), (30002, 983), (40002, 958), (50002, 930), (60002, 924), (70002, 879), (80002, 901), (90002, 877), (100002, 878), (110002, 861), (120002, 848), (130002, 858), (140002, 851), (150002, 839), (160002, 835), (170002, 813), (180002, 846), (190002, 827), (200002, 814), (210002, 823), (220002, 811), (230002, 819), (240002, 784), (250002, 823), (260002, 793), (270002, 806), (280002, 790), (290002, 791), (300002, 773), (310002, 803), (320002, 808), (330002, 796), (340002, 778), (350002, 795), (360002, 780), (370002, 765), (380002, 778), (390002, 768), (400002, 792), (410002, 754), (420002, 777), (430002, 771), (440002, 779), (450002, 766), (460002, 751), (470002, 765), (480002, 782), (490002, 762), (500002, 771), (510002, 753), (520002, 770), (530002, 764), (540002, 747), (550002, 750), (560002, 750), (570002, 748), (580002, 769), (590002, 762), (600002, 747), (610002, 763), (620002, 751), (630002, 729), (640002, 733), (650002, 757), (660002, 734), (670002, 745), (680002, 753), (690002, 752), (700002, 729), (710002, 762), (720002, 723), (730002, 760), (740002, 742), (750002, 707), (760002, 740), (770002, 755), (780002, 735), (790002, 738), (800002, 745), (810002, 732), (820002, 733), (830002, 745), (840002, 729), (850002, 727), (860002, 725), (870002, 753), (880002, 729), (890002, 731), (900002, 720), (910002, 751), (920002, 708), (930002, 740), (940002, 714), (950002, 719), (960002, 711), (970002, 732), (980002, 717), (990002, 711), (1000002, 720), (1010002, 753), (1020002, 720), (1030002, 731), (1040002, 701), (1050002, 731), (1060002, 698), (1070002, 716), (1080002, 722), (1090002, 706), (1100002, 738), (1110002, 736), (1120002, 717), (1130002, 717), (1140002, 718), (1150002, 700), (1160002, 728), (1170002, 734), (1180002, 726), (1190002, 735), (1200002, 713), (1210002, 676), (1220002, 744), (1230002, 693), (1240002, 694), (1250002, 724), (1260002, 713), (1270002, 719), (1280002, 709), (1290002, 722), (1300002, 689), (1310002, 709), (1320002, 703), (1330002, 714), (1340002, 705), (1350002, 693), (1360002, 713), (1370002, 709), (1380002, 723), (1390002, 695), (1400002, 741), (1410002, 679), (1420002, 682), (1430002, 718), (1440002, 723), (1450002, 702), (1460002, 701), (1470002, 716), (1480002, 706), (1490002, 705), (1500002, 697), (1510002, 731), (1520002, 702), (1530002, 691), (1540002, 686), (1550002, 698), (1560002, 713), (1570002, 681), (1580002, 701), (1590002, 693), (1600002, 676), (1610002, 719), (1620002, 695), (1630002, 709), (1640002, 692), (1650002, 693), (1660002, 700), (1670002, 716), (1680002, 702), (1690002, 675), (1700002, 713), (1710002, 696), (1720002, 685), (1730002, 691), (1740002, 689), (1750002, 706), (1760002, 684), (1770002, 680), (1780002, 700), (1790002, 687), (1800002, 713), (1810002, 705), (1820002, 671), (1830002, 718), (1840002, 675), (1850002, 701), (1860002, 707), (1870002, 703), (1880002, 689), (1890002, 697), (1900002, 691), (1910002, 689), (1920002, 697), (1930002, 710), (1940002, 685), (1950002, 692), (1960002, 684), (1970002, 673), (1980002, 670), (1990002, 690), (2000002, 714), (2010002, 705), (2020002, 691), (2030002, 692), (2040002, 690), (2050002, 671), (2060002, 696), (2070002, 694), (2080002, 673), (2090002, 686), (2100002, 675), (2110002, 699), (2120002, 682), (2130002, 698), (2140002, 673), (2150002, 692), (2160002, 713), (2170002, 666), (2180002, 690), (2190002, 679), (2200002, 664), (2210002, 701), (2220002, 660), (2230002, 696), (2240002, 679), (2250002, 683), (2260002, 688), (2270002, 701), (2280002, 694), (2290002, 662), (2300002, 685), (2310002, 690), (2320002, 663), (2330002, 671), (2340002, 672), (2350002, 667), (2360002, 689), (2370002, 691), (2380002, 662), (2390002, 705), (2400002, 682), (2410002, 659), (2420002, 692), (2430002, 672), (2440002, 657), (2450002, 701), (2460002, 687), (2470002, 669), (2480002, 671), (2490002, 687), (2500002, 674), (2510002, 676), (2520002, 675), (2530002, 698), (2540002, 671), (2550002, 671), (2560002, 671), (2570002, 678), (2580002, 699), (2590002, 693), (2600002, 676), (2610002, 653), (2620002, 681), (2630002, 672), (2640002, 681), (2650002, 689), (2660002, 695), (2670002, 662), (2680002, 665), (2690002, 681), (2700002, 686), (2710002, 679), (2720002, 695), (2730002, 646), (2740002, 656), (2750002, 672), (2760002, 671), (2770002, 685), (2780002, 666), (2790002, 664), (2800002, 684), (2810002, 689), (2820002, 696), (2830002, 666), (2840002, 704), (2850002, 671), (2860002, 654), (2870002, 673), (2880002, 653), (2890002, 679), (2900002, 661), (2910002, 681), (2920002, 663), (2930002, 671), (2940002, 680), (2950002, 650), (2960002, 651), (2970002, 694), (2980002, 660), (2990002, 670), (3000002, 687), (3010002, 671), (3020002, 658), (3030002, 663), (3040002, 657), (3050002, 671), (3060002, 657), (3070002, 664), (3080002, 695), (3090002, 686), (3100002, 654), (3110002, 676), (3120002, 677), (3130002, 666), (3140002, 666), (3150002, 659), (3160002, 676), (3170002, 668), (3180002, 663), (3190002, 692), (3200002, 674), (3210002, 687), (3220002, 673), (3230002, 672), (3240002, 687), (3250002, 649), (3260002, 662), (3270002, 677), (3280002, 666), (3290002, 670), (3300002, 649), (3310002, 672), (3320002, 660), (3330002, 677), (3340002, 645), (3350002, 675), (3360002, 623), (3370002, 689), (3380002, 666), (3390002, 669), (3400002, 662), (3410002, 677), (3420002, 666), (3430002, 672), (3440002, 685), (3450002, 670), (3460002, 646), (3470002, 654), (3480002, 637), (3490002, 636), (3500002, 668), (3510002, 651), (3520002, 663), (3530002, 630), (3540002, 663), (3550002, 655), (3560002, 668), (3570002, 671), (3580002, 640), (3590002, 666), (3600002, 670), (3610002, 691), (3620002, 670), (3630002, 686), (3640002, 652), (3650002, 638), (3660002, 650), (3670002, 663), (3680002, 701), (3690002, 638), (3700002, 682), (3710002, 654), (3720002, 671), (3730002, 687), (3740002, 658), (3750002, 650), (3760002, 666), (3770002, 632), (3780002, 655), (3790002, 660), (3800002, 656), (3810002, 656), (3820002, 682), (3830002, 674), (3840002, 646), (3850002, 677), (3860002, 650), (3870002, 647), (3880002, 650), (3890002, 661), (3900002, 681), (3910002, 652), (3920002, 657), (3930002, 676), (3940002, 647), (3950002, 678), (3960002, 643), (3970002, 638), (3980002, 668), (3990002, 635), (4000002, 641), (4010002, 660), (4020002, 658), (4030002, 668), (4040002, 677), (4050002, 681), (4060002, 643), (4070002, 653), (4080002, 671), (4090002, 653), (4100002, 664), (4110002, 663), (4120002, 628), (4130002, 652), (4140002, 633), (4150002, 660), (4160002, 662), (4170002, 671), (4180002, 651), (4190002, 673), (4200002, 647), (4210002, 670), (4220002, 644), (4230002, 663), (4240002, 628), (4250002, 664), (4260002, 661), (4270002, 643), (4280002, 656), (4290002, 632), (4300002, 649), (4310002, 662), (4320002, 666), (4330002, 641), (4340002, 656), (4350002, 635), (4360002, 641), (4370002, 652), (4380002, 662), (4390002, 661), (4400002, 635), (4410002, 641), (4420002, 680), (4430002, 682), (4440002, 657), (4450002, 671), (4460002, 655), (4470002, 660), (4480002, 647), (4490002, 682), (4500002, 638), (4510002, 653), (4520002, 638), (4530002, 646), (4540002, 631), (4550002, 648), (4560002, 660), (4570002, 673), (4580002, 649), (4590002, 640), (4600002, 655), (4610002, 662), (4620002, 657), (4630002, 644), (4640002, 651), (4650002, 651), (4660002, 617), (4670002, 664), (4680002, 667), (4690002, 667), (4700002, 643), (4710002, 652), (4720002, 653), (4730002, 643), (4740002, 663), (4750002, 645), (4760002, 641), (4770002, 655), (4780002, 628), (4790002, 657), (4800002, 638), (4810002, 657), (4820002, 655), (4830002, 631), (4840002, 678), (4850002, 634), (4860002, 645), (4870002, 670), (4880002, 635), (4890002, 670), (4900002, 679), (4910002, 650), (4920002, 634), (4930002, 654), (4940002, 654), (4950002, 650), (4960002, 641), (4970002, 682), (4980002, 661), (4990002, 653), (5000002, 641), (5010002, 639), (5020002, 639), (5030002, 658), (5040002, 638), (5050002, 628), (5060002, 668), (5070002, 639), (5080002, 648), (5090002, 655), (5100002, 646), (5110002, 632), (5120002, 641), (5130002, 656), (5140002, 659), (5150002, 639), (5160002, 644), (5170002, 646), (5180002, 630), (5190002, 642), (5200002, 647), (5210002, 659), (5220002, 650), (5230002, 649), (5240002, 647), (5250002, 673), (5260002, 631), (5270002, 648), (5280002, 653), (5290002, 629), (5300002, 654), (5310002, 654), (5320002, 637), (5330002, 643), (5340002, 649), (5350002, 648), (5360002, 642), (5370002, 642), (5380002, 653), (5390002, 654), (5400002, 641), (5410002, 629), (5420002, 640), (5430002, 657), (5440002, 650), (5450002, 635), (5460002, 659), (5470002, 641), (5480002, 623), (5490002, 651), (5500002, 652), (5510002, 638), (5520002, 624), (5530002, 633), (5540002, 666), (5550002, 618), (5560002, 635), (5570002, 654), (5580002, 636), (5590002, 641), (5600002, 657), (5610002, 633), (5620002, 639), (5630002, 637), (5640002, 643), (5650002, 624), (5660002, 641), (5670002, 635), (5680002, 639), (5690002, 634), (5700002, 679), (5710002, 635), (5720002, 667), (5730002, 632), (5740002, 633), (5750002, 653), (5760002, 636), (5770002, 618), (5780002, 636), (5790002, 637), (5800002, 640), (5810002, 654), (5820002, 632), (5830002, 628), (5840002, 640), (5850002, 657), (5860002, 627), (5870002, 635), (5880002, 641), (5890002, 677), (5900002, 645), (5910002, 648), (5920002, 667), (5930002, 649), (5940002, 646), (5950002, 633), (5960002, 639), (5970002, 634), (5980002, 635), (5990002, 644), (6000002, 625), (6010002, 661), (6020002, 638), (6030002, 664), (6040002, 601), (6050002, 627), (6060002, 666), (6070002, 615), (6080002, 653), (6090002, 629), (6100002, 644), (6110002, 651), (6120002, 641), (6130002, 636), (6140002, 637), (6150002, 637), (6160002, 645), (6170002, 658), (6180002, 628), (6190002, 618), (6200002, 650), (6210002, 644), (6220002, 603), (6230002, 652), (6240002, 633), (6250002, 636), (6260002, 650), (6270002, 648), (6280002, 635), (6290002, 664), (6300002, 660), (6310002, 646), (6320002, 634), (6330002, 649), (6340002, 633), (6350002, 630), (6360002, 637), (6370002, 626), (6380002, 609), (6390002, 629), (6400002, 644), (6410002, 630), (6420002, 643), (6430002, 635), (6440002, 611), (6450002, 633), (6460002, 659), (6470002, 632), (6480002, 628), (6490002, 637), (6500002, 639), (6510002, 642), (6520002, 640), (6530002, 646), (6540002, 629), (6550002, 642), (6560002, 639), (6570002, 635), (6580002, 638), (6590002, 659), (6600002, 633), (6610002, 640), (6620002, 662), (6630002, 615), (6640002, 620), (6650002, 640), (6660002, 613), (6670002, 648), (6680002, 630), (6690002, 619), (6700002, 650), (6710002, 655), (6720002, 634), (6730002, 646), (6740002, 634), (6750002, 642), (6760002, 661), (6770002, 618), (6780002, 632), (6790002, 620), (6800002, 633), (6810002, 632), (6820002, 654), (6830002, 633), (6840002, 631), (6850002, 633), (6860002, 663), (6870002, 660), (6880002, 623), (6890002, 651), (6900002, 632), (6910002, 636), (6920002, 641), (6930002, 615), (6940002, 652), (6950002, 642), (6960002, 632), (6970002, 647), (6980002, 632), (6990002, 631), (7000002, 636), (7010002, 629), (7020002, 630), (7030002, 653), (7040002, 648), (7050002, 656), (7060002, 628), (7070002, 594), (7080002, 661), (7090002, 640), (7100002, 628), (7110002, 664), (7120002, 607), (7130002, 611), (7140002, 617), (7150002, 653), (7160002, 640), (7170002, 629), (7180002, 615), (7190002, 630), (7200002, 638), (7210002, 633), (7220002, 629), (7230002, 635), (7240002, 626), (7250002, 652), (7260002, 615), (7270002, 647), (7280002, 642), (7290002, 637), (7300002, 632), (7310002, 627), (7320002, 630), (7330002, 636), (7340002, 616), (7350002, 621), (7360002, 642), (7370002, 643), (7380002, 635), (7390002, 626), (7400002, 619), (7410002, 620), (7420002, 642), (7430002, 632), (7440002, 635), (7450002, 656), (7460002, 615), (7470002, 610), (7480002, 647), (7490002, 631), (7500002, 611), (7510002, 626), (7520002, 626), (7530002, 613), (7540002, 638), (7550002, 653), (7560002, 645), (7570002, 615), (7580002, 607), (7590002, 638), (7600002, 643), (7610002, 657), (7620002, 616), (7630002, 649), (7640002, 611), (7650002, 642), (7660002, 633), (7670002, 625), (7680002, 630), (7690002, 639), (7700002, 643), (7710002, 612), (7720002, 646), (7730002, 629), (7740002, 607), (7750002, 622), (7760002, 626), (7770002, 613), (7780002, 646), (7790002, 611), (7800002, 632), (7810002, 638), (7820002, 631), (7830002, 623), (7840002, 642), (7850002, 646), (7860002, 630), (7870002, 628), (7880002, 647), (7890002, 641), (7900002, 627), (7910002, 629), (7920002, 616), (7930002, 633), (7940002, 628), (7950002, 640), (7960002, 603), (7970002, 634), (7980002, 638), (7990002, 635), (8000002, 614), (8010002, 637), (8020002, 609), (8030002, 631), (8040002, 605), (8050002, 640), (8060002, 650), (8070002, 627), (8080002, 623), (8090002, 618), (8100002, 607), (8110002, 619), (8120002, 633), (8130002, 651), (8140002, 602), (8150002, 621), (8160002, 648), (8165753, 374)]

theorem Nat.nth_prime_550171 : Nat.nth Nat.Prime 550171 ≤ 8165753 :=
  _root_.Nat.nth_prime_550171

lemma nonempty_of_surjective (h : ∀ y : ZMod 550172, ∃ k, 1 ≤ k ∧ (2 ^ k - k : ZMod 550172) = y) :
    ∃ m, A232616_prop 550172 m := by
  let f (y : ZMod 550172) : ℕ := Classical.choose (h y)
  have h_spec (y : ZMod 550172) : 1 ≤ f y ∧ (2 ^ (f y) - (f y) : ZMod 550172) = y := Classical.choose_spec (h y)
  let m := (univ : Finset (ZMod 550172)).sup f
  use m
  unfold A232616_prop
  ext y
  constructor
  · intro _
    rw [Finset.mem_image]
    use f y
    refine ⟨?_, (h_spec y).2⟩
    rw [Finset.mem_Icc]
    refine ⟨(h_spec y).1, ?_⟩
    apply Finset.le_sup (mem_univ y)
  · intro _
    exact mem_univ y

theorem A232616_550172_ge : A232616 550172 ≥ 16331504 := by
  have h_zero : 550172 ≠ 0 := by decide
  rw [A232616, dif_neg h_zero]
  have h_nonempty : {m | A232616_prop 550172 m}.Nonempty := by
    have h_surj : ∀ y : ZMod 550172, ∃ k : ℕ, 1 ≤ k ∧ (2 ^ k - k : ZMod 550172) = y := preimage_exists
    rcases nonempty_of_surjective h_surj with ⟨m, hm⟩
    exact ⟨m, hm⟩
  have h_mem := Nat.sInf_mem h_nonempty
  have h_not : 0 ∉ {m | A232616_prop 550172 m} := by
    intro h_prop
    unfold A232616_prop at h_prop
    have h_mem_univ : (0 : ZMod 550172) ∈ (univ : Finset (ZMod 550172)) := mem_univ 0
    rw [h_prop] at h_mem_univ
    rw [Finset.mem_image] at h_mem_univ
    rcases h_mem_univ with ⟨k, hk, _⟩
    rw [Finset.mem_Icc] at hk
    omega
  have h_ne_zero : sInf {m | A232616_prop 550172 m} ≠ 0 := by
    intro hc
    rw [hc] at h_mem
    exact h_not h_mem
  have h_spec := h_mem
  change A232616_prop 550172 (sInf {m | A232616_prop 550172 m}) at h_spec
  by_contra! h_lt
  have h_le : sInf {m | A232616_prop 550172 m} ≤ 16331503 := by omega
  have h_prop_16331503 : A232616_prop 550172 16331503 := A232616_prop_mono 550172 (sInf {m | A232616_prop 550172 m}) 16331503 h_le h_spec
  unfold A232616_prop at h_prop_16331503
  have h_mem_univ : (13573 : ZMod 550172) ∈ (univ : Finset (ZMod 550172)) := mem_univ 13573
  rw [h_prop_16331503] at h_mem_univ
  rw [Finset.mem_image] at h_mem_univ
  rcases h_mem_univ with ⟨k, hk, h_eq⟩
  rw [Finset.mem_Icc] at hk
  have h_ne := k_not_covered k hk.1 hk.2
  have h_eq2 : (2 ^ k - k : ZMod 550172) = 13573 := by
    rw [← h_eq]
    rw [Nat.cast_sub (k_le_pow_two k)]
    push_cast
    rfl
  exact h_ne h_eq2

/--
Conjecture (i): $a(n) < 2 \cdot (       ext{prime}(n) - 1)$ for all $n > 0$,
where $ ext{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ), 0 < n → A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have h_spec := h 550172 (by decide)
  change A232616 550172 < 2 * (Nat.nth Nat.Prime 550171 - 1) at h_spec
  have h_prime := Nat.nth_prime_550171
  have h_bound : 2 * (Nat.nth Nat.Prime 550171 - 1) ≤ 16331504 := by omega
  have h_A := A232616_550172_ge
  omega
