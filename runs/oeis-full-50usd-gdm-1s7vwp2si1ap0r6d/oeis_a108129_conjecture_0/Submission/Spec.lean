/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports
set_option warn.sorry false

open Nat Classical

/--
Riesel problem: let $k=2n-1$; then a(n)=smallest $m \ge 1$ such that $k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.
We use PNat for the exponent $m$ to correctly model $m \ge 1$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let k : ℕ := 2 * n - 1
    -- The predicate P(m) for m in PNat (m >= 1).
    let P (m : PNat) : Prop := (k * (2 ^ (m : ℕ)) - 1).Prime

    -- Use classical choice to find the minimum, or return -1 if no such prime exists.
    dite (∃ m : PNat, P m)
    (fun h_exists : ∃ m : PNat, P m =>
      -- PNat.find returns the minimum element. We coerce it to ℕ, then to ℤ.
      let m_min := PNat.find h_exists
      (m_min : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )

lemma helper (q r d p : ℕ) (h_ord : (2^d) % p = 1) : (2^(q * d + r)) % p = (2^r) % p := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h_split : (q + 1) * d + r = q * d + r + d := by ring
    rw [h_split, pow_add]
    rw [Nat.mul_mod, ih, h_ord]
    simp

theorem test_case_0 (m q : ℕ) (h_m : m = q * 24 + 0) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^0 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^0) % 3 := by
    rw [h_m]
    exact helper q 0 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^0) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^0) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^0 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^0 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_1 (m q : ℕ) (h_m : m = q * 24 + 1) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^1 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^1) % 5 := by
    rw [h_m]
    exact helper q 1 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^1) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^1) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^1 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^1 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_2 (m q : ℕ) (h_m : m = q * 24 + 2) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^2 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^2) % 3 := by
    rw [h_m]
    exact helper q 2 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^2) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^2) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^2 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^2 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_3 (m q : ℕ) (h_m : m = q * 24 + 3) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 241 = 1 := by decide
  have h_rem : (509203 * 2^3 - 1) % 241 = 0 := by decide
  have h_pow_eq : (2^m) % 241 = (2^3) % 241 := by
    rw [h_m]
    exact helper q 3 24 241 h_ord
  have h_pow_modeq : Nat.ModEq 241 (2^m) (2^3) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 241 (509203 * 2^m) (509203 * 2^3) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 241 (509203 * 2^m - 1) (509203 * 2^3 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 241 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 241 = (509203 * 2^3 - 1) % 241 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 241 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_4 (m q : ℕ) (h_m : m = q * 24 + 4) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^4 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^4) % 3 := by
    rw [h_m]
    exact helper q 4 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^4) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^4) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^4 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^4 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_5 (m q : ℕ) (h_m : m = q * 24 + 5) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^5 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^5) % 5 := by
    rw [h_m]
    exact helper q 5 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^5) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^5) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^5 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^5 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_6 (m q : ℕ) (h_m : m = q * 24 + 6) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^6 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^6) % 3 := by
    rw [h_m]
    exact helper q 6 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^6) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^6) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^6 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^6 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_7 (m q : ℕ) (h_m : m = q * 24 + 7) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 13 = 1 := by decide
  have h_rem : (509203 * 2^7 - 1) % 13 = 0 := by decide
  have h_pow_eq : (2^m) % 13 = (2^7) % 13 := by
    rw [h_m]
    exact helper q 7 24 13 h_ord
  have h_pow_modeq : Nat.ModEq 13 (2^m) (2^7) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 13 (509203 * 2^m) (509203 * 2^7) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 13 (509203 * 2^m - 1) (509203 * 2^7 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 13 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 13 = (509203 * 2^7 - 1) % 13 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 13 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_8 (m q : ℕ) (h_m : m = q * 24 + 8) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^8 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^8) % 3 := by
    rw [h_m]
    exact helper q 8 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^8) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^8) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^8 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^8 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_9 (m q : ℕ) (h_m : m = q * 24 + 9) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^9 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^9) % 5 := by
    rw [h_m]
    exact helper q 9 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^9) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^9) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^9 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^9 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_10 (m q : ℕ) (h_m : m = q * 24 + 10) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^10 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^10) % 3 := by
    rw [h_m]
    exact helper q 10 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^10) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^10) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^10 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^10 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_11 (m q : ℕ) (h_m : m = q * 24 + 11) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 7 = 1 := by decide
  have h_rem : (509203 * 2^11 - 1) % 7 = 0 := by decide
  have h_pow_eq : (2^m) % 7 = (2^11) % 7 := by
    rw [h_m]
    exact helper q 11 24 7 h_ord
  have h_pow_modeq : Nat.ModEq 7 (2^m) (2^11) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 7 (509203 * 2^m) (509203 * 2^11) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 7 (509203 * 2^m - 1) (509203 * 2^11 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 7 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 7 = (509203 * 2^11 - 1) % 7 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 7 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_12 (m q : ℕ) (h_m : m = q * 24 + 12) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^12 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^12) % 3 := by
    rw [h_m]
    exact helper q 12 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^12) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^12) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^12 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^12 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_13 (m q : ℕ) (h_m : m = q * 24 + 13) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^13 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^13) % 5 := by
    rw [h_m]
    exact helper q 13 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^13) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^13) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^13 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^13 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_14 (m q : ℕ) (h_m : m = q * 24 + 14) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^14 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^14) % 3 := by
    rw [h_m]
    exact helper q 14 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^14) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^14) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^14 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^14 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_15 (m q : ℕ) (h_m : m = q * 24 + 15) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 17 = 1 := by decide
  have h_rem : (509203 * 2^15 - 1) % 17 = 0 := by decide
  have h_pow_eq : (2^m) % 17 = (2^15) % 17 := by
    rw [h_m]
    exact helper q 15 24 17 h_ord
  have h_pow_modeq : Nat.ModEq 17 (2^m) (2^15) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 17 (509203 * 2^m) (509203 * 2^15) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 17 (509203 * 2^m - 1) (509203 * 2^15 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 17 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 17 = (509203 * 2^15 - 1) % 17 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 17 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_16 (m q : ℕ) (h_m : m = q * 24 + 16) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^16 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^16) % 3 := by
    rw [h_m]
    exact helper q 16 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^16) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^16) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^16 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^16 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_17 (m q : ℕ) (h_m : m = q * 24 + 17) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^17 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^17) % 5 := by
    rw [h_m]
    exact helper q 17 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^17) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^17) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^17 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^17 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_18 (m q : ℕ) (h_m : m = q * 24 + 18) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^18 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^18) % 3 := by
    rw [h_m]
    exact helper q 18 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^18) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^18) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^18 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^18 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_19 (m q : ℕ) (h_m : m = q * 24 + 19) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 13 = 1 := by decide
  have h_rem : (509203 * 2^19 - 1) % 13 = 0 := by decide
  have h_pow_eq : (2^m) % 13 = (2^19) % 13 := by
    rw [h_m]
    exact helper q 19 24 13 h_ord
  have h_pow_modeq : Nat.ModEq 13 (2^m) (2^19) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 13 (509203 * 2^m) (509203 * 2^19) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 13 (509203 * 2^m - 1) (509203 * 2^19 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 13 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 13 = (509203 * 2^19 - 1) % 13 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 13 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_20 (m q : ℕ) (h_m : m = q * 24 + 20) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^20 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^20) % 3 := by
    rw [h_m]
    exact helper q 20 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^20) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^20) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^20 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^20 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_21 (m q : ℕ) (h_m : m = q * 24 + 21) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 5 = 1 := by decide
  have h_rem : (509203 * 2^21 - 1) % 5 = 0 := by decide
  have h_pow_eq : (2^m) % 5 = (2^21) % 5 := by
    rw [h_m]
    exact helper q 21 24 5 h_ord
  have h_pow_modeq : Nat.ModEq 5 (2^m) (2^21) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 5 (509203 * 2^m) (509203 * 2^21) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 5 (509203 * 2^m - 1) (509203 * 2^21 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 5 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 5 = (509203 * 2^21 - 1) % 5 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 5 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_22 (m q : ℕ) (h_m : m = q * 24 + 22) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 3 = 1 := by decide
  have h_rem : (509203 * 2^22 - 1) % 3 = 0 := by decide
  have h_pow_eq : (2^m) % 3 = (2^22) % 3 := by
    rw [h_m]
    exact helper q 22 24 3 h_ord
  have h_pow_modeq : Nat.ModEq 3 (2^m) (2^22) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 3 (509203 * 2^m) (509203 * 2^22) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 3 (509203 * 2^m - 1) (509203 * 2^22 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 3 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 3 = (509203 * 2^22 - 1) % 3 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 3 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem test_case_23 (m q : ℕ) (h_m : m = q * 24 + 23) : ¬ (509203 * 2^m - 1).Prime := by
  have h_ord : (2^24) % 7 = 1 := by decide
  have h_rem : (509203 * 2^23 - 1) % 7 = 0 := by decide
  have h_pow_eq : (2^m) % 7 = (2^23) % 7 := by
    rw [h_m]
    exact helper q 23 24 7 h_ord
  have h_pow_modeq : Nat.ModEq 7 (2^m) (2^23) := h_pow_eq
  have h_mul_modeq : Nat.ModEq 7 (509203 * 2^m) (509203 * 2^23) := Nat.ModEq.mul_left 509203 h_pow_modeq
  have h_sub_modeq : Nat.ModEq 7 (509203 * 2^m - 1) (509203 * 2^23 - 1) := Nat.ModEq.sub (by omega) (by omega) h_mul_modeq (Nat.ModEq.refl 1)
  have h_mod_zero : (509203 * 2^m - 1) % 7 = 0 := by
    have h_trans : (509203 * 2^m - 1) % 7 = (509203 * 2^23 - 1) % 7 := h_sub_modeq
    rw [h_trans, h_rem]
  have h_dvd : 7 ∣ 509203 * 2^m - 1 := Nat.dvd_of_mod_eq_zero h_mod_zero
  apply Nat.not_prime_of_dvd_of_lt h_dvd
  · decide
  · omega

theorem not_prime_509203 (m : ℕ) : ¬ (509203 * 2^m - 1).Prime := by
  have h_r : m % 24 < 24 := Nat.mod_lt m (by decide)
  match h_r : m % 24 with
  | 0 => exact test_case_0 m (m / 24) (by omega)
  | 1 => exact test_case_1 m (m / 24) (by omega)
  | 2 => exact test_case_2 m (m / 24) (by omega)
  | 3 => exact test_case_3 m (m / 24) (by omega)
  | 4 => exact test_case_4 m (m / 24) (by omega)
  | 5 => exact test_case_5 m (m / 24) (by omega)
  | 6 => exact test_case_6 m (m / 24) (by omega)
  | 7 => exact test_case_7 m (m / 24) (by omega)
  | 8 => exact test_case_8 m (m / 24) (by omega)
  | 9 => exact test_case_9 m (m / 24) (by omega)
  | 10 => exact test_case_10 m (m / 24) (by omega)
  | 11 => exact test_case_11 m (m / 24) (by omega)
  | 12 => exact test_case_12 m (m / 24) (by omega)
  | 13 => exact test_case_13 m (m / 24) (by omega)
  | 14 => exact test_case_14 m (m / 24) (by omega)
  | 15 => exact test_case_15 m (m / 24) (by omega)
  | 16 => exact test_case_16 m (m / 24) (by omega)
  | 17 => exact test_case_17 m (m / 24) (by omega)
  | 18 => exact test_case_18 m (m / 24) (by omega)
  | 19 => exact test_case_19 m (m / 24) (by omega)
  | 20 => exact test_case_20 m (m / 24) (by omega)
  | 21 => exact test_case_21 m (m / 24) (by omega)
  | 22 => exact test_case_22 m (m / 24) (by omega)
  | 23 => exact test_case_23 m (m / 24) (by omega)
  | x + 24 => omega

theorem a_254602_eq : a 254602 = -1 := by
  have h_not : ¬ ∃ m : PNat, (509203 * 2 ^ (m : ℕ) - 1).Prime := by
    intro h_exists
    rcases h_exists with ⟨m, h_prime⟩
    exact not_prime_509203 (m : ℕ) h_prime
  unfold a
  have h_ne : 254602 ≠ 0 := by decide
  rw [if_neg h_ne]
  exact dif_neg h_not

lemma a_ne_minus_one_of_exists (n : ℕ) (h_ne : n ≠ 0) (h_exists : ∃ m : PNat, ((2*n-1) * 2^(m:ℕ) - 1).Prime) : a n ≠ -1 := by
  unfold a
  rw [if_neg h_ne]
  rw [dif_pos h_exists]
  intro h_eq
  have h_ge : 0 ≤ ((PNat.find h_exists : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [h_eq] at h_ge
  contradiction

lemma a_ne_minus_one_of_prime (n : ℕ) (h_ne : n ≠ 0) (m : PNat) (hp : ((2*n-1) * 2^(m:ℕ) - 1).Prime) : a n ≠ -1 := by
  apply a_ne_minus_one_of_exists n h_ne
  use m

/--
It is conjectured that the integer k = 509203 is the smallest Riesel number,
that is, the first n such that a(n) = -1 is 254602.
-/
theorem oeis_a108129_conjecture_0 :
  a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) := by
  constructor
  · exact a_254602_eq
  · intro n hn
    sorry


