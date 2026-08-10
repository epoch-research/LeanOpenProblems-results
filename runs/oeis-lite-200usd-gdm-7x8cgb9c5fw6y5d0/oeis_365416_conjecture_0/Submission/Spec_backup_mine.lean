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

open Nat
set_option maxRecDepth 200000

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

namespace A365416

lemma isCompositePrimePow_iff (m : ℕ) :
    IsCompositePrimePow m ↔ IsPrimePow m ∧ ¬ Nat.Prime m := by
  constructor
  · rintro ⟨p, e, hp, he, rfl⟩
    constructor
    · rw [isPrimePow_nat_iff]
      refine ⟨p, e, hp, by omega, rfl⟩
    · intro h_prime
      have he2 : 2 ≤ e := by omega
      obtain ⟨e', he_eq⟩ := Nat.exists_eq_add_of_le he2
      have he_eq' : e = e' + 2 := by rw [he_eq, add_comm]
      have hpe : p ^ (e' + 2) = p ^ e := by rw [← he_eq']
      rw [← hpe] at h_prime
      have h_div : p ∣ p ^ (e' + 2) := dvd_pow_self _ (by omega)
      have h_eq := h_prime.eq_one_or_self_of_dvd p h_div
      rcases h_eq with hp1 | hpe_eq
      · exact hp.ne_one hp1
      · have h_mul : p * p ^ (e' + 1) = p * 1 := by
          calc p * p ^ (e' + 1) = p ^ (e' + 2) := by ring
          _ = p := hpe_eq.symm
          _ = p * 1 := by ring
        have h_pow : p ^ (e' + 1) = 1 := Nat.eq_of_mul_eq_mul_left hp.pos h_mul
        have hp2 : p ^ (e' + 1) ≥ 2 := by
          calc p ^ (e' + 1) ≥ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
          _ = p := pow_one p
          _ ≥ 2 := hp.two_le
        omega
  · rintro ⟨hpow, hnp⟩
    rw [isPrimePow_nat_iff] at hpow
    obtain ⟨p, e, hp, he, rfl⟩ := hpow
    have he1 : e > 1 := by
      by_contra! he_le
      have he_eq : e = 1 := by omega
      subst he_eq
      rw [pow_one] at hnp
      exact hnp hp
    exact ⟨p, e, hp, he1, rfl⟩

lemma not_isPrimePow_of_two_prime_divisors {n p1 p2 : ℕ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp12 : p1 ≠ p2)
    (hdvd1 : p1 ∣ n) (hdvd2 : p2 ∣ n) : ¬ IsPrimePow n := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, hp, hunique⟩
  have h1 : p1 = p := hunique p1 ⟨hp1, hdvd1⟩
  have h2 : p2 = p := hunique p2 ⟨hp2, hdvd2⟩
  subst h1 h2
  exact hp12 rfl

lemma not_isCompositePrimePow_of_not_isPrimePow {m : ℕ} (h : ¬ IsPrimePow m) : ¬ IsCompositePrimePow m := by
  rw [isCompositePrimePow_iff]
  rintro ⟨h1, -⟩
  exact h h1

lemma not_isCompositePrimePow_zero : ¬ IsCompositePrimePow 0 :=
  not_isCompositePrimePow_of_not_isPrimePow not_isPrimePow_zero

lemma not_isCompositePrimePow_one : ¬ IsCompositePrimePow 1 :=
  not_isCompositePrimePow_of_not_isPrimePow not_isPrimePow_one

lemma not_isCompositePrimePow_of_prime {m : ℕ} (hp : m.Prime) : ¬ IsCompositePrimePow m := by
  rw [isCompositePrimePow_iff]
  rintro ⟨-, hnp⟩
  exact hnp hp

lemma not_isCompositePrimePow_15 : ¬ IsCompositePrimePow 15 :=
  not_isCompositePrimePow_of_not_isPrimePow (not_isPrimePow_of_two_prime_divisors (p1 := 3) (p2 := 5) (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num))

lemma not_isCompositePrimePow_21 : ¬ IsCompositePrimePow 21 :=
  not_isCompositePrimePow_of_not_isPrimePow (not_isPrimePow_of_two_prime_divisors (p1 := 3) (p2 := 7) (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num))

lemma h_no_sq_diff (A B : ℕ) (hAB : A^2 = B^2 + 2) : False := by
  by_cases hB : B = 0
  · subst hB
    have hA : A = 0 ∨ A = 1 ∨ A ≥ 2 := by omega
    rcases hA with rfl | rfl | hA_ge
    · norm_num at hAB
    · norm_num at hAB
    · have hA2 : A^2 ≥ 4 := by nlinarith
      omega
  · have hB_ge : B ≥ 1 := by omega
    have hA_gt : A > B := by
      by_contra! h_le
      have hA2 : A^2 ≤ B^2 := by nlinarith
      omega
    have hA_ge : A ≥ B + 1 := by omega
    have hA2 : A^2 ≥ (B + 1)^2 := by nlinarith
    have h_ring2 : (B+1)^2 = B^2 + 2 * B + 1 := by ring
    rw [h_ring2] at hA2
    omega

lemma add_mul_mod_self_nine (k x : ℕ) : (9 * k + x) % 9 = x % 9 := by
  omega

lemma sq_neq_two_mod_nine (X : ℕ) : X^2 % 9 ≠ 2 := by
  generalize h_Q : X / 9 = Q
  generalize h_r : X % 9 = r
  have hr : r < 9 := by
    rw [← h_r]
    exact Nat.mod_lt _ (by decide)
  have h_eq : X = 9 * Q + r := by
    rw [← h_r, ← h_Q]
    exact (Nat.div_add_mod X 9).symm
  have h_sq : X^2 = 9 * (9 * Q^2 + 2 * Q * r) + r^2 := by
    rw [h_eq]
    ring
  rw [h_sq]
  rw [add_mul_mod_self_nine]
  interval_cases r <;> (intro h; revert h; decide)

lemma test_p_odd (k p e : ℕ) (hk : k > 13) (hp : p.Prime) (he : e ≥ 2) (hpe : p^e = 2 * k - 1) : p ≠ 2 := by
  intro hp_eq_2
  subst hp_eq_2
  have h_pow : 2 ^ e = 2 * 2 ^ (e - 1) := by
    have : e = (e - 1) + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_even : (2 * k - 1) % 2 = 0 := by
    rw [← hpe, h_pow]
    omega
  have h_odd : (2 * k - 1) % 2 = 1 := by
    omega
  omega

lemma test_q_odd (k q d : ℕ) (hk : k > 13) (hq : q.Prime) (hd : d ≥ 2) (hqd : q^d = 2 * k + 1) : q ≠ 2 := by
  intro hq_eq_2
  subst hq_eq_2
  have h_pow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    have : d = (d - 1) + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_even : (2 * k + 1) % 2 = 0 := by
    rw [← hqd, h_pow]
    omega
  have h_odd : (2 * k + 1) % 2 = 1 := by
    omega
  omega

lemma nine_dvd_pow_three_of_ge_two (e : ℕ) (he : e ≥ 2) : 9 ∣ 3^e := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  have h_pow : 3 ^ (2 + e') = 9 * 3 ^ e' := by ring
  rw [h_pow]
  exact dvd_mul_right 9 (3 ^ e')

lemma no_solution_p_three_d_even (q d e : ℕ) (hd : ∃ d', d = 2 * d' ∧ d' ≥ 1) (he : e ≥ 2) (h : q^d = 3^e + 2) : False := by
  rcases hd with ⟨d', rfl, hd'⟩
  have h_sq : q ^ (2 * d') = (q ^ d') ^ 2 := by ring
  rw [h_sq] at h
  have h_dvd := nine_dvd_pow_three_of_ge_two e he
  rcases h_dvd with ⟨k, hk⟩
  have h_eq : (q ^ d') ^ 2 = 9 * k + 2 := by
    calc (q ^ d') ^ 2 = 3 ^ e + 2 := h
    _ = 9 * k + 2 := by rw [hk]
  have h_mod : (q ^ d') ^ 2 % 9 = 2 := by
    rw [h_eq]
    omega
  exact sq_neq_two_mod_nine (q ^ d') h_mod

theorem oeis_365416_conjecture_0_le12 (k : ℕ) (hk : k < 13) :
    ¬ (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) := by
  intro h
  interval_cases k
  · exact not_isCompositePrimePow_zero h.1
  · exact not_isCompositePrimePow_one h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.2
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_15 h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1
  · exact not_isCompositePrimePow_21 h.1
  · exact not_isCompositePrimePow_of_prime (by norm_num) h.1

lemma odd_of_not_even {e : ℕ} (h : ¬ ∃ e', e = 2 * e') : ∃ e', e = 2 * e' + 1 := by
  have h_mod : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · exfalso
    apply h
    use e / 2
    omega
  · use e / 2
    omega

lemma pow_mod_eq (a d p m : ℕ) (hp : a^p ≡ 1 [MOD m]) : a^d ≡ a^(d % p) [MOD m] := by
  have h_eq : d = p * (d / p) + d % p := (Nat.div_add_mod d p).symm
  nth_rw 1 [h_eq]
  rw [pow_add, pow_mul]
  have h1 : (a^p)^(d/p) ≡ 1^(d/p) [MOD m] := hp.pow _
  rw [one_pow] at h1
  have h2 : (a^p)^(d/p) * a^(d % p) ≡ 1 * a^(d % p) [MOD m] := h1.mul (by rfl)
  rw [one_mul] at h2
  exact h2

lemma helper_d_mod_100 (d : ℕ) (h : 3^d ≡ 2 [MOD 125]) : d % 100 = 43 := by
  have hp : 3^100 ≡ 1 [MOD 125] := by decide
  have h_eq : 3^d ≡ 3^(d % 100) [MOD 125] := pow_mod_eq 3 d 100 125 hp
  have h_trans : 3^(d % 100) ≡ 2 [MOD 125] := h_eq.symm.trans h
  have h_lt : d % 100 < 100 := Nat.mod_lt _ (by decide)
  generalize h_mod : d % 100 = x
  rw [h_mod] at h_lt h_trans
  interval_cases x <;> { revert h_trans; decide }

lemma helper_d_mod_5 (d : ℕ) (h_mod100 : d % 100 = 43) : d % 5 = 3 := by
  have h_eq : d = 100 * (d / 100) + d % 100 := (Nat.div_add_mod d 100).symm
  rw [h_mod100] at h_eq
  rw [h_eq]
  omega

lemma helper_3_pow_mod_11 (d : ℕ) (hd5 : d % 5 = 3) : 3^d ≡ 5 [MOD 11] := by
  have hp : 3^5 ≡ 1 [MOD 11] := by decide
  have h_eq : 3^d ≡ 3^(d % 5) [MOD 11] := pow_mod_eq 3 d 5 11 hp
  rw [hd5] at h_eq
  have h_dec : 3^3 ≡ 5 [MOD 11] := by decide
  exact h_eq.trans h_dec

lemma helper_5_pow_mod_11 (e': ℕ) (h : 5^(2 * e') + 2 ≡ 5 [MOD 11]) : e' % 5 = 1 := by
  have h_eq : 5^(2 * e') ≡ 3 [MOD 11] := by
    have h1 : (5^(2*e') + 2) % 11 = 5 := h
    have h2 : 5^(2*e') % 11 = 3 := by omega
    exact h2
  have hp : 5^5 ≡ 1 [MOD 11] := by decide
  have h_mod : 5^(2*e') ≡ 5^((2*e') % 5) [MOD 11] := pow_mod_eq 5 (2*e') 5 11 hp
  have h_trans : 5^((2*e') % 5) ≡ 3 [MOD 11] := h_mod.symm.trans h_eq
  have h_lt : (2*e') % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize h_y : (2*e') % 5 = y
  rw [h_y] at h_lt h_trans
  have hy2 : y = 2 := by
    interval_cases y <;> { revert h_trans; decide }
  rw [hy2] at h_y
  have h_eq2 : (2 * e') % 5 = (2 * (e' % 5)) % 5 := by
    rw [Nat.mul_mod]
  rw [h_eq2] at h_y
  have h_lt2 : e' % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize h_z : e' % 5 = z
  rw [h_z] at h_y h_lt2
  interval_cases z <;> { revert h_y; decide }

lemma helper_e'_mod_25 (e': ℕ) (he5 : e' % 5 = 1) :
    e' % 25 = 1 ∨ e' % 25 = 6 ∨ e' % 25 = 11 ∨ e' % 25 = 16 ∨ e' % 25 = 21 := by
  have h_eq : e' = 25 * (e' / 25) + e' % 25 := (Nat.div_add_mod e' 25).symm
  have h_lt : e' % 25 < 25 := Nat.mod_lt _ (by decide)
  have h_mod : (25 * (e' / 25) + e' % 25) % 5 = 1 := by
    rw [← he5, ← h_eq]
  have h_mod2 : (25 * (e' / 25) + e' % 25) % 5 = (e' % 25) % 5 := by
    have h_ring : 25 * (e' / 25) + e' % 25 = e' % 25 + 5 * (5 * (e' / 25)) := by ring
    rw [h_ring, Nat.add_mul_mod_self_left]
  rw [h_mod2] at h_mod
  generalize h_x : e' % 25 = x
  rw [h_x] at h_lt h_mod
  interval_cases x <;> { revert h_mod; decide }

lemma helper_2e'_mod_25 (e': ℕ) (he25 : e' % 25 = 1 ∨ e' % 25 = 6 ∨ e' % 25 = 11 ∨ e' % 25 = 16 ∨ e' % 25 = 21) :
    (2 * e') % 25 = 2 ∨ (2 * e') % 25 = 12 ∨ (2 * e') % 25 = 22 ∨ (2 * e') % 25 = 7 ∨ (2 * e') % 25 = 17 := by
  have h_eq : 2 * e' = 2 * (25 * (e' / 25) + e' % 25) := by
    nth_rw 1 [← Nat.div_add_mod e' 25]
  have h_mod : (2 * e') % 25 = (2 * (e' % 25)) % 25 := by
    have h_ring : 2 * (25 * (e' / 25) + e' % 25) = 2 * (e' % 25) + 25 * (2 * (e' / 25)) := by ring
    rw [h_eq, h_ring, Nat.add_mul_mod_self_left]
  rw [h_mod]
  rcases he25 with h1 | h2 | h3 | h4 | h5
  · rw [h1]; left; decide
  · rw [h2]; right; left; decide
  · rw [h3]; right; right; left; decide
  · rw [h4]; right; right; right; left; decide
  · rw [h5]; right; right; right; right; decide

lemma helper_5_2e'_mod_101 (e': ℕ) (h2e25 : (2 * e') % 25 = 2 ∨ (2 * e') % 25 = 12 ∨ (2 * e') % 25 = 22 ∨ (2 * e') % 25 = 7 ∨ (2 * e') % 25 = 17) :
    5^(2 * e') ≡ 25 [MOD 101] ∨ 5^(2 * e') ≡ 92 [MOD 101] ∨ 5^(2 * e') ≡ 80 [MOD 101] ∨ 5^(2 * e') ≡ 52 [MOD 101] ∨ 5^(2 * e') ≡ 54 [MOD 101] := by
  have hp : 5^25 ≡ 1 [MOD 101] := by decide
  have h_eq : 5^(2 * e') ≡ 5^((2 * e') % 25) [MOD 101] := pow_mod_eq 5 (2 * e') 25 101 hp
  rcases h2e25 with h1 | h2 | h3 | h4 | h5
  · rw [h1] at h_eq
    left
    have h_dec : 5^2 ≡ 25 [MOD 101] := by decide
    exact h_eq.trans h_dec
  · rw [h2] at h_eq
    right; left
    have h_dec : 5^12 ≡ 92 [MOD 101] := by decide
    exact h_eq.trans h_dec
  · rw [h3] at h_eq
    right; right; left
    have h_dec : 5^22 ≡ 80 [MOD 101] := by decide
    exact h_eq.trans h_dec
  · rw [h4] at h_eq
    right; right; right; left
    have h_dec : 5^7 ≡ 52 [MOD 101] := by decide
    exact h_eq.trans h_dec
  · rw [h5] at h_eq
    right; right; right; right
    have h_dec : 5^17 ≡ 54 [MOD 101] := by decide
    exact h_eq.trans h_dec

lemma helper_3_d_mod_101 (d : ℕ) (hd100 : d % 100 = 43) : 3^d ≡ 26 [MOD 101] := by
  have hp : 3^100 ≡ 1 [MOD 101] := by decide
  have h_eq : 3^d ≡ 3^(d % 100) [MOD 101] := pow_mod_eq 3 d 100 101 hp
  rw [hd100] at h_eq
  have h_dec : 3^43 ≡ 26 [MOD 101] := by decide
  exact h_eq.trans h_dec

lemma no_solution_5_pow_eq_3_pow (d e': ℕ) (h_eq : 5^(2 * e') + 2 = 3^d) (hd_mod : 3^d ≡ 2 [MOD 125]) : False := by
  have hd100 : d % 100 = 43 := helper_d_mod_100 d hd_mod
  have hd5 : d % 5 = 3 := helper_d_mod_5 d hd100
  have h3_11 : 3^d ≡ 5 [MOD 11] := helper_3_pow_mod_11 d hd5
  have h5_11 : 5^(2 * e') + 2 ≡ 5 [MOD 11] := by
    have h_mod : (5^(2*e') + 2) % 11 = 3^d % 11 := by rw [h_eq]
    have h3_11_mod : 3^d % 11 = 5 := h3_11
    rw [h3_11_mod] at h_mod
    exact h_mod
  have he'5 : e' % 5 = 1 := helper_5_pow_mod_11 e' h5_11
  have he'25 : e' % 25 = 1 ∨ e' % 25 = 6 ∨ e' % 25 = 11 ∨ e' % 25 = 16 ∨ e' % 25 = 21 := helper_e'_mod_25 e' he'5
  have h2e'25 : (2 * e') % 25 = 2 ∨ (2 * e') % 25 = 12 ∨ (2 * e') % 25 = 22 ∨ (2 * e') % 25 = 7 ∨ (2 * e') % 25 = 17 := helper_2e'_mod_25 e' he'25
  have h5_101 : 5^(2 * e') ≡ 25 [MOD 101] ∨ 5^(2 * e') ≡ 92 [MOD 101] ∨ 5^(2 * e') ≡ 80 [MOD 101] ∨ 5^(2 * e') ≡ 52 [MOD 101] ∨ 5^(2 * e') ≡ 54 [MOD 101] := helper_5_2e'_mod_101 e' h2e'25
  have h3_101 : 3^d ≡ 26 [MOD 101] := helper_3_d_mod_101 d hd100
  have h_eq_mod : (5^(2 * e') + 2) % 101 = 3^d % 101 := by rw [h_eq]
  have h_3_101_mod : 3^d % 101 = 26 := h3_101
  rw [h_3_101_mod] at h_eq_mod
  rcases h5_101 with h1 | h2 | h3 | h4 | h5
  · have h1' : (5^(2*e') + 2) % 101 = 27 := by
      have h1_mod : 5^(2*e') % 101 = 25 := h1
      omega
    omega
  · have h2' : (5^(2*e') + 2) % 101 = 94 := by
      have h2_mod : 5^(2*e') % 101 = 92 := h2
      omega
    omega
  · have h3' : (5^(2*e') + 2) % 101 = 82 := by
      have h3_mod : 5^(2*e') % 101 = 80 := h3
      omega
    omega
  · have h4' : (5^(2*e') + 2) % 101 = 54 := by
      have h4_mod : 5^(2*e') % 101 = 52 := h4
      omega
    omega
  · have h5' : (5^(2*e') + 2) % 101 = 56 := by
      have h5_mod : 5^(2*e') % 101 = 54 := h5
      omega
    omega


lemma helper_d_not_33_mod_48 (d : ℕ) (hd33 : d % 48 = 33) (hq73 : ∃ Y, Y^2 % 73 = (3^d + 71) % 73) : False := by
  rcases hq73 with ⟨Y, hY⟩
  have hp : 3^12 ≡ 1 [MOD 73] := by decide
  have h_eq : 3^d ≡ 3^(d % 12) [MOD 73] := pow_mod_eq 3 d 12 73 hp
  have h_trans : (3^d + 71) % 73 = (3^(d % 12) + 71) % 73 := by
    rw [Nat.add_mod, h_eq, ← Nat.add_mod]
  have hd12 : d % 12 = 9 := by omega
  rw [hd12] at h_trans
  rw [h_trans] at hY
  generalize h_Y_mod : Y % 73 = y
  have h_Y_sq : Y^2 % 73 = (y * y) % 73 := by
    have h1 : Y^2 % 73 = (Y * Y) % 73 := by rw [Nat.pow_two]
    have h2 : (Y * Y) % 73 = (Y % 73 * (Y % 73)) % 73 := Nat.mul_mod Y Y 73
    rw [h1, h2, h_Y_mod]
  rw [h_Y_sq] at hY
  have hy_lt : y < 73 := by
    rw [← h_Y_mod]
    exact Nat.mod_lt _ (by decide)
  have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 ∨ y = 17 ∨ y = 18 ∨ y = 19 ∨ y = 20 ∨ y = 21 ∨ y = 22 ∨ y = 23 ∨ y = 24 ∨ y = 25 ∨ y = 26 ∨ y = 27 ∨ y = 28 ∨ y = 29 ∨ y = 30 ∨ y = 31 ∨ y = 32 ∨ y = 33 ∨ y = 34 ∨ y = 35 ∨ y = 36 ∨ y = 37 ∨ y = 38 ∨ y = 39 ∨ y = 40 ∨ y = 41 ∨ y = 42 ∨ y = 43 ∨ y = 44 ∨ y = 45 ∨ y = 46 ∨ y = 47 ∨ y = 48 ∨ y = 49 ∨ y = 50 ∨ y = 51 ∨ y = 52 ∨ y = 53 ∨ y = 54 ∨ y = 55 ∨ y = 56 ∨ y = 57 ∨ y = 58 ∨ y = 59 ∨ y = 60 ∨ y = 61 ∨ y = 62 ∨ y = 63 ∨ y = 64 ∨ y = 65 ∨ y = 66 ∨ y = 67 ∨ y = 68 ∨ y = 69 ∨ y = 70 ∨ y = 71 ∨ y = 72 := by omega
  rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> { revert hY; decide }


lemma no_solution_3_pow_eq_sq_add_two (d Y : ℕ) (h_eq : 3^d = Y^2 + 2) (hY : Y % 5 ≠ 0) (hY_ge3 : Y ≥ 3) (hd : d % 2 = 1) : d % 48 = 1 := by
  have hd4 : d % 4 = 1 := by
    have hp : 3^4 ≡ 1 [MOD 5] := by decide
    have h_eq5 : 3^d ≡ 3^(d % 4) [MOD 5] := pow_mod_eq 3 d 4 5 hp
    have h_eq5_val : 3^d % 5 = (Y^2 + 2) % 5 := by omega
    have h_eq5_omega : (Y^2 + 2) % 5 = ((Y % 5)^2 + 2) % 5 := by
      rw [Nat.add_mod, Nat.pow_mod Y 2 5, ← Nat.add_mod]
    have h_eq5' : ((Y % 5)^2 + 2) % 5 = 3^(d % 4) % 5 := by
      calc ((Y % 5)^2 + 2) % 5 = (Y^2 + 2) % 5 := h_eq5_omega.symm
      _ = 3^d % 5 := h_eq5_val.symm
      _ = 3^(d % 4) % 5 := h_eq5
    have hY5 : Y % 5 < 5 := Nat.mod_lt _ (by decide)
    have hd4_cases : d % 4 = 1 ∨ d % 4 = 3 := by omega
    rcases hd4_cases with h_1 | h_3
    · exact h_1
    · exfalso
      generalize h_y : Y % 5 = y
      rw [h_y] at hY h_eq5' hY5
      rw [h_3] at h_eq5'
      interval_cases y <;> { revert hY h_eq5'; decide }
  have hd16 : d % 16 = 1 := by
    have hd16_cases : d % 16 = 1 ∨ d % 16 = 5 ∨ d % 16 = 9 ∨ d % 16 = 13 := by omega
    rcases hd16_cases with h1 | h2 | h3 | h4
    · exact h1
    · exfalso
      have hp : 3^16 ≡ 1 [MOD 17] := by decide
      have h_eq17 : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
      have h_eq17_val : 3^d % 17 = (Y^2 + 2) % 17 := by omega
      have h_eq17_omega : (Y^2 + 2) % 17 = ((Y % 17)^2 + 2) % 17 := by
        rw [Nat.add_mod, Nat.pow_mod Y 2 17, ← Nat.add_mod]
      have h_eq17' : ((Y % 17)^2 + 2) % 17 = 3^(d % 16) % 17 := by
        calc ((Y % 17)^2 + 2) % 17 = (Y^2 + 2) % 17 := h_eq17_omega.symm
        _ = 3^d % 17 := h_eq17_val.symm
        _ = 3^(d % 16) % 17 := h_eq17
      rw [h2] at h_eq17'
      have hY17 : Y % 17 < 17 := Nat.mod_lt _ (by decide)
      generalize h_y : Y % 17 = y
      rw [h_y] at h_eq17' hY17
      interval_cases y <;> { revert h_eq17'; decide }
    · exfalso
      have hp : 3^16 ≡ 1 [MOD 17] := by decide
      have h_eq17 : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
      have h_eq17_val : 3^d % 17 = (Y^2 + 2) % 17 := by omega
      have h_eq17_omega : (Y^2 + 2) % 17 = ((Y % 17)^2 + 2) % 17 := by
        rw [Nat.add_mod, Nat.pow_mod Y 2 17, ← Nat.add_mod]
      have h_eq17' : ((Y % 17)^2 + 2) % 17 = 3^(d % 16) % 17 := by
        calc ((Y % 17)^2 + 2) % 17 = (Y^2 + 2) % 17 := h_eq17_omega.symm
        _ = 3^d % 17 := h_eq17_val.symm
        _ = 3^(d % 16) % 17 := h_eq17
      rw [h3] at h_eq17'
      have hY17 : Y % 17 < 17 := Nat.mod_lt _ (by decide)
      generalize h_y : Y % 17 = y
      rw [h_y] at h_eq17' hY17
      interval_cases y <;> { revert h_eq17'; decide }
    · exfalso
      have hp : 3^16 ≡ 1 [MOD 17] := by decide
      have h_eq17 : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
      have h_eq17_val : 3^d % 17 = (Y^2 + 2) % 17 := by omega
      have h_eq17_omega : (Y^2 + 2) % 17 = ((Y % 17)^2 + 2) % 17 := by
        rw [Nat.add_mod, Nat.pow_mod Y 2 17, ← Nat.add_mod]
      have h_eq17' : ((Y % 17)^2 + 2) % 17 = 3^(d % 16) % 17 := by
        calc ((Y % 17)^2 + 2) % 17 = (Y^2 + 2) % 17 := h_eq17_omega.symm
        _ = 3^d % 17 := h_eq17_val.symm
        _ = 3^(d % 16) % 17 := h_eq17
      rw [h4] at h_eq17'
      have hY17 : Y % 17 < 17 := Nat.mod_lt _ (by decide)
      generalize h_y : Y % 17 = y
      rw [h_y] at h_eq17' hY17
      interval_cases y <;> { revert h_eq17'; decide }
  have hd12_cases : d % 12 = 1 ∨ d % 12 = 5 ∨ d % 12 = 9 := by omega
  have hd48_cases : d % 48 = 1 ∨ d % 48 = 17 ∨ d % 48 = 33 := by
    have h_div : d = 48 * (d / 48) + d % 48 := (Nat.div_add_mod d 48).symm
    have h_lt : d % 48 < 48 := Nat.mod_lt _ (by decide)
    have h_mod16 : d % 16 = (d % 48) % 16 := by omega
    have h_mod12 : d % 12 = (d % 48) % 12 := by omega
    rw [hd16] at h_mod16
    generalize h_r : d % 48 = r
    rw [h_r] at h_lt h_mod16 h_mod12
    rcases hd12_cases with h1 | h2 | h3
    · rw [h1] at h_mod12
      interval_cases r <;> { revert h_mod16 h_mod12; decide }
    · rw [h2] at h_mod12
      interval_cases r <;> { revert h_mod16 h_mod12; decide }
    · rw [h3] at h_mod12
      interval_cases r <;> { revert h_mod16 h_mod12; decide }
  rcases hd48_cases with h_1 | h_17 | h_33
  · exact h_1
  · exfalso
    have hd96_cases : d % 96 = 17 ∨ d % 96 = 65 := by omega
    rcases hd96_cases with hh1 | hh2
    · exfalso
      have hp : 3^96 ≡ 1 [MOD 97] := by decide
      have h_eq97 : 3^d ≡ 3^(d % 96) [MOD 97] := pow_mod_eq 3 d 96 97 hp
      have h_eq97_val : 3^d % 97 = (Y^2 + 2) % 97 := by omega
      have h_eq97_omega : (Y^2 + 2) % 97 = ((Y % 97)^2 + 2) % 97 := by
        rw [Nat.add_mod, Nat.pow_mod Y 2 97, ← Nat.add_mod]
      have h_eq97' : ((Y % 97)^2 + 2) % 97 = 3^(d % 96) % 97 := by
        calc ((Y % 97)^2 + 2) % 97 = (Y^2 + 2) % 97 := h_eq97_omega.symm
        _ = 3^d % 97 := h_eq97_val.symm
        _ = 3^(d % 96) % 97 := h_eq97
      rw [hh1] at h_eq97'
      have hY97 : Y % 97 < 97 := Nat.mod_lt _ (by decide)
      generalize h_y : Y % 97 = y
      rw [h_y] at h_eq97' hY97
      interval_cases y <;> { revert h_eq97'; decide }
    · exfalso
      have hp : 3^96 ≡ 1 [MOD 73] := by decide
      have h_eq73 : 3^d ≡ 3^(d % 96) [MOD 73] := pow_mod_eq 3 d 96 73 hp
      have h_eq73_val : 3^d % 73 = (Y^2 + 2) % 73 := by omega
      have h_eq73_omega : (Y^2 + 2) % 73 = ((Y % 73)^2 + 2) % 73 := by
        rw [Nat.add_mod, Nat.pow_mod Y 2 73, ← Nat.add_mod]
      have h_eq73' : ((Y % 73)^2 + 2) % 73 = 3^(d % 96) % 73 := by
        calc ((Y % 73)^2 + 2) % 73 = (Y^2 + 2) % 73 := h_eq73_omega.symm
        _ = 3^d % 73 := h_eq73_val.symm
        _ = 3^(d % 96) % 73 := h_eq73
      have hY73 : Y % 73 < 73 := Nat.mod_lt _ (by decide)
      generalize h_y : Y % 73 = y
      rw [hh2] at h_eq73'
      rw [h_y] at h_eq73' hY73
      interval_cases y <;> { revert h_eq73'; decide }
  · exfalso
    have hq73 : ∃ Y_val, Y_val^2 % 73 = (3^d + 71) % 73 := by
      use Y
      omega
    exact helper_d_not_33_mod_48 d h_33 hq73


lemma helper_d_mod_20 (d : ℕ) (hd25 : 3^d ≡ 2 [MOD 25]) : d % 20 = 3 := by
  have hp : 3^20 ≡ 1 [MOD 25] := by decide
  have h_eq : 3^d ≡ 3^(d % 20) [MOD 25] := pow_mod_eq 3 d 20 25 hp
  have h_trans : 3^(d % 20) ≡ 2 [MOD 25] := h_eq.symm.trans hd25
  have h_lt : d % 20 < 20 := Nat.mod_lt _ (by decide)
  generalize h_r : d % 20 = r
  rw [h_r] at h_trans h_lt
  interval_cases r <;> { revert h_trans; decide }

lemma helper_e_mod_10 (e : ℕ) (he_odd : e % 2 = 1) (h5_11 : 5^e ≡ 3 [MOD 11]) : e % 10 = 7 := by
  have hp : 5^5 ≡ 1 [MOD 11] := by decide
  have h_eq : 5^e ≡ 5^(e % 5) [MOD 11] := pow_mod_eq 5 e 5 11 hp
  have h_trans : 5^(e % 5) ≡ 3 [MOD 11] := h_eq.symm.trans h5_11
  have h_lt : e % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize h_r : e % 5 = r
  rw [h_r] at h_trans h_lt
  have hr2 : r = 2 := by
    interval_cases r <;> { revert h_trans; decide }
  rw [hr2] at h_r
  have h_eq2 : e = 10 * (e / 10) + e % 10 := (Nat.div_add_mod e 10).symm
  have h_lt2 : e % 10 < 10 := Nat.mod_lt _ (by decide)
  have h_mod5 : (10 * (e / 10) + e % 10) % 5 = 2 := by rw [← h_r, ← h_eq2]
  have h_mod2 : (10 * (e / 10) + e % 10) % 2 = 1 := by rw [← he_odd, ← h_eq2]
  have h_mod5_simp : (e % 10) % 5 = 2 := by
    have h_ring : 10 * (e / 10) + e % 10 = e % 10 + 5 * (2 * (e / 10)) := by ring
    rw [h_ring, Nat.add_mul_mod_self_left] at h_mod5
    exact h_mod5
  have h_mod2_simp : (e % 10) % 2 = 1 := by
    have h_ring : 10 * (e / 10) + e % 10 = e % 10 + 2 * (5 * (e / 10)) := by ring
    rw [h_ring, Nat.add_mul_mod_self_left] at h_mod2
    exact h_mod2
  generalize h_x : e % 10 = x
  rw [h_x] at h_lt2 h_mod5_simp h_mod2_simp
  interval_cases x <;> { revert h_mod5_simp h_mod2_simp; decide }


lemma no_solution_3_pow_eq_5_pow_odd (d e : ℕ) (h_eq : 5^d = 3^e + 2) (he3 : e ≥ 3) (he_odd : e % 2 = 1) : False := by
  have hd_mod18 : d % 18 = 11 := by
    have hp : 5^18 ≡ 1 [MOD 27] := by decide
    have h_eq27 : 5^d ≡ 5^(d % 18) [MOD 27] := pow_mod_eq 5 d 18 27 hp
    have h_val : 5^d % 27 = (3^e + 2) % 27 := by rw [h_eq]
    have h3e_zero : 3^e % 27 = 0 := by
      obtain ⟨e', he_eq⟩ := Nat.exists_eq_add_of_le he3
      have h_pow : 3^(3 + e') = 27 * 3^e' := by ring
      rw [he_eq, h_pow]
      omega
    have h_eq27_val : (3^e + 2) % 27 = 2 := by
      rw [Nat.add_mod, h3e_zero]
    have h_trans : 5^(d % 18) ≡ 2 [MOD 27] := by
      have h_trans_val : 5^(d % 18) % 27 = 2 := by
        calc 5^(d % 18) % 27 = 5^d % 27 := h_eq27.symm
        _ = (3^e + 2) % 27 := h_val
        _ = 2 := h_eq27_val
      exact h_trans_val
    have hd_lt : d % 18 < 18 := Nat.mod_lt _ (by decide)
    generalize h_r : d % 18 = r
    rw [h_r] at h_trans hd_lt
    interval_cases r <;> { revert h_trans; decide }
  have he_even_con : e % 18 = 14 := by
    have hp : 3^18 ≡ 1 [MOD 19] := by decide
    have h_eq19 : 3^e ≡ 3^(e % 18) [MOD 19] := pow_mod_eq 3 e 18 19 hp
    have h_val : 3^e % 19 = (5^d + 17) % 19 := by omega
    have h_5d : 5^d % 19 = 5^(d % 18) % 19 := by
      have hp5 : 5^18 ≡ 1 [MOD 19] := by decide
      exact pow_mod_eq 5 d 18 19 hp5
    rw [hd_mod18] at h_5d
    have h_5d_val : 5^11 % 19 = 6 := by decide
    rw [h_5d_val] at h_5d
    have h_val' : (5^d + 17) % 19 = 4 := by
      rw [Nat.add_mod, h_5d]
    have h_trans : 3^(e % 18) ≡ 4 [MOD 19] := by
      have h_trans_val : 3^(e % 18) % 19 = 4 := by
        calc 3^(e % 18) % 19 = 3^e % 19 := h_eq19.symm
        _ = (5^d + 17) % 19 := h_val
        _ = 4 := h_val'
      exact h_trans_val
    have he_lt : e % 18 < 18 := Nat.mod_lt _ (by decide)
    generalize h_r : e % 18 = r
    rw [h_r] at h_trans he_lt
    interval_cases r <;> { revert h_trans; decide }
  have he_even_con2 : e % 2 = 0 := by
    have h_div : e = 18 * (e / 18) + e % 18 := (Nat.div_add_mod e 18).symm
    rw [he_even_con] at h_div
    rw [h_div]
    omega
  omega

lemma no_solution_5_pow_eq_3_pow_odd (d e : ℕ) (h_eq : 3^d = 5^e + 2) (he_odd : e % 2 = 1) (he3 : e ≥ 3) : False := by
  have hd_mod25 : 3^d ≡ 2 [MOD 25] := by
    have h_pow : 5^e = 25 * 5^(e-2) := by
      have : e = 2 + (e - 2) := by omega
      nth_rw 1 [this]
      ring
    have h_mod : (5^e + 2) % 25 = 2 := by
      rw [h_pow]
      omega
    have h_val : 3^d = 5^e + 2 := h_eq
    rw [h_val]
    exact h_mod
  have hd20 : d % 20 = 3 := helper_d_mod_20 d hd_mod25
  have hd5 : d % 5 = 3 := by omega
  have h3_11 : 3^d ≡ 5 [MOD 11] := by
    have hp : 3^5 ≡ 1 [MOD 11] := by decide
    have h_eq_mod : 3^d ≡ 3^(d % 5) [MOD 11] := pow_mod_eq 3 d 5 11 hp
    rw [hd5] at h_eq_mod
    have h_dec : 3^3 ≡ 5 [MOD 11] := by decide
    exact h_eq_mod.trans h_dec
  have h5_11 : 5^e ≡ 3 [MOD 11] := by
    have h_mod : (5^e + 2) % 11 = 3^d % 11 := by rw [h_eq]
    have h3_11_mod : 3^d % 11 = 5 := h3_11
    rw [h3_11_mod] at h_mod
    have h_mod_add : (5^e + 2) % 11 = (5^e % 11 + 2) % 11 := Nat.add_mod (5^e) 2 11
    rw [h_mod_add] at h_mod
    change 5^e % 11 = 3
    generalize h_X : 5^e % 11 = X
    rw [h_X] at h_mod
    omega
  have he10 : e % 10 = 7 := helper_e_mod_10 e he_odd h5_11
  have hd_mod240 : d % 240 % 20 = 3 := by
    rw [Nat.mod_mod_of_dvd d (by decide : 20 ∣ 240)]
    exact hd20
  have he_mod80 : e % 80 % 10 = 7 := by
    rw [Nat.mod_mod_of_dvd e (by decide : 10 ∣ 80)]
    exact he10
  have hd_lt : d % 240 < 240 := Nat.mod_lt _ (by decide)
  have he_lt : e % 80 < 80 := Nat.mod_lt _ (by decide)
  generalize h_d240 : d % 240 = d240
  generalize h_e80 : e % 80 = e80
  rw [h_d240] at hd_mod240 hd_lt
  rw [h_e80] at he_mod80 he_lt
  have h_eq_13 : 3^d ≡ 5^e + 2 [MOD 13] := by
    have h_mod : (3^d) % 13 = (5^e + 2) % 13 := by rw [h_eq]
    exact h_mod
  have hp3_13 : 3^240 ≡ 1 [MOD 13] := by decide
  have hp5_13 : 5^80 ≡ 1 [MOD 13] := by decide
  have h3_13 : 3^d ≡ 3^(d % 240) [MOD 13] := pow_mod_eq 3 d 240 13 hp3_13
  have h5_13 : 5^e ≡ 5^(e % 80) [MOD 13] := pow_mod_eq 5 e 80 13 hp5_13
  have h5_13_add : (5^e + 2) % 13 = (5^(e % 80) + 2) % 13 := by
    rw [Nat.add_mod, h5_13, ← Nat.add_mod]
  have h_eq_13_simp : 3^(d % 240) ≡ 5^(e % 80) + 2 [MOD 13] :=
    h3_13.symm.trans (h_eq_13.trans h5_13_add)
  rw [h_d240, h_e80] at h_eq_13_simp
  have h_eq_17 : 3^d ≡ 5^e + 2 [MOD 17] := by
    have h_mod : (3^d) % 17 = (5^e + 2) % 17 := by rw [h_eq]
    exact h_mod
  have hp3_17 : 3^240 ≡ 1 [MOD 17] := by decide
  have hp5_17 : 5^80 ≡ 1 [MOD 17] := by decide
  have h3_17 : 3^d ≡ 3^(d % 240) [MOD 17] := pow_mod_eq 3 d 240 17 hp3_17
  have h5_17 : 5^e ≡ 5^(e % 80) [MOD 17] := pow_mod_eq 5 e 80 17 hp5_17
  have h5_17_add : (5^e + 2) % 17 = (5^(e % 80) + 2) % 17 := by
    rw [Nat.add_mod, h5_17, ← Nat.add_mod]
  have h_eq_17_simp : 3^(d % 240) ≡ 5^(e % 80) + 2 [MOD 17] :=
    h3_17.symm.trans (h_eq_17.trans h5_17_add)
  rw [h_d240, h_e80] at h_eq_17_simp
  have hd_cases : d240 = 3 ∨ d240 = 23 ∨ d240 = 43 ∨ d240 = 63 ∨ d240 = 83 ∨ d240 = 103 ∨ d240 = 123 ∨ d240 = 143 ∨ d240 = 163 ∨ d240 = 183 ∨ d240 = 203 ∨ d240 = 223 := by
    omega
  have he_cases : e80 = 7 ∨ e80 = 17 ∨ e80 = 27 ∨ e80 = 37 ∨ e80 = 47 ∨ e80 = 57 ∨ e80 = 67 ∨ e80 = 77 := by
    omega
  rcases hd_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  rcases he_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  { revert h_eq_13_simp h_eq_17_simp; decide }


lemma helper_d_mod_6 (d : ℕ) (hd_odd : d % 2 = 1) (hq13 : ∃ Y, Y^2 % 13 = (3^d + 11) % 13) : d % 6 = 1 ∨ d % 6 = 3 := by
  have hd_cases : d % 6 = 1 ∨ d % 6 = 3 ∨ d % 6 = 5 := by omega
  rcases hd_cases with h1 | h3 | h5
  · left; exact h1
  · right; exact h3
  · exfalso
    rcases hq13 with ⟨Y, hY⟩
    have hp : 3^6 ≡ 1 [MOD 13] := by decide
    have h_eq : 3^d ≡ 3^(d % 6) [MOD 13] := pow_mod_eq 3 d 6 13 hp
    have h_trans : (3^d + 11) % 13 = (3^(d % 6) + 11) % 13 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h5] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 13 = y
    have h_Y_sq : Y^2 % 13 = (y * y) % 13 := by
      have h1 : Y^2 % 13 = (Y * Y) % 13 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 13 = (Y % 13 * (Y % 13)) % 13 := Nat.mul_mod Y Y 13
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 13 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }

lemma helper_d_mod_16 (d : ℕ) (hd_odd : d % 2 = 1) (hq17 : ∃ Y, Y^2 % 17 = (3^d + 15) % 17) :
    d % 16 = 1 ∨ d % 16 = 3 ∨ d % 16 = 7 ∨ d % 16 = 15 := by
  have hd_cases : d % 16 = 1 ∨ d % 16 = 3 ∨ d % 16 = 5 ∨ d % 16 = 7 ∨ d % 16 = 9 ∨ d % 16 = 11 ∨ d % 16 = 13 ∨ d % 16 = 15 := by omega
  rcases hd_cases with h1|h3|h5|h7|h9|h11|h13|h15
  · left; exact h1
  · right; left; exact h3
  · exfalso
    rcases hq17 with ⟨Y, hY⟩
    have hp : 3^16 ≡ 1 [MOD 17] := by decide
    have h_eq : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
    have h_trans : (3^d + 15) % 17 = (3^(d % 16) + 15) % 17 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h5] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 17 = y
    have h_Y_sq : Y^2 % 17 = (y * y) % 17 := by
      have h1 : Y^2 % 17 = (Y * Y) % 17 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 17 = (Y % 17 * (Y % 17)) % 17 := Nat.mul_mod Y Y 17
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 17 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · right; right; left; exact h7
  · exfalso
    rcases hq17 with ⟨Y, hY⟩
    have hp : 3^16 ≡ 1 [MOD 17] := by decide
    have h_eq : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
    have h_trans : (3^d + 15) % 17 = (3^(d % 16) + 15) % 17 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h9] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 17 = y
    have h_Y_sq : Y^2 % 17 = (y * y) % 17 := by
      have h1 : Y^2 % 17 = (Y * Y) % 17 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 17 = (Y % 17 * (Y % 17)) % 17 := Nat.mul_mod Y Y 17
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 17 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · exfalso
    rcases hq17 with ⟨Y, hY⟩
    have hp : 3^16 ≡ 1 [MOD 17] := by decide
    have h_eq : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
    have h_trans : (3^d + 15) % 17 = (3^(d % 16) + 15) % 17 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h11] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 17 = y
    have h_Y_sq : Y^2 % 17 = (y * y) % 17 := by
      have h1 : Y^2 % 17 = (Y * Y) % 17 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 17 = (Y % 17 * (Y % 17)) % 17 := Nat.mul_mod Y Y 17
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 17 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · exfalso
    rcases hq17 with ⟨Y, hY⟩
    have hp : 3^16 ≡ 1 [MOD 17] := by decide
    have h_eq : 3^d ≡ 3^(d % 16) [MOD 17] := pow_mod_eq 3 d 16 17 hp
    have h_trans : (3^d + 15) % 17 = (3^(d % 16) + 15) % 17 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h13] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 17 = y
    have h_Y_sq : Y^2 % 17 = (y * y) % 17 := by
      have h1 : Y^2 % 17 = (Y * Y) % 17 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 17 = (Y % 17 * (Y % 17)) % 17 := Nat.mul_mod Y Y 17
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 17 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · right; right; right; exact h15

lemma helper_d_mod_4 (d : ℕ) (hd_odd : d % 2 = 1) (hq5 : ∃ Y, Y % 5 ≠ 0 ∧ Y^2 % 5 = (3^d + 3) % 5) : d % 4 = 1 := by
  have hd_cases : d % 4 = 1 ∨ d % 4 = 3 := by omega
  rcases hd_cases with h1 | h3
  · exact h1
  · exfalso
    rcases hq5 with ⟨Y, hY_nz, hY⟩
    have hp : 3^4 ≡ 1 [MOD 5] := by decide
    have h_eq : 3^d ≡ 3^(d % 4) [MOD 5] := pow_mod_eq 3 d 4 5 hp
    have h_trans : (3^d + 3) % 5 = (3^(d % 4) + 3) % 5 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    rw [h3] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 5 = y
    have h_Y_sq : Y^2 % 5 = (y * y) % 5 := by
      have h1 : Y^2 % 5 = (Y * Y) % 5 := by rw [Nat.pow_two]
      have h2 : (Y * Y) % 5 = (Y % 5 * (Y % 5)) % 5 := Nat.mul_mod Y Y 5
      rw [h1, h2, h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 5 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_nz : y ≠ 0 := by
      rw [← h_Y_mod]
      exact hY_nz
    have hy_cases : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl <;>
    { revert hY; decide }


lemma helper_d_mod_5_of_11 (d : ℕ) (hd48 : d % 48 = 1) (hq11 : ∃ Y, Y^2 % 11 = (3^d + 9) % 11) :
    d % 5 = 1 ∨ d % 5 = 3 := by
  have hd_cases : d % 240 = 1 ∨ d % 240 = 49 ∨ d % 240 = 97 ∨ d % 240 = 145 ∨ d % 240 = 193 := by omega
  rcases hd_cases with h1|h49|h97|h145|h193
  · left; omega
  · exfalso
    rcases hq11 with ⟨Y, hY⟩
    have hp : 3^5 ≡ 1 [MOD 11] := by decide
    have h_eq : 3^d ≡ 3^(d % 5) [MOD 11] := pow_mod_eq 3 d 5 11 hp
    have h_trans : (3^d + 9) % 11 = (3^(d % 5) + 9) % 11 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    have hd5 : d % 5 = 4 := by omega
    rw [hd5] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 11 = y
    have h_Y_sq : Y^2 % 11 = (y * y) % 11 := by
      have h1' : Y^2 % 11 = (Y * Y) % 11 := by rw [Nat.pow_two]
      have h2' : (Y * Y) % 11 = (Y % 11 * (Y % 11)) % 11 := Nat.mul_mod Y Y 11
      rw [h1', h2', h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 11 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · exfalso
    rcases hq11 with ⟨Y, hY⟩
    have hp : 3^5 ≡ 1 [MOD 11] := by decide
    have h_eq : 3^d ≡ 3^(d % 5) [MOD 11] := pow_mod_eq 3 d 5 11 hp
    have h_trans : (3^d + 9) % 11 = (3^(d % 5) + 9) % 11 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    have hd5 : d % 5 = 2 := by omega
    rw [hd5] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 11 = y
    have h_Y_sq : Y^2 % 11 = (y * y) % 11 := by
      have h1' : Y^2 % 11 = (Y * Y) % 11 := by rw [Nat.pow_two]
      have h2' : (Y * Y) % 11 = (Y % 11 * (Y % 11)) % 11 := Nat.mul_mod Y Y 11
      rw [h1', h2', h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 11 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · exfalso
    rcases hq11 with ⟨Y, hY⟩
    have hp : 3^5 ≡ 1 [MOD 11] := by decide
    have h_eq : 3^d ≡ 3^(d % 5) [MOD 11] := pow_mod_eq 3 d 5 11 hp
    have h_trans : (3^d + 9) % 11 = (3^(d % 5) + 9) % 11 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    have hd5 : d % 5 = 0 := by omega
    rw [hd5] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 11 = y
    have h_Y_sq : Y^2 % 11 = (y * y) % 11 := by
      have h1' : Y^2 % 11 = (Y * Y) % 11 := by rw [Nat.pow_two]
      have h2' : (Y * Y) % 11 = (Y % 11 * (Y % 11)) % 11 := Nat.mul_mod Y Y 11
      rw [h1', h2', h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 11 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }
  · right; omega

lemma helper_d_mod_5_of_31 (d : ℕ) (hd48 : d % 48 = 1) (hq31 : ∃ Y, Y^2 % 31 = (3^d + 29) % 31) :
    d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 4 := by
  have hd_cases : d % 240 = 1 ∨ d % 240 = 49 ∨ d % 240 = 97 ∨ d % 240 = 145 ∨ d % 240 = 193 := by omega
  rcases hd_cases with h1|h49|h97|h145|h193
  · right; left; clear hq31; omega
  · right; right; right; clear hq31; omega
  · right; right; left; clear hq31; omega
  · left; clear hq31; omega
  · exfalso
    rcases hq31 with ⟨Y, hY⟩
    have hp : 3^30 ≡ 1 [MOD 31] := by decide
    have h_eq : 3^d ≡ 3^(d % 30) [MOD 31] := pow_mod_eq 3 d 30 31 hp
    have h_trans : (3^d + 29) % 31 = (3^(d % 30) + 29) % 31 := by
      rw [Nat.add_mod, h_eq, ← Nat.add_mod]
    have hd30 : d % 30 = 13 := by omega
    rw [hd30] at h_trans
    rw [h_trans] at hY
    generalize h_Y_mod : Y % 31 = y
    have h_Y_sq : Y^2 % 31 = (y * y) % 31 := by
      have h1' : Y^2 % 31 = (Y * Y) % 31 := by rw [Nat.pow_two]
      have h2' : (Y * Y) % 31 = (Y % 31 * (Y % 31)) % 31 := Nat.mul_mod Y Y 31
      rw [h1', h2', h_Y_mod]
    rw [h_Y_sq] at hY
    have hy_lt : y < 31 := by
      rw [← h_Y_mod]
      exact Nat.mod_lt _ (by decide)
    have hy_cases : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 ∨ y = 14 ∨ y = 15 ∨ y = 16 ∨ y = 17 ∨ y = 18 ∨ y = 19 ∨ y = 20 ∨ y = 21 ∨ y = 22 ∨ y = 23 ∨ y = 24 ∨ y = 25 ∨ y = 26 ∨ y = 27 ∨ y = 28 ∨ y = 29 ∨ y = 30 := by omega
    rcases hy_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    { revert hY; decide }




lemma sq_sub_eq_of_le {z : ℕ} (hz : z ≤ 7297) : (7297 - z)^2 + 2 * 7297 * z = z^2 + 7297^2 := by
  zify [hz]
  ring

def check_sq (y : ℕ) : Bool :=
  (y^2 + 2) % 7297 == 7294

def check_all : ℕ → Bool
  | 0 => check_sq 0
  | n + 1 => check_sq (n + 1) || check_all n

lemma check_all_false : check_all 3648 = false := by decide

lemma check_all_false_of_le {n z : ℕ} (h_all : check_all n = false) (hz : z ≤ n) : check_sq z = false := by
  induction n generalizing z with
  | zero =>
    have : z = 0 := by omega
    subst this
    exact h_all
  | succ n ih =>
    have h_succ : check_all (n + 1) = (check_sq (n + 1) || check_all n) := rfl
    have h_or : check_sq (n + 1) = false ∧ check_all n = false := by
      have h1 : check_all (n + 1) = false := h_all
      rw [h_succ] at h1
      exact Bool.or_eq_false_iff.mp h1
    have h_lt : z ≤ n ∨ z = n + 1 := by omega
    rcases h_lt with h1 | h2
    · exact ih h_or.2 h1
    · subst h2
      exact h_or.1

lemma sq_add_two_neq_7294_mod_7297 (y : ℕ) : (y^2 + 2) % 7297 ≠ 7294 := by
  intro h_eq
  have hy : y % 7297 < 7297 := Nat.mod_lt _ (by decide)
  have h_eq_mod : ((y % 7297)^2 + 2) % 7297 = (y^2 + 2) % 7297 := by
    have h1_mod : (y^2) % 7297 = ((y % 7297)^2) % 7297 := Nat.pow_mod y 2 7297
    have h2_mod : (y^2 + 2) % 7297 = ((y^2) % 7297 + 2) % 7297 := Nat.add_mod (y^2) 2 7297
    have h3_mod : ((y % 7297)^2 + 2) % 7297 = (((y % 7297)^2) % 7297 + 2) % 7297 := Nat.add_mod ((y % 7297)^2) 2 7297
    rw [h2_mod, h3_mod, h1_mod]
  have h_eq2 : ((y % 7297)^2 + 2) % 7297 = 7294 := by rw [h_eq_mod, h_eq]
  generalize h_z : y % 7297 = z
  rw [h_z] at hy h_eq2
  have hz_half : z ≤ 3648 ∨ z ≥ 3649 := by omega
  rcases hz_half with hz1 | hz2
  · have h_all : check_sq z = false := check_all_false_of_le check_all_false hz1
    have h_sq_eq : (z^2 + 2) % 7297 = 7294 := h_eq2
    revert h_all
    unfold check_sq
    rw [h_sq_eq]
    decide
  · have h_symm : (7297 - z) ≤ 3648 := by omega
    have h_all : check_sq (7297 - z) = false := check_all_false_of_le check_all_false h_symm
    have h_sq_eq : ((7297 - z)^2 + 2) % 7297 = (z^2 + 2) % 7297 := by
      have h_eq : (7297 - z)^2 + 2 * 7297 * z = z^2 + 7297^2 := sq_sub_eq_of_le (by omega)
      have h_mod : ((7297 - z)^2 + 2 * 7297 * z) % 7297 = (z^2 + 7297^2) % 7297 := by rw [h_eq]
      have h_lhs : ((7297 - z)^2 + 2 * 7297 * z) % 7297 = (7297 - z)^2 % 7297 := by
        have : (7297 - z)^2 + 2 * 7297 * z = (7297 - z)^2 + 7297 * (2 * z) := by ring
        rw [this, Nat.add_mul_mod_self_left]
      have h_rhs : (z^2 + 7297^2) % 7297 = z^2 % 7297 := by
        have : z^2 + 7297^2 = z^2 + 7297 * 7297 := by ring
        rw [this, Nat.add_mul_mod_self_left]
      have h_eq_sub : (7297 - z)^2 % 7297 = z^2 % 7297 := by
        rw [← h_lhs, h_mod, h_rhs]
      have h_mod2 : ((7297 - z)^2 + 2) % 7297 = (((7297 - z)^2) % 7297 + 2) % 7297 := Nat.add_mod ((7297 - z)^2) 2 7297
      have h_mod3 : (z^2 + 2) % 7297 = ((z^2) % 7297 + 2) % 7297 := Nat.add_mod (z^2) 2 7297
      rw [h_mod2, h_mod3, h_eq_sub]
    revert h_all
    unfold check_sq
    rw [h_sq_eq, h_eq2]
    decide

lemma sq_add_two_neq_94_mod_97 (y : ℕ) : (y^2 + 2) % 97 ≠ 94 := by
  have h : ∀ y < 97, (y^2 + 2) % 97 ≠ 94 := by decide
  intro h_eq
  have hy : y % 97 < 97 := Nat.mod_lt _ (by decide)
  have h_eq_mod : ((y % 97)^2 + 2) % 97 = (y^2 + 2) % 97 := by
    have h1 : (y^2) % 97 = ((y % 97)^2) % 97 := Nat.pow_mod y 2 97
    have h2 : (y^2 + 2) % 97 = ((y^2) % 97 + 2) % 97 := Nat.add_mod (y^2) 2 97
    have h3 : ((y % 97)^2 + 2) % 97 = (((y % 97)^2) % 97 + 2) % 97 := Nat.add_mod ((y % 97)^2) 2 97
    rw [h2, h3, h1]
  have h_eq2 : ((y % 97)^2 + 2) % 97 = 94 := by rw [h_eq_mod, h_eq]
  exact h (y % 97) hy h_eq2

lemma no_solution_5_pow_eq_3_pow_even (d e' : ℕ) (hd : d ≥ 1) (h_eq : 5^d = 3^(2*e') + 2) : False := by
  have h_mod5 : (3^(2*e') + 2) % 5 = 0 := by
    calc (3^(2*e') + 2) % 5 = (5^d) % 5 := by rw [h_eq]
    _ = 0 := by
      have : d = (d - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_add]
      exact Nat.mul_mod_left (5^(d-1)) 5
  have h_pow3 : 3^(2*e') % 5 = 3 := by omega
  have h_sq : 3^(2*e') = (3^e')^2 := by ring
  rw [h_sq] at h_pow3
  generalize h_y : 3^e' = y
  rw [h_y] at h_pow3
  have hy_mod : (y^2) % 5 = 3 := h_pow3
  have hy5 : y % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize h_mod_val : y % 5 = r
  rw [h_mod_val] at hy5
  have h_sq_mod : y^2 % 5 = (r * r) % 5 := by
    have : y^2 = y * y := by ring
    rw [this, Nat.mul_mod, ← h_mod_val, ← Nat.mul_mod, ← pow_two]
  rw [h_sq_mod] at hy_mod
  interval_cases r <;> { revert hy_mod; decide }

lemma no_solution_11_pow_eq_3_pow_even (d e' : ℕ) (hd : d ≥ 2) (h_eq : 11^d = 3^(2*e') + 2) : False := by
  have h_mod121 : (3^(2*e') + 2) % 121 = 0 := by
    calc (3^(2*e') + 2) % 121 = (11^d) % 121 := by rw [h_eq]
    _ = 0 := by
      have : d = (d - 2) + 2 := by omega
      nth_rw 1 [this]
      rw [pow_add]
      exact Nat.mul_mod_left (11^(d-2)) 121
  have h_pow3 : 3^(2*e') % 121 = 119 := by omega
  have hp : 3^5 ≡ 1 [MOD 121] := by decide
  have h_eq_mod : 3^(2*e') ≡ 3^((2*e') % 5) [MOD 121] := pow_mod_eq 3 (2*e') 5 121 hp
  have h_trans : 3^((2*e') % 5) ≡ 119 [MOD 121] := h_eq_mod.symm.trans h_pow3
  have h_lt : (2*e') % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize h_r : (2*e') % 5 = r
  rw [h_r] at h_trans h_lt
  interval_cases r <;> { revert h_trans; decide }

lemma hpq3_proof (p q d e : ℕ) (hp : p.Prime) (hq : q.Prime) (hd : d ≥ 2) (he : e ≥ 2) (hd_odd : d % 2 = 1) (he_odd : e % 2 = 1) (h_diff : q^d = p^e + 2) :
    (p = 3 ∨ q = 3) ∨ (p % 3 = 2 ∧ q % 3 = 1) := by
  have hq_ge_3 : q ≥ 3 := by
    have hq2 := hq.two_le
    have hq_neq2 : q ≠ 2 := by
      intro hq2_eq
      subst hq2_eq
      by_cases hp2 : p = 2
      · subst hp2
        have h_pow_d : 2^d % 4 = 0 := by
          have : d = (d - 2) + 2 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          exact Nat.mul_mod_left (2 ^ (d - 2)) 4
        have h_pow_e : 2^e % 4 = 0 := by
          have : e = (e - 2) + 2 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          exact Nat.mul_mod_left (2 ^ (e - 2)) 4
        have h_diff_mod : 2^d % 4 = (2^e + 2) % 4 := by rw [h_diff]
        rw [h_pow_d, Nat.add_mod, h_pow_e] at h_diff_mod
        revert h_diff_mod
        decide
      · have hp_odd : p % 2 = 1 := by
          have hp2_le := hp.two_le
          have h_cases : p % 2 = 0 ∨ p % 2 = 1 := by omega
          rcases h_cases with h0 | h1
          · exfalso
            have h_dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
            have hp_eq2 := hp.eq_one_or_self_of_dvd 2 h_dvd
            omega
          · exact h1
        have hpe_odd : p^e % 2 = 1 := by
          rw [Nat.pow_mod]
          rw [hp_odd]
          show 1^e % 2 = 1
          rw [one_pow]
          decide
        have h_even : 2^d % 2 = 0 := by
          have : d = (d - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          exact Nat.mul_mod_left (2 ^ (d - 1)) 2
        have h_diff_mod : 2^d % 2 = (p^e + 2) % 2 := by rw [h_diff]
        rw [h_even, Nat.add_mod, hpe_odd] at h_diff_mod
        revert h_diff_mod
        decide
    omega
  have hp3_proof : (p = 3 ∨ q = 3) ∨ (p % 3 = 2 ∧ q % 3 = 1) := by
    by_cases hp3 : p = 3
    · left; left; exact hp3
    · by_cases hq3 : q = 3
      · left; right; exact hq3
      · right
        have hp_mod3 : p % 3 = 1 ∨ p % 3 = 2 := by
          have hp2 := hp.two_le
          have h_cases : p % 3 = 0 ∨ (p % 3 = 1 ∨ p % 3 = 2) := by omega
          rcases h_cases with h0 | h12
          · exfalso
            have h_dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
            have hp_eq3 := hp.eq_one_or_self_of_dvd 3 h_dvd
            omega
          · exact h12
        have hq_mod3 : q % 3 = 1 ∨ q % 3 = 2 := by
          have hq2 := hq.two_le
          have h_cases : q % 3 = 0 ∨ (q % 3 = 1 ∨ q % 3 = 2) := by omega
          rcases h_cases with h0 | h12
          · exfalso
            have h_dvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
            have hq_eq3 := hq.eq_one_or_self_of_dvd 3 h_dvd
            omega
          · exact h12
        rcases hp_mod3 with hp1 | hp2
        · have hp_pow : p^e % 3 = 1 := by
            have hp1_equiv : p ≡ 1 [MOD 3] := hp1
            have hp_equiv : p^e ≡ 1^e [MOD 3] := hp1_equiv.pow e
            rw [one_pow] at hp_equiv
            exact hp_equiv
          have hq_dvd3 : 3 ∣ q^d := by
            have h_mod3 : (q^d) % 3 = 0 := by
              have h_mod : (q^d) % 3 = (p^e + 2) % 3 := by rw [h_diff]
              rw [h_mod, Nat.add_mod, hp_pow]
            exact Nat.dvd_of_mod_eq_zero h_mod3
          have hq3_eq : q = 3 := by
            have h_prime_dvd := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hq_dvd3
            have h_cases := hq.eq_one_or_self_of_dvd 3 h_prime_dvd
            omega
          exfalso; exact hq3 hq3_eq
        · rcases hq_mod3 with hq1 | hq2
          · exact ⟨hp2, hq1⟩
          · have hq_pow : q^d % 3 = 2 := by
              have h_eq : d = 2 * (d / 2) + 1 := by omega
              have hq2_equiv : q ≡ 2 [MOD 3] := hq2
              have hqd_equiv : q^d ≡ 2^d [MOD 3] := hq2_equiv.pow d
              have h_pow2 : 2^d = 2^(2 * (d/2)) * 2 := by
                nth_rw 1 [h_eq]
                ring
              have h_pow3 : 2^(2 * (d/2)) = 4^(d/2) := by
                have h_eq2 : (2^2)^(d/2) = 4^(d/2) := by rfl
                rw [← h_eq2, pow_mul]
              have h_pow4 : 4^(d/2) ≡ 1^(d/2) [MOD 3] := by
                have : 4 ≡ 1 [MOD 3] := by decide
                exact this.pow (d/2)
              rw [one_pow] at h_pow4
              have h_pow5 : 2^(2 * (d/2)) * 2 ≡ 1 * 2 [MOD 3] := by
                rw [h_pow3]
                exact h_pow4.mul (by rfl)
              rw [one_mul] at h_pow5
              have hqd_equiv2 : q^d ≡ 2 [MOD 3] := hqd_equiv.trans (by
                rw [h_pow2]
                exact h_pow5)
              exact hqd_equiv2
            have hp_dvd3 : 3 ∣ p^e := by
              have h_mod3 : (p^e) % 3 = 0 := by
                have h_eq : p^e = q^d - 2 := by omega
                rw [h_eq]
                have h_qd_ge2 : q^d ≥ 2 := by
                  have : q^d ≥ q^1 := Nat.pow_le_pow_right hq.pos (by omega)
                  rw [pow_one] at this
                  omega
                omega
              exact Nat.dvd_of_mod_eq_zero h_mod3
            have hp3_eq : p = 3 := by
              have h_prime_dvd := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hp_dvd3
              have h_cases := hp.eq_one_or_self_of_dvd 3 h_prime_dvd
              omega
            exfalso; exact hp3 hp3_eq
  exact hp3_proof

lemma coprime3_pow18 (q : ℕ) (hq3 : q % 3 ≠ 0) : q^18 ≡ 1 [MOD 27] := by
  have h_eq : q^18 % 27 = (q % 27)^18 % 27 := Nat.pow_mod q 18 27
  have hq27 : q % 27 < 27 := Nat.mod_lt _ (by decide)
  have h_coprime : (q % 27) % 3 ≠ 0 := by
    have : q % 3 = (q % 27) % 3 := by omega
    omega
  change q^18 % 27 = 1 % 27
  rw [h_eq]
  generalize q % 27 = r at hq27 h_coprime ⊢
  interval_cases r <;> { revert h_coprime; decide }

lemma q_mod27_cases (q d : ℕ) (hq3 : q % 3 ≠ 0) (hd_odd : d % 2 = 1) (h_mod : q^d % 27 = 2) :
    q % 27 = 2 ∨ q % 27 = 5 ∨ q % 27 = 11 ∨ q % 27 = 14 ∨ q % 27 = 20 ∨ q % 27 = 23 := by
  have hp : q^18 ≡ 1 [MOD 27] := coprime3_pow18 q hq3
  have h_eq : q^d ≡ q^(d % 18) [MOD 27] := pow_mod_eq q d 18 27 hp
  have h_trans : q^(d % 18) ≡ 2 [MOD 27] := h_eq.symm.trans h_mod
  have hd_lt : d % 18 < 18 := Nat.mod_lt _ (by decide)
  have hd_odd_mod : (d % 18) % 2 = 1 := by
    have : d = 18 * (d / 18) + d % 18 := (Nat.div_add_mod d 18).symm
    omega
  have hq_lt : q % 27 < 27 := Nat.mod_lt _ (by decide)
  have h_pow_mod : q^(d % 18) % 27 = (q % 27)^(d % 18) % 27 := Nat.pow_mod q (d % 18) 27
  change q^(d % 18) % 27 = 2 at h_trans
  rw [h_pow_mod] at h_trans
  generalize h_r : d % 18 = r
  generalize h_y : q % 27 = y
  rw [h_r] at hd_lt hd_odd_mod h_trans
  rw [h_y] at hq_lt h_trans
  have h_trans_val : y^r % 27 = 2 := h_trans
  interval_cases r <;> { interval_cases y <;> { revert hd_odd_mod h_trans_val; decide } }






theorem oeis_365416_conjecture_0_gt13 (k : ℕ) (hk : k > 13)
    (h : IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) : False := by
  obtain ⟨p, e, hp, he, hpe⟩ := h.1
  obtain ⟨q, d, hq, hd, hqd⟩ := h.2
  have h_diff : q^d = p^e + 2 := by omega
  have hp_neq_2 : p ≠ 2 := test_p_odd k p e hk hp he hpe
  have hq_neq_2 : q ≠ 2 := test_q_odd k q d hk hq hd hqd
  have hp_ge_3 : p ≥ 3 := by
    have hp2 := hp.two_le
    omega
  have hq_ge_3 : q ≥ 3 := by
    have hq2 := hq.two_le
    omega
  by_cases he_even : ∃ e', e = 2 * e'
  · rcases he_even with ⟨e', rfl⟩
    have he'_ge1 : e' ≥ 1 := by omega
    by_cases hd_even : ∃ d', d = 2 * d'
    · rcases hd_even with ⟨d', rfl⟩
      have hd'_ge1 : d' ≥ 1 := by omega
      have h_sq_diff : (q^d')^2 = (p^e')^2 + 2 := by
        calc (q^d')^2 = q^(2*d') := by ring
        _ = p^(2*e') + 2 := h_diff
        _ = (p^e')^2 + 2 := by ring
      exact h_no_sq_diff (q^d') (p^e') h_sq_diff
    · -- e even, d odd: q^d = p^(2*e') + 2
      by_cases hp3 : p = 3
      · subst hp3
        by_cases he'1 : e' = 1
        · subst he'1
          have h_qd : q^d = 11 := by
            calc q^d = 3^(2 * 1) + 2 := h_diff
            _ = 11 := by decide
          have hd3 : d ≥ 3 := by omega
          have hq5 : q ≥ 3 := hq_ge_3
          have hq_d_ge : q^d ≥ 27 := by
            calc q^d ≥ 3^d := Nat.pow_le_pow_left hq5 d
            _ ≥ 3^3 := Nat.pow_le_pow_right (by decide) hd3
            _ = 27 := by decide
          omega
        · have he'_ge2 : e' ≥ 2 := by omega
          by_cases he'2 : e' = 2
          · subst he'2
            have h_qd : q^d = 83 := by
              calc q^d = 3^(2 * 2) + 2 := h_diff
              _ = 83 := by decide
            have h_prime : Nat.Prime 83 := by norm_num
            have hq83 : q = 83 := by
              have h_dvd : q ∣ q^d := dvd_pow_self q (by omega)
              rw [h_qd] at h_dvd
              have h_eq := h_prime.eq_one_or_self_of_dvd q h_dvd
              rcases h_eq with hq1 | hq83
              · exact False.elim (hq.ne_one hq1)
              · exact hq83
            subst hq83
            have hd1 : d = 1 := by
              by_contra! hd_gt1
              have hd_ge2 : d ≥ 2 := by omega
              have h_pow_ge : 83^d ≥ 83^2 := Nat.pow_le_pow_right (by decide) hd_ge2
              rw [h_qd] at h_pow_ge
              norm_num at h_pow_ge
            omega
          · have he'_ge3 : e' ≥ 3 := by omega
            by_cases he'3 : e' = 3
            · subst he'3
              have h_qd : q^d = 731 := by
                calc q^d = 3^(2 * 3) + 2 := h_diff
                _ = 731 := by decide
              have h_not_prime_pow : ¬ IsPrimePow 731 := by
                apply not_isPrimePow_of_two_prime_divisors (p1 := 17) (p2 := 43) (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
              have h_prime_pow : IsPrimePow (q^d) := by
                rw [isPrimePow_nat_iff]
                exact ⟨q, d, hq, by omega, rfl⟩
              rw [h_qd] at h_prime_pow
              contradiction
            · have he'_ge4 : e' ≥ 4 := by omega
              by_cases he'4 : e' = 4
              · subst he'4
                have h_qd : q^d = 6563 := by
                  calc q^d = 3^(2 * 4) + 2 := h_diff
                  _ = 6563 := by decide
                have h_prime : Nat.Prime 6563 := by norm_num
                have hq6563 : q = 6563 := by
                  have h_dvd : q ∣ q^d := dvd_pow_self q (by omega)
                  rw [h_qd] at h_dvd
                  have h_eq := h_prime.eq_one_or_self_of_dvd q h_dvd
                  rcases h_eq with hq1 | hq6563
                  · exact False.elim (hq.ne_one hq1)
                  · exact hq6563
                subst hq6563
                have hd1 : d = 1 := by
                  by_contra! hd_gt1
                  have hd_ge2 : d ≥ 2 := by omega
                  have h_pow_ge : 6563^d ≥ 6563^2 := Nat.pow_le_pow_right (by decide) hd_ge2
                  rw [h_qd] at h_pow_ge
                  norm_num at h_pow_ge
                omega
              · have he'_ge5 : e' ≥ 5 := by omega
                sorry
      · -- p != 3.
        -- Modulo 3: since p is prime and p != 2, 3, we have p^2 ≡ 1 [MOD 3].
        -- So p^(2*e') ≡ 1 [MOD 3].
        -- So q^d = p^(2*e') + 2 ≡ 3 ≡ 0 [MOD 3].
        -- Since q is prime, this implies q = 3.
        -- So we have 3^d = p^(2*e') + 2.
        have hp_mod3 : p % 3 = 1 ∨ p % 3 = 2 := by
          have hp2 : p ≥ 2 := hp.two_le
          have h_cases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
          rcases h_cases with h0 | h1 | h2
          · exfalso
            have h_dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
            have hp_eq3 := hp.eq_one_or_self_of_dvd 3 h_dvd
            omega
          · left; exact h1
          · right; exact h2
        have hp2_mod3 : p^2 % 3 = 1 := by
          rcases hp_mod3 with h1 | h2
          · rw [Nat.pow_two, Nat.mul_mod, h1]
          · rw [Nat.pow_two, Nat.mul_mod, h2]
        have hpe_mod3 : p^(2 * e') % 3 = 1 := by
          have h_pow : p^(2 * e') = (p^2)^e' := by ring
          rw [h_pow]
          have h_equiv : (p^2)^e' ≡ 1^e' [MOD 3] := by
            have hp2_mod3_equiv : p^2 ≡ 1 [MOD 3] := hp2_mod3
            exact hp2_mod3_equiv.pow _
          rw [one_pow] at h_equiv
          exact h_equiv
        have h_q_dvd3 : 3 ∣ q^d := by
          have h_mod3 : (q^d) % 3 = 0 := by
            calc (q^d) % 3 = (p^(2 * e') + 2) % 3 := by rw [h_diff]
            _ = (p^(2 * e') % 3 + 2 % 3) % 3 := by rw [Nat.add_mod]
            _ = (1 + 2) % 3 := by rw [hpe_mod3]
            _ = 0 := by decide
          exact Nat.dvd_of_mod_eq_zero h_mod3
        have h_q3 : q = 3 := by
          have h_prime_dvd := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h_q_dvd3
          have h_cases := hq.eq_one_or_self_of_dvd 3 h_prime_dvd
          omega
        subst h_q3
        -- So 3^d = p^(2*e') + 2.
        by_cases hp5 : p = 5
        · subst hp5
          -- 3^d = 5^(2*e') + 2.
          -- Since k > 13, 5^(2*e') = 2*k - 1 > 25 => 2*e' > 2 => e' >= 2.
          -- So 5^(2*e') is a multiple of 125, so 3^d ≡ 2 [MOD 125].
          have he'_ge2 : e' ≥ 2 := by
            by_contra! he'_lt2
            have he'_eq1 : e' = 1 := by omega
            subst he'_eq1
            norm_num at hpe
            omega
          have h_5_pow_125 : 5^(2*e') % 125 = 0 := by
            have h_pow : 5^(2*e') = 5^3 * 5^(2*e' - 3) := by
              have : 2*e' ≥ 3 := by omega
              nth_rw 1 [show 2*e' = 3 + (2*e' - 3) by omega]
              rw [pow_add]
            rw [h_pow]
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 125 (5 ^ (2 * e' - 3)))
          have hd_mod125 : 3^d ≡ 2 [MOD 125] := by
            have h_eq_mod : (5^(2*e') + 2) % 125 = 2 := by
              rw [Nat.add_mod, h_5_pow_125]
            have h_eq_val : 3^d = 5^(2*e') + 2 := h_diff
            rw [h_eq_val]
            exact h_eq_mod
          exact no_solution_5_pow_eq_3_pow d e' h_diff.symm hd_mod125
        · -- p != 5 (and p != 3).
          -- So we have 3^d = p^(2*e') + 2.
          -- Since d >= 2 and d is odd, d is odd.
          -- Also, p != 5 => p % 5 != 0 => p^(2*e') % 5 != 0.
          -- This is solved by:
          have hp5_nz : p^e' % 5 ≠ 0 := by
            intro h_div
            have h_dvd : 5 ∣ p^e' := Nat.dvd_of_mod_eq_zero h_div
            have h_prime_dvd := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h_dvd
            have : p = 5 := by
              have h_cases := hp.eq_one_or_self_of_dvd 5 h_prime_dvd
              omega
            contradiction
          have hd_odd : d % 2 = 1 := by
            have h_cases := Nat.mod_two_eq_zero_or_one d
            rcases h_cases with h0 | h1
            · exfalso
              apply hd_even
              use d / 2
              omega
            · exact h1
          have h_eq_val : 3^d = (p^e')^2 + 2 := by
            calc 3^d = p^(2*e') + 2 := h_diff
            _ = (p^e')^2 + 2 := by ring
          have hpe'_ge3 : p^e' ≥ 3 := by
            calc p^e' ≥ p^1 := Nat.pow_le_pow_right hp.pos he'_ge1
            _ = p := by rw [pow_one]
            _ ≥ 3 := hp_ge_3
          have hd48_1 : d % 48 = 1 := no_solution_3_pow_eq_sq_add_two d (p^e') h_eq_val hp5_nz hpe'_ge3 hd_odd
          have h_sub : (p^e')^2 = 3^d - 2 := by omega
          have h_sub_mod : (p^e')^2 % 11 = (3^d - 2) % 11 := by rw [h_sub]
          have h_eq_mod : (3^d - 2) % 11 = (3^d + 9) % 11 := by
            have h_pow : 3^d ≥ 3^1 := Nat.pow_le_pow_right (by decide : 3 > 0) (by omega)
            rw [pow_one] at h_pow
            have h_eq_add : 3^d - 2 + 11 = 3^d + 9 := by omega
            have h_mod : (3^d - 2 + 11) % 11 = (3^d - 2) % 11 := Nat.add_mod_right (3^d - 2) 11
            rw [← h_mod, h_eq_add]
          have hq11 : ∃ Y, Y^2 % 11 = (3^d + 9) % 11 := by
            use p^e'
            rw [h_sub_mod, h_eq_mod]

          have h_sub31 : (p^e')^2 = 3^d - 2 := by omega
          have h_sub_mod31 : (p^e')^2 % 31 = (3^d - 2) % 31 := by rw [h_sub31]
          have h_eq_mod31 : (3^d - 2) % 31 = (3^d + 29) % 31 := by
            have h_pow : 3^d ≥ 3^1 := Nat.pow_le_pow_right (by decide : 3 > 0) (by omega)
            rw [pow_one] at h_pow
            have h_eq_add : 3^d - 2 + 31 = 3^d + 29 := by omega
            have h_mod : (3^d - 2 + 31) % 31 = (3^d - 2) % 31 := Nat.add_mod_right (3^d - 2) 31
            rw [← h_mod, h_eq_add]
          have hq31 : ∃ Y, Y^2 % 31 = (3^d + 29) % 31 := by
            use p^e'
            rw [h_sub_mod31, h_eq_mod31]

          have hd5_11 : d % 5 = 1 ∨ d % 5 = 3 := helper_d_mod_5_of_11 d hd48_1 hq11
          have hd5_31 : d % 5 = 0 ∨ d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 4 := helper_d_mod_5_of_31 d hd48_1 hq31
          have hd5_1 : d % 5 = 1 := by omega
          have hd240_1 : d % 240 = 1 := by
            have h48 : d % 48 = d % 240 % 48 := (Nat.mod_mod_of_dvd d (by decide : 48 ∣ 240)).symm
            have h5 : d % 5 = d % 240 % 5 := (Nat.mod_mod_of_dvd d (by decide : 5 ∣ 240)).symm
            rw [h48] at hd48_1
            rw [h5] at hd5_1
            have h_lt : d % 240 < 240 := Nat.mod_lt _ (by decide)
            generalize h_r : d % 240 = r
            rw [h_r] at hd48_1 hd5_1 h_lt
            have : r = 1 := by omega
            exact this

          have hp : 3^192 ≡ 1 [MOD 7297] := by decide
          have h_eq7297 : 3^d ≡ 3^(d % 192) [MOD 7297] := pow_mod_eq 3 d 192 7297 hp
          
          have hd192_cases : d % 192 = 1 ∨ d % 192 = 49 ∨ d % 192 = 97 ∨ d % 192 = 145 := by
            have h_mod : d % 48 = d % 192 % 48 := (Nat.mod_mod_of_dvd d (by decide : 48 ∣ 192)).symm
            rw [h_mod] at hd48_1
            have h_lt : d % 192 < 192 := Nat.mod_lt _ (by decide)
            generalize h_r : d % 192 = r
            rw [h_r] at hd48_1 h_lt
            have : r = 1 ∨ r = 49 ∨ r = 97 ∨ r = 145 := by omega
            exact this
          rcases hd192_cases with h1 | h49 | h97 | h145
          · sorry
          · sorry
          · have h_mod_val : 3^(d % 192) % 7297 = 7294 := by
              rw [h97]
              decide
            have h_eq_mod7297 : 3^d % 7297 = 7294 := by
              rw [h_eq7297]
              exact h_mod_val
            have h_contradiction : ((p^e')^2 + 2) % 7297 = 7294 := by
              rw [← h_eq_val]
              exact h_eq_mod7297
            exact sq_add_two_neq_7294_mod_7297 (p^e') h_contradiction
          · sorry
  · have he_odd : ∃ e', e = 2 * e' + 1 := odd_of_not_even he_even
    by_cases hd_even : ∃ d', d = 2 * d'
    · rcases hd_even with ⟨d', rfl⟩
      have hd'_ge1 : d' ≥ 1 := by omega
      by_cases hp3 : p = 3
      · subst hp3
        have he_ge2 : e ≥ 2 := he
        exact no_solution_p_three_d_even q (2 * d') e ⟨d', rfl, hd'_ge1⟩ he_ge2 h_diff
      · -- p != 3.
        sorry
    · -- e is odd, d is odd
      sorry

end A365416

open A365416

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro h
    by_cases hk : k = 13
    · exact hk
    · exfalso
      rcases lt_or_ge k 13 with h_lt | h_ge
      · exact oeis_365416_conjecture_0_le12 k h_lt h
      · have hk_gt : k > 13 := by omega
        exact oeis_365416_conjecture_0_gt13 k hk_gt h
  · rintro rfl
    constructor
    · use 5, 2
      refine ⟨by norm_num, by norm_num, by norm_num⟩
    · use 3, 3
      refine ⟨by norm_num, by norm_num, by norm_num⟩
