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
open Finset

set_option linter.style.namespace false in
/--
Conjecture: For $n \ge 1$, $(30n-1)$ divides $\frac{(30n)! n!}{(15n)! (10n)! (6n)!}$.
-/
@[category research open, AMS 11]
theorem oeis_a211417_conjecture (n : ℕ) :
    (30 * n - 1 : ℤ) ∣ ((30 * n).factorial * n.factorial : ℤ) / ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial : ℤ) := by
  
    have lt_two_pow (x : ℕ) : x < 2 ^ (x + 1) := by
    induction x with
    | zero => decide
    | succ x ih =>
      rw [pow_succ]
      omega

    have lt_two_pow_self (x : ℕ) : x < 2 ^ x := by
    induction x with
    | zero => decide
    | succ x ih =>
      rw [pow_succ]
      omega

    have log_lt_self_add_one {p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) : Nat.log p x < x + 1 := by
    apply Nat.log_lt_of_lt_pow hx
    have h2 : x < 2 ^ (x + 1) := lt_two_pow x
    have hp_le : 2 ^ (x + 1) ≤ p ^ (x + 1) := Nat.pow_le_pow_left hp.two_le (x + 1)
    omega

    have coprime_of_ident {m d r : ℕ} (h : 30 * r = d * m + 1) : Nat.Coprime m 30 := by
    have h1 : Nat.gcd m 30 ∣ d * m := dvd_mul_of_dvd_right (Nat.gcd_dvd_left m 30) d
    have h2 : Nat.gcd m 30 ∣ 30 * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_right m 30) r
    rw [h] at h2
    show Nat.gcd m 30 = 1
    generalize d * m = X at h1 h2
    generalize Nat.gcd m 30 = g at h1 h2 ⊢
    have h_g1 : g ∣ 1 := by
      rcases h1 with ⟨k1, hk1⟩
      rcases h2 with ⟨k2, hk2⟩
      use k2 - k1
      rw [Nat.mul_sub_left_distrib, ← hk2, ← hk1]
      omega
    exact Nat.eq_one_of_dvd_one h_g1

    have k_ineq_coprime (m : ℕ) (hm : m < 30) (h_cop : Nat.Coprime m 30) : m / 2 + m / 3 + m / 5 + 1 ≤ m := by
    interval_cases m <;> revert h_cop <;> decide

    have r_ident {n d c q r x : ℕ} (_hd : 0 < d) (hd2 : 2 ≤ d) (hn : 30 * n = d * c + 1)
      (hq : x = d * q + r) (_hr : r < d) (h_n_eq : x = n) : 30 * r = d * (c - 30 * q) + 1 := by
    have h_ident : d * (30 * q) + 30 * r = d * c + 1 := by
      calc d * (30 * q) + 30 * r = 30 * (d * q + r) := by ring
      _ = 30 * x := by rw [← hq]
      _ = 30 * n := by rw [h_n_eq]
      _ = d * c + 1 := hn
    have h_m : c ≥ 30 * q := by
      by_contra hc
      have hc_lt : c < 30 * q := by omega
      have h_le : d * c + d ≤ d * (30 * q) := by
        calc d * c + d = d * (c + 1) := by ring
        _ ≤ d * (30 * q) := Nat.mul_le_mul_left d hc_lt
      omega
    have : d * c = d * (30 * q) + d * (c - 30 * q) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le h_m]
    omega

    have div_prop_2 {r d k : ℕ} (hd : 0 < d) (hk : k = (30 * r) / d) (_hr : r < d) : (15 * r) / d = k / 2 := by
    have hk_eq : 30 * r = d * k + (30 * r) % d := by
      nth_rw 1 [← Nat.div_add_mod (30 * r) d]
      congr 2
      exact hk.symm
    have h_mod : (30 * r) % d < d := Nat.mod_lt _ hd
    rw [Nat.div_eq_iff hd]
    have hk_eq2 : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
    have h_linear : 30 * r = 2 * (d * (k / 2)) + d * (k % 2) + (30 * r) % d := by
      calc 30 * r = d * k + (30 * r) % d := hk_eq
      _ = d * (2 * (k / 2) + k % 2) + (30 * r) % d := by nth_rw 1 [hk_eq2]
      _ = 2 * (d * (k / 2)) + d * (k % 2) + (30 * r) % d := by ring
    simp_rw [mul_comm (k / 2) d]
    rcases Nat.mod_two_eq_zero_or_one k with h_mod2 | h_mod2
    · rw [h_mod2] at h_linear
      simp only [mul_zero, add_zero] at h_linear
      omega
    · rw [h_mod2] at h_linear
      simp only [mul_one] at h_linear
      omega

    have div_prop_3 {r d k : ℕ} (hd : 0 < d) (hk : k = (30 * r) / d) : (10 * r) / d = k / 3 := by
    have hk_eq : 30 * r = d * k + (30 * r) % d := by
      nth_rw 1 [← Nat.div_add_mod (30 * r) d]
      congr 2
      exact hk.symm
    have h_mod : (30 * r) % d < d := Nat.mod_lt _ hd
    rw [Nat.div_eq_iff hd]
    have hk_eq2 : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    have h_linear : 30 * r = 3 * (d * (k / 3)) + d * (k % 3) + (30 * r) % d := by
      calc 30 * r = d * k + (30 * r) % d := hk_eq
      _ = d * (3 * (k / 3) + k % 3) + (30 * r) % d := by nth_rw 1 [hk_eq2]
      _ = 3 * (d * (k / 3)) + d * (k % 3) + (30 * r) % d := by ring
    simp_rw [mul_comm (k / 3) d]
    have h_cases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
      have : k % 3 < 3 := Nat.mod_lt k (by decide)
      omega
    rcases h_cases with h | h | h
    · rw [h] at h_linear
      simp only [mul_zero, add_zero] at h_linear
      omega
    · rw [h] at h_linear
      simp only [mul_one] at h_linear
      omega
    · rw [h] at h_linear
      have : d * 2 = 2 * d := mul_comm d 2
      rw [this] at h_linear
      omega

    have div_prop_5 {r d k : ℕ} (hd : 0 < d) (hk : k = (30 * r) / d) : (6 * r) / d = k / 5 := by
    have hk_eq : 30 * r = d * k + (30 * r) % d := by
      nth_rw 1 [← Nat.div_add_mod (30 * r) d]
      congr 2
      exact hk.symm
    have h_mod : (30 * r) % d < d := Nat.mod_lt _ hd
    rw [Nat.div_eq_iff hd]
    have hk_eq2 : k = 5 * (k / 5) + k % 5 := (Nat.div_add_mod k 5).symm
    have h_linear : 30 * r = 5 * (d * (k / 5)) + d * (k % 5) + (30 * r) % d := by
      calc 30 * r = d * k + (30 * r) % d := hk_eq
      _ = d * (5 * (k / 5) + k % 5) + (30 * r) % d := by nth_rw 1 [hk_eq2]
      _ = 5 * (d * (k / 5)) + d * (k % 5) + (30 * r) % d := by ring
    simp_rw [mul_comm (k / 5) d]
    have h_cases : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
      have : k % 5 < 5 := Nat.mod_lt k (by decide)
      omega
    rcases h_cases with h | h | h | h | h
    · rw [h] at h_linear; simp only [mul_zero, add_zero] at h_linear; omega
    · rw [h] at h_linear; simp only [mul_one] at h_linear; omega
    · rw [h] at h_linear; have : d * 2 = 2 * d := mul_comm d 2; rw [this] at h_linear; omega
    · rw [h] at h_linear; have : d * 3 = 3 * d := mul_comm d 3; rw [this] at h_linear; omega
    · rw [h] at h_linear; have : d * 4 = 4 * d := mul_comm d 4; rw [this] at h_linear; omega

    have E_ge_one {n p i : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hi : p^i ∣ 30 * n - 1) (hi_pos : 1 ≤ i) :
      (15 * n) / p^i + (10 * n) / p^i + (6 * n) / p^i + 1 ≤ n / p^i + (30 * n) / p^i := by
    have hd : 0 < p^i := Nat.pos_of_ne_zero (pow_ne_zero i hp.ne_zero)
    have hd2 : 2 ≤ p^i := by
      calc 2 ≤ p := hp.two_le
      _ = p^1 := (pow_one p).symm
      _ ≤ p^i := Nat.pow_le_pow_right hp.pos hi_pos
    have h_dvd_eq : 30 * n = p^i * ((30 * n - 1) / p^i) + 1 := by
      have : p^i ∣ 30 * n - 1 := hi
      have h_sub : 30 * n = 30 * n - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
      nth_rw 1 [h_sub]
      congr 1
      exact (Nat.mul_div_cancel' this).symm
    have h_mod : n % p^i < p^i := Nat.mod_lt _ hd
    generalize h_div : n / p^i = q
    generalize h_mod_val : n % p^i = r
    have hq_eq : n = p^i * q + r := by
      calc n = p^i * (n / p^i) + n % p^i := (Nat.div_add_mod n (p^i)).symm
      _ = p^i * q + r := by rw [h_div, h_mod_val]
    have hr_lt : r < p^i := by omega
    have h_r_ident := r_ident hd hd2 h_dvd_eq hq_eq hr_lt rfl
    generalize hm : (30 * n - 1) / p^i - 30 * q = m
    rw [hm] at h_r_ident
    have h30 : 30 * n = p^i * (30 * q) + 30 * r := by
      calc 30 * n = 30 * (p^i * q + r) := by rw [← hq_eq]
      _ = p^i * (30 * q) + 30 * r := by ring
    have h15 : 15 * n = p^i * (15 * q) + 15 * r := by
      calc 15 * n = 15 * (p^i * q + r) := by rw [← hq_eq]
      _ = p^i * (15 * q) + 15 * r := by ring
    have h10 : 10 * n = p^i * (10 * q) + 10 * r := by
      calc 10 * n = 10 * (p^i * q + r) := by rw [← hq_eq]
      _ = p^i * (10 * q) + 10 * r := by ring
    have h6 : 6 * n = p^i * (6 * q) + 6 * r := by
      calc 6 * n = 6 * (p^i * q + r) := by rw [← hq_eq]
      _ = p^i * (6 * q) + 6 * r := by ring
    have h30_div : (30 * n) / p^i = 30 * q + (30 * r) / p^i := by
      rw [h30, Nat.add_div_of_dvd_right (dvd_mul_right (p^i) (30 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (30 * q) hd
    have h15_div : (15 * n) / p^i = 15 * q + (15 * r) / p^i := by
      rw [h15, Nat.add_div_of_dvd_right (dvd_mul_right (p^i) (15 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (15 * q) hd
    have h10_div : (10 * n) / p^i = 10 * q + (10 * r) / p^i := by
      rw [h10, Nat.add_div_of_dvd_right (dvd_mul_right (p^i) (10 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (10 * q) hd
    have h6_div : (6 * n) / p^i = 6 * q + (6 * r) / p^i := by
      rw [h6, Nat.add_div_of_dvd_right (dvd_mul_right (p^i) (6 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (6 * q) hd
    rw [h30_div, h15_div, h10_div, h6_div]
    have hk_eq : (30 * r) / p^i = m := by
      rw [Nat.div_eq_iff hd]
      have h_r : 30 * r = p^i * m + 1 := h_r_ident
      have : (m + 1) * p^i = p^i * m + p^i := by ring
      have : m * p^i = p^i * m := mul_comm m (p^i)
      omega
    have hm_lt : m < 30 := by
      rw [← hk_eq]
      exact Nat.div_lt_of_lt_mul (by omega)
    have h_cop : Nat.Coprime m 30 := coprime_of_ident h_r_ident
    have h_ineq := k_ineq_coprime m hm_lt h_cop
    have h2 := div_prop_2 hd hk_eq.symm hr_lt
    have h3 := div_prop_3 hd hk_eq.symm
    have h5 := div_prop_5 hd hk_eq.symm
    rw [h2, h3, h5]
    omega

    have k_ineq (k : ℕ) (hk : k < 30) : k / 2 + k / 3 + k / 5 ≤ k := by
    omega

    have term_ineq (x d : ℕ) (hd : 0 < d) :
      (15 * x) / d + (10 * x) / d + (6 * x) / d ≤ x / d + (30 * x) / d := by
    have hq_eq : x = d * (x / d) + x % d := (Nat.div_add_mod x d).symm
    have h_mod : x % d < d := Nat.mod_lt _ hd
    generalize h_div : x / d = q
    generalize h_mod_val : x % d = r
    rw [h_div, h_mod_val] at hq_eq
    have h30 : 30 * x = d * (30 * q) + 30 * r := by
      calc 30 * x = 30 * (d * q + r) := by rw [hq_eq]
      _ = d * (30 * q) + 30 * r := by ring
    have h15 : 15 * x = d * (15 * q) + 15 * r := by
      calc 15 * x = 15 * (d * q + r) := by rw [hq_eq]
      _ = d * (15 * q) + 15 * r := by ring
    have h10 : 10 * x = d * (10 * q) + 10 * r := by
      calc 10 * x = 10 * (d * q + r) := by rw [hq_eq]
      _ = d * (10 * q) + 10 * r := by ring
    have h6 : 6 * x = d * (6 * q) + 6 * r := by
      calc 6 * x = 6 * (d * q + r) := by rw [hq_eq]
      _ = d * (6 * q) + 6 * r := by ring
    have h30_div : (30 * x) / d = 30 * q + (30 * r) / d := by
      rw [h30, Nat.add_div_of_dvd_right (dvd_mul_right d (30 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (30 * q) hd
    have h15_div : (15 * x) / d = 15 * q + (15 * r) / d := by
      rw [h15, Nat.add_div_of_dvd_right (dvd_mul_right d (15 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (15 * q) hd
    have h10_div : (10 * x) / d = 10 * q + (10 * r) / d := by
      rw [h10, Nat.add_div_of_dvd_right (dvd_mul_right d (10 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (10 * q) hd
    have h6_div : (6 * x) / d = 6 * q + (6 * r) / d := by
      rw [h6, Nat.add_div_of_dvd_right (dvd_mul_right d (6 * q))]
      congr 1
      exact Nat.mul_div_cancel_left (6 * q) hd
    rw [h30_div, h15_div, h10_div, h6_div]
    generalize hk : (30 * r) / d = k
    have hk_lt : k < 30 := by
      rw [← hk]
      exact Nat.div_lt_of_lt_mul (by omega)
    have hr_lt : r < d := by omega
    have h2 := div_prop_2 hd hk.symm hr_lt
    have h3 := div_prop_3 hd hk.symm
    have h5 := div_prop_5 hd hk.symm
    rw [h2, h3, h5]
    have := k_ineq k hk_lt
    omega

    have cast_div_eq {a b : ℕ} (h : b ∣ a) : ((a / b : ℕ) : ℤ) = (a : ℤ) / (b : ℤ) := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · rcases h with ⟨k, rfl⟩
      have : b * k / b = k := Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hb)
      omega

    have dvd_div_of_mul_dvd {a b c : ℕ} (ha : a ≠ 0) (h : a * b ∣ c) : b ∣ c / a := by
    rcases h with ⟨k, rfl⟩
    use k
    rw [mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)]

    have my_dvd_of_mul_left_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c := by
    rcases h with ⟨k, rfl⟩
    use a * k
    ring

    have my_dvd_of_mul_right_dvd {a b c : ℕ} (h : a * b ∣ c) : a ∣ c := by
    rcases h with ⟨k, rfl⟩
    use b * k
    ring

cases n with
  | zero => decide
  | succ n =>
    have h_nz1 : (30 * (n + 1) - 1) * ((15 * (n + 1)).factorial * (10 * (n + 1)).factorial * (6 * (n + 1)).factorial) ≠ 0 := by
      apply Nat.mul_ne_zero
      · omega
      · apply Nat.mul_ne_zero
        · apply Nat.mul_ne_zero
          · exact Nat.factorial_ne_zero _
          · exact Nat.factorial_ne_zero _
        · exact Nat.factorial_ne_zero _
    have h_nz2 : (30 * (n + 1)).factorial * (n + 1).factorial ≠ 0 := by
      apply Nat.mul_ne_zero <;> exact Nat.factorial_ne_zero _
    have h_dvd_nat : ((30 * (n + 1) - 1) * ((15 * (n + 1)).factorial * (10 * (n + 1)).factorial * (6 * (n + 1)).factorial)) ∣ (30 * (n + 1)).factorial * (n + 1).factorial := by
      apply (factorization_prime_le_iff_dvd h_nz1 h_nz2).mp
      intro p hp
      have h_fac_lhs : ((30 * (n + 1) - 1) * ((15 * (n + 1)).factorial * (10 * (n + 1)).factorial * (6 * (n + 1)).factorial)).factorization p =
          (30 * (n + 1) - 1).factorization p + (15 * (n + 1)).factorial.factorization p + (10 * (n + 1)).factorial.factorization p + (6 * (n + 1)).factorial.factorization p := by
        have h_mul1 : ((15 * (n + 1)).factorial * (10 * (n + 1)).factorial * (6 * (n + 1)).factorial) ≠ 0 := by
          apply Nat.mul_ne_zero
          · apply Nat.mul_ne_zero <;> exact Nat.factorial_ne_zero _
          · exact Nat.factorial_ne_zero _
        have h_mul2 : (15 * (n + 1)).factorial * (10 * (n + 1)).factorial ≠ 0 := by
          apply Nat.mul_ne_zero <;> exact Nat.factorial_ne_zero _
        rw [Nat.factorization_mul (by omega) h_mul1, Nat.factorization_mul h_mul2 (Nat.factorial_ne_zero _), Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
        simp only [Finsupp.coe_add, Pi.add_apply]
        ring
      have h_fac_rhs : ((30 * (n + 1)).factorial * (n + 1).factorial).factorization p =
          (30 * (n + 1)).factorial.factorization p + (n + 1).factorial.factorization p := by
        rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
        simp only [Finsupp.coe_add, Pi.add_apply]
      rw [h_fac_lhs, h_fac_rhs]
      have h_log_lt : ∀ x, x ≤ 30 * (n + 1) → log p x < 30 * (n + 1) + 1 := by
        intro x hx
        rcases eq_or_ne x 0 with rfl | hx0
        · simp
        · have : log p x < x + 1 := log_lt_self_add_one hp hx0
          omega
      have h15_sum : (15 * (n + 1)).factorial.factorization p = ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (15 * (n + 1)) / p ^ i :=
        factorization_factorial hp (h_log_lt (15 * (n + 1)) (by omega))
      have h10_sum : (10 * (n + 1)).factorial.factorization p = ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (10 * (n + 1)) / p ^ i :=
        factorization_factorial hp (h_log_lt (10 * (n + 1)) (by omega))
      have h6_sum : (6 * (n + 1)).factorial.factorization p = ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (6 * (n + 1)) / p ^ i :=
        factorization_factorial hp (h_log_lt (6 * (n + 1)) (by omega))
      have h30_sum : (30 * (n + 1)).factorial.factorization p = ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (30 * (n + 1)) / p ^ i :=
        factorization_factorial hp (h_log_lt (30 * (n + 1)) (by omega))
      have h1_sum : (n + 1).factorial.factorization p = ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (n + 1) / p ^ i :=
        factorization_factorial hp (h_log_lt (n + 1) (by omega))
      rw [h15_sum, h10_sum, h6_sum, h30_sum, h1_sum]
      let k := (30 * (n + 1) - 1).factorization p
      rcases eq_or_ne k 0 with hk0 | hk_pos
      · have hk0' : (30 * (n + 1) - 1).factorization p = 0 := hk0
        rw [hk0']
        simp only [zero_add]
        repeat rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        have hp_pow_pos : 0 < p^i := Nat.pos_of_ne_zero (pow_ne_zero i hp.ne_zero)
        have := term_ineq (n + 1) (p^i) hp_pow_pos
        omega
      · have h_pk_dvd : p^k ∣ 30 * (n + 1) - 1 := by
          apply (hp.pow_dvd_iff_le_factorization (by omega)).mpr (le_refl k)
        have h_pk_le : p^k ≤ 30 * (n + 1) - 1 := Nat.le_of_dvd (by omega) h_pk_dvd
        have h_k_lt_pk : k < p^k := by
          calc k < 2^k := lt_two_pow_self k
          _ ≤ p^k := Nat.pow_le_pow_left hp.two_le k
        have h_k_lt_b : k < 30 * (n + 1) + 1 := by omega
        have h1 : 1 ≤ k + 1 := by omega
        have h2 : k + 1 ≤ 30 * (n + 1) + 1 := by omega
        have h15_split : ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (15 * (n + 1)) / p ^ i = ∑ i ∈ Ico 1 (k + 1), (15 * (n + 1)) / p ^ i + ∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (15 * (n + 1)) / p ^ i :=
          (Finset.sum_Ico_consecutive _ h1 h2).symm
        have h10_split : ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (10 * (n + 1)) / p ^ i = ∑ i ∈ Ico 1 (k + 1), (10 * (n + 1)) / p ^ i + ∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (10 * (n + 1)) / p ^ i :=
          (Finset.sum_Ico_consecutive _ h1 h2).symm
        have h6_split : ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (6 * (n + 1)) / p ^ i = ∑ i ∈ Ico 1 (k + 1), (6 * (n + 1)) / p ^ i + ∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (6 * (n + 1)) / p ^ i :=
          (Finset.sum_Ico_consecutive _ h1 h2).symm
        have h30_split : ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (30 * (n + 1)) / p ^ i = ∑ i ∈ Ico 1 (k + 1), (30 * (n + 1)) / p ^ i + ∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (30 * (n + 1)) / p ^ i :=
          (Finset.sum_Ico_consecutive _ h1 h2).symm
        have h1_split : ∑ i ∈ Ico 1 (30 * (n + 1) + 1), (n + 1) / p ^ i = ∑ i ∈ Ico 1 (k + 1), (n + 1) / p ^ i + ∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (n + 1) / p ^ i :=
          (Finset.sum_Ico_consecutive _ h1 h2).symm

        have h_part1 : k + (∑ i ∈ Ico 1 (k + 1), (15 * (n + 1)) / p ^ i) + (∑ i ∈ Ico 1 (k + 1), (10 * (n + 1)) / p ^ i) + (∑ i ∈ Ico 1 (k + 1), (6 * (n + 1)) / p ^ i) ≤
            (∑ i ∈ Ico 1 (k + 1), (30 * (n + 1)) / p ^ i) + (∑ i ∈ Ico 1 (k + 1), (n + 1) / p ^ i) := by
          have h_sum_one : ∑ i ∈ Ico 1 (k + 1), 1 = k := by simp
          nth_rw 1 [← h_sum_one]
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro i hi
          have h_mem : i ∈ Ico 1 (k + 1) := hi
          have hi_le : i ≤ k := by rw [Finset.mem_Ico] at h_mem; omega
          have hi_pos : 1 ≤ i := by rw [Finset.mem_Ico] at h_mem; omega
          have h_dvd : p^i ∣ 30 * (n + 1) - 1 := by
            have h_pi_dvd : p^i ∣ p^k := Nat.pow_dvd_pow p hi_le
            exact dvd_trans h_pi_dvd h_pk_dvd
          have h_ineq := E_ge_one hp (by omega) h_dvd hi_pos
          omega

        have h_part2 : (∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (15 * (n + 1)) / p ^ i) + (∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (10 * (n + 1)) / p ^ i) + (∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (6 * (n + 1)) / p ^ i) ≤
            (∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (30 * (n + 1)) / p ^ i) + (∑ i ∈ Ico (k + 1) (30 * (n + 1) + 1), (n + 1) / p ^ i) := by
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro i hi
          have hp_pow_pos : 0 < p^i := Nat.pos_of_ne_zero (pow_ne_zero i hp.ne_zero)
          have h_ineq := term_ineq (n + 1) (p^i) hp_pow_pos
          omega

        rw [h15_split, h10_split, h6_split, h30_split, h1_split]
        omega
    have h_fac_nz : (15 * (n + 1))! * (10 * (n + 1))! * (6 * (n + 1))! ≠ 0 := by
      apply Nat.mul_ne_zero
      · apply Nat.mul_ne_zero <;> exact Nat.factorial_ne_zero _
      · exact Nat.factorial_ne_zero _
    rw [mul_comm] at h_dvd_nat
    have h_div_nat : (30 * (n + 1) - 1) ∣ ((30 * (n + 1))! * (n + 1)!) / ((15 * (n + 1))! * (10 * (n + 1))! * (6 * (n + 1))!) := by
      exact dvd_div_of_mul_dvd h_fac_nz h_dvd_nat
    have h_div_int : (((30 * (n + 1) - 1) : ℕ) : ℤ) ∣ (((30 * (n + 1))! * (n + 1)!) / ((15 * (n + 1))! * (10 * (n + 1))! * (6 * (n + 1))!) : ℕ) := by
      exact @Nat.cast_dvd_cast ℤ _ _ _ h_div_nat
    have h_dvd_fac : ((15 * (n + 1))! * (10 * (n + 1))! * (6 * (n + 1))!) ∣ (30 * (n + 1))! * (n + 1)! := by
      have h_mul_dvd : ((15 * (n + 1))! * (10 * (n + 1))! * (6 * (n + 1))!) * (30 * (n + 1) - 1) ∣ (30 * (n + 1))! * (n + 1)! := h_dvd_nat
      exact my_dvd_of_mul_right_dvd h_mul_dvd
    have h_sub_cast : (((30 * (n + 1) - 1) : ℕ) : ℤ) = (30 * (n + 1) - 1 : ℤ) := by omega
    rw [h_sub_cast] at h_div_int
    rw [cast_div_eq h_dvd_fac] at h_div_int
    push_cast at h_div_int
    exact h_div_int







