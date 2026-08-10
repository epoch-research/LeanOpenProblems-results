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


open Finset Nat

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false


lemma neg_one_pow_even (k : ℕ) : (-1 : ℤ)^(2 * k) = 1 := by
  rw [pow_mul]
  have h1 : (-1 : ℤ)^2 = 1 := by norm_num
  rw [h1, one_pow]

lemma neg_one_pow_odd (k : ℕ) : (-1 : ℤ)^(2 * k + 1) = -1 := by
  rw [pow_add, neg_one_pow_even]
  ring

lemma neg_two_pow_even (k : ℕ) : (-2 : ℤ)^(2 * k) = 2^(2 * k) := by
  rw [pow_mul, pow_mul]
  have h2 : (-2 : ℤ)^2 = 4 := by norm_num
  have h3 : (2 : ℤ)^2 = 4 := by norm_num
  rw [h2, h3]

lemma neg_two_pow_odd (k : ℕ) : (-2 : ℤ)^(2 * k + 1) = - 2^(2 * k + 1) := by
  rw [pow_add, neg_two_pow_even]
  ring

def C (j : ℕ) : ℤ :=
  if j % 2 = 0 then - (2 ^ (j - 1)) else 1 + 2 ^ (j - 1)

lemma C_spec (j : ℕ) (hj : 1 ≤ j) :
    2 * C j = 1 - (-1 : ℤ)^j - (-2 : ℤ)^j := by
  rw [C]
  split_ifs with h_mod
  · -- j is even
    have h_even : Even j := Nat.even_iff.mpr h_mod
    rcases h_even with ⟨k, rfl⟩
    have hk : k ≠ 0 := by omega
    rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k', rfl⟩
    have hj_eq : 2 * (k' + 1) = 2 * k' + 2 := by ring
    have hj_sub : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
    have h_goal_rewrite : k'.succ + k'.succ = 2 * (k' + 1) := by omega
    rw [h_goal_rewrite]
    rw [hj_sub, hj_eq]
    have h_lhs : 2 * - (2 ^ (2 * k' + 1) : ℤ) = - 2 ^ (2 * k' + 2) := by
      rw [mul_neg]
      congr 1
      rw [mul_comm, ← pow_succ]
    rw [h_lhs]
    have h_even_1 : (-1 : ℤ)^(2 * k' + 2) = 1 := by
      have h_eq : 2 * k' + 2 = 2 * (k' + 1) := by ring
      rw [h_eq, neg_one_pow_even]
    have h_even_2 : (-2 : ℤ)^(2 * k' + 2) = 2^(2 * k' + 2) := by
      have h_eq : 2 * k' + 2 = 2 * (k' + 1) := by ring
      rw [h_eq, neg_two_pow_even]
    rw [h_even_1, h_even_2]
    ring
  · -- j is odd
    have h_odd_mod : j % 2 = 1 := by omega
    have h_odd : Odd j := Nat.odd_iff.mpr h_odd_mod
    rcases h_odd with ⟨k, rfl⟩
    have hj_sub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hj_sub]
    have h_lhs : 2 * (1 + 2 ^ (2 * k) : ℤ) = 2 + 2 ^ (2 * k + 1) := by
      rw [mul_add]
      congr 1
      rw [mul_comm, ← pow_succ]
    rw [h_lhs]
    rw [neg_one_pow_odd k, neg_two_pow_odd k]
    ring

noncomputable def a_int (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | m + 1 =>
    let sum_val : ℤ := Finset.sum (Finset.range (m + 1)) (fun k =>
      let j := k + 1
      ((m + 1).choose j : ℤ) * C j * a_int (m + 1 - j)
    )
    (-1 : ℤ)^(m + 1) + sum_val

lemma a_int_recurrence (n : ℕ) (hn : n ≥ 1) :
    2 * a_int n = 2 * (-1 : ℤ)^n + Finset.sum (Finset.range n) (fun k =>
      let j := k + 1
      (n.choose j : ℤ) * (1 - (-1 : ℤ)^j - (-2 : ℤ)^j) * a_int (n - j)
    ) := by
  rcases n with _ | m
  · omega
  · rw [a_int]
    rw [mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    dsimp only
    have hj : k + 1 ≥ 1 := by omega
    have h_coeff : 2 * C (k + 1) = 1 - (-1 : ℤ)^(k + 1) - (-2 : ℤ)^(k + 1) := C_spec (k + 1) hj
    have hj_sub : m + 1 - (k + 1) = m - k := by omega
    rw [hj_sub]
    have h_ring : 2 * ( ((m + 1).choose (k + 1) : ℤ) * C (k + 1) * a_int (m - k) ) = ((m + 1).choose (k + 1) : ℤ) * (2 * C (k + 1)) * a_int (m - k) := by ring
    rw [h_ring, h_coeff]

noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1
      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j
      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

theorem a_eq_a_int (n : ℕ) : a n = (a_int n : ℚ) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | m
  · rw [a, a_int]
    rfl
  · rw [a, a_int]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hj : k + 1 ≥ 1 := by omega
    have h_coeff : 1 - (-1 : ℚ)^(k + 1) - (-2 : ℚ)^(k + 1) = 2 * (C (k + 1) : ℚ) := by
      have h_int : (((1 - (-1 : ℤ)^(k + 1) - (-2 : ℤ)^(k + 1) : ℤ) : ℚ)) = (((2 * C (k + 1) : ℤ) : ℚ)) := by
        congr 1
        rw [← C_spec (k + 1) hj]
      push_cast at h_int
      exact h_int
    rw [ih (m - k) (by omega)]
    rw [h_coeff]
    ring

lemma a_num_eq_a_int (n : ℕ) : (a n).num = a_int n := by
  rw [a_eq_a_int]
  exact Rat.num_intCast (a_int n)

def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

lemma a_mod_k_eq_a_int (k : ℕ) (n : ℕ) : a_mod_k k n = (a_int n : ZMod k) := by
  rw [a_mod_k, a_num_eq_a_int]

lemma le_pow_self_of_two_le (p e : ℕ) (hp : 2 ≤ p) : e ≤ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    have h1 : p ^ e * 2 ≤ p ^ e * p := Nat.mul_le_mul_left (p ^ e) hp
    have h_one : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
    have h3 : e + 1 ≤ p ^ e + p ^ e := by omega
    have h5 : p ^ e + p ^ e = p ^ e * 2 := by ring
    rw [h5] at h3
    exact h3.trans h1

lemma dvd_of_modEq_one {a m : ℕ} (hm : 2 ≤ m) (h : a ≡ 1 [MOD m]) : m ∣ a - 1 := by
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : a % m = 1 := by
    have h_eq : a % m = 1 % m := h
    rw [h_eq, h1]
  have h3 : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
  rw [h2] at h3
  have h4 : a - 1 = m * (a / m) := by omega
  rw [h4]
  exact dvd_mul_right m (a / m)

lemma prime_power_dvd (p : ℕ) (hp : p.Prime) (e : ℕ) (g : ℕ) (n : ℕ) (hn : p^e ≤ n) :
    p^e ∣ g^n * (g ^ (totient (p^e)) - 1) := by
  by_cases he : e = 0
  · rw [he, pow_zero]
    exact one_dvd _
  · have h_pe_ge_two : 2 ≤ p^e := by
      rcases Nat.exists_eq_succ_of_ne_zero he with ⟨e', rfl⟩
      rw [pow_succ]
      have hp2 : 2 ≤ p := hp.two_le
      have h_one : 1 ≤ p ^ e' := Nat.one_le_pow e' p (by omega)
      have h_ge : p ≤ p ^ e' * p := by
        have h_mul : 1 * p ≤ p ^ e' * p := Nat.mul_le_mul_right p h_one
        rw [one_mul] at h_mul
        exact h_mul
      omega
    by_cases h_div : p ∣ g
    · rcases h_div with ⟨q, rfl⟩
      have h_pow : (p * q) ^ n = p ^ n * q ^ n := mul_pow p q n
      rw [h_pow]
      have h_le : e ≤ p ^ e := le_pow_self_of_two_le p e hp.two_le
      have h_en : e ≤ n := by omega
      have h_dvd_pn : p^e ∣ p^n := pow_dvd_pow p h_en
      have h_dvd_gn : p^e ∣ p^n * q^n := dvd_mul_of_dvd_left h_dvd_pn (q^n)
      exact dvd_mul_of_dvd_left h_dvd_gn _
    · have h_coprime_p : g.Coprime p := ((hp.coprime_iff_not_dvd).mpr h_div).symm
      have h_coprime_pe : g.Coprime (p^e) := h_coprime_p.pow_right e
      have h_modeq : g ^ (totient (p^e)) ≡ 1 [MOD p^e] := Nat.ModEq.pow_totient h_coprime_pe
      have h_dvd_diff : p^e ∣ g ^ (totient (p^e)) - 1 := dvd_of_modEq_one h_pe_ge_two h_modeq
      exact dvd_mul_of_dvd_right h_dvd_diff _

lemma k_dvd_of_prime_pow_dvd (g : ℕ) (k : ℕ) (n : ℕ) (hn : k ≤ n) :
    k ∣ g ^ n * (g ^ (totient k) - 1) := by
  by_cases hk : k = 0
  · rw [hk]
    exact dvd_zero _
  · rw [dvd_iff_prime_pow_dvd_dvd]
    intro p k' hp hp_dvd
    have h_le_k : p ^ k' ≤ k := Nat.le_of_dvd (by omega) hp_dvd
    have h_le_n : p ^ k' ≤ n := h_le_k.trans hn
    have h_dvd_p_pow : p ^ k' ∣ g ^ n * (g ^ (totient (p ^ k')) - 1) := prime_power_dvd p hp k' g n h_le_n
    have h_tot_dvd : totient (p ^ k') ∣ totient k := totient_dvd_of_dvd hp_dvd
    have h_sub_dvd : g ^ (totient (p ^ k')) - 1 ∣ g ^ (totient k) - 1 := pow_sub_one_dvd_pow_sub_one g h_tot_dvd
    have h_mul_dvd : g ^ n * (g ^ (totient (p ^ k')) - 1) ∣ g ^ n * (g ^ (totient k) - 1) := mul_dvd_mul_left (g ^ n) h_sub_dvd
    exact dvd_trans h_dvd_p_pow h_mul_dvd

lemma pow_add_totient_eq (k : ℕ) (g : ZMod k) (n : ℕ) (hn : k ≤ n) :
    g ^ (n + totient k) = g ^ n := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have : NeZero k := ⟨hk⟩
    have h_val_eq : g = (g.val : ZMod k) := by
      apply ZMod.val_injective k
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt g.val_lt]
    rw [h_val_eq]
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    rw [ZMod.natCast_eq_natCast_iff]
    rw [Nat.ModEq]
    rw [pow_add]
    have h_dvd : k ∣ g.val ^ n * g.val ^ totient k - g.val ^ n := by
      have h_factor : g.val ^ n * g.val ^ totient k - g.val ^ n = g.val ^ n * (g.val ^ totient k - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      rw [h_factor]
      exact k_dvd_of_prime_pow_dvd g.val k n hn
    have h_le_pow : g.val ^ n ≤ g.val ^ n * g.val ^ totient k := by
      by_cases hg : g.val = 0
      · rw [hg]
        have hn1 : 1 ≤ n := by omega
        rw [zero_pow (by omega)]
        simp
      · have hg1 : 1 ≤ g.val := by omega
        have h_pow_pos : 1 ≤ g.val ^ totient k := Nat.one_le_pow _ _ hg1
        exact Nat.le_mul_of_pos_right _ h_pow_pos
    have h_eq : g.val ^ n * g.val ^ totient k ≡ g.val ^ n [MOD k] := by
      exact ((Nat.modEq_iff_dvd' h_le_pow).mpr h_dvd).symm
    exact h_eq

lemma dvd_of_mul_dvd_mul (a b k : ℤ) (h : 2 * k ∣ 2 * a - 2 * b) : k ∣ a - b := by
  have h_eq : 2 * a - 2 * b = 2 * (a - b) := by ring
  rw [h_eq] at h
  rcases h with ⟨q, hq⟩
  have hq_mul : 2 * (a - b) = 2 * (k * q) := by
    calc
      2 * (a - b) = 2 * k * q := hq
      _ = 2 * (k * q) := by ring
  have h_eq2 : a - b = k * q := by
    exact mul_left_cancel₀ (by decide) hq_mul
  rw [h_eq2]
  exact dvd_mul_right k q

lemma modeq_of_modeq_mul (a b : ℤ) (k : ℕ) (h : 2 * a ≡ 2 * b [ZMOD 2 * k]) :
    a ≡ b [ZMOD k] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  exact dvd_of_mul_dvd_mul b a (k : ℤ) h

lemma c_periodic (k : ℕ) (hk : 2 < k) (j : ℕ) (hj : k ≤ j) :
    (((1 - (-1 : ℤ)^(j + totient k) - (-2 : ℤ)^(j + totient k) : ℤ) : ZMod k)) =
    (((1 - (-1 : ℤ)^j - (-2 : ℤ)^j : ℤ) : ZMod k)) := by
  push_cast
  have h_even : Even (totient k) := Nat.totient_even hk
  rcases h_even with ⟨r, hr⟩
  have h_neg_one : (-1 : ZMod k)^(j + totient k) = (-1 : ZMod k)^j := by
    rw [hr]
    have h_mul : j + (r + r) = j + r * 2 := by ring
    rw [h_mul, pow_add]
    have h_pow2 : (-1 : ZMod k)^(r * 2) = 1 := by
      have h_comm : r * 2 = 2 * r := by ring
      rw [h_comm, pow_mul]
      have h_sq : (-1 : ZMod k)^2 = 1 := by ring
      rw [h_sq, one_pow]
    rw [h_pow2, mul_one]
  have h_neg_two : (-2 : ZMod k)^(j + totient k) = (-2 : ZMod k)^j := by
    exact pow_add_totient_eq k (-2 : ZMod k) j hj
  rw [h_neg_one, h_neg_two]

lemma a_int_cast_rec (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    (a_int n : ZMod k) = (-1 : ZMod k)^n + Finset.sum (Finset.range n) (fun i =>
      ((n.choose (i + 1) : ZMod k) * (C (i + 1) : ZMod k) * (a_int (n - (i + 1)) : ZMod k))
    ) := by
  rcases n with _ | m
  · omega
  · rw [a_int]
    push_cast
    rfl


noncomputable def S (n : ℕ) (c : ℤ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) (fun j => (n.choose j : ℤ) * c^j * a_int (n - j))

lemma S_split (n : ℕ) (c : ℤ) :
    S n c = a_int n + Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * c^(i + 1) * a_int (n - (i + 1))) := by
  rw [S]
  rw [Finset.sum_range_succ']
  have h_term : (n.choose 0 : ℤ) * c^0 * a_int (n - 0) = a_int n := by
    simp
  rw [h_term]
  rw [add_comm]

lemma S_relation (n : ℕ) (hn : n ≥ 1) :
    S n 1 - S n (-1) - S n (-2) + a_int n = 2 * a_int n - 2 * (-1 : ℤ)^n := by
  rw [S_split n 1, S_split n (-1), S_split n (-2)]
  have h_ring :
      a_int n + Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * 1^(i + 1) * a_int (n - (i + 1))) -
      (a_int n + Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-1)^(i + 1) * a_int (n - (i + 1)))) -
      (a_int n + Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-2)^(i + 1) * a_int (n - (i + 1)))) +
      a_int n =
      Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * 1^(i + 1) * a_int (n - (i + 1))) -
      Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-1)^(i + 1) * a_int (n - (i + 1))) -
      Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-2)^(i + 1) * a_int (n - (i + 1))) := by ring
  rw [h_ring]
  have h_combine :
    Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * 1^(i + 1) * a_int (n - (i + 1))) -
    Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-1)^(i + 1) * a_int (n - (i + 1))) -
    Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (-2)^(i + 1) * a_int (n - (i + 1))) =
    Finset.sum (Finset.range n) (fun i => (n.choose (i + 1) : ℤ) * (1 - (-1)^(i + 1) - (-2)^(i + 1)) * a_int (n - (i + 1))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  rw [h_combine]
  have h_rec := a_int_recurrence n hn
  linarith


lemma a_int_eq_S (n : ℕ) (hn : n ≥ 1) :
    a_int n = S n 1 - S n (-1) - S n (-2) + 2 * (-1 : ℤ)^n := by
  have h := S_relation n hn
  omega


lemma binomial_sum (x y : ℤ) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * x ^ m * y ^ (n - m) := by
  rw [add_pow]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  ring

lemma binomial_sum_range_succ (x y : ℤ) (n : ℕ) :
    ∑ m ∈ Finset.range n, ((n.choose (m+1) : ℤ) * x ^ (m+1) * y ^ (n - (m+1))) =
    (x + y) ^ n - y ^ n := by
  have h_add := binomial_sum x y n
  rw [Finset.sum_range_succ'] at h_add
  have h_choose : n.choose 0 = 1 := Nat.choose_zero_right n
  rw [h_choose] at h_add
  simp only [Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at h_add
  omega



lemma S_diff_expand (n : ℕ) (hn : n ≥ 1) (c : ℤ) :
    S n c - S n (c-1) - S n (c-2) - S n (c-3) =
    - 2 * (-1 : ℤ)^n + ∑ i ∈ Finset.range n, ((n.choose (i+1) : ℤ) *
      (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1) - (1 - (-1)^(i+1) - (-2)^(i+1))) *
      a_int (n - (i+1))) := by
  rw [S_split n c, S_split n (c-1), S_split n (c-2), S_split n (c-3)]
  have h_rec := a_int_recurrence n hn
  have h_ring_step :
      a_int n + ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * c^(i+1) * a_int (n - (i+1)) : ℤ)) -
      (a_int n + ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-1)^(i+1) * a_int (n - (i+1)) : ℤ))) -
      (a_int n + ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-2)^(i+1) * a_int (n - (i+1)) : ℤ))) -
      (a_int n + ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-3)^(i+1) * a_int (n - (i+1)) : ℤ))) =
      - 2 * a_int n +
      (∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * c^(i+1) * a_int (n - (i+1)) : ℤ)) -
       ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-1)^(i+1) * a_int (n - (i+1)) : ℤ)) -
       ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-2)^(i+1) * a_int (n - (i+1)) : ℤ)) -
       ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-3)^(i+1) * a_int (n - (i+1)) : ℤ))) := by ring
  rw [h_ring_step]
  have h_sums :
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * c^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-1)^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-2)^(i+1) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c-3)^(i+1) * a_int (n - (i+1)) : ℤ)) =
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1)) * a_int (n - (i+1)) : ℤ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  rw [h_sums]
  have h_rec_neg : - 2 * a_int n = - 2 * (-1 : ℤ)^n - ∑ k ∈ Finset.range n, ((n.choose (k+1) : ℤ) * (1 - (-1 : ℤ)^(k+1) - (-2 : ℤ)^(k+1)) * a_int (n - (k+1))) := by linarith
  rw [h_rec_neg]
  have h_combine :
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1)) * a_int (n - (i+1)) : ℤ)) -
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (1 - (-1)^(i+1) - (-2)^(i+1)) * a_int (n - (i+1)) : ℤ)) =
      ∑ i ∈ Finset.range n, (((n.choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1) - (1 - (-1)^(i+1) - (-2)^(i+1))) * a_int (n - (i+1)) : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  rw [← h_combine]
  ring

lemma S_rec (n : ℕ) (c : ℤ) :
    S n c = S n (c-1) + S n (c-2) + S n (c-3) - 2 * (c-2)^n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | m
  · rw [S, S, S, S]
    simp [a_int]
  · have hn : m + 1 ≥ 1 := by omega
    have h_diff := S_diff_expand (m+1) hn c
    have h_sub_eq : ∀ i, m + 1 - (i + 1) = m - i := fun i => by omega
    simp_rw [h_sub_eq] at h_diff
    have h_sum_eq : ∑ i ∈ Finset.range (m+1), (((m+1).choose (i+1) : ℤ) * (c^(i+1) - (c-1)^(i+1) - (c-2)^(i+1) - (c-3)^(i+1) - (1 - (-1)^(i+1) - (-2)^(i+1))) * a_int (m - i)) = - 2 * (c-2)^(m+1) + 2 * (-1)^(m+1) := by
      sorry
    linarith


theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  use totient k
  constructor
  · exact dvd_refl (totient k)
  · rw [eventually_periodic]
    use k
    intro n hn
    rw [a_mod_k_eq_a_int, a_mod_k_eq_a_int]
    have hn1 : n ≥ 1 := by omega
    have hn2 : n + totient k ≥ 1 := by omega
    rw [a_int_eq_S n hn1, a_int_eq_S (n + totient k) hn2]
    push_cast
    have h1 : (S (n + totient k) 1 : ZMod k) = (S n 1 : ZMod k) := by
      sorry
    have h2 : (S (n + totient k) (-1) : ZMod k) = (S n (-1) : ZMod k) := by
      sorry
    have h3 : (S (n + totient k) (-2) : ZMod k) = (S n (-2) : ZMod k) := by
      sorry
    rw [h1, h2, h3]
    have h_pow : (-1 : ZMod k)^(n + totient k) = (-1 : ZMod k)^n := by
      exact pow_add_totient_eq k (-1 : ZMod k) n hn
    rw [h_pow]






