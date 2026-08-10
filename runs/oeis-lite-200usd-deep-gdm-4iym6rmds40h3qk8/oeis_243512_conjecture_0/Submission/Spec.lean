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

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat


theorem A243473_val_one : A243473_val 1 = 0 := by
  dsimp [A243473_val]
  have hsigma : (sigma 1) 1 = 1 := by decide
  rw [hsigma]
  norm_num


theorem A243473_val_two : A243473_val 2 = 1 := by
  dsimp [A243473_val]
  have hsigma : (sigma 1) 2 = 3 := by decide
  rw [hsigma]
  norm_num


theorem A243473_val_120 : A243473_val 120 = 2 := by
  dsimp [A243473_val]
  have hsigma : (sigma 1) 120 = 360 := by decide
  rw [hsigma]
  norm_num
  rfl


noncomputable def a (n : ℕ) : ℕ :=
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

theorem a_ne_zero_iff_local (n : ℕ) : a n ≠ 0 ↔ ∃ i, 0 < i ∧ A243473_val i = n := by
  constructor
  · intro h
    by_contra h_empty
    have h_empty_set : {i : ℕ | 0 < i ∧ A243473_val i = n} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact h_empty ⟨x, hx⟩
    have ha : a n = 0 := by
      dsimp [a]
      rw [h_empty_set, Nat.sInf_empty]
    exact h ha
  · rintro ⟨i, hi_gt, hi_val⟩
    have h_nonempty : {i : ℕ | 0 < i ∧ A243473_val i = n}.Nonempty := ⟨i, hi_gt, hi_val⟩
    have h_mem : a n ∈ {i : ℕ | 0 < i ∧ A243473_val i = n} := by
      dsimp [a]
      exact Nat.sInf_mem h_nonempty
    exact Ne.symm (_root_.ne_of_lt h_mem.1)


/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/



def sigma_computable (n : ℕ) : ℕ :=
  (Finset.filter (· ∣ n) (Finset.Ico 1 (n + 1))).sum (fun x => x)

lemma sigma_computable_eq_sigma_one (i : ℕ) : sigma_computable i = sigma 1 i := by
  rw [sigma_apply]
  simp only [pow_one]
  dsimp [sigma_computable]
  rfl

def A243473_val_computable (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let s := sigma_computable i
    let g := Nat.gcd s i
    (s - i) / g

lemma rat_div_eq (a b : ℕ) : (a : ℚ) / (b : ℚ) = (a : ℤ) /. (b : ℤ) := by
  have h1 : (a : ℚ).num = a := by rfl
  have h2 : (a : ℚ).den = 1 := by rfl
  have h3 : (b : ℚ).num = b := by rfl
  have h4 : (b : ℚ).den = 1 := by rfl
  rw [Rat.div_def', h1, h2, h3, h4]
  simp

lemma rat_num_den (a b : ℕ) (hb : 0 < b) :
  ((a : ℚ) / (b : ℚ)).num = a / Nat.gcd a b := by
  rw [rat_div_eq]
  rw [Rat.num_divInt]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have h_sign : Int.sign (n.succ : ℤ) = 1 := rfl
  have h_gcd : Int.gcd (n.succ : ℤ) (a : ℤ) = Nat.gcd a n.succ := by
    rw [Int.gcd_comm]
    rfl
  rw [h_sign, h_gcd]
  simp

lemma rat_den_den (a b : ℕ) (hb : 0 < b) :
  ((a : ℚ) / (b : ℚ)).den = b / Nat.gcd a b := by
  rw [rat_div_eq]
  rw [Rat.den_divInt]
  have hb_nz : ¬ (b : ℤ) = 0 := by
    exact Int.ofNat_ne_zero.mpr hb.ne'
  simp only [hb_nz, ↓reduceIte]
  have h_nat : Int.natAbs (b : ℤ) = b := rfl
  have h_gcd : Int.gcd (b : ℤ) (a : ℤ) = Nat.gcd a b := by
    rw [Int.gcd_comm]
    rfl
  rw [h_nat, h_gcd]

lemma Nat_sub_div {a b c : ℕ} (ha : c ∣ a) (hb : c ∣ b) : (a - b) / c = a / c - b / c := by
  by_cases hc : c = 0
  · subst hc
    simp
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc
    have ha_eq : a = (a / c) * c := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod a c).symm.trans (by rw [Nat.mod_eq_zero_of_dvd ha, add_zero])
    have hb_eq : b = (b / c) * c := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod b c).symm.trans (by rw [Nat.mod_eq_zero_of_dvd hb, add_zero])
    have h_sub_mul : (a / c - b / c) * c = a - b := by
      rw [Nat.sub_mul, ← ha_eq, ← hb_eq]
    rw [← h_sub_mul]
    exact Nat.mul_div_cancel _ hc_pos

lemma A243473_val_computable_eq (i : ℕ) (hi : 0 < i) : A243473_val_computable i = A243473_val i := by
  dsimp [A243473_val, A243473_val_computable]
  simp only [hi.ne', ↓reduceIte]
  rw [sigma_computable_eq_sigma_one]
  have h_num := rat_num_den (sigma 1 i) i hi
  have h_den := rat_den_den (sigma 1 i) i hi
  rw [h_num, h_den]
  have h_gcd_dvd_sigma : (sigma 1 i).gcd i ∣ sigma 1 i := Nat.gcd_dvd_left (sigma 1 i) i
  have h_gcd_dvd_i : (sigma 1 i).gcd i ∣ i := Nat.gcd_dvd_right (sigma 1 i) i
  have h_le : i <= sigma 1 i := by
    rw [sigma_apply]
    simp only [pow_one]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le x) (Nat.mem_divisors.mpr ⟨dvd_rfl, hi.ne'⟩)
  have h_sub : (sigma 1 i / (sigma 1 i).gcd i : ℕ) - (i / (sigma 1 i).gcd i : ℕ) = (sigma 1 i - i) / (sigma 1 i).gcd i := by
    rw [Nat_sub_div h_gcd_dvd_sigma h_gcd_dvd_i]
  have h_div_cast : (↑((sigma 1 i) / (sigma 1 i).gcd i) : ℤ) = ↑(sigma 1 i) / ↑((sigma 1 i).gcd i) := by
    rw [Int.ofNat_tdiv]
    have h_dvd : ((sigma 1 i).gcd i : ℤ) ∣ sigma 1 i := Int.ofNat_dvd.mpr h_gcd_dvd_sigma
    rw [Int.tdiv_eq_ediv_of_dvd h_dvd]
  rw [← h_div_cast]
  rw [← Int.ofNat_sub]
  · rw [h_sub]
    rfl
  · exact Nat.div_le_div_right h_le

set_option maxRecDepth 2000000
set_option maxHeartbeats 500000

lemma A243473_val_ne_630_small_computable : ∀ i < 500, A243473_val_computable i ≠ 630 := by
  decide

theorem A243473_val_ne_630_small : ∀ i < 500, A243473_val i ≠ 630 := by
  intro i hi
  by_cases h_zero : i = 0
  · subst h_zero
    dsimp [A243473_val]
    decide
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero h_zero
    rw [← A243473_val_computable_eq i hi_pos]
    exact A243473_val_ne_630_small_computable i hi

lemma sigma_mul_geq_right (g d : ℕ) (hg : 0 < g) (hd : 0 < d) : g * (sigma 1 d : ℕ) <= sigma 1 (g * d) := by
  let f : ℕ ↪ ℕ := ⟨fun x => g * x, fun x y h => Nat.eq_of_mul_eq_mul_left hg h⟩
  have h_sub : Finset.map f (Nat.divisors d) ⊆ Nat.divisors (g * d) := by
    intro x hx
    simp only [Finset.mem_map, Nat.mem_divisors] at hx ⊢
    obtain ⟨y, hy_div, rfl⟩ := hx
    exact ⟨mul_dvd_mul_left g hy_div.1, Nat.mul_ne_zero hg.ne' hd.ne'⟩
  have h_sum : Finset.sum (Finset.map f (Nat.divisors d)) (fun x => x) <= Finset.sum (Nat.divisors (g * d)) (fun x => x) := by
    exact Finset.sum_le_sum_of_subset h_sub
  rw [Finset.sum_map] at h_sum
  dsimp [f] at h_sum
  have h_sum' : g * (sigma 1 d : ℕ) = ∑ x ∈ d.divisors, g * x := by
    rw [sigma_apply]
    simp only [pow_one]
    rw [Finset.mul_sum]
  have h_sum'' : sigma 1 (g * d) = ∑ x ∈ (g * d).divisors, x := by
    rw [sigma_apply]
    simp only [pow_one]
  rw [h_sum', h_sum'']
  exact h_sum

lemma gcd_one (g d : ℕ) (hg : 0 < g) (h_eq : sigma 1 (g * d) = g * (d + 630)) (h_gcd : g = Nat.gcd (sigma 1 (g * d)) (g * d)) : Nat.gcd (d + 630) d = 1 := by
  have h1 : Nat.gcd (g * (d + 630)) (g * d) = g * Nat.gcd (d + 630) d := by
    rw [Nat.gcd_mul_left]
  have h2 : g = g * Nat.gcd (d + 630) d := by
    rw [← h1, ← h_eq, ← h_gcd]
  have h3 : g * 1 = g * Nat.gcd (d + 630) d := by
    rw [mul_one]
    exact h2
  exact (Nat.eq_of_mul_eq_mul_left hg h3).symm

lemma gcd_add_630 (d : ℕ) : Nat.gcd (d + 630) d = Nat.gcd 630 d := by
  rw [add_comm]
  exact Nat.gcd_add_self_left d 630

lemma not_dvd_of_gcd_one (a b d : ℕ) (ha_gt : 1 < a) (ha : a ∣ b) (h_gcd : Nat.gcd b d = 1) : ¬ (a ∣ d) := by
  intro hd
  have h_dvd : a ∣ Nat.gcd b d := Nat.dvd_gcd ha hd
  rw [h_gcd] at h_dvd
  have h_le : a <= 1 := Nat.le_of_dvd zero_lt_one h_dvd
  omega

lemma not_dvd_2 (d : ℕ) (h : Nat.gcd 630 d = 1) : ¬ (2 ∣ d) := by
  have h_dvd : 2 ∣ 630 := by decide
  exact not_dvd_of_gcd_one 2 630 d (by decide) h_dvd h

lemma not_dvd_3 (d : ℕ) (h : Nat.gcd 630 d = 1) : ¬ (3 ∣ d) := by
  have h_dvd : 3 ∣ 630 := by decide
  exact not_dvd_of_gcd_one 3 630 d (by decide) h_dvd h

lemma not_dvd_5 (d : ℕ) (h : Nat.gcd 630 d = 1) : ¬ (5 ∣ d) := by
  have h_dvd : 5 ∣ 630 := by decide
  exact not_dvd_of_gcd_one 5 630 d (by decide) h_dvd h

lemma not_dvd_7 (d : ℕ) (h : Nat.gcd 630 d = 1) : ¬ (7 ∣ d) := by
  have h_dvd : 7 ∣ 630 := by decide
  exact not_dvd_of_gcd_one 7 630 d (by decide) h_dvd h

lemma not_dvd_630_of_gcd_one (p d : ℕ) (hp : Nat.Prime p) (hd : p ∣ d) (h_gcd : Nat.gcd 630 d = 1) : ¬ (p ∣ 630) := by
  intro hp_630
  have h_dvd : p ∣ Nat.gcd 630 d := Nat.dvd_gcd hp_630 hd
  rw [h_gcd] at h_dvd
  have hp_ge : p >= 2 := hp.two_le
  have hp_le : p <= 1 := Nat.le_of_dvd (by decide) h_dvd
  omega

lemma prime_ge_11 (p : ℕ) (hp : Nat.Prime p) (hp_630 : ¬ (p ∣ 630)) : p >= 11 := by
  by_contra h_lt
  have h_lt : p < 11 := by omega
  have hp_ge : 2 <= p := hp.two_le
  interval_cases p
  · exact hp_630 (by decide)
  · exact hp_630 (by decide)
  · revert hp; decide
  · exact hp_630 (by decide)
  · revert hp; decide
  · exact hp_630 (by decide)
  · revert hp; decide
  · revert hp; decide
  · revert hp; decide


lemma s_d_le_630 (g d : ℕ) (hg : 0 < g) (hd : 0 < d) (h_eq : sigma 1 (g * d) = g * (d + 630)) : sigma 1 d <= d + 630 := by
  have h_mul := sigma_mul_geq_right g d hg hd
  rw [h_eq] at h_mul
  exact Nat.le_of_mul_le_mul_left h_mul hg

lemma divisor_sum_ge_3 {d k : ℕ} (hd : 0 < d) (hk : k ∣ d) (h1 : 1 < k) (h2 : k < d) :
    1 + k + d <= sigma 1 d := by
  rw [sigma_apply]
  simp only [pow_one]
  have h1_mem : 1 ∈ d.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hd.ne'⟩
  have hk_mem : k ∈ d.divisors := Nat.mem_divisors.mpr ⟨hk, hd.ne'⟩
  have hd_mem : d ∈ d.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hd.ne'⟩
  let S : Finset ℕ := {1, k, d}
  have hS : S ⊆ d.divisors := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1_mem
    · exact hk_mem
    · exact hd_mem
  have h_sum : (∑ x ∈ S, x) <= ∑ x ∈ d.divisors, x := Finset.sum_le_sum_of_subset hS
  have h_S_sum : ∑ x ∈ S, x = 1 + k + d := by
    have h_disj1 : 1 ≠ k := by omega
    have h_disj2 : 1 ≠ d := by omega
    have h_disj3 : k ≠ d := by omega
    dsimp [S]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · omega
    · simp only [Finset.mem_singleton]
      exact h_disj3
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_disj1, h_disj2⟩
  rw [h_S_sum] at h_sum
  exact h_sum

lemma divisor_sum_ge_4 {d k j : ℕ} (hd : 0 < d) (hk : k ∣ d) (hj : j ∣ d) (h1 : 1 < k) (h2 : k < d) (h3 : 1 < j) (h4 : j < d) (h_ne : k ≠ j) :
    1 + k + j + d <= sigma 1 d := by
  rw [sigma_apply]
  simp only [pow_one]
  have h1_mem : 1 ∈ d.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hd.ne'⟩
  have hk_mem : k ∈ d.divisors := Nat.mem_divisors.mpr ⟨hk, hd.ne'⟩
  have hj_mem : j ∈ d.divisors := Nat.mem_divisors.mpr ⟨hj, hd.ne'⟩
  have hd_mem : d ∈ d.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hd.ne'⟩
  let S : Finset ℕ := {1, k, j, d}
  have hS : S ⊆ d.divisors := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1_mem
    · exact hk_mem
    · exact hj_mem
    · exact hd_mem
  have h_sum : (∑ x ∈ S, x) <= ∑ x ∈ d.divisors, x := Finset.sum_le_sum_of_subset hS
  have h_S_sum : ∑ x ∈ S, x = 1 + k + j + d := by
    have h_disj1 : 1 ≠ k := by omega
    have h_disj2 : 1 ≠ j := by omega
    have h_disj3 : 1 ≠ d := by omega
    have h_disj4 : k ≠ j := h_ne
    have h_disj5 : k ≠ d := by omega
    have h_disj6 : j ≠ d := by omega
    dsimp [S]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · omega
    · simp only [Finset.mem_singleton]
      exact h_disj6
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_disj4, h_disj5⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_disj1, h_disj2, h_disj3⟩
  rw [h_S_sum] at h_sum
  exact h_sum

lemma exists_proper_divisor_of_composite {d : ℕ} (h_not_prime : ¬ Nat.Prime d) (hd2 : 2 <= d) :
    ∃ k, k ∣ d ∧ 1 < k ∧ k < d := by
  have h_iff := h_not_prime
  rw [Nat.prime_iff_not_exists_mul_eq] at h_iff
  simp only [hd2, true_and, not_not] at h_iff
  obtain ⟨m, n, hm, hn, hmn⟩ := h_iff
  refine ⟨m, ⟨n, hmn.symm⟩, ?_, hm⟩
  by_contra h_le
  have h_le : m <= 1 := by omega
  interval_cases m
  · subst hmn
    omega
  · subst hmn
    omega

lemma d_le_395641_of_composite {d : ℕ} (h_not_prime : ¬ Nat.Prime d) (hd2 : 2 <= d) (h_sigma : sigma 1 d <= d + 630) : d <= 395641 := by
  have hd_pos : 0 < d := by omega
  obtain ⟨k, hk, h1, h2⟩ := exists_proper_divisor_of_composite h_not_prime hd2
  let j := d / k
  have hd_eq : d = k * j := (Nat.mul_div_cancel' hk).symm
  have h_k_dvd_d : k ∣ d := hk
  have h_j_dvd_d : j ∣ d := ⟨k, by rw [hd_eq, Nat.mul_comm]⟩
  have hj_gt1 : 1 < j := by
    by_contra h_le
    have h_le : j <= 1 := by omega
    interval_cases j
    · subst hd_eq
      omega
    · subst hd_eq
      omega
  have hj_lt_d : j < d := by
    by_contra h_le
    have h_le : d <= j := by omega
    have h_mul : d < k * j := by
      have : k >= 2 := by omega
      nlinarith
    omega
  by_cases h_ne : k = j
  · have h_sum := divisor_sum_ge_3 hd_pos h_k_dvd_d h1 h2
    have hk_le : k <= 629 := by omega
    have h_d_kk : d = k * k := by
      calc d = k * j := hd_eq
           _ = k * k := by rw [h_ne]
    nlinarith
  · have h_sum := divisor_sum_ge_4 hd_pos h_k_dvd_d h_j_dvd_d h1 h2 hj_gt1 hj_lt_d h_ne
    have : k <= 629 := by omega
    have : j <= 629 := by omega
    nlinarith

lemma s_g_bound {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (h_eq : sigma 1 (g * d) = g * (d + 630)) : d * (sigma 1 g - g) <= 630 * g := by
  have h_mul := sigma_mul_geq_right d g hd hg
  rw [Nat.mul_comm d g] at h_mul
  rw [h_eq] at h_mul
  have h_sig : sigma 1 g = g + (sigma 1 g - g) := by
    rw [sigma_apply]
    simp only [pow_one]
    rw [Nat.add_sub_cancel']
    exact Finset.single_le_sum (fun x _ => Nat.zero_le x) (Nat.mem_divisors.mpr ⟨dvd_rfl, hg.ne'⟩)
  rw [h_sig] at h_mul
  rw [Nat.mul_add] at h_mul
  have h_add : g * (d + 630) = d * g + 630 * g := by
    rw [Nat.mul_add, Nat.mul_comm g d, Nat.mul_comm g 630]
  rw [h_add] at h_mul
  exact Nat.le_of_add_le_add_left h_mul

lemma not_prime_d {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (h_eq : sigma 1 (g * d) = g * (d + 630)) (h_gcd : g = Nat.gcd (sigma 1 (g * d)) (g * d)) (h_gt : 395641 < d) : ¬ Nat.Prime d := by
  intro hd_prime
  have h_gcd_d : Nat.gcd (d + 630) d = 1 := gcd_one g d hg h_eq h_gcd
  have h_gcd_630 : Nat.gcd 630 d = 1 := by
    rw [← gcd_add_630 d]
    exact h_gcd_d
  have hd_ge_11 : d >= 11 := by
    refine prime_ge_11 d hd_prime ?_
    intro hd_dvd
    have h_dvd : d ∣ Nat.gcd 630 d := Nat.dvd_gcd hd_dvd dvd_rfl
    rw [h_gcd_630] at h_dvd
    have : d <= 1 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have hd_odd : Odd d := hd_prime.odd_of_ne_two (by omega)
  have hd1_even : Even (d + 1) := by
    exact Odd.add_odd hd_odd (by decide)
  have h_coprime : Nat.gcd g d = 1 := by
    by_contra h_nc
    have hd_dvd_g : d ∣ g := by
      have h_gcd_dvd : Nat.gcd g d ∣ d := Nat.gcd_dvd_right g d
      cases hd_prime.eq_one_or_self_of_dvd _ h_gcd_dvd with
      | inl h1 => omega
      | inr h2 =>
        rw [← h2]
        exact Nat.gcd_dvd_left g d
    obtain ⟨m, h_g_eq⟩ := hd_dvd_g
    have h_s_g : sigma 1 g - g >= m := by
      have hm_pos : 0 < m := by
        by_contra h_zero
        have : m = 0 := by omega
        subst this
        omega
      have hm_div : m ∣ g := ⟨d, by rw [h_g_eq, Nat.mul_comm]⟩
      have hm_mem : m ∈ g.divisors := Nat.mem_divisors.mpr ⟨hm_div, hg.ne'⟩
      have hm_ne_g : m ≠ g := by
        intro h_eq
        rw [h_eq] at h_g_eq
        have hd1 : 1 = d := (Nat.mul_right_inj hg.ne').mp (by rw [mul_one, Nat.mul_comm, ← h_g_eq])
        omega
      have h_sum : ∑ x ∈ g.divisors, x >= g + m := by
        let S : Finset ℕ := {m, g}
        have hS : S ⊆ g.divisors := by
          intro x hx
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hm_mem
          · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hg.ne'⟩
        have h_sum' : (∑ x ∈ S, x) <= ∑ x ∈ g.divisors, x := Finset.sum_le_sum_of_subset hS
        have h_S_sum : ∑ x ∈ S, x = g + m := by
          dsimp [S]
          rw [Finset.sum_insert, Finset.sum_singleton]
          · omega
          · simp only [Finset.mem_singleton]
            exact hm_ne_g
        rw [h_S_sum] at h_sum'
        exact h_sum'
      rw [sigma_apply]
      simp only [pow_one]
      omega
    have h_bound := s_g_bound hg hd h_eq
    have : d * m <= d * (sigma 1 g - g) := Nat.mul_le_mul_left d h_s_g
    have : g <= d * (sigma 1 g - g) := by omega
    have h_d_le : d <= 630 := by
      by_contra h_gt'
      have h_gt' : d > 630 := by omega
      have h_mul_lt : 630 * m < d * m := by
        nlinarith
      omega
    omega
  have h_sig_g_d : sigma 1 (g * d) = sigma 1 g * (d + 1) := by
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.isMultiplicative_sigma h_coprime]
    have h_sig_d : sigma 1 d = d + 1 := by
      rw [sigma_apply]
      simp [hd_prime]
    rw [h_sig_d]
  have h_eq' : sigma 1 g * (d + 1) = g * (d + 630) := by rw [← h_sig_g_d, h_eq]
  have h_sub_eq : (sigma 1 g - g) * (d + 1) = 629 * g := by
    have h_sub_mul : (sigma 1 g - g) * (d + 1) = sigma 1 g * (d + 1) - g * (d + 1) := by
      rw [Nat.sub_mul]
    rw [h_sub_mul, h_eq']
    have h_add : g * (d + 630) = g * d + 630 * g := by ring
    have h_add2 : g * (d + 1) = g * d + g := by ring
    rw [h_add, h_add2]
    rw [Nat.add_sub_add_left]
    omega
  by_cases hg1 : g = 1
  · subst hg1
    simp at h_sub_eq
  · have hg_even : Even g := by
      by_contra h_odd
      have hg_odd : Odd g := Nat.not_even_iff_odd.mp h_odd
      have h_odd' : Odd (629 * g) := Odd.mul (by decide) hg_odd
      have h_even : Even ((sigma 1 g - g) * (d + 1)) := by
        obtain ⟨k, hk⟩ := hd1_even
        use (sigma 1 g - g) * k
        rw [hk]
        ring
      rw [h_sub_eq] at h_even
      omega
    have h_s_g_even : sigma 1 g - g >= g / 2 := by
      have h_dvd : 2 ∣ g := even_iff_two_dvd.mp hg_even
      let m := g / 2
      have h_g_eq : g = 2 * m := (Nat.mul_div_cancel' h_dvd).symm
      have hm_pos : 0 < m := by omega
      have hm_div : m ∣ g := ⟨2, by omega⟩
      have hm_mem : m ∈ g.divisors := Nat.mem_divisors.mpr ⟨hm_div, hg.ne'⟩
      have hm_ne_g : m ≠ g := by omega
      have h_sum : ∑ x ∈ g.divisors, x >= g + m := by
        let S : Finset ℕ := {m, g}
        have hS : S ⊆ g.divisors := by
          intro x hx
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hm_mem
          · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hg.ne'⟩
        have h_sum' : (∑ x ∈ S, x) <= ∑ x ∈ g.divisors, x := Finset.sum_le_sum_of_subset hS
        have h_S_sum : ∑ x ∈ S, x = g + m := by
          dsimp [S]
          rw [Finset.sum_insert, Finset.sum_singleton]
          · omega
          · simp only [Finset.mem_singleton]
            exact hm_ne_g
        rw [h_S_sum] at h_sum'
        exact h_sum'
      rw [sigma_apply]
      simp only [pow_one]
      omega
    have h_bound := s_g_bound hg hd h_eq
    have h_g_eq : g = 2 * (g / 2) := (Nat.mul_div_cancel' (even_iff_two_dvd.mp hg_even)).symm
    have : d * (g / 2) <= d * (sigma 1 g - g) := Nat.mul_le_mul_left d h_s_g_even
    have h_d_le : d <= 1260 := by
      by_contra h_gt'
      have h_gt' : d > 1260 := by omega
      have ⟨k, hk⟩ : ∃ k, g = 2 * k := even_iff_two_dvd.mp hg_even
      have h_mul_lt : 630 * g < d * (g / 2) := by
        rw [hk]
        have : (2 * k) / 2 = k := by
          rw [Nat.mul_comm, Nat.mul_div_cancel _ (by decide)]
        rw [this]
        nlinarith
      omega
    omega

lemma d_le_395641 {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (h_eq : sigma 1 (g * d) = g * (d + 630)) (h_gcd : g = Nat.gcd (sigma 1 (g * d)) (g * d)) : d <= 395641 := by
  by_cases hd_prime : Nat.Prime d
  · by_cases h_le : d <= 395641
    · exact h_le
    · have h_gt : d > 395641 := by omega
      have h_not := not_prime_d hg hd h_eq h_gcd h_gt
      exact (h_not hd_prime).elim
  · by_cases hd1 : d = 1
    · subst hd1
      omega
    · have hd2 : 2 <= d := by omega
      have h_sigma : sigma 1 d <= d + 630 := s_d_le_630 g d hg hd h_eq
      exact d_le_395641_of_composite hd_prime hd2 h_sigma


def sqrt_fast_aux (guess : ℕ) (n : ℕ) : ℕ :=
  match guess with
  | 0 => 0
  | g + 1 =>
    if (g + 1) * (g + 1) <= n then g + 1
    else sqrt_fast_aux g n

def sqrt_fast (n : ℕ) : ℕ :=
  sqrt_fast_aux 630 n

def sum_divisors_aux (n : ℕ) (i : ℕ) (acc : ℕ) : ℕ :=
  match i with
  | 0 => acc
  | i' + 1 =>
    if n % (i' + 1) == 0 then
      let d1 := i' + 1
      let d2 := n / d1
      if d1 == d2 then sum_divisors_aux n i' (acc + d1)
      else sum_divisors_aux n i' (acc + d1 + d2)
    else sum_divisors_aux n i' acc

def sigma_fast (n : ℕ) : ℕ :=
  sum_divisors_aux n (sqrt_fast n) 0

def is_prime_fast_aux (n : ℕ) (limit : ℕ) : Bool :=
  match limit with
  | 0 => true
  | i + 1 =>
    if i + 1 == 1 then true
    else if n % (i + 1) == 0 then false
    else is_prime_fast_aux n i

def is_prime_fast (n : ℕ) : Bool :=
  if n <= 1 then false
  else is_prime_fast_aux n (sqrt_fast n)

def has_sol_g (d : ℕ) (g : ℕ) : Bool :=
  match g with
  | 0 => false
  | g' + 1 =>
    if sigma_fast ((g' + 1) * d) == (g' + 1) * (d + 630) then true
    else has_sol_g d g'

def check_fast (d : ℕ) : Bool :=
  if d % 2 == 0 || d % 3 == 0 || d % 5 == 0 || d % 7 == 0 then true
  else if is_prime_fast d then true
  else if has_sol_g d 5 then false
  else true

def check_bin (fuel : ℕ) (lo hi : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    if lo >= hi then true
    else if lo + 1 = hi then
      check_fast lo
    else
      let mid := lo + (hi - lo) / 2
      check_bin fuel' lo mid && check_bin fuel' mid hi

theorem node_16_2_24729 : check_bin 16 2 24729 = true := by decide

theorem node_16_24729_49457 : check_bin 16 24729 49457 = true := by decide

theorem node_16_49457_74184 : check_bin 16 49457 74184 = true := by decide

theorem node_16_74184_98912 : check_bin 16 74184 98912 = true := by decide

theorem node_16_98912_123639 : check_bin 16 98912 123639 = true := by decide

theorem node_16_123639_148367 : check_bin 16 123639 148367 = true := by decide

theorem node_16_148367_173094 : check_bin 16 148367 173094 = true := by decide

theorem node_16_173094_197822 : check_bin 16 173094 197822 = true := by decide

theorem node_16_197822_222549 : check_bin 16 197822 222549 = true := by decide

theorem node_16_222549_247277 : check_bin 16 222549 247277 = true := by decide

theorem node_16_247277_272004 : check_bin 16 247277 272004 = true := by decide

theorem node_16_272004_296732 : check_bin 16 272004 296732 = true := by decide

theorem node_16_296732_321459 : check_bin 16 296732 321459 = true := by decide

theorem node_16_321459_346187 : check_bin 16 321459 346187 = true := by decide

theorem node_16_346187_370914 : check_bin 16 346187 370914 = true := by decide

theorem node_16_370914_395642 : check_bin 16 370914 395642 = true := by decide

theorem node_17_2_49457 : check_bin 17 2 49457 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_2_24729, node_16_24729_49457]
  rfl

theorem node_17_49457_98912 : check_bin 17 49457 98912 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_49457_74184, node_16_74184_98912]
  rfl

theorem node_17_98912_148367 : check_bin 17 98912 148367 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_98912_123639, node_16_123639_148367]
  rfl

theorem node_17_148367_197822 : check_bin 17 148367 197822 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_148367_173094, node_16_173094_197822]
  rfl

theorem node_17_197822_247277 : check_bin 17 197822 247277 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_197822_222549, node_16_222549_247277]
  rfl

theorem node_17_247277_296732 : check_bin 17 247277 296732 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_247277_272004, node_16_272004_296732]
  rfl

theorem node_17_296732_346187 : check_bin 17 296732 346187 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_296732_321459, node_16_321459_346187]
  rfl

theorem node_17_346187_395642 : check_bin 17 346187 395642 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_16_346187_370914, node_16_370914_395642]
  rfl

theorem node_18_2_98912 : check_bin 18 2 98912 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_17_2_49457, node_17_49457_98912]
  rfl

theorem node_18_98912_197822 : check_bin 18 98912 197822 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_17_98912_148367, node_17_148367_197822]
  rfl

theorem node_18_197822_296732 : check_bin 18 197822 296732 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_17_197822_247277, node_17_247277_296732]
  rfl

theorem node_18_296732_395642 : check_bin 18 296732 395642 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_17_296732_346187, node_17_346187_395642]
  rfl

theorem node_19_2_197822 : check_bin 19 2 197822 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_18_2_98912, node_18_98912_197822]
  rfl

theorem node_19_197822_395642 : check_bin 19 197822 395642 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_18_197822_296732, node_18_296732_395642]
  rfl

theorem node_20_2_395642 : check_bin 20 2 395642 = true := by
  dsimp [check_bin]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [node_19_2_197822, node_19_197822_395642]
  rfl


theorem oeis_243512_conjecture_0.disproof : ¬ (∀ n, a n ≠ 0) := by
  intro h
  have h_630 := h 630
  rw [a_ne_zero_iff_local] at h_630
  obtain ⟨i, hi_pos, hi_val⟩ := h_630
  have h_d_le : i / (sigma 1 i).gcd i <= 395641 := by
    have h_comp : A243473_val_computable i = 630 := by
      rw [A243473_val_computable_eq i hi_pos]
      exact hi_val
    dsimp [A243473_val_computable] at h_comp
    split_ifs at h_comp with hi_zero
    · contradiction
    · rw [sigma_computable_eq_sigma_one] at h_comp
      let g := (sigma 1 i).gcd i
      let d := i / g
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (sigma 1 i) hi_pos
      have hd_pos : 0 < d := by
        have h_div : g ∣ i := Nat.gcd_dvd_right (sigma 1 i) i
        exact Nat.div_pos (Nat.le_of_dvd hi_pos h_div) hg_pos
      have h_eq : sigma 1 (g * d) = g * (d + 630) := by
        have h_div : g ∣ (sigma 1 i - i) := Nat.dvd_sub' (Nat.gcd_dvd_left (sigma 1 i) i) (Nat.gcd_dvd_right (sigma 1 i) i)
        have h_div_cancel := Nat.div_mul_cancel h_div
        have h_mul_gcd : (sigma 1 i - i) / g * g = sigma 1 i - i := h_div_cancel
        rw [h_comp] at h_mul_gcd
        have h_sigma_eq : sigma 1 i = i + 630 * g := by
          omega
        have h_i_eq : i = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right (sigma 1 i) i)).symm
        rw [← h_i_eq]
        rw [h_sigma_eq]
        ring
      have h_gcd : g = Nat.gcd (sigma 1 (g * d)) (g * d) := by
        have h_i_eq : i = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right (sigma 1 i) i)).symm
        rw [← h_i_eq]
      exact d_le_395641 hg_pos hd_pos h_eq h_gcd

  let g := (sigma 1 i).gcd i
  let d := i / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (sigma 1 i) hi_pos
  have hd_pos : 0 < d := by
    have h_div : g ∣ i := Nat.gcd_dvd_right (sigma 1 i) i
    exact Nat.div_pos (Nat.le_of_dvd hi_pos h_div) hg_pos
  have h_eq : sigma 1 (g * d) = g * (d + 630) := by
    have h_comp : A243473_val_computable i = 630 := by
      rw [A243473_val_computable_eq i hi_pos]
      exact hi_val
    dsimp [A243473_val_computable] at h_comp
    split_ifs at h_comp with hi_zero
    · contradiction
    · rw [sigma_computable_eq_sigma_one] at h_comp
      have h_div : g ∣ (sigma 1 i - i) := Nat.dvd_sub' (Nat.gcd_dvd_left (sigma 1 i) i) (Nat.gcd_dvd_right (sigma 1 i) i)
      have h_div_cancel := Nat.div_mul_cancel h_div
      have h_mul_gcd : (sigma 1 i - i) / g * g = sigma 1 i - i := h_div_cancel
      rw [h_comp] at h_mul_gcd
      have h_sigma_eq : sigma 1 i = i + 630 * g := by
        omega
      have h_i_eq : i = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right (sigma 1 i) i)).symm
      rw [← h_i_eq]
      rw [h_sigma_eq]
      ring

  have h_gcd : g = Nat.gcd (sigma 1 (g * d)) (g * d) := by
    have h_i_eq : i = g * d := (Nat.mul_div_cancel' (Nat.gcd_dvd_right (sigma 1 i) i)).symm
    rw [← h_i_eq]

  -- Since check_bin 20 2 395642 = true, we can show that check_fast d = true
  have h_tree := node_20_2_395642
  -- now we can prove a contradiction...
  sorry
