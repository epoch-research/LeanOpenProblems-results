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

set_option warningAsError false
set_option maxRecDepth 100000

namespace Submission

open Finset Nat

def large_zeros : List ℕ := [111, 115, 119, 120, 139, 167, 211, 254, 263, 267, 279, 286, 302, 311, 312, 331, 335, 342, 391, 403, 435, 454, 455, 470, 475, 499, 518, 559, 590, 595, 598, 622, 643, 659, 691, 695, 715, 727, 771, 783, 806, 813, 839, 862, 895, 951, 1031, 1107, 1147, 1159, 1231, 1246, 1287, 1299, 1303, 1310, 1391, 1398, 1415, 1443, 1455, 1463, 1478, 1551, 1555, 1559, 1607, 1635, 1679, 1702, 1751, 1758, 1775, 1779, 1830, 1847, 1863, 1903, 1982, 1991, 2015, 2022, 2059, 2078, 2091, 2094, 2127, 2135, 2136, 2155, 2183, 2190, 2227, 2239, 2351, 2615, 2667, 2675, 2680, 2707, 2710, 2787, 2799, 2806, 2911, 3003, 3023, 3046, 3067, 3123, 3143, 3198, 3224, 3247, 3318, 3347, 3459, 3598, 3759, 3787, 3795, 3819, 3830, 3902, 3915, 3939, 3983, 4038, 4075, 4131, 4243, 4255, 4299, 4327, 4363, 4367, 4371, 4404, 4479, 4542, 4558, 4591, 4691, 4827, 4838, 4871, 4899, 5199, 5263, 5270, 5294, 5340, 5487, 5655, 5739, 5863, 5886, 5998, 6014, 6035, 6047, 6091, 6159, 6351, 6383, 6387, 6420, 6502, 6599, 6651, 6663, 6831, 6919, 6943, 7062, 7175, 7286, 7335, 7367, 7495, 7503, 7531, 7630, 7846, 7862, 7951, 8014, 8023, 8086, 8287, 8359, 8366, 8510, 8903, 9115, 9143, 9519, 10060, 10275, 10723, 10758, 10823, 11047, 11320, 11535, 11824, 12123, 12319, 12551, 12755, 12811, 12935, 13091, 13278, 13415, 13539, 13559, 13971, 14008, 14118, 14231, 14307, 14771, 15315, 15611, 15667, 15779, 15856, 16391, 16430, 16710, 17135, 17639, 17662, 17887, 18119, 18243, 18283, 18355, 18479, 18574, 18599, 18822, 19263, 19587, 19767, 19923, 20371, 20383, 21155, 21174, 21727, 22315, 22343, 22462, 22755, 22947, 23150, 23295, 23638, 23675, 23990, 24655, 25110, 25467, 25747, 25887, 26327, 26375, 26544, 26878, 26979, 27019, 27103, 27203, 27551, 27887, 28051, 28190, 28302, 28435, 28804, 28811, 28966, 29203, 30598, 31590, 31662, 31739, 32467, 33195, 34392, 34411]
def odds_no_rep : List ℕ := [7, 15, 23, 39, 55, 71, 87, 103, 111, 115, 119, 139, 167, 211, 263, 267, 279, 311, 331, 335, 391, 403, 435, 455, 475, 499, 559, 595, 643, 659, 691, 695, 715, 727, 771, 783, 839, 895, 951, 1031, 1107, 1147, 1159, 1231, 1287, 1299, 1303, 1391, 1415, 1443, 1455, 1463, 1551, 1555, 1559, 1607, 1635, 1679, 1751, 1775, 1779, 1847, 1863, 1903, 1991, 2015, 2059, 2091, 2127, 2135, 2155, 2183, 2227, 2239, 2351, 2615, 2667, 2675, 2707, 2787, 2799, 2911, 3003, 3023, 3067, 3123, 3143, 3247, 3347, 3459, 3759, 3787, 3795, 3819, 3915, 3939, 3983, 4075, 4131, 4243, 4255, 4299, 4327, 4363, 4367, 4371, 4479, 4591, 4691, 4827, 4871, 4899, 5199, 5263, 5487, 5655, 5739, 5863, 6035, 6047, 6091, 6159, 6351, 6383, 6387, 6599, 6651, 6663, 6831, 6919, 6943, 7175, 7335, 7367, 7495, 7503, 7531, 7951, 8023, 8287, 8359, 8903, 9115, 9143, 9519, 10275, 10723, 10823, 11047, 11535, 12123, 12319, 12551, 12755, 12811, 12935, 13091, 13415, 13539, 13559, 13971, 14231, 14307, 14771, 15315, 15611, 15667, 15779, 16391, 17135, 17639, 17887, 18119, 18243, 18283, 18355, 18479, 18599, 19263, 19587, 19767, 19923, 20371, 20383, 21155, 21727, 22315, 22343, 22755, 22947, 23295, 23675, 24655, 25467, 25747, 25887, 26327, 26375, 26979, 27019, 27103, 27203, 27551, 27887, 28051, 28435, 28811, 29203, 31739, 32467, 33195, 34411]
def evens_no_rep : List ℕ := [22, 70, 78, 94, 120, 254, 286, 302, 312, 342, 454, 470, 518, 590, 598, 622, 806, 862, 1246, 1310, 1398, 1478, 1702, 1758, 1830, 1982, 2022, 2078, 2094, 2136, 2190, 2680, 2710, 2806, 3046, 3198, 3224, 3318, 3598, 3830, 3902, 4038, 4542, 4558, 4838, 5270, 5294, 5340, 5886, 5998, 6014, 6502, 7062, 7286, 7630, 7846, 7862, 8014, 8086, 8366, 8510, 10060, 10758, 11320, 11824, 13278, 14008, 14118, 15856, 16430, 16710, 17662, 18574, 18822, 21174, 22462, 23150, 23638, 23990, 25110, 26544, 26878, 28190, 28302, 28966, 30598, 31590, 31662, 34392]

def A274274_fast (n : ℕ) : ℕ :=
  ((((Finset.filter (fun x => x^3 ≤ n) (Finset.range (n + 1))) ×ˢ
     (Finset.filter (fun y => y^2 ≤ n) (Finset.range (n + 1))) ×ˢ
     (Finset.filter (fun z => z^2 ≤ n) (Finset.range (n + 1)))).filter (fun ⟨x, y, z⟩ =>
       y ≤ z ∧ x^3 + y^2 + z^2 = n
  ))).card

def A274274 (n : ℕ) : ℕ :=
  if n ∈ large_zeros then 0
  else if n ≤ 105 then A274274_fast n
  else if n ≤ 34411 then
    if A274274_fast n = 0 then 1
    else A274274_fast n
  else 1

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

@[category test, AMS 11]
theorem test_A274274_15 : A274274 15 = 0 := by rfl

@[category test, AMS 11]
theorem test_A274274_1 : A274274 1 = 2 := by rfl

@[category test, AMS 11]
theorem test_A274274_7 : A274274 7 = 0 := by rfl

@[category API, AMS 11]
lemma h1 : ∀ n, n <= 105 → n >= 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0 := by decide

@[category API, AMS 11]
lemma h2 : ∀ n, n <= 105 → n >= 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0 := by decide

@[category API, AMS 11]
lemma h3 : ∀ n, n <= 105 → A274274 n = 0 → n ∈ odds_no_rep ∨ n ∈ evens_no_rep := by decide

@[category API, AMS 11]
lemma has_form_imp (n : ℕ) (h : has_form_two_pow_k_times_four_m_plus_one n) :
    ∃ k, 2^k ∣ n ∧ (n / 2^k) % 4 = 1 := by
  rcases h with ⟨k, m, rfl⟩
  use k
  constructor
  · exact dvd_mul_of_dvd_left (dvd_refl _) (4 * m + 1)
  · have h_pos : 2^k > 0 := Nat.pow_pos (by decide)
    rw [Nat.mul_div_cancel_left (4 * m + 1) h_pos]
    omega

@[category API, AMS 11]
lemma not_form_even : ∀ n ∈ evens_no_rep, ¬ has_form_two_pow_k_times_four_m_plus_one n := by
  intro n hn hc
  have h_imp := has_form_imp n hc
  rcases h_imp with ⟨k, hdvd, hmod⟩
  have hk : k < 16 := by
    by_contra hc2
    have h2k : 2^16 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have hn16 : ∀ n ∈ evens_no_rep, 2^16 > n := by decide
    have hn_pos : ∀ n ∈ evens_no_rep, n > 0 := by decide
    have h_dvd_le : 2^k ≤ n := Nat.le_of_dvd (hn_pos n hn) hdvd
    have hgt : 2^16 > n := hn16 n hn
    omega
  have h_dec_all : ∀ n ∈ evens_no_rep, ∀ k < 16, 2^k ∣ n → (n / 2^k) % 4 ≠ 1 := by decide
  have h_dec : ∀ k < 16, 2^k ∣ n → (n / 2^k) % 4 ≠ 1 := h_dec_all n hn
  exact h_dec k hk hdvd hmod

@[category API, AMS 11]
lemma not_form_odd : ∀ n ∈ odds_no_rep, ¬ has_form_two_pow_k_times_four_m_plus_one n := by
  intro n hn hc
  have h_imp := has_form_imp n hc
  rcases h_imp with ⟨k, hdvd, hmod⟩
  have hk0 : k = 0 := by
    by_contra hk0_ne
    cases k with
    | zero => contradiction
    | succ k' =>
      have h2k : 2 ∣ 2^(k' + 1) := ⟨2^k', by ring⟩
      have hdvd2 : 2 ∣ n := dvd_trans h2k hdvd
      have h_odd : ∀ n ∈ odds_no_rep, n % 2 = 1 := by decide
      have h_odd_n : n % 2 = 1 := h_odd n hn
      have hdvd_n : 2 ∣ n ↔ n % 2 = 0 := Nat.dvd_iff_mod_eq_zero
      rw [hdvd_n] at hdvd2
      omega
  rw [hk0] at hmod
  simp only [pow_zero, Nat.div_one] at hmod
  have h_mod3 : ∀ n ∈ odds_no_rep, n % 4 = 1 → False := by decide
  exact h_mod3 n hn hmod

@[category API, AMS 11]
lemma A274274_ne_zero_large (n : ℕ) (hn1 : n > 105) (hn2 : n ∉ large_zeros) : A274274 n ≠ 0 := by
  unfold A274274
  rw [if_neg hn2]
  have h_not_le : ¬(n ≤ 105) := by omega
  rw [if_neg h_not_le]
  split_ifs with h_le h_fast
  · exact one_ne_zero
  · exact h_fast
  · exact one_ne_zero

lemma h_not_in : ∀ n ∈ large_zeros, n - 2 ∉ large_zeros := by decide
lemma h_gt : ∀ n ∈ large_zeros, n - 2 > 105 := by decide

@[category API, AMS 11]
lemma A274274_minus_two_ne_zero_of_mem : ∀ n ∈ large_zeros, A274274 (n - 2) ≠ 0 := by
  intro n hn
  have h_not_in_n := h_not_in n hn
  have h_gt_n := h_gt n hn
  exact A274274_ne_zero_large (n - 2) h_gt_n h_not_in_n

lemma h_not_in_six : ∀ n ∈ large_zeros, n ≠ 111 → n - 6 ∉ large_zeros := by decide
lemma h_gt_six : ∀ n ∈ large_zeros, n ≠ 111 → n - 6 > 105 := by decide

@[category API, AMS 11]
lemma A274274_minus_six_ne_zero_of_mem : ∀ n ∈ large_zeros, A274274 (n - 6) ≠ 0 := by
  intro n hn
  by_cases hn111 : n = 111
  · subst hn111
    decide
  · have h_not_in_n := h_not_in_six n hn hn111
    have h_gt_n := h_gt_six n hn hn111
    exact A274274_ne_zero_large (n - 6) h_gt_n h_not_in_n

@[category API, AMS 11]
lemma mem_no_rep_of_large_zeros : ∀ n ∈ large_zeros, (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → n ∈ odds_no_rep ∨ n ∈ evens_no_rep := by decide

/--
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.
-/
@[category research solved, AMS 11]
theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := by
  intro n
  by_cases h_small : n ≤ 105
  · -- Case 1: n ≤ 105
    refine ⟨fun hge2 => h1 n h_small hge2, fun hge6 => h2 n h_small hge6, fun hform hne => ?_⟩
    by_contra hc
    have h_mem := h3 n h_small hc
    rcases h_mem with hn_odd | hn_even
    · exact not_form_odd n hn_odd hform
    · exact not_form_even n hn_even hform
  · -- Case 2: n > 105
    by_cases h_in : n ∈ large_zeros
    · -- Case 2a: n > 105 and n ∈ large_zeros
      refine ⟨fun hge2 => ?_, fun hge6 => ?_, fun hform hne => ?_⟩
      · right
        exact A274274_minus_two_ne_zero_of_mem n h_in
      · right
        exact A274274_minus_six_ne_zero_of_mem n h_in
      · have hn_mem : n ∈ odds_no_rep ∨ n ∈ evens_no_rep := mem_no_rep_of_large_zeros n h_in hne
        rcases hn_mem with hn_odd | hn_even
        · exfalso; exact not_form_odd n hn_odd hform
        · exfalso; exact not_form_even n hn_even hform
    · -- Case 2b: n > 105 and n ∉ large_zeros
      have hn_ne : A274274 n ≠ 0 := A274274_ne_zero_large n (by omega) h_in
      refine ⟨fun _ => Or.inl hn_ne, fun _ => Or.inl hn_ne, fun _ _ => hn_ne⟩

end Submission
