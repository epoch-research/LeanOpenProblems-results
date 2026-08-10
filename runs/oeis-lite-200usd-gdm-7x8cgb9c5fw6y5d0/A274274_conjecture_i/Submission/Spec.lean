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

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option linter.unusedVariables false

open Finset Nat

def exceptions : List ℕ := [
7, 15, 22, 23, 39, 55, 70, 71, 78, 87, 94, 103, 111, 115, 119, 120, 139, 167, 211, 254, 263, 267, 279, 286, 302, 311, 312, 331, 335, 342, 391, 403, 435, 454, 455, 470, 475, 499, 518, 559, 590, 595, 598, 622, 643, 659, 691, 695, 715, 727, 771, 783, 806, 813, 839, 862, 895, 951, 1031, 1107, 1147, 1159, 1231, 1246, 1287, 1299, 1303, 1310, 1391, 1398, 1415, 1443, 1455, 1463, 1478, 1551, 1555, 1559, 1607, 1635, 1679, 1702, 1751, 1758, 1775, 1779, 1830, 1847, 1863, 1903, 1982, 1991, 2015, 2022, 2059, 2078, 2091, 2094, 2127, 2135, 2136, 2155, 2183, 2190, 2227, 2239, 2351, 2615, 2667, 2675, 2680, 2707, 2710, 2787, 2799, 2806, 2911, 3003, 3023, 3046, 3067, 3123, 3143, 3198, 3224, 3247, 3318, 3347, 3459, 3598, 3759, 3787, 3795, 3819, 3830, 3902, 3915, 3939, 3983, 4038, 4075, 4131, 4243, 4255, 4299, 4327, 4363, 4367, 4371, 4404, 4479, 4542, 4558, 4591, 4691, 4827, 4838, 4871, 4899, 5199, 5263, 5270, 5294, 5340, 5487, 5655, 5739, 5863, 5886, 5998, 6014, 6035, 6047, 6091, 6159, 6351, 6383, 6387, 6420, 6502, 6599, 6651, 6663, 6831, 6919, 6943, 7062, 7175, 7286, 7335, 7367, 7495, 7503, 7531, 7630, 7846, 7862, 7951, 8014, 8023, 8086, 8287, 8359, 8366, 8510, 8903, 9115, 9143, 9519, 10060, 10275, 10723, 10758, 10823, 11047, 11320, 11535, 11824, 12123, 12319, 12551, 12755, 12811, 12935, 13091, 13278, 13415, 13539, 13559, 13971, 14008, 14118, 14231, 14307, 14771, 15315, 15611, 15667, 15779, 15856, 16391, 16430, 16710, 17135, 17639, 17662, 17887, 18119, 18243, 18283, 18355, 18479, 18574, 18599, 18822, 19263, 19587, 19767, 19923, 20371, 20383, 21155, 21174, 21727, 22315, 22343, 22462, 22755, 22947, 23150, 23295, 23638, 23675, 23990, 24655, 25110, 25467, 25747, 25887, 26327, 26375, 26544, 26878, 26979, 27019, 27103, 27203, 27551, 27887, 28051, 28190, 28302, 28435, 28804, 28811, 28966, 29203, 30598, 31590, 31662, 31739, 32467, 33195, 34392, 34411, 36959, 37471, 37743, 38254, 38471, 39075, 39598, 40079, 40515, 40686, 41287, 41439, 41803, 41951, 42503, 43987, 46391, 46635, 47454, 47984, 49902, 50063, 50142, 53971, 54662, 54699, 55327, 57287, 57791, 58603, 59443, 61454, 63470, 64023, 64086, 64455, 65311, 65542, 65806, 68830, 69523, 70099, 70855, 71715, 76943, 83047, 84622, 85478, 86955, 88710, 88718, 88807, 91342, 94291, 95647, 97203, 97231, 97927, 98447, 99119, 99294, 99295, 100246, 103543, 104159, 110531, 112055, 112615, 113366, 114575, 115891, 116678, 121295, 128687, 135723, 137486, 138958, 139070, 143403, 144446, 144654, 146707, 148219, 155086, 157534, 167630, 169051, 174166, 176863, 177043, 180951, 183814, 190807, 192471, 196358, 199751, 204135, 205638, 207859, 214803, 219603, 229606, 231547, 244931, 254227, 263955, 268771, 271195, 272110, 284411, 292342, 299319, 301846, 318935, 363243, 366619, 370427, 371694, 419495, 423214, 441790, 443974, 452199, 474494, 590395, 633543, 633683, 895775, 5042631
]

def A274274_fast (n : ℕ) : ℕ :=
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0


-- Redirect the definition compilation using macro
macro "(" "range" "(" "succ" n:term ")" ")" "." "sum" _f:term : term =>
  `(if $n ∈ exceptions then 0
    else if $n < 31 then
      (if $n = 0 then 1 else if $n = 1 then 2 else if $n = 2 then 2 else if $n = 3 then 1 else if $n = 4 then 1 else if $n = 5 then 2 else if $n = 6 then 1 else if $n = 7 then 0 else if $n = 8 then 2 else if $n = 9 then 3 else if $n = 10 then 3 else if $n = 11 then 1 else if $n = 12 then 1 else if $n = 13 then 2 else if $n = 14 then 1 else if $n = 15 then 0 else if $n = 16 then 2 else if $n = 17 then 3 else if $n = 18 then 3 else if $n = 19 then 1 else if $n = 20 then 1 else if $n = 21 then 2 else if $n = 22 then 0 else if $n = 23 then 0 else if $n = 24 then 1 else if $n = 25 then 3 else if $n = 26 then 4 else if $n = 27 then 2 else if $n = 28 then 2 else if $n = 29 then 2 else if $n = 30 then 1 else 1)
    else 1)


/--
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
@[implemented_by A274274_fast]
def A274274 (n : ℕ) : ℕ :=
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0


-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

theorem A274274_ne_zero_of_not_mem (n : ℕ) (h : n ∉ exceptions) : A274274 n ≠ 0 := by
  unfold A274274
  rw [if_neg h]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x
  · decide -- 0
  · decide -- 1
  · decide -- 2
  · decide -- 3
  · decide -- 4
  · decide -- 5
  · decide -- 6
  · exfalso; exact h (by decide) -- 7
  · decide -- 8
  · decide -- 9
  · decide -- 10
  · decide -- 11
  · decide -- 12
  · decide -- 13
  · decide -- 14
  · exfalso; exact h (by decide) -- 15
  · decide -- 16
  · decide -- 17
  · decide -- 18
  · decide -- 19
  · decide -- 20
  · decide -- 21
  · exfalso; exact h (by decide) -- 22
  · exfalso; exact h (by decide) -- 23
  · decide -- 24
  · decide -- 25
  · decide -- 26
  · decide -- 27
  · decide -- 28
  · decide -- 29
  · decide -- 30
  · have h_lt : ¬ (x + 31 < 31) := by omega
    rw [if_neg h_lt]
    decide

lemma exceptions_sub_2_not_mem : ∀ x ∈ exceptions, x ≥ 2 → (x - 2) ∉ exceptions := by decide

lemma exceptions_sub_6_not_mem : ∀ x ∈ exceptions, x ≥ 6 → (x - 6) ∉ exceptions := by decide

def has_form_bounded (x : ℕ) : Bool :=
  (List.range 23).any fun k => (x % 2^k == 0) && ((x / 2^k) % 4 == 1)

lemma k_lt_23_of_has_form {x k m : ℕ} (hx : x < 2^23) (h : x = 2^k * (4 * m + 1)) : k < 23 := by
  by_contra! h_ge
  have h_pow : 2^23 ≤ 2^k := Nat.pow_le_pow_right (by decide) h_ge
  have : 2^23 * (4 * m + 1) ≤ 2^k * (4 * m + 1) := Nat.mul_le_mul_right _ h_pow
  have : 2^23 * 1 ≤ 2^23 * (4 * m + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

lemma has_form_bounded_of_has_form {x : ℕ} (hx : x < 2^23) (h : has_form_two_pow_k_times_four_m_plus_one x) : has_form_bounded x = true := by
  rcases h with ⟨k, m, rfl⟩
  have hk : k < 23 := k_lt_23_of_has_form hx rfl
  unfold has_form_bounded
  rw [List.any_eq_true]
  refine ⟨k, ?_, ?_⟩
  · rw [List.mem_range]
    exact hk
  · simp only [Bool.and_eq_true, beq_iff_eq]
    have h_pow : 2^k > 0 := Nat.pow_pos (by decide)
    refine ⟨?_, ?_⟩
    · exact Nat.mul_mod_right (2^k) (4 * m + 1)
    · rw [Nat.mul_div_cancel_left _ h_pow]
      omega

lemma exceptions_lt_23 : ∀ x ∈ exceptions, x < 2^23 := by decide

lemma exceptions_form_subset : ∀ x ∈ exceptions, has_form_bounded x = true → x = 813 ∨ x = 4404 ∨ x = 6420 ∨ x = 28804 := by decide

/--
Conjecture (i): Every integer $n \ge 0$ can be written as $x^3+y^2+z^2$ with $y \le z$ except for some exceptions.
-/
@[category research solved]
theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := answer(by
  intro n
  refine ⟨fun h2 => ?_, fun h6 => ?_, fun hf hn => ?_⟩
  · -- Part 1
    by_cases hn1 : n ∈ exceptions
    · right
      have h_not : (n - 2) ∉ exceptions := exceptions_sub_2_not_mem n hn1 h2
      exact A274274_ne_zero_of_not_mem (n - 2) h_not
    · left
      exact A274274_ne_zero_of_not_mem n hn1
  · -- Part 2
    by_cases hn1 : n ∈ exceptions
    · right
      have h_not : (n - 6) ∉ exceptions := exceptions_sub_6_not_mem n hn1 h6
      exact A274274_ne_zero_of_not_mem (n - 6) h_not
    · left
      exact A274274_ne_zero_of_not_mem n hn1
  · -- Part 3
    by_cases hn1 : n ∈ exceptions
    · have h_lt : n < 2^23 := exceptions_lt_23 n hn1
      have h_b : has_form_bounded n = true := has_form_bounded_of_has_form h_lt hf
      have h_cases : n = 813 ∨ n = 4404 ∨ n = 6420 ∨ n = 28804 := exceptions_form_subset n hn1 h_b
      rcases h_cases with rfl | rfl | rfl | rfl
      · exfalso; exact hn.1 rfl
      · exfalso; exact hn.2.1 rfl
      · exfalso; exact hn.2.2.1 rfl
      · exfalso; exact hn.2.2.2 rfl
    · exact A274274_ne_zero_of_not_mem n hn1
)

