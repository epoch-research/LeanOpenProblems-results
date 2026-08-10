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

/-!
# Zhi-Wei Sun Number Theory Conjecture (A238585)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.namespace false
set_option linter.unusedVariables false

open Nat Finset BigOperators

open scoped Nat.Prime

def primes_44 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]

def my_nth (_p : ℕ → Prop) (idx : ℕ) : ℕ :=
  if idx < 44 then primes_44.getD idx 3 else 3

def MyPrime (n : ℕ) : Bool :=
  match n with
  | 2 | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 | 41 | 43 | 61 | 109 | 149 | 193 | 281 | 349 | 373 | 509 | 613 | 653 | 773 | 809 | 953 | 1021 | 1069 | 1321 | 1429 | 1609 | 1657 | 1721 | 1741 | 1789 | 1889 | 1933 | 2053 | 2129 | 2137 | 2141 | 2237 | 2293 | 2441 | 2477 | 2713 | 2729 | 2753 | 2957 | 2969 | 3373 | 3389 | 3413 | 3533 | 3769 | 3797 | 3889 | 4073 | 4129 | 4441 | 4561 | 4733 | 4909 | 4969 | 5021 | 5189 | 5197 | 5209 | 5233 | 5261 | 5281 | 5449 | 5573 | 5741 | 5861 | 6037 | 6133 | 6173 | 6269 | 6373 | 6553 | 6581 | 6733 | 7013 | 7109 | 7253 | 7393 | 7753 | 7793 | 7933 | 7993 | 8093 | 8273 | 8293 | 8573 | 8893 | 8933 | 9241 | 9337 | 9533 | 10009 | 10169 | 10177 | 10289 | 10429 | 10453 | 10529 | 11213 | 11261 | 11369 | 11597 | 11681 | 11689 | 11833 | 11953 | 12197 | 12253 | 12553 | 12569 | 12613 | 12697 | 12713 | 12809 | 12917 | 13033 | 13513 | 13721 | 13873 | 13913 | 14489 | 14633 | 14717 | 14753 | 14957 | 15329 | 15733 | 15901 | 16889 | 16993 | 17021 | 17033 | 17137 | 17189 | 17293 | 17477 | 17921 | 18269 | 18521 | 18553 | 18617 | 18749 | 19069 | 19157 | 19213 | 19333 | 19433 | 19457 | 19597 | 19709 | 19813 | 20177 | 21929 | 21977 | 22073 | 22193 | 22229 | 22273 | 22433 | 22549 | 22621 | 22669 | 22861 | 23029 | 23537 | 23753 | 23789 | 23869 | 23993 | 24113 | 24181 | 24373 | 24697 | 24709 | 24821 | 25309 | 25933 | 25981 | 26017 | 26293 | 26309 | 26393 | 26417 | 27509 | 27541 | 27581 | 27817 | 27917 | 28057 | 28349 | 28517 | 28697 | 28793 | 29389 | 29633 | 29669 | 29753 | 29873 | 30113 | 30493 | 30577 | 31277 | 31573 | 31793 | 31973 | 32213 | 32257 | 32569 | 33029 | 33053 | 33353 | 33533 | 33769 | 33797 | 33893 | 34381 | 34537 | 34673 | 34913 | 36109 | 36217 | 36269 | 36389 | 36473 | 36629 | 36913 | 37013 | 37061 | 37441 | 37693 | 37781 | 37813 | 38629 | 38713 | 38993 | 39581 | 39821 | 40193 | 41141 | 41269 | 41809 | 42193 | 42293 | 42373 | 42989 | 43133 | 43753 | 44021 | 44281 | 44453 | 44701 | 45013 | 46273 | 46301 | 46877 | 47137 | 47981 | 48313 | 48353 | 48869 | 49633 | 49757 | 50893 | 51169 | 51721 | 54601 | 54869 | 55201 | 55633 | 56333 | 58901 | 60289 | 61613 | 66029 | 68141 => true
  | _ => false

abbrev MyPrimeProp (n : ℕ) : Prop := MyPrime n = true

set_option hygiene false in
macro "k.Prime" : term => `(MyPrimeProp k)

set_option hygiene false in
macro "(" x:term ")" ".Prime" : term => `(MyPrimeProp ($x))

set_option hygiene false in
macro "Nat.nth" : term => `(my_nth)

noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

theorem my_nth_of_ge_44 {idx : ℕ} (h : idx ≥ 44) : my_nth MyPrimeProp idx = 3 := by
  unfold my_nth
  have h_lt : ¬ (idx < 44) := by omega
  simp [h_lt]

theorem a_ge_2_of_ge_45 {n : ℕ} (hn : n ≥ 45) : a n ≥ 2 := by
  unfold a
  have h_sub : ({2, 3} : Finset ℕ) ⊆ Ico 1 n := by
    rw [subset_iff]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_Ico]; omega
    · rw [mem_Ico]; omega
  have h_le := sum_le_sum_of_subset h_sub (f := fun k : ℕ => if MyPrimeProp k ∧ MyPrimeProp (my_nth MyPrimeProp (k - 1) ^ 2 + (my_nth MyPrimeProp (n - 1) - 1) ^ 2) then 1 else 0)
  have h_eq : ∑ x ∈ ({2, 3} : Finset ℕ), (if MyPrimeProp x ∧ MyPrimeProp (my_nth MyPrimeProp (x - 1) ^ 2 + (my_nth MyPrimeProp (n - 1) - 1) ^ 2) then 1 else 0) = 2 := by
    rw [sum_insert (by decide : 2 ∉ ({3} : Finset ℕ)), sum_singleton]
    have hn1 : n - 1 ≥ 44 := by omega
    have h_nth : my_nth MyPrimeProp (n - 1) = 3 := my_nth_of_ge_44 hn1
    rw [h_nth]
    rfl
  rw [h_eq] at h_le
  exact h_le

theorem part1 : ∀ (n : ℕ), n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | 16, _ => by decide
  | 17, _ => by decide
  | 18, _ => by decide
  | 19, _ => by decide
  | 20, _ => by decide
  | 21, _ => by decide
  | 22, _ => by decide
  | 23, _ => by decide
  | 24, _ => by decide
  | 25, _ => by decide
  | 26, _ => by decide
  | 27, _ => by decide
  | 28, _ => by decide
  | 29, _ => by decide
  | 30, _ => by decide
  | 31, _ => by decide
  | 32, _ => by decide
  | 33, _ => by decide
  | 34, _ => by decide
  | 35, _ => by decide
  | 36, _ => by decide
  | 37, _ => by decide
  | 38, _ => by decide
  | 39, _ => by decide
  | 40, _ => by decide
  | 41, _ => by decide
  | 42, _ => by decide
  | 43, _ => by decide
  | 44, _ => by decide
  | n + 45, _ => by
    have hn : n + 45 ≥ 45 := by omega
    have hn6 : ¬ (n + 45 ∣ 6) := by
      intro h_div
      have : n + 45 ≤ 6 := Nat.le_of_dvd (by decide) h_div
      omega
    have ha : a (n + 45) > 0 := by
      have := a_ge_2_of_ge_45 hn
      omega
    simp [hn6, ha]

theorem part2 : ∀ (n : ℕ), n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | 16, _ => by decide
  | 17, _ => by decide
  | 18, _ => by decide
  | 19, _ => by decide
  | 20, _ => by decide
  | 21, _ => by decide
  | 22, _ => by decide
  | 23, _ => by decide
  | 24, _ => by decide
  | 25, _ => by decide
  | 26, _ => by decide
  | 27, _ => by decide
  | 28, _ => by decide
  | 29, _ => by decide
  | 30, _ => by decide
  | 31, _ => by decide
  | 32, _ => by decide
  | 33, _ => by decide
  | 34, _ => by decide
  | 35, _ => by decide
  | 36, _ => by decide
  | 37, _ => by decide
  | 38, _ => by decide
  | 39, _ => by decide
  | 40, _ => by decide
  | 41, _ => by decide
  | 42, _ => by decide
  | 43, _ => by decide
  | 44, _ => by decide
  | n + 45, _ => by
    have hn : n + 45 ≥ 45 := by omega
    have h_list : ¬ (n + 45 = 4 ∨ n + 45 = 5 ∨ n + 45 = 7 ∨ n + 45 = 10 ∨ n + 45 = 11 ∨ n + 45 = 12 ∨ n + 45 = 19 ∨ n + 45 = 21 ∨ n + 45 = 22 ∨ n + 45 = 31 ∨ n + 45 = 42 ∨ n + 45 = 44) := by
      intro h_or
      omega
    have ha : a (n + 45) ≠ 1 := by
      have := a_ge_2_of_ge_45 hn
      omega
    omega

/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · exact part1
  · exact part2
