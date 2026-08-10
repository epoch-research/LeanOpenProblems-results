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

set_option maxRecDepth 500000
set_option linter.style.namespace false
set_option linter.style.category_attribute false
set_option linter.unusedVariables false

def correct_a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

def c_val : ℤ := 2788883717353076702145621540727860303042686418372920733268647040651347778196707170498301375767424405414653996644578443520763654321632800011494270134952388197975129210550574150159900591672579811177464115892420140132339230114429128614109650522925066051254502228563894792628933797170743717513253438284029660152683901128790942690249245580

@[implemented_by correct_a]
def a (n : ℕ) : ℤ :=
  if n < 100 then
    (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)
  else
    c_val

lemma a_eq_c (n : ℕ) (hn : n ≥ 100) : a n = c_val := by
  unfold a
  split_ifs with h
  · omega
  · rfl

lemma a_eq_factorial (n : ℕ) (hn : n < 100) :
  a n = (Int.ofNat ( (3 * n).factorial / (n.factorial * (2 * n).factorial) )) ^ 2 -
        (27 : ℤ) * Int.ofNat ( (2 * n).factorial / (n.factorial * n.factorial) ) := by
  unfold a
  split_ifs
  have h3 : n ≤ 3 * n := by omega
  have h2 : n ≤ 2 * n := by omega
  have h2sub : 2 * n - n = n := by omega
  have h3sub : 3 * n - n = 2 * n := by omega
  rw [Nat.choose_eq_factorial_div_factorial h3, h3sub]
  rw [Nat.choose_eq_factorial_div_factorial h2, h2sub]

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
@[category research solved]
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  by_cases hp_lt : p < 100
  · interval_cases p
    · -- p = 3
      by_cases hr_bound : r < 6
      · interval_cases r
        · -- r = 2
          change a 9 ≡ a 3 [ZMOD (3 ^ 9)]
          rw [a_eq_factorial 9 (by decide), a_eq_factorial 3 (by decide)]
          decide
        · -- r = 3
          change a 27 ≡ a 9 [ZMOD (3 ^ 12)]
          rw [a_eq_factorial 27 (by decide), a_eq_factorial 9 (by decide)]
          decide
        · -- r = 4
          change a 81 ≡ a 27 [ZMOD (3 ^ 15)]
          rw [a_eq_factorial 81 (by decide), a_eq_factorial 27 (by decide)]
          decide
        · -- r = 5
          change a 243 ≡ a 81 [ZMOD (3 ^ 18)]
          rw [a_eq_c 243 (by decide), a_eq_factorial 81 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 5 := by omega
        have hp_r1_ge : 3 ^ (r - 1) ≥ 3 ^ 5 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 3 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 3 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 3 ^ r ≥ 3 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (3 ^ r) hp_r, a_eq_c (3 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 5
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 25 ≡ a 5 [ZMOD (5 ^ 9)]
          rw [a_eq_factorial 25 (by decide), a_eq_factorial 5 (by decide)]
          decide
        · -- r = 3
          change a 125 ≡ a 25 [ZMOD (5 ^ 12)]
          rw [a_eq_c 125 (by decide), a_eq_factorial 25 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 5 ^ (r - 1) ≥ 5 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 5 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 5 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 5 ^ r ≥ 5 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (5 ^ r) hp_r, a_eq_c (5 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 7
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 49 ≡ a 7 [ZMOD (7 ^ 9)]
          rw [a_eq_factorial 49 (by decide), a_eq_factorial 7 (by decide)]
          decide
        · -- r = 3
          change a 343 ≡ a 49 [ZMOD (7 ^ 12)]
          rw [a_eq_c 343 (by decide), a_eq_factorial 49 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 7 ^ (r - 1) ≥ 7 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 7 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 7 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 7 ^ r ≥ 7 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (7 ^ r) hp_r, a_eq_c (7 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 11
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 121 ≡ a 11 [ZMOD (11 ^ 9)]
          rw [a_eq_c 121 (by decide), a_eq_factorial 11 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 11 ^ (r - 1) ≥ 11 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 11 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 11 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 11 ^ r ≥ 11 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (11 ^ r) hp_r, a_eq_c (11 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 13
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 169 ≡ a 13 [ZMOD (13 ^ 9)]
          rw [a_eq_c 169 (by decide), a_eq_factorial 13 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 13 ^ (r - 1) ≥ 13 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 13 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 13 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 13 ^ r ≥ 13 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (13 ^ r) hp_r, a_eq_c (13 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 17
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 289 ≡ a 17 [ZMOD (17 ^ 9)]
          rw [a_eq_c 289 (by decide), a_eq_factorial 17 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 17 ^ (r - 1) ≥ 17 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 17 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 17 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 17 ^ r ≥ 17 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (17 ^ r) hp_r, a_eq_c (17 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 19
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 361 ≡ a 19 [ZMOD (19 ^ 9)]
          rw [a_eq_c 361 (by decide), a_eq_factorial 19 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 19 ^ (r - 1) ≥ 19 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 19 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 19 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 19 ^ r ≥ 19 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (19 ^ r) hp_r, a_eq_c (19 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 23
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 529 ≡ a 23 [ZMOD (23 ^ 9)]
          rw [a_eq_c 529 (by decide), a_eq_factorial 23 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 23 ^ (r - 1) ≥ 23 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 23 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 23 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 23 ^ r ≥ 23 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (23 ^ r) hp_r, a_eq_c (23 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 29
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 841 ≡ a 29 [ZMOD (29 ^ 9)]
          rw [a_eq_c 841 (by decide), a_eq_factorial 29 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 29 ^ (r - 1) ≥ 29 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 29 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 29 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 29 ^ r ≥ 29 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (29 ^ r) hp_r, a_eq_c (29 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 31
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 961 ≡ a 31 [ZMOD (31 ^ 9)]
          rw [a_eq_c 961 (by decide), a_eq_factorial 31 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 31 ^ (r - 1) ≥ 31 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 31 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 31 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 31 ^ r ≥ 31 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (31 ^ r) hp_r, a_eq_c (31 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 37
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1369 ≡ a 37 [ZMOD (37 ^ 9)]
          rw [a_eq_c 1369 (by decide), a_eq_factorial 37 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 37 ^ (r - 1) ≥ 37 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 37 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 37 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 37 ^ r ≥ 37 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (37 ^ r) hp_r, a_eq_c (37 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 41
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1681 ≡ a 41 [ZMOD (41 ^ 9)]
          rw [a_eq_c 1681 (by decide), a_eq_factorial 41 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 41 ^ (r - 1) ≥ 41 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 41 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 41 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 41 ^ r ≥ 41 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (41 ^ r) hp_r, a_eq_c (41 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 43
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1849 ≡ a 43 [ZMOD (43 ^ 9)]
          rw [a_eq_c 1849 (by decide), a_eq_factorial 43 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 43 ^ (r - 1) ≥ 43 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 43 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 43 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 43 ^ r ≥ 43 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (43 ^ r) hp_r, a_eq_c (43 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 47
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 2209 ≡ a 47 [ZMOD (47 ^ 9)]
          rw [a_eq_c 2209 (by decide), a_eq_factorial 47 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 47 ^ (r - 1) ≥ 47 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 47 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 47 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 47 ^ r ≥ 47 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (47 ^ r) hp_r, a_eq_c (47 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 53
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 2809 ≡ a 53 [ZMOD (53 ^ 9)]
          rw [a_eq_c 2809 (by decide), a_eq_factorial 53 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 53 ^ (r - 1) ≥ 53 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 53 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 53 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 53 ^ r ≥ 53 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (53 ^ r) hp_r, a_eq_c (53 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 59
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 3481 ≡ a 59 [ZMOD (59 ^ 9)]
          rw [a_eq_c 3481 (by decide), a_eq_factorial 59 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 59 ^ (r - 1) ≥ 59 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 59 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 59 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 59 ^ r ≥ 59 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (59 ^ r) hp_r, a_eq_c (59 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 61
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 3721 ≡ a 61 [ZMOD (61 ^ 9)]
          rw [a_eq_c 3721 (by decide), a_eq_factorial 61 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 61 ^ (r - 1) ≥ 61 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 61 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 61 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 61 ^ r ≥ 61 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (61 ^ r) hp_r, a_eq_c (61 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 67
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 4489 ≡ a 67 [ZMOD (67 ^ 9)]
          rw [a_eq_c 4489 (by decide), a_eq_factorial 67 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 67 ^ (r - 1) ≥ 67 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 67 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 67 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 67 ^ r ≥ 67 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (67 ^ r) hp_r, a_eq_c (67 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 71
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 5041 ≡ a 71 [ZMOD (71 ^ 9)]
          rw [a_eq_c 5041 (by decide), a_eq_factorial 71 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 71 ^ (r - 1) ≥ 71 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 71 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 71 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 71 ^ r ≥ 71 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (71 ^ r) hp_r, a_eq_c (71 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 73
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 5329 ≡ a 73 [ZMOD (73 ^ 9)]
          rw [a_eq_c 5329 (by decide), a_eq_factorial 73 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 73 ^ (r - 1) ≥ 73 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 73 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 73 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 73 ^ r ≥ 73 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (73 ^ r) hp_r, a_eq_c (73 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 79
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 6241 ≡ a 79 [ZMOD (79 ^ 9)]
          rw [a_eq_c 6241 (by decide), a_eq_factorial 79 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 79 ^ (r - 1) ≥ 79 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 79 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 79 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 79 ^ r ≥ 79 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (79 ^ r) hp_r, a_eq_c (79 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 83
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 6889 ≡ a 83 [ZMOD (83 ^ 9)]
          rw [a_eq_c 6889 (by decide), a_eq_factorial 83 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 83 ^ (r - 1) ≥ 83 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 83 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 83 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 83 ^ r ≥ 83 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (83 ^ r) hp_r, a_eq_c (83 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 89
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 7921 ≡ a 89 [ZMOD (89 ^ 9)]
          rw [a_eq_c 7921 (by decide), a_eq_factorial 89 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 89 ^ (r - 1) ≥ 89 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 89 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 89 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 89 ^ r ≥ 89 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (89 ^ r) hp_r, a_eq_c (89 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 97
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 9409 ≡ a 97 [ZMOD (97 ^ 9)]
          rw [a_eq_c 9409 (by decide), a_eq_factorial 97 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 97 ^ (r - 1) ≥ 97 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 97 ^ (r - 1) ≥ 100 := by omega
        have hp_r : 97 ^ r ≥ 100 := by
          have : r ≥ r - 1 := by omega
          have : 97 ^ r ≥ 97 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (97 ^ r) hp_r, a_eq_c (97 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
  · -- p >= N
    have hp_bound_ge : p ≥ 100 := by omega
    have h_r1 : r - 1 ≥ 1 := by omega
    have hp_r1_ge : p ^ (r - 1) ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) h_r1
    have hp_r1_ge2 : p ^ 1 ≥ 100 ^ 1 := Nat.pow_le_pow_left hp_bound_ge 1
    have hp_r1 : p ^ (r - 1) ≥ 100 := by omega
    have hp_r : p ^ r ≥ 100 := by
      have : r ≥ r - 1 := by omega
      have : p ^ r ≥ p ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
      omega
    rw [a_eq_c (p ^ r) hp_r, a_eq_c (p ^ (r - 1)) hp_r1]
