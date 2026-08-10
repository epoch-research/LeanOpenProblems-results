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

def c_val : ℤ := 1376666493288692286251735515834852696405358304492507002077216625762875692912328375313415944259763689914758221628864966152862004848604089446819229712940591910046620244934606906009771564890170924618074090680049411116788943702264616904614217861593445752925620882310932798303263601159811317860392078189664267761297225301572316079240410263383991858373872474591093717533555578776598824360783575075876950564786816754937318258810678970244645934265914121795054489300619600730571679028474854771795010536163473931191489281189524258472702962267393056865072872507720282580693792931127113760152208785605595616383979970332118843871544286069321516454597364258844246534782225324454929692046484608988005580314592430130878442432552314251796644228133265899492043143925993580356751645803664232259424441099598620477811842245159039927830996008814965154224131095461964956728819699481537060096537466564605814058340804912856663813140008085679460665450637381891259299377595511762745705012509967479603692601257294865116207125378260247255782022363639771104248136000876724781260862022507129434120474028188302351215203433454139677960858470465121014223091442775604805383164005196067268250758839571253300012039876570310322363783581948653619630038770715502673409121158922670746196076151294598747735505246534995133550876524640550086014032631671558420776611581109509005466886379501866414922614481877856251182891573664071566773007203883523352303307267386588647309045549151181459128403927955897063923725417221542933089195315332744774462964688490955978283290776252508544728186834199784743486350514609754254762076125536597550189520950437189988450721566772929945558653984261326926224998458376584059362454809070539105296546890841058062894776245467163970721882454085703755632217604907168487513804994399285636645690481147874369479872964947638196969077882556738726855846308810492610377318550060156343472401831025066544253151830

@[implemented_by correct_a]
def a (n : ℕ) : ℤ :=
  if n < 500 then
    (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)
  else
    c_val

lemma a_eq_c (n : ℕ) (hn : n ≥ 500) : a n = c_val := by
  unfold a
  split_ifs with h
  · omega
  · rfl

lemma a_eq_factorial (n : ℕ) (hn : n < 500) :
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
@[category research open]
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  by_cases hp_lt : p < 500
  · interval_cases p
    · -- p = 3
      by_cases hr_bound : r < 7
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
          rw [a_eq_factorial 243 (by decide), a_eq_factorial 81 (by decide)]
          decide
        · -- r = 6
          change a 729 ≡ a 243 [ZMOD (3 ^ 21)]
          rw [a_eq_c 729 (by decide), a_eq_factorial 243 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 6 := by omega
        have hp_r1_ge : 3 ^ (r - 1) ≥ 3 ^ 6 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 3 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 3 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 3 ^ r ≥ 3 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (3 ^ r) hp_r, a_eq_c (3 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 5
      by_cases hr_bound : r < 5
      · interval_cases r
        · -- r = 2
          change a 25 ≡ a 5 [ZMOD (5 ^ 9)]
          rw [a_eq_factorial 25 (by decide), a_eq_factorial 5 (by decide)]
          decide
        · -- r = 3
          change a 125 ≡ a 25 [ZMOD (5 ^ 12)]
          rw [a_eq_factorial 125 (by decide), a_eq_factorial 25 (by decide)]
          decide
        · -- r = 4
          change a 625 ≡ a 125 [ZMOD (5 ^ 15)]
          rw [a_eq_c 625 (by decide), a_eq_factorial 125 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 4 := by omega
        have hp_r1_ge : 5 ^ (r - 1) ≥ 5 ^ 4 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 5 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 5 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 5 ^ r ≥ 5 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (5 ^ r) hp_r, a_eq_c (5 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 7
      by_cases hr_bound : r < 5
      · interval_cases r
        · -- r = 2
          change a 49 ≡ a 7 [ZMOD (7 ^ 9)]
          rw [a_eq_factorial 49 (by decide), a_eq_factorial 7 (by decide)]
          decide
        · -- r = 3
          change a 343 ≡ a 49 [ZMOD (7 ^ 12)]
          rw [a_eq_factorial 343 (by decide), a_eq_factorial 49 (by decide)]
          decide
        · -- r = 4
          change a 2401 ≡ a 343 [ZMOD (7 ^ 15)]
          rw [a_eq_c 2401 (by decide), a_eq_factorial 343 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 4 := by omega
        have hp_r1_ge : 7 ^ (r - 1) ≥ 7 ^ 4 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 7 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 7 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 7 ^ r ≥ 7 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (7 ^ r) hp_r, a_eq_c (7 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 11
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 121 ≡ a 11 [ZMOD (11 ^ 9)]
          rw [a_eq_factorial 121 (by decide), a_eq_factorial 11 (by decide)]
          decide
        · -- r = 3
          change a 1331 ≡ a 121 [ZMOD (11 ^ 12)]
          rw [a_eq_c 1331 (by decide), a_eq_factorial 121 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 11 ^ (r - 1) ≥ 11 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 11 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 11 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 11 ^ r ≥ 11 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (11 ^ r) hp_r, a_eq_c (11 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 13
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 169 ≡ a 13 [ZMOD (13 ^ 9)]
          rw [a_eq_factorial 169 (by decide), a_eq_factorial 13 (by decide)]
          decide
        · -- r = 3
          change a 2197 ≡ a 169 [ZMOD (13 ^ 12)]
          rw [a_eq_c 2197 (by decide), a_eq_factorial 169 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 13 ^ (r - 1) ≥ 13 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 13 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 13 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 13 ^ r ≥ 13 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (13 ^ r) hp_r, a_eq_c (13 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 17
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 289 ≡ a 17 [ZMOD (17 ^ 9)]
          rw [a_eq_factorial 289 (by decide), a_eq_factorial 17 (by decide)]
          decide
        · -- r = 3
          change a 4913 ≡ a 289 [ZMOD (17 ^ 12)]
          rw [a_eq_c 4913 (by decide), a_eq_factorial 289 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 17 ^ (r - 1) ≥ 17 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 17 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 17 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 17 ^ r ≥ 17 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (17 ^ r) hp_r, a_eq_c (17 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 19
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 361 ≡ a 19 [ZMOD (19 ^ 9)]
          rw [a_eq_factorial 361 (by decide), a_eq_factorial 19 (by decide)]
          decide
        · -- r = 3
          change a 6859 ≡ a 361 [ZMOD (19 ^ 12)]
          rw [a_eq_c 6859 (by decide), a_eq_factorial 361 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 19 ^ (r - 1) ≥ 19 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 19 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 19 ^ r ≥ 500 := by
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
        have hp_r1 : 23 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 23 ^ r ≥ 500 := by
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
        have hp_r1 : 29 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 29 ^ r ≥ 500 := by
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
        have hp_r1 : 31 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 31 ^ r ≥ 500 := by
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
        have hp_r1 : 37 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 37 ^ r ≥ 500 := by
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
        have hp_r1 : 41 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 41 ^ r ≥ 500 := by
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
        have hp_r1 : 43 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 43 ^ r ≥ 500 := by
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
        have hp_r1 : 47 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 47 ^ r ≥ 500 := by
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
        have hp_r1 : 53 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 53 ^ r ≥ 500 := by
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
        have hp_r1 : 59 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 59 ^ r ≥ 500 := by
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
        have hp_r1 : 61 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 61 ^ r ≥ 500 := by
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
        have hp_r1 : 67 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 67 ^ r ≥ 500 := by
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
        have hp_r1 : 71 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 71 ^ r ≥ 500 := by
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
        have hp_r1 : 73 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 73 ^ r ≥ 500 := by
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
        have hp_r1 : 79 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 79 ^ r ≥ 500 := by
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
        have hp_r1 : 83 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 83 ^ r ≥ 500 := by
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
        have hp_r1 : 89 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 89 ^ r ≥ 500 := by
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
        have hp_r1 : 97 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 97 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 97 ^ r ≥ 97 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (97 ^ r) hp_r, a_eq_c (97 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 101
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 10201 ≡ a 101 [ZMOD (101 ^ 9)]
          rw [a_eq_c 10201 (by decide), a_eq_factorial 101 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 101 ^ (r - 1) ≥ 101 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 101 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 101 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 101 ^ r ≥ 101 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (101 ^ r) hp_r, a_eq_c (101 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 103
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 10609 ≡ a 103 [ZMOD (103 ^ 9)]
          rw [a_eq_c 10609 (by decide), a_eq_factorial 103 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 103 ^ (r - 1) ≥ 103 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 103 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 103 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 103 ^ r ≥ 103 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (103 ^ r) hp_r, a_eq_c (103 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 107
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 11449 ≡ a 107 [ZMOD (107 ^ 9)]
          rw [a_eq_c 11449 (by decide), a_eq_factorial 107 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 107 ^ (r - 1) ≥ 107 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 107 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 107 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 107 ^ r ≥ 107 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (107 ^ r) hp_r, a_eq_c (107 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 109
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 11881 ≡ a 109 [ZMOD (109 ^ 9)]
          rw [a_eq_c 11881 (by decide), a_eq_factorial 109 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 109 ^ (r - 1) ≥ 109 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 109 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 109 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 109 ^ r ≥ 109 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (109 ^ r) hp_r, a_eq_c (109 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 113
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 12769 ≡ a 113 [ZMOD (113 ^ 9)]
          rw [a_eq_c 12769 (by decide), a_eq_factorial 113 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 113 ^ (r - 1) ≥ 113 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 113 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 113 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 113 ^ r ≥ 113 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (113 ^ r) hp_r, a_eq_c (113 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 127
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 16129 ≡ a 127 [ZMOD (127 ^ 9)]
          rw [a_eq_c 16129 (by decide), a_eq_factorial 127 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 127 ^ (r - 1) ≥ 127 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 127 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 127 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 127 ^ r ≥ 127 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (127 ^ r) hp_r, a_eq_c (127 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 131
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 17161 ≡ a 131 [ZMOD (131 ^ 9)]
          rw [a_eq_c 17161 (by decide), a_eq_factorial 131 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 131 ^ (r - 1) ≥ 131 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 131 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 131 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 131 ^ r ≥ 131 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (131 ^ r) hp_r, a_eq_c (131 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 137
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 18769 ≡ a 137 [ZMOD (137 ^ 9)]
          rw [a_eq_c 18769 (by decide), a_eq_factorial 137 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 137 ^ (r - 1) ≥ 137 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 137 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 137 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 137 ^ r ≥ 137 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (137 ^ r) hp_r, a_eq_c (137 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 139
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 19321 ≡ a 139 [ZMOD (139 ^ 9)]
          rw [a_eq_c 19321 (by decide), a_eq_factorial 139 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 139 ^ (r - 1) ≥ 139 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 139 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 139 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 139 ^ r ≥ 139 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (139 ^ r) hp_r, a_eq_c (139 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 149
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 22201 ≡ a 149 [ZMOD (149 ^ 9)]
          rw [a_eq_c 22201 (by decide), a_eq_factorial 149 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 149 ^ (r - 1) ≥ 149 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 149 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 149 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 149 ^ r ≥ 149 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (149 ^ r) hp_r, a_eq_c (149 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 151
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 22801 ≡ a 151 [ZMOD (151 ^ 9)]
          rw [a_eq_c 22801 (by decide), a_eq_factorial 151 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 151 ^ (r - 1) ≥ 151 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 151 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 151 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 151 ^ r ≥ 151 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (151 ^ r) hp_r, a_eq_c (151 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 157
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 24649 ≡ a 157 [ZMOD (157 ^ 9)]
          rw [a_eq_c 24649 (by decide), a_eq_factorial 157 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 157 ^ (r - 1) ≥ 157 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 157 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 157 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 157 ^ r ≥ 157 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (157 ^ r) hp_r, a_eq_c (157 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 163
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 26569 ≡ a 163 [ZMOD (163 ^ 9)]
          rw [a_eq_c 26569 (by decide), a_eq_factorial 163 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 163 ^ (r - 1) ≥ 163 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 163 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 163 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 163 ^ r ≥ 163 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (163 ^ r) hp_r, a_eq_c (163 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 167
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 27889 ≡ a 167 [ZMOD (167 ^ 9)]
          rw [a_eq_c 27889 (by decide), a_eq_factorial 167 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 167 ^ (r - 1) ≥ 167 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 167 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 167 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 167 ^ r ≥ 167 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (167 ^ r) hp_r, a_eq_c (167 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 173
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 29929 ≡ a 173 [ZMOD (173 ^ 9)]
          rw [a_eq_c 29929 (by decide), a_eq_factorial 173 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 173 ^ (r - 1) ≥ 173 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 173 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 173 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 173 ^ r ≥ 173 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (173 ^ r) hp_r, a_eq_c (173 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 179
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 32041 ≡ a 179 [ZMOD (179 ^ 9)]
          rw [a_eq_c 32041 (by decide), a_eq_factorial 179 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 179 ^ (r - 1) ≥ 179 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 179 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 179 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 179 ^ r ≥ 179 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (179 ^ r) hp_r, a_eq_c (179 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 181
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 32761 ≡ a 181 [ZMOD (181 ^ 9)]
          rw [a_eq_c 32761 (by decide), a_eq_factorial 181 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 181 ^ (r - 1) ≥ 181 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 181 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 181 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 181 ^ r ≥ 181 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (181 ^ r) hp_r, a_eq_c (181 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 191
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 36481 ≡ a 191 [ZMOD (191 ^ 9)]
          rw [a_eq_c 36481 (by decide), a_eq_factorial 191 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 191 ^ (r - 1) ≥ 191 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 191 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 191 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 191 ^ r ≥ 191 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (191 ^ r) hp_r, a_eq_c (191 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 193
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 37249 ≡ a 193 [ZMOD (193 ^ 9)]
          rw [a_eq_c 37249 (by decide), a_eq_factorial 193 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 193 ^ (r - 1) ≥ 193 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 193 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 193 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 193 ^ r ≥ 193 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (193 ^ r) hp_r, a_eq_c (193 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 197
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 38809 ≡ a 197 [ZMOD (197 ^ 9)]
          rw [a_eq_c 38809 (by decide), a_eq_factorial 197 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 197 ^ (r - 1) ≥ 197 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 197 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 197 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 197 ^ r ≥ 197 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (197 ^ r) hp_r, a_eq_c (197 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 199
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 39601 ≡ a 199 [ZMOD (199 ^ 9)]
          rw [a_eq_c 39601 (by decide), a_eq_factorial 199 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 199 ^ (r - 1) ≥ 199 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 199 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 199 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 199 ^ r ≥ 199 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (199 ^ r) hp_r, a_eq_c (199 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 211
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 44521 ≡ a 211 [ZMOD (211 ^ 9)]
          rw [a_eq_c 44521 (by decide), a_eq_factorial 211 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 211 ^ (r - 1) ≥ 211 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 211 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 211 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 211 ^ r ≥ 211 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (211 ^ r) hp_r, a_eq_c (211 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 223
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 49729 ≡ a 223 [ZMOD (223 ^ 9)]
          rw [a_eq_c 49729 (by decide), a_eq_factorial 223 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 223 ^ (r - 1) ≥ 223 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 223 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 223 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 223 ^ r ≥ 223 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (223 ^ r) hp_r, a_eq_c (223 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 227
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 51529 ≡ a 227 [ZMOD (227 ^ 9)]
          rw [a_eq_c 51529 (by decide), a_eq_factorial 227 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 227 ^ (r - 1) ≥ 227 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 227 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 227 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 227 ^ r ≥ 227 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (227 ^ r) hp_r, a_eq_c (227 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 229
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 52441 ≡ a 229 [ZMOD (229 ^ 9)]
          rw [a_eq_c 52441 (by decide), a_eq_factorial 229 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 229 ^ (r - 1) ≥ 229 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 229 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 229 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 229 ^ r ≥ 229 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (229 ^ r) hp_r, a_eq_c (229 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 233
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 54289 ≡ a 233 [ZMOD (233 ^ 9)]
          rw [a_eq_c 54289 (by decide), a_eq_factorial 233 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 233 ^ (r - 1) ≥ 233 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 233 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 233 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 233 ^ r ≥ 233 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (233 ^ r) hp_r, a_eq_c (233 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 239
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 57121 ≡ a 239 [ZMOD (239 ^ 9)]
          rw [a_eq_c 57121 (by decide), a_eq_factorial 239 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 239 ^ (r - 1) ≥ 239 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 239 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 239 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 239 ^ r ≥ 239 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (239 ^ r) hp_r, a_eq_c (239 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 241
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 58081 ≡ a 241 [ZMOD (241 ^ 9)]
          rw [a_eq_c 58081 (by decide), a_eq_factorial 241 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 241 ^ (r - 1) ≥ 241 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 241 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 241 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 241 ^ r ≥ 241 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (241 ^ r) hp_r, a_eq_c (241 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 251
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 63001 ≡ a 251 [ZMOD (251 ^ 9)]
          rw [a_eq_c 63001 (by decide), a_eq_factorial 251 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 251 ^ (r - 1) ≥ 251 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 251 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 251 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 251 ^ r ≥ 251 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (251 ^ r) hp_r, a_eq_c (251 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 257
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 66049 ≡ a 257 [ZMOD (257 ^ 9)]
          rw [a_eq_c 66049 (by decide), a_eq_factorial 257 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 257 ^ (r - 1) ≥ 257 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 257 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 257 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 257 ^ r ≥ 257 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (257 ^ r) hp_r, a_eq_c (257 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 263
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 69169 ≡ a 263 [ZMOD (263 ^ 9)]
          rw [a_eq_c 69169 (by decide), a_eq_factorial 263 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 263 ^ (r - 1) ≥ 263 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 263 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 263 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 263 ^ r ≥ 263 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (263 ^ r) hp_r, a_eq_c (263 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 269
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 72361 ≡ a 269 [ZMOD (269 ^ 9)]
          rw [a_eq_c 72361 (by decide), a_eq_factorial 269 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 269 ^ (r - 1) ≥ 269 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 269 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 269 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 269 ^ r ≥ 269 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (269 ^ r) hp_r, a_eq_c (269 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 271
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 73441 ≡ a 271 [ZMOD (271 ^ 9)]
          rw [a_eq_c 73441 (by decide), a_eq_factorial 271 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 271 ^ (r - 1) ≥ 271 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 271 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 271 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 271 ^ r ≥ 271 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (271 ^ r) hp_r, a_eq_c (271 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 277
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 76729 ≡ a 277 [ZMOD (277 ^ 9)]
          rw [a_eq_c 76729 (by decide), a_eq_factorial 277 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 277 ^ (r - 1) ≥ 277 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 277 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 277 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 277 ^ r ≥ 277 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (277 ^ r) hp_r, a_eq_c (277 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 281
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 78961 ≡ a 281 [ZMOD (281 ^ 9)]
          rw [a_eq_c 78961 (by decide), a_eq_factorial 281 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 281 ^ (r - 1) ≥ 281 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 281 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 281 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 281 ^ r ≥ 281 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (281 ^ r) hp_r, a_eq_c (281 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 283
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 80089 ≡ a 283 [ZMOD (283 ^ 9)]
          rw [a_eq_c 80089 (by decide), a_eq_factorial 283 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 283 ^ (r - 1) ≥ 283 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 283 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 283 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 283 ^ r ≥ 283 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (283 ^ r) hp_r, a_eq_c (283 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 293
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 85849 ≡ a 293 [ZMOD (293 ^ 9)]
          rw [a_eq_c 85849 (by decide), a_eq_factorial 293 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 293 ^ (r - 1) ≥ 293 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 293 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 293 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 293 ^ r ≥ 293 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (293 ^ r) hp_r, a_eq_c (293 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 307
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 94249 ≡ a 307 [ZMOD (307 ^ 9)]
          rw [a_eq_c 94249 (by decide), a_eq_factorial 307 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 307 ^ (r - 1) ≥ 307 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 307 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 307 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 307 ^ r ≥ 307 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (307 ^ r) hp_r, a_eq_c (307 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 311
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 96721 ≡ a 311 [ZMOD (311 ^ 9)]
          rw [a_eq_c 96721 (by decide), a_eq_factorial 311 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 311 ^ (r - 1) ≥ 311 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 311 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 311 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 311 ^ r ≥ 311 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (311 ^ r) hp_r, a_eq_c (311 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 313
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 97969 ≡ a 313 [ZMOD (313 ^ 9)]
          rw [a_eq_c 97969 (by decide), a_eq_factorial 313 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 313 ^ (r - 1) ≥ 313 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 313 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 313 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 313 ^ r ≥ 313 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (313 ^ r) hp_r, a_eq_c (313 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 317
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 100489 ≡ a 317 [ZMOD (317 ^ 9)]
          rw [a_eq_c 100489 (by decide), a_eq_factorial 317 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 317 ^ (r - 1) ≥ 317 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 317 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 317 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 317 ^ r ≥ 317 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (317 ^ r) hp_r, a_eq_c (317 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 331
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 109561 ≡ a 331 [ZMOD (331 ^ 9)]
          rw [a_eq_c 109561 (by decide), a_eq_factorial 331 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 331 ^ (r - 1) ≥ 331 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 331 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 331 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 331 ^ r ≥ 331 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (331 ^ r) hp_r, a_eq_c (331 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 337
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 113569 ≡ a 337 [ZMOD (337 ^ 9)]
          rw [a_eq_c 113569 (by decide), a_eq_factorial 337 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 337 ^ (r - 1) ≥ 337 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 337 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 337 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 337 ^ r ≥ 337 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (337 ^ r) hp_r, a_eq_c (337 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 347
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 120409 ≡ a 347 [ZMOD (347 ^ 9)]
          rw [a_eq_c 120409 (by decide), a_eq_factorial 347 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 347 ^ (r - 1) ≥ 347 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 347 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 347 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 347 ^ r ≥ 347 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (347 ^ r) hp_r, a_eq_c (347 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 349
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 121801 ≡ a 349 [ZMOD (349 ^ 9)]
          rw [a_eq_c 121801 (by decide), a_eq_factorial 349 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 349 ^ (r - 1) ≥ 349 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 349 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 349 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 349 ^ r ≥ 349 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (349 ^ r) hp_r, a_eq_c (349 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 353
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 124609 ≡ a 353 [ZMOD (353 ^ 9)]
          rw [a_eq_c 124609 (by decide), a_eq_factorial 353 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 353 ^ (r - 1) ≥ 353 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 353 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 353 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 353 ^ r ≥ 353 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (353 ^ r) hp_r, a_eq_c (353 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 359
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 128881 ≡ a 359 [ZMOD (359 ^ 9)]
          rw [a_eq_c 128881 (by decide), a_eq_factorial 359 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 359 ^ (r - 1) ≥ 359 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 359 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 359 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 359 ^ r ≥ 359 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (359 ^ r) hp_r, a_eq_c (359 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 367
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 134689 ≡ a 367 [ZMOD (367 ^ 9)]
          rw [a_eq_c 134689 (by decide), a_eq_factorial 367 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 367 ^ (r - 1) ≥ 367 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 367 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 367 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 367 ^ r ≥ 367 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (367 ^ r) hp_r, a_eq_c (367 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 373
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 139129 ≡ a 373 [ZMOD (373 ^ 9)]
          rw [a_eq_c 139129 (by decide), a_eq_factorial 373 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 373 ^ (r - 1) ≥ 373 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 373 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 373 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 373 ^ r ≥ 373 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (373 ^ r) hp_r, a_eq_c (373 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 379
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 143641 ≡ a 379 [ZMOD (379 ^ 9)]
          rw [a_eq_c 143641 (by decide), a_eq_factorial 379 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 379 ^ (r - 1) ≥ 379 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 379 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 379 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 379 ^ r ≥ 379 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (379 ^ r) hp_r, a_eq_c (379 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 383
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 146689 ≡ a 383 [ZMOD (383 ^ 9)]
          rw [a_eq_c 146689 (by decide), a_eq_factorial 383 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 383 ^ (r - 1) ≥ 383 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 383 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 383 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 383 ^ r ≥ 383 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (383 ^ r) hp_r, a_eq_c (383 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 389
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 151321 ≡ a 389 [ZMOD (389 ^ 9)]
          rw [a_eq_c 151321 (by decide), a_eq_factorial 389 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 389 ^ (r - 1) ≥ 389 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 389 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 389 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 389 ^ r ≥ 389 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (389 ^ r) hp_r, a_eq_c (389 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 397
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 157609 ≡ a 397 [ZMOD (397 ^ 9)]
          rw [a_eq_c 157609 (by decide), a_eq_factorial 397 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 397 ^ (r - 1) ≥ 397 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 397 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 397 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 397 ^ r ≥ 397 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (397 ^ r) hp_r, a_eq_c (397 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 401
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 160801 ≡ a 401 [ZMOD (401 ^ 9)]
          rw [a_eq_c 160801 (by decide), a_eq_factorial 401 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 401 ^ (r - 1) ≥ 401 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 401 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 401 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 401 ^ r ≥ 401 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (401 ^ r) hp_r, a_eq_c (401 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 409
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 167281 ≡ a 409 [ZMOD (409 ^ 9)]
          rw [a_eq_c 167281 (by decide), a_eq_factorial 409 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 409 ^ (r - 1) ≥ 409 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 409 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 409 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 409 ^ r ≥ 409 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (409 ^ r) hp_r, a_eq_c (409 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 419
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 175561 ≡ a 419 [ZMOD (419 ^ 9)]
          rw [a_eq_c 175561 (by decide), a_eq_factorial 419 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 419 ^ (r - 1) ≥ 419 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 419 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 419 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 419 ^ r ≥ 419 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (419 ^ r) hp_r, a_eq_c (419 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 421
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 177241 ≡ a 421 [ZMOD (421 ^ 9)]
          rw [a_eq_c 177241 (by decide), a_eq_factorial 421 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 421 ^ (r - 1) ≥ 421 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 421 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 421 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 421 ^ r ≥ 421 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (421 ^ r) hp_r, a_eq_c (421 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 431
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 185761 ≡ a 431 [ZMOD (431 ^ 9)]
          rw [a_eq_c 185761 (by decide), a_eq_factorial 431 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 431 ^ (r - 1) ≥ 431 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 431 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 431 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 431 ^ r ≥ 431 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (431 ^ r) hp_r, a_eq_c (431 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 433
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 187489 ≡ a 433 [ZMOD (433 ^ 9)]
          rw [a_eq_c 187489 (by decide), a_eq_factorial 433 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 433 ^ (r - 1) ≥ 433 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 433 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 433 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 433 ^ r ≥ 433 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (433 ^ r) hp_r, a_eq_c (433 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 439
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 192721 ≡ a 439 [ZMOD (439 ^ 9)]
          rw [a_eq_c 192721 (by decide), a_eq_factorial 439 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 439 ^ (r - 1) ≥ 439 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 439 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 439 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 439 ^ r ≥ 439 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (439 ^ r) hp_r, a_eq_c (439 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 443
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 196249 ≡ a 443 [ZMOD (443 ^ 9)]
          rw [a_eq_c 196249 (by decide), a_eq_factorial 443 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 443 ^ (r - 1) ≥ 443 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 443 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 443 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 443 ^ r ≥ 443 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (443 ^ r) hp_r, a_eq_c (443 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 449
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 201601 ≡ a 449 [ZMOD (449 ^ 9)]
          rw [a_eq_c 201601 (by decide), a_eq_factorial 449 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 449 ^ (r - 1) ≥ 449 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 449 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 449 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 449 ^ r ≥ 449 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (449 ^ r) hp_r, a_eq_c (449 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 457
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 208849 ≡ a 457 [ZMOD (457 ^ 9)]
          rw [a_eq_c 208849 (by decide), a_eq_factorial 457 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 457 ^ (r - 1) ≥ 457 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 457 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 457 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 457 ^ r ≥ 457 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (457 ^ r) hp_r, a_eq_c (457 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 461
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 212521 ≡ a 461 [ZMOD (461 ^ 9)]
          rw [a_eq_c 212521 (by decide), a_eq_factorial 461 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 461 ^ (r - 1) ≥ 461 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 461 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 461 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 461 ^ r ≥ 461 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (461 ^ r) hp_r, a_eq_c (461 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 463
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 214369 ≡ a 463 [ZMOD (463 ^ 9)]
          rw [a_eq_c 214369 (by decide), a_eq_factorial 463 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 463 ^ (r - 1) ≥ 463 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 463 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 463 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 463 ^ r ≥ 463 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (463 ^ r) hp_r, a_eq_c (463 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 467
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 218089 ≡ a 467 [ZMOD (467 ^ 9)]
          rw [a_eq_c 218089 (by decide), a_eq_factorial 467 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 467 ^ (r - 1) ≥ 467 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 467 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 467 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 467 ^ r ≥ 467 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (467 ^ r) hp_r, a_eq_c (467 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 479
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 229441 ≡ a 479 [ZMOD (479 ^ 9)]
          rw [a_eq_c 229441 (by decide), a_eq_factorial 479 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 479 ^ (r - 1) ≥ 479 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 479 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 479 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 479 ^ r ≥ 479 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (479 ^ r) hp_r, a_eq_c (479 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 487
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 237169 ≡ a 487 [ZMOD (487 ^ 9)]
          rw [a_eq_c 237169 (by decide), a_eq_factorial 487 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 487 ^ (r - 1) ≥ 487 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 487 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 487 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 487 ^ r ≥ 487 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (487 ^ r) hp_r, a_eq_c (487 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 491
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 241081 ≡ a 491 [ZMOD (491 ^ 9)]
          rw [a_eq_c 241081 (by decide), a_eq_factorial 491 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 491 ^ (r - 1) ≥ 491 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 491 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 491 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 491 ^ r ≥ 491 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (491 ^ r) hp_r, a_eq_c (491 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 499
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 249001 ≡ a 499 [ZMOD (499 ^ 9)]
          rw [a_eq_c 249001 (by decide), a_eq_factorial 499 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 499 ^ (r - 1) ≥ 499 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 499 ^ (r - 1) ≥ 500 := by omega
        have hp_r : 499 ^ r ≥ 500 := by
          have : r ≥ r - 1 := by omega
          have : 499 ^ r ≥ 499 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (499 ^ r) hp_r, a_eq_c (499 ^ (r - 1)) hp_r1]
  · -- p >= N
    have hp_bound_ge : p ≥ 500 := by omega
    have h_r1 : r - 1 ≥ 1 := by omega
    have hp_r1_ge : p ^ (r - 1) ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) h_r1
    have hp_r1_ge2 : p ^ 1 ≥ 500 ^ 1 := Nat.pow_le_pow_left hp_bound_ge 1
    have hp_r1 : p ^ (r - 1) ≥ 500 := by omega
    have hp_r : p ^ r ≥ 500 := by
      have : r ≥ r - 1 := by omega
      have : p ^ r ≥ p ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
      omega
    rw [a_eq_c (p ^ r) hp_r, a_eq_c (p ^ (r - 1)) hp_r1]
