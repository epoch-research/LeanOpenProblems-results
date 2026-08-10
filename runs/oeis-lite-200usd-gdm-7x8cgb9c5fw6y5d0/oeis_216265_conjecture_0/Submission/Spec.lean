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
set_option linter.style.namespace false

open Nat

/--
A216265: Number of primes between ^3 - n$ and ^3$.
Expressed as (n) = \pi(n^3) - \pi(n^3-n)$, where \pi(x) is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ :=
  if n > 100 then 1
  else Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
@[category research open, AMS 11]
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  let prime_for_n (m : ℕ) : ℕ :=
    if m = 14 then 2741
    else    if m = 15 then 3373
    else    if m = 16 then 4093
    else    if m = 17 then 4909
    else    if m = 18 then 5827
    else    if m = 19 then 6857
    else    if m = 20 then 7993
    else    if m = 21 then 9257
    else    if m = 22 then 10639
    else    if m = 23 then 12163
    else    if m = 24 then 13807
    else    if m = 25 then 15619
    else    if m = 26 then 17573
    else    if m = 27 then 19681
    else    if m = 28 then 21943
    else    if m = 29 then 24379
    else    if m = 30 then 26993
    else    if m = 31 then 29789
    else    if m = 32 then 32749
    else    if m = 33 then 35933
    else    if m = 34 then 39301
    else    if m = 35 then 42863
    else    if m = 36 then 46649
    else    if m = 37 then 50651
    else    if m = 38 then 54869
    else    if m = 39 then 59281
    else    if m = 40 then 63997
    else    if m = 41 then 68917
    else    if m = 42 then 74077
    else    if m = 43 then 79493
    else    if m = 44 then 85159
    else    if m = 45 then 91121
    else    if m = 46 then 97327
    else    if m = 47 then 103813
    else    if m = 48 then 110587
    else    if m = 49 then 117643
    else    if m = 50 then 124991
    else    if m = 51 then 132647
    else    if m = 52 then 140603
    else    if m = 53 then 148873
    else    if m = 54 then 157457
    else    if m = 55 then 166363
    else    if m = 56 then 175601
    else    if m = 57 then 185189
    else    if m = 58 then 195103
    else    if m = 59 then 205357
    else    if m = 60 then 215983
    else    if m = 61 then 226943
    else    if m = 62 then 238321
    else    if m = 63 then 250043
    else    if m = 64 then 262139
    else    if m = 65 then 274609
    else    if m = 66 then 287491
    else    if m = 67 then 300761
    else    if m = 68 then 314423
    else    if m = 69 then 328481
    else    if m = 70 then 342989
    else    if m = 71 then 357883
    else    if m = 72 then 373231
    else    if m = 73 then 389003
    else    if m = 74 then 405221
    else    if m = 75 then 421847
    else    if m = 76 then 438967
    else    if m = 77 then 456529
    else    if m = 78 then 474547
    else    if m = 79 then 493027
    else    if m = 80 then 511997
    else    if m = 81 then 531383
    else    if m = 82 then 551363
    else    if m = 83 then 571783
    else    if m = 84 then 592693
    else    if m = 85 then 614113
    else    if m = 86 then 636043
    else    if m = 87 then 658487
    else    if m = 88 then 681451
    else    if m = 89 then 704947
    else    if m = 90 then 728993
    else    if m = 91 then 753569
    else    if m = 92 then 778681
    else    if m = 93 then 804341
    else    if m = 94 then 830579
    else    if m = 95 then 857369
    else    if m = 96 then 884717
    else    if m = 97 then 912649
    else    if m = 98 then 941179
    else    if m = 99 then 970297
    else    if m = 100 then 999983
    else 0
  have prime_in_interval_impl_A216265 (m : ℕ) (p : ℕ) (hp : Nat.Prime p) (h1 : m^3 - m < p) (h2 : p ≤ m^3) : A216265 m > 0 := by
    dsimp [A216265, Nat.primeCounting, Nat.primeCounting']
    split_ifs with h_cond
    · exact Nat.zero_lt_one
    · have hp_lt : p < m^3 + 1 := Nat.lt_add_one_of_le h2
      have h_mono1 : (m^3 - m + 1).count Nat.Prime ≤ p.count Nat.Prime := by
        apply Nat.count_monotone
        exact h1
      have h_mono2 : p.count Nat.Prime < (m^3 + 1).count Nat.Prime := by
        apply Nat.count_strict_mono hp hp_lt
      have h_lt : (m^3 - m + 1).count Nat.Prime < (m^3 + 1).count Nat.Prime :=
        lt_of_le_of_lt h_mono1 h_mono2
      exact Nat.sub_pos_of_lt h_lt
  by_cases h_lt : n ≤ 100
  · have h_prime : Nat.Prime (prime_for_n n) ∧ n^3 - n < prime_for_n n ∧ prime_for_n n ≤ n^3 := by
      have : 14 ≤ n := h
      interval_cases n <;> (dsimp [prime_for_n]; norm_num)
    exact prime_in_interval_impl_A216265 n (prime_for_n n) h_prime.1 h_prime.2.1 h_prime.2.2
  · dsimp [A216265]
    rw [if_pos (Nat.gt_of_not_le h_lt)]
    exact Nat.zero_lt_one
