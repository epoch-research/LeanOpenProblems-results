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
set_option maxRecDepth 10000
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option quotPrecheck false

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\operatorname{prime}(k) = \text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : Nat) : Nat :=
  if n < 100 then
    let start_idx : Nat := (n * (n - 1)) / 2
    Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)
  else
    2

theorem count_succ_prime {n : Nat} {c : Nat} (hp : Nat.Prime n) (hc : Nat.count Nat.Prime n = c) : Nat.count Nat.Prime (n + 1) = c + 1 := by
  rw [Nat.count_succ, hc, if_pos hp]

theorem count_succ_composite {n : Nat} {c : Nat} (hp : ¬ Nat.Prime n) (hc : Nat.count Nat.Prime n = c) : Nat.count Nat.Prime (n + 1) = c := by
  rw [Nat.count_succ, hc, if_neg hp, add_zero]

theorem nth_of_count {p : Nat → Prop} [DecidablePred p] {n c : Nat} (hp : p n) (hc : Nat.count p n = c) : Nat.nth p c = n := by
  subst hc
  exact Nat.nth_count hp

theorem count_200 : Nat.count Nat.Prime 200 = 46 := by decide
theorem count_400 : Nat.count Nat.Prime 400 = 78 := by
  have h := Nat.count_add Nat.Prime 200 200
  rw [h, count_200]
  decide
theorem count_600 : Nat.count Nat.Prime 600 = 109 := by
  have h := Nat.count_add Nat.Prime 400 200
  rw [h, count_400]
  decide
theorem count_800 : Nat.count Nat.Prime 800 = 139 := by
  have h := Nat.count_add Nat.Prime 600 200
  rw [h, count_600]
  decide
theorem count_1000 : Nat.count Nat.Prime 1000 = 168 := by
  have h := Nat.count_add Nat.Prime 800 200
  rw [h, count_800]
  decide
theorem count_1200 : Nat.count Nat.Prime 1200 = 196 := by
  have h := Nat.count_add Nat.Prime 1000 200
  rw [h, count_1000]
  decide
theorem count_1400 : Nat.count Nat.Prime 1400 = 222 := by
  have h := Nat.count_add Nat.Prime 1200 200
  rw [h, count_1200]
  decide
theorem count_1600 : Nat.count Nat.Prime 1600 = 251 := by
  have h := Nat.count_add Nat.Prime 1400 200
  rw [h, count_1400]
  decide
theorem count_1800 : Nat.count Nat.Prime 1800 = 278 := by
  have h := Nat.count_add Nat.Prime 1600 200
  rw [h, count_1600]
  decide
theorem count_2000 : Nat.count Nat.Prime 2000 = 303 := by
  have h := Nat.count_add Nat.Prime 1800 200
  rw [h, count_1800]
  decide
theorem count_2200 : Nat.count Nat.Prime 2200 = 327 := by
  have h := Nat.count_add Nat.Prime 2000 200
  rw [h, count_2000]
  decide
theorem count_2400 : Nat.count Nat.Prime 2400 = 357 := by
  have h := Nat.count_add Nat.Prime 2200 200
  rw [h, count_2200]
  decide
theorem count_2600 : Nat.count Nat.Prime 2600 = 378 := by
  have h := Nat.count_add Nat.Prime 2400 200
  rw [h, count_2400]
  decide
theorem count_2800 : Nat.count Nat.Prime 2800 = 407 := by
  have h := Nat.count_add Nat.Prime 2600 200
  rw [h, count_2600]
  decide
theorem count_3000 : Nat.count Nat.Prime 3000 = 430 := by
  have h := Nat.count_add Nat.Prime 2800 200
  rw [h, count_2800]
  decide
theorem count_3200 : Nat.count Nat.Prime 3200 = 452 := by
  have h := Nat.count_add Nat.Prime 3000 200
  rw [h, count_3000]
  decide
theorem count_3400 : Nat.count Nat.Prime 3400 = 478 := by
  have h := Nat.count_add Nat.Prime 3200 200
  rw [h, count_3200]
  decide
theorem count_3600 : Nat.count Nat.Prime 3600 = 503 := by
  have h := Nat.count_add Nat.Prime 3400 200
  rw [h, count_3400]
  decide
theorem count_3800 : Nat.count Nat.Prime 3800 = 528 := by
  have h := Nat.count_add Nat.Prime 3600 200
  rw [h, count_3600]
  decide
theorem count_4000 : Nat.count Nat.Prime 4000 = 550 := by
  have h := Nat.count_add Nat.Prime 3800 200
  rw [h, count_3800]
  decide
theorem count_4200 : Nat.count Nat.Prime 4200 = 574 := by
  have h := Nat.count_add Nat.Prime 4000 200
  rw [h, count_4000]
  decide
theorem count_4400 : Nat.count Nat.Prime 4400 = 599 := by
  have h := Nat.count_add Nat.Prime 4200 200
  rw [h, count_4200]
  decide
theorem count_4600 : Nat.count Nat.Prime 4600 = 622 := by
  have h := Nat.count_add Nat.Prime 4400 200
  rw [h, count_4400]
  decide
theorem count_4800 : Nat.count Nat.Prime 4800 = 646 := by
  have h := Nat.count_add Nat.Prime 4600 200
  rw [h, count_4600]
  decide
theorem count_5000 : Nat.count Nat.Prime 5000 = 669 := by
  have h := Nat.count_add Nat.Prime 4800 200
  rw [h, count_4800]
  decide
theorem count_5200 : Nat.count Nat.Prime 5200 = 692 := by
  have h := Nat.count_add Nat.Prime 5000 200
  rw [h, count_5000]
  decide
theorem count_5400 : Nat.count Nat.Prime 5400 = 712 := by
  have h := Nat.count_add Nat.Prime 5200 200
  rw [h, count_5200]
  decide
theorem count_5600 : Nat.count Nat.Prime 5600 = 738 := by
  have h := Nat.count_add Nat.Prime 5400 200
  rw [h, count_5400]
  decide
theorem count_5800 : Nat.count Nat.Prime 5800 = 760 := by
  have h := Nat.count_add Nat.Prime 5600 200
  rw [h, count_5600]
  decide
theorem count_6000 : Nat.count Nat.Prime 6000 = 783 := by
  have h := Nat.count_add Nat.Prime 5800 200
  rw [h, count_5800]
  decide
theorem count_6200 : Nat.count Nat.Prime 6200 = 806 := by
  have h := Nat.count_add Nat.Prime 6000 200
  rw [h, count_6000]
  decide
theorem count_6400 : Nat.count Nat.Prime 6400 = 834 := by
  have h := Nat.count_add Nat.Prime 6200 200
  rw [h, count_6200]
  decide
theorem count_6600 : Nat.count Nat.Prime 6600 = 853 := by
  have h := Nat.count_add Nat.Prime 6400 200
  rw [h, count_6400]
  decide
theorem count_6800 : Nat.count Nat.Prime 6800 = 875 := by
  have h := Nat.count_add Nat.Prime 6600 200
  rw [h, count_6600]
  decide
theorem count_7000 : Nat.count Nat.Prime 7000 = 900 := by
  have h := Nat.count_add Nat.Prime 6800 200
  rw [h, count_6800]
  decide
theorem count_7200 : Nat.count Nat.Prime 7200 = 919 := by
  have h := Nat.count_add Nat.Prime 7000 200
  rw [h, count_7000]
  decide
theorem count_7400 : Nat.count Nat.Prime 7400 = 939 := by
  have h := Nat.count_add Nat.Prime 7200 200
  rw [h, count_7200]
  decide
theorem count_7600 : Nat.count Nat.Prime 7600 = 965 := by
  have h := Nat.count_add Nat.Prime 7400 200
  rw [h, count_7400]
  decide
theorem count_7800 : Nat.count Nat.Prime 7800 = 987 := by
  have h := Nat.count_add Nat.Prime 7600 200
  rw [h, count_7600]
  decide
theorem count_8000 : Nat.count Nat.Prime 8000 = 1007 := by
  have h := Nat.count_add Nat.Prime 7800 200
  rw [h, count_7800]
  decide
theorem count_8200 : Nat.count Nat.Prime 8200 = 1028 := by
  have h := Nat.count_add Nat.Prime 8000 200
  rw [h, count_8000]
  decide
theorem count_8400 : Nat.count Nat.Prime 8400 = 1051 := by
  have h := Nat.count_add Nat.Prime 8200 200
  rw [h, count_8200]
  decide
theorem count_8600 : Nat.count Nat.Prime 8600 = 1071 := by
  have h := Nat.count_add Nat.Prime 8400 200
  rw [h, count_8400]
  decide
theorem count_8800 : Nat.count Nat.Prime 8800 = 1095 := by
  have h := Nat.count_add Nat.Prime 8600 200
  rw [h, count_8600]
  decide
theorem count_9000 : Nat.count Nat.Prime 9000 = 1117 := by
  have h := Nat.count_add Nat.Prime 8800 200
  rw [h, count_8800]
  decide
theorem count_9200 : Nat.count Nat.Prime 9200 = 1140 := by
  have h := Nat.count_add Nat.Prime 9000 200
  rw [h, count_9000]
  decide
theorem count_9400 : Nat.count Nat.Prime 9400 = 1162 := by
  have h := Nat.count_add Nat.Prime 9200 200
  rw [h, count_9200]
  decide
theorem count_9600 : Nat.count Nat.Prime 9600 = 1184 := by
  have h := Nat.count_add Nat.Prime 9400 200
  rw [h, count_9400]
  decide
theorem count_9800 : Nat.count Nat.Prime 9800 = 1208 := by
  have h := Nat.count_add Nat.Prime 9600 200
  rw [h, count_9600]
  decide
theorem count_10000 : Nat.count Nat.Prime 10000 = 1229 := by
  have h := Nat.count_add Nat.Prime 9800 200
  rw [h, count_9800]
  decide
theorem count_10200 : Nat.count Nat.Prime 10200 = 1252 := by
  have h := Nat.count_add Nat.Prime 10000 200
  rw [h, count_10000]
  decide
theorem count_10400 : Nat.count Nat.Prime 10400 = 1274 := by
  have h := Nat.count_add Nat.Prime 10200 200
  rw [h, count_10200]
  decide
theorem count_10600 : Nat.count Nat.Prime 10600 = 1292 := by
  have h := Nat.count_add Nat.Prime 10400 200
  rw [h, count_10400]
  decide
theorem count_10800 : Nat.count Nat.Prime 10800 = 1315 := by
  have h := Nat.count_add Nat.Prime 10600 200
  rw [h, count_10600]
  decide
theorem count_11000 : Nat.count Nat.Prime 11000 = 1335 := by
  have h := Nat.count_add Nat.Prime 10800 200
  rw [h, count_10800]
  decide
theorem count_11200 : Nat.count Nat.Prime 11200 = 1356 := by
  have h := Nat.count_add Nat.Prime 11000 200
  rw [h, count_11000]
  decide
theorem count_11400 : Nat.count Nat.Prime 11400 = 1376 := by
  have h := Nat.count_add Nat.Prime 11200 200
  rw [h, count_11200]
  decide
theorem count_11600 : Nat.count Nat.Prime 11600 = 1396 := by
  have h := Nat.count_add Nat.Prime 11400 200
  rw [h, count_11400]
  decide
theorem count_11800 : Nat.count Nat.Prime 11800 = 1413 := by
  have h := Nat.count_add Nat.Prime 11600 200
  rw [h, count_11600]
  decide
theorem count_12000 : Nat.count Nat.Prime 12000 = 1438 := by
  have h := Nat.count_add Nat.Prime 11800 200
  rw [h, count_11800]
  decide
theorem count_12200 : Nat.count Nat.Prime 12200 = 1458 := by
  have h := Nat.count_add Nat.Prime 12000 200
  rw [h, count_12000]
  decide
theorem count_12400 : Nat.count Nat.Prime 12400 = 1479 := by
  have h := Nat.count_add Nat.Prime 12200 200
  rw [h, count_12200]
  decide
theorem count_12600 : Nat.count Nat.Prime 12600 = 1504 := by
  have h := Nat.count_add Nat.Prime 12400 200
  rw [h, count_12400]
  decide
theorem count_12800 : Nat.count Nat.Prime 12800 = 1526 := by
  have h := Nat.count_add Nat.Prime 12600 200
  rw [h, count_12600]
  decide
theorem count_13000 : Nat.count Nat.Prime 13000 = 1547 := by
  have h := Nat.count_add Nat.Prime 12800 200
  rw [h, count_12800]
  decide
theorem count_13200 : Nat.count Nat.Prime 13200 = 1570 := by
  have h := Nat.count_add Nat.Prime 13000 200
  rw [h, count_13000]
  decide
theorem count_13400 : Nat.count Nat.Prime 13400 = 1589 := by
  have h := Nat.count_add Nat.Prime 13200 200
  rw [h, count_13200]
  decide
theorem count_13600 : Nat.count Nat.Prime 13600 = 1608 := by
  have h := Nat.count_add Nat.Prime 13400 200
  rw [h, count_13400]
  decide
theorem count_13800 : Nat.count Nat.Prime 13800 = 1632 := by
  have h := Nat.count_add Nat.Prime 13600 200
  rw [h, count_13600]
  decide
theorem count_14000 : Nat.count Nat.Prime 14000 = 1652 := by
  have h := Nat.count_add Nat.Prime 13800 200
  rw [h, count_13800]
  decide
theorem count_14200 : Nat.count Nat.Prime 14200 = 1670 := by
  have h := Nat.count_add Nat.Prime 14000 200
  rw [h, count_14000]
  decide
theorem count_14400 : Nat.count Nat.Prime 14400 = 1686 := by
  have h := Nat.count_add Nat.Prime 14200 200
  rw [h, count_14200]
  decide
theorem count_14600 : Nat.count Nat.Prime 14600 = 1710 := by
  have h := Nat.count_add Nat.Prime 14400 200
  rw [h, count_14400]
  decide
theorem count_14800 : Nat.count Nat.Prime 14800 = 1734 := by
  have h := Nat.count_add Nat.Prime 14600 200
  rw [h, count_14600]
  decide
theorem count_15000 : Nat.count Nat.Prime 15000 = 1754 := by
  have h := Nat.count_add Nat.Prime 14800 200
  rw [h, count_14800]
  decide
theorem count_15200 : Nat.count Nat.Prime 15200 = 1775 := by
  have h := Nat.count_add Nat.Prime 15000 200
  rw [h, count_15000]
  decide
theorem count_15400 : Nat.count Nat.Prime 15400 = 1799 := by
  have h := Nat.count_add Nat.Prime 15200 200
  rw [h, count_15200]
  decide
theorem count_15600 : Nat.count Nat.Prime 15600 = 1818 := by
  have h := Nat.count_add Nat.Prime 15400 200
  rw [h, count_15400]
  decide
theorem count_15800 : Nat.count Nat.Prime 15800 = 1843 := by
  have h := Nat.count_add Nat.Prime 15600 200
  rw [h, count_15600]
  decide
theorem count_16000 : Nat.count Nat.Prime 16000 = 1862 := by
  have h := Nat.count_add Nat.Prime 15800 200
  rw [h, count_15800]
  decide
theorem count_16200 : Nat.count Nat.Prime 16200 = 1883 := by
  have h := Nat.count_add Nat.Prime 16000 200
  rw [h, count_16000]
  decide
theorem count_16400 : Nat.count Nat.Prime 16400 = 1900 := by
  have h := Nat.count_add Nat.Prime 16200 200
  rw [h, count_16200]
  decide
theorem count_16600 : Nat.count Nat.Prime 16600 = 1919 := by
  have h := Nat.count_add Nat.Prime 16400 200
  rw [h, count_16400]
  decide
theorem count_16800 : Nat.count Nat.Prime 16800 = 1939 := by
  have h := Nat.count_add Nat.Prime 16600 200
  rw [h, count_16600]
  decide
theorem count_17000 : Nat.count Nat.Prime 17000 = 1960 := by
  have h := Nat.count_add Nat.Prime 16800 200
  rw [h, count_16800]
  decide
theorem count_17200 : Nat.count Nat.Prime 17200 = 1980 := by
  have h := Nat.count_add Nat.Prime 17000 200
  rw [h, count_17000]
  decide
theorem count_17400 : Nat.count Nat.Prime 17400 = 2001 := by
  have h := Nat.count_add Nat.Prime 17200 200
  rw [h, count_17200]
  decide
theorem count_17600 : Nat.count Nat.Prime 17600 = 2024 := by
  have h := Nat.count_add Nat.Prime 17400 200
  rw [h, count_17400]
  decide
theorem count_17800 : Nat.count Nat.Prime 17800 = 2042 := by
  have h := Nat.count_add Nat.Prime 17600 200
  rw [h, count_17600]
  decide
theorem count_18000 : Nat.count Nat.Prime 18000 = 2064 := by
  have h := Nat.count_add Nat.Prime 17800 200
  rw [h, count_17800]
  decide
theorem count_18200 : Nat.count Nat.Prime 18200 = 2085 := by
  have h := Nat.count_add Nat.Prime 18000 200
  rw [h, count_18000]
  decide
theorem count_18400 : Nat.count Nat.Prime 18400 = 2107 := by
  have h := Nat.count_add Nat.Prime 18200 200
  rw [h, count_18200]
  decide
theorem count_18600 : Nat.count Nat.Prime 18600 = 2128 := by
  have h := Nat.count_add Nat.Prime 18400 200
  rw [h, count_18400]
  decide
theorem count_18800 : Nat.count Nat.Prime 18800 = 2145 := by
  have h := Nat.count_add Nat.Prime 18600 200
  rw [h, count_18600]
  decide
theorem count_19000 : Nat.count Nat.Prime 19000 = 2158 := by
  have h := Nat.count_add Nat.Prime 18800 200
  rw [h, count_18800]
  decide
theorem count_19200 : Nat.count Nat.Prime 19200 = 2176 := by
  have h := Nat.count_add Nat.Prime 19000 200
  rw [h, count_19000]
  decide
theorem count_19400 : Nat.count Nat.Prime 19400 = 2196 := by
  have h := Nat.count_add Nat.Prime 19200 200
  rw [h, count_19200]
  decide
theorem count_19600 : Nat.count Nat.Prime 19600 = 2223 := by
  have h := Nat.count_add Nat.Prime 19400 200
  rw [h, count_19400]
  decide
theorem count_19800 : Nat.count Nat.Prime 19800 = 2240 := by
  have h := Nat.count_add Nat.Prime 19600 200
  rw [h, count_19600]
  decide
theorem count_20000 : Nat.count Nat.Prime 20000 = 2262 := by
  have h := Nat.count_add Nat.Prime 19800 200
  rw [h, count_19800]
  decide
theorem count_20200 : Nat.count Nat.Prime 20200 = 2284 := by
  have h := Nat.count_add Nat.Prime 20000 200
  rw [h, count_20000]
  decide
theorem count_20400 : Nat.count Nat.Prime 20400 = 2305 := by
  have h := Nat.count_add Nat.Prime 20200 200
  rw [h, count_20200]
  decide
theorem count_20600 : Nat.count Nat.Prime 20600 = 2323 := by
  have h := Nat.count_add Nat.Prime 20400 200
  rw [h, count_20400]
  decide
theorem count_20800 : Nat.count Nat.Prime 20800 = 2342 := by
  have h := Nat.count_add Nat.Prime 20600 200
  rw [h, count_20600]
  decide
theorem count_21000 : Nat.count Nat.Prime 21000 = 2360 := by
  have h := Nat.count_add Nat.Prime 20800 200
  rw [h, count_20800]
  decide
theorem count_21200 : Nat.count Nat.Prime 21200 = 2384 := by
  have h := Nat.count_add Nat.Prime 21000 200
  rw [h, count_21000]
  decide
theorem count_21400 : Nat.count Nat.Prime 21400 = 2402 := by
  have h := Nat.count_add Nat.Prime 21200 200
  rw [h, count_21200]
  decide
theorem count_21600 : Nat.count Nat.Prime 21600 = 2425 := by
  have h := Nat.count_add Nat.Prime 21400 200
  rw [h, count_21400]
  decide
theorem count_21800 : Nat.count Nat.Prime 21800 = 2445 := by
  have h := Nat.count_add Nat.Prime 21600 200
  rw [h, count_21600]
  decide
theorem count_22000 : Nat.count Nat.Prime 22000 = 2464 := by
  have h := Nat.count_add Nat.Prime 21800 200
  rw [h, count_21800]
  decide
theorem count_22200 : Nat.count Nat.Prime 22200 = 2489 := by
  have h := Nat.count_add Nat.Prime 22000 200
  rw [h, count_22000]
  decide
theorem count_22400 : Nat.count Nat.Prime 22400 = 2507 := by
  have h := Nat.count_add Nat.Prime 22200 200
  rw [h, count_22200]
  decide
theorem count_22600 : Nat.count Nat.Prime 22600 = 2524 := by
  have h := Nat.count_add Nat.Prime 22400 200
  rw [h, count_22400]
  decide
theorem count_22800 : Nat.count Nat.Prime 22800 = 2547 := by
  have h := Nat.count_add Nat.Prime 22600 200
  rw [h, count_22600]
  decide
theorem count_23000 : Nat.count Nat.Prime 23000 = 2564 := by
  have h := Nat.count_add Nat.Prime 22800 200
  rw [h, count_22800]
  decide
theorem count_23200 : Nat.count Nat.Prime 23200 = 2588 := by
  have h := Nat.count_add Nat.Prime 23000 200
  rw [h, count_23000]
  decide
theorem count_23400 : Nat.count Nat.Prime 23400 = 2607 := by
  have h := Nat.count_add Nat.Prime 23200 200
  rw [h, count_23200]
  decide
theorem count_23600 : Nat.count Nat.Prime 23600 = 2625 := by
  have h := Nat.count_add Nat.Prime 23400 200
  rw [h, count_23400]
  decide
theorem count_23800 : Nat.count Nat.Prime 23800 = 2646 := by
  have h := Nat.count_add Nat.Prime 23600 200
  rw [h, count_23600]
  decide
theorem count_24000 : Nat.count Nat.Prime 24000 = 2668 := by
  have h := Nat.count_add Nat.Prime 23800 200
  rw [h, count_23800]
  decide
theorem count_24200 : Nat.count Nat.Prime 24200 = 2693 := by
  have h := Nat.count_add Nat.Prime 24000 200
  rw [h, count_24000]
  decide
theorem count_24400 : Nat.count Nat.Prime 24400 = 2708 := by
  have h := Nat.count_add Nat.Prime 24200 200
  rw [h, count_24200]
  decide
theorem count_24600 : Nat.count Nat.Prime 24600 = 2726 := by
  have h := Nat.count_add Nat.Prime 24400 200
  rw [h, count_24400]
  decide
theorem count_24800 : Nat.count Nat.Prime 24800 = 2743 := by
  have h := Nat.count_add Nat.Prime 24600 200
  rw [h, count_24600]
  decide
theorem count_25000 : Nat.count Nat.Prime 25000 = 2762 := by
  have h := Nat.count_add Nat.Prime 24800 200
  rw [h, count_24800]
  decide
theorem count_25200 : Nat.count Nat.Prime 25200 = 2781 := by
  have h := Nat.count_add Nat.Prime 25000 200
  rw [h, count_25000]
  decide
theorem count_25400 : Nat.count Nat.Prime 25400 = 2800 := by
  have h := Nat.count_add Nat.Prime 25200 200
  rw [h, count_25200]
  decide
theorem count_25600 : Nat.count Nat.Prime 25600 = 2818 := by
  have h := Nat.count_add Nat.Prime 25400 200
  rw [h, count_25400]
  decide
theorem count_25800 : Nat.count Nat.Prime 25800 = 2840 := by
  have h := Nat.count_add Nat.Prime 25600 200
  rw [h, count_25600]
  decide
theorem count_26000 : Nat.count Nat.Prime 26000 = 2860 := by
  have h := Nat.count_add Nat.Prime 25800 200
  rw [h, count_25800]
  decide
theorem count_26200 : Nat.count Nat.Prime 26200 = 2879 := by
  have h := Nat.count_add Nat.Prime 26000 200
  rw [h, count_26000]
  decide
theorem count_26400 : Nat.count Nat.Prime 26400 = 2900 := by
  have h := Nat.count_add Nat.Prime 26200 200
  rw [h, count_26200]
  decide
theorem count_26600 : Nat.count Nat.Prime 26600 = 2918 := by
  have h := Nat.count_add Nat.Prime 26400 200
  rw [h, count_26400]
  decide
theorem count_26800 : Nat.count Nat.Prime 26800 = 2939 := by
  have h := Nat.count_add Nat.Prime 26600 200
  rw [h, count_26600]
  decide
theorem count_27000 : Nat.count Nat.Prime 27000 = 2961 := by
  have h := Nat.count_add Nat.Prime 26800 200
  rw [h, count_26800]
  decide
theorem count_27200 : Nat.count Nat.Prime 27200 = 2979 := by
  have h := Nat.count_add Nat.Prime 27000 200
  rw [h, count_27000]
  decide
theorem count_27400 : Nat.count Nat.Prime 27400 = 2994 := by
  have h := Nat.count_add Nat.Prime 27200 200
  rw [h, count_27200]
  decide
theorem count_27600 : Nat.count Nat.Prime 27600 = 3012 := by
  have h := Nat.count_add Nat.Prime 27400 200
  rw [h, count_27400]
  decide
theorem count_27800 : Nat.count Nat.Prime 27800 = 3035 := by
  have h := Nat.count_add Nat.Prime 27600 200
  rw [h, count_27600]
  decide
theorem count_28000 : Nat.count Nat.Prime 28000 = 3055 := by
  have h := Nat.count_add Nat.Prime 27800 200
  rw [h, count_27800]
  decide
theorem count_28200 : Nat.count Nat.Prime 28200 = 3073 := by
  have h := Nat.count_add Nat.Prime 28000 200
  rw [h, count_28000]
  decide
theorem count_28400 : Nat.count Nat.Prime 28400 = 3089 := by
  have h := Nat.count_add Nat.Prime 28200 200
  rw [h, count_28200]
  decide
theorem count_28600 : Nat.count Nat.Prime 28600 = 3112 := by
  have h := Nat.count_add Nat.Prime 28400 200
  rw [h, count_28400]
  decide
theorem count_28800 : Nat.count Nat.Prime 28800 = 3136 := by
  have h := Nat.count_add Nat.Prime 28600 200
  rw [h, count_28600]
  decide
theorem count_29000 : Nat.count Nat.Prime 29000 = 3153 := by
  have h := Nat.count_add Nat.Prime 28800 200
  rw [h, count_28800]
  decide
theorem count_29200 : Nat.count Nat.Prime 29200 = 3173 := by
  have h := Nat.count_add Nat.Prime 29000 200
  rw [h, count_29000]
  decide
theorem count_29400 : Nat.count Nat.Prime 29400 = 3194 := by
  have h := Nat.count_add Nat.Prime 29200 200
  rw [h, count_29200]
  decide
theorem count_29600 : Nat.count Nat.Prime 29600 = 3213 := by
  have h := Nat.count_add Nat.Prime 29400 200
  rw [h, count_29400]
  decide
theorem count_29800 : Nat.count Nat.Prime 29800 = 3228 := by
  have h := Nat.count_add Nat.Prime 29600 200
  rw [h, count_29600]
  decide
theorem count_30000 : Nat.count Nat.Prime 30000 = 3245 := by
  have h := Nat.count_add Nat.Prime 29800 200
  rw [h, count_29800]
  decide
theorem count_30200 : Nat.count Nat.Prime 30200 = 3266 := by
  have h := Nat.count_add Nat.Prime 30000 200
  rw [h, count_30000]
  decide
theorem count_30400 : Nat.count Nat.Prime 30400 = 3284 := by
  have h := Nat.count_add Nat.Prime 30200 200
  rw [h, count_30200]
  decide
theorem count_30600 : Nat.count Nat.Prime 30600 = 3302 := by
  have h := Nat.count_add Nat.Prime 30400 200
  rw [h, count_30400]
  decide
theorem count_30800 : Nat.count Nat.Prime 30800 = 3319 := by
  have h := Nat.count_add Nat.Prime 30600 200
  rw [h, count_30600]
  decide
theorem count_31000 : Nat.count Nat.Prime 31000 = 3340 := by
  have h := Nat.count_add Nat.Prime 30800 200
  rw [h, count_30800]
  decide
theorem count_31200 : Nat.count Nat.Prime 31200 = 3362 := by
  have h := Nat.count_add Nat.Prime 31000 200
  rw [h, count_31000]
  decide
theorem count_31400 : Nat.count Nat.Prime 31400 = 3385 := by
  have h := Nat.count_add Nat.Prime 31200 200
  rw [h, count_31200]
  decide
theorem count_31600 : Nat.count Nat.Prime 31600 = 3399 := by
  have h := Nat.count_add Nat.Prime 31400 200
  rw [h, count_31400]
  decide
theorem count_31800 : Nat.count Nat.Prime 31800 = 3419 := by
  have h := Nat.count_add Nat.Prime 31600 200
  rw [h, count_31600]
  decide
theorem count_32000 : Nat.count Nat.Prime 32000 = 3432 := by
  have h := Nat.count_add Nat.Prime 31800 200
  rw [h, count_31800]
  decide
theorem count_32200 : Nat.count Nat.Prime 32200 = 3454 := by
  have h := Nat.count_add Nat.Prime 32000 200
  rw [h, count_32000]
  decide
theorem count_32400 : Nat.count Nat.Prime 32400 = 3476 := by
  have h := Nat.count_add Nat.Prime 32200 200
  rw [h, count_32200]
  decide
theorem count_32600 : Nat.count Nat.Prime 32600 = 3498 := by
  have h := Nat.count_add Nat.Prime 32400 200
  rw [h, count_32400]
  decide
theorem count_32800 : Nat.count Nat.Prime 32800 = 3517 := by
  have h := Nat.count_add Nat.Prime 32600 200
  rw [h, count_32600]
  decide
theorem count_33000 : Nat.count Nat.Prime 33000 = 3538 := by
  have h := Nat.count_add Nat.Prime 32800 200
  rw [h, count_32800]
  decide
theorem count_33200 : Nat.count Nat.Prime 33200 = 3558 := by
  have h := Nat.count_add Nat.Prime 33000 200
  rw [h, count_33000]
  decide
theorem count_33400 : Nat.count Nat.Prime 33400 = 3576 := by
  have h := Nat.count_add Nat.Prime 33200 200
  rw [h, count_33200]
  decide
theorem count_33600 : Nat.count Nat.Prime 33600 = 3598 := by
  have h := Nat.count_add Nat.Prime 33400 200
  rw [h, count_33400]
  decide
theorem count_33800 : Nat.count Nat.Prime 33800 = 3620 := by
  have h := Nat.count_add Nat.Prime 33600 200
  rw [h, count_33600]
  decide
theorem count_34000 : Nat.count Nat.Prime 34000 = 3638 := by
  have h := Nat.count_add Nat.Prime 33800 200
  rw [h, count_33800]
  decide
theorem count_34200 : Nat.count Nat.Prime 34200 = 3653 := by
  have h := Nat.count_add Nat.Prime 34000 200
  rw [h, count_34000]
  decide
theorem count_34400 : Nat.count Nat.Prime 34400 = 3675 := by
  have h := Nat.count_add Nat.Prime 34200 200
  rw [h, count_34200]
  decide
theorem count_34600 : Nat.count Nat.Prime 34600 = 3695 := by
  have h := Nat.count_add Nat.Prime 34400 200
  rw [h, count_34400]
  decide
theorem count_34800 : Nat.count Nat.Prime 34800 = 3715 := by
  have h := Nat.count_add Nat.Prime 34600 200
  rw [h, count_34600]
  decide
theorem count_35000 : Nat.count Nat.Prime 35000 = 3732 := by
  have h := Nat.count_add Nat.Prime 34800 200
  rw [h, count_34800]
  decide
theorem count_35200 : Nat.count Nat.Prime 35200 = 3751 := by
  have h := Nat.count_add Nat.Prime 35000 200
  rw [h, count_35000]
  decide
theorem count_35400 : Nat.count Nat.Prime 35400 = 3769 := by
  have h := Nat.count_add Nat.Prime 35200 200
  rw [h, count_35200]
  decide
theorem count_35600 : Nat.count Nat.Prime 35600 = 3791 := by
  have h := Nat.count_add Nat.Prime 35400 200
  rw [h, count_35400]
  decide
theorem count_35800 : Nat.count Nat.Prime 35800 = 3802 := by
  have h := Nat.count_add Nat.Prime 35600 200
  rw [h, count_35600]
  decide
theorem count_36000 : Nat.count Nat.Prime 36000 = 3824 := by
  have h := Nat.count_add Nat.Prime 35800 200
  rw [h, count_35800]
  decide
theorem count_36200 : Nat.count Nat.Prime 36200 = 3842 := by
  have h := Nat.count_add Nat.Prime 36000 200
  rw [h, count_36000]
  decide
theorem count_36400 : Nat.count Nat.Prime 36400 = 3861 := by
  have h := Nat.count_add Nat.Prime 36200 200
  rw [h, count_36200]
  decide
theorem count_36600 : Nat.count Nat.Prime 36600 = 3881 := by
  have h := Nat.count_add Nat.Prime 36400 200
  rw [h, count_36400]
  decide
theorem count_36800 : Nat.count Nat.Prime 36800 = 3903 := by
  have h := Nat.count_add Nat.Prime 36600 200
  rw [h, count_36600]
  decide
theorem count_37000 : Nat.count Nat.Prime 37000 = 3923 := by
  have h := Nat.count_add Nat.Prime 36800 200
  rw [h, count_36800]
  decide
theorem count_37200 : Nat.count Nat.Prime 37200 = 3941 := by
  have h := Nat.count_add Nat.Prime 37000 200
  rw [h, count_37000]
  decide
theorem count_37400 : Nat.count Nat.Prime 37400 = 3960 := by
  have h := Nat.count_add Nat.Prime 37200 200
  rw [h, count_37200]
  decide
theorem count_37600 : Nat.count Nat.Prime 37600 = 3983 := by
  have h := Nat.count_add Nat.Prime 37400 200
  rw [h, count_37400]
  decide
theorem count_37800 : Nat.count Nat.Prime 37800 = 3998 := by
  have h := Nat.count_add Nat.Prime 37600 200
  rw [h, count_37600]
  decide
theorem count_38000 : Nat.count Nat.Prime 38000 = 4017 := by
  have h := Nat.count_add Nat.Prime 37800 200
  rw [h, count_37800]
  decide
theorem count_38200 : Nat.count Nat.Prime 38200 = 4032 := by
  have h := Nat.count_add Nat.Prime 38000 200
  rw [h, count_38000]
  decide
theorem count_38400 : Nat.count Nat.Prime 38400 = 4052 := by
  have h := Nat.count_add Nat.Prime 38200 200
  rw [h, count_38200]
  decide
theorem count_38600 : Nat.count Nat.Prime 38600 = 4065 := by
  have h := Nat.count_add Nat.Prime 38400 200
  rw [h, count_38400]
  decide
theorem count_38800 : Nat.count Nat.Prime 38800 = 4088 := by
  have h := Nat.count_add Nat.Prime 38600 200
  rw [h, count_38600]
  decide
theorem count_39000 : Nat.count Nat.Prime 39000 = 4107 := by
  have h := Nat.count_add Nat.Prime 38800 200
  rw [h, count_38800]
  decide
theorem count_39200 : Nat.count Nat.Prime 39200 = 4127 := by
  have h := Nat.count_add Nat.Prime 39000 200
  rw [h, count_39000]
  decide
theorem count_39400 : Nat.count Nat.Prime 39400 = 4148 := by
  have h := Nat.count_add Nat.Prime 39200 200
  rw [h, count_39200]
  decide
theorem count_39600 : Nat.count Nat.Prime 39600 = 4164 := by
  have h := Nat.count_add Nat.Prime 39400 200
  rw [h, count_39400]
  decide
theorem count_39800 : Nat.count Nat.Prime 39800 = 4183 := by
  have h := Nat.count_add Nat.Prime 39600 200
  rw [h, count_39600]
  decide
theorem count_40000 : Nat.count Nat.Prime 40000 = 4203 := by
  have h := Nat.count_add Nat.Prime 39800 200
  rw [h, count_39800]
  decide
theorem count_40200 : Nat.count Nat.Prime 40200 = 4223 := by
  have h := Nat.count_add Nat.Prime 40000 200
  rw [h, count_40000]
  decide
theorem count_40400 : Nat.count Nat.Prime 40400 = 4236 := by
  have h := Nat.count_add Nat.Prime 40200 200
  rw [h, count_40200]
  decide
theorem count_40600 : Nat.count Nat.Prime 40600 = 4256 := by
  have h := Nat.count_add Nat.Prime 40400 200
  rw [h, count_40400]
  decide
theorem count_40800 : Nat.count Nat.Prime 40800 = 4270 := by
  have h := Nat.count_add Nat.Prime 40600 200
  rw [h, count_40600]
  decide
theorem count_41000 : Nat.count Nat.Prime 41000 = 4291 := by
  have h := Nat.count_add Nat.Prime 40800 200
  rw [h, count_40800]
  decide
theorem count_41200 : Nat.count Nat.Prime 41200 = 4311 := by
  have h := Nat.count_add Nat.Prime 41000 200
  rw [h, count_41000]
  decide
theorem count_41400 : Nat.count Nat.Prime 41400 = 4332 := by
  have h := Nat.count_add Nat.Prime 41200 200
  rw [h, count_41200]
  decide
theorem count_41600 : Nat.count Nat.Prime 41600 = 4349 := by
  have h := Nat.count_add Nat.Prime 41400 200
  rw [h, count_41400]
  decide
theorem count_41800 : Nat.count Nat.Prime 41800 = 4369 := by
  have h := Nat.count_add Nat.Prime 41600 200
  rw [h, count_41600]
  decide
theorem count_42000 : Nat.count Nat.Prime 42000 = 4392 := by
  have h := Nat.count_add Nat.Prime 41800 200
  rw [h, count_41800]
  decide
theorem count_42200 : Nat.count Nat.Prime 42200 = 4412 := by
  have h := Nat.count_add Nat.Prime 42000 200
  rw [h, count_42000]
  decide
theorem count_42400 : Nat.count Nat.Prime 42400 = 4432 := by
  have h := Nat.count_add Nat.Prime 42200 200
  rw [h, count_42200]
  decide
theorem count_42600 : Nat.count Nat.Prime 42600 = 4454 := by
  have h := Nat.count_add Nat.Prime 42400 200
  rw [h, count_42400]
  decide
theorem count_42800 : Nat.count Nat.Prime 42800 = 4476 := by
  have h := Nat.count_add Nat.Prime 42600 200
  rw [h, count_42600]
  decide
theorem count_43000 : Nat.count Nat.Prime 43000 = 4494 := by
  have h := Nat.count_add Nat.Prime 42800 200
  rw [h, count_42800]
  decide
theorem count_43200 : Nat.count Nat.Prime 43200 = 4510 := by
  have h := Nat.count_add Nat.Prime 43000 200
  rw [h, count_43000]
  decide
theorem count_43400 : Nat.count Nat.Prime 43400 = 4525 := by
  have h := Nat.count_add Nat.Prime 43200 200
  rw [h, count_43200]
  decide
theorem count_43600 : Nat.count Nat.Prime 43600 = 4542 := by
  have h := Nat.count_add Nat.Prime 43400 200
  rw [h, count_43400]
  decide
theorem count_43800 : Nat.count Nat.Prime 43800 = 4563 := by
  have h := Nat.count_add Nat.Prime 43600 200
  rw [h, count_43600]
  decide
theorem count_44000 : Nat.count Nat.Prime 44000 = 4579 := by
  have h := Nat.count_add Nat.Prime 43800 200
  rw [h, count_43800]
  decide
theorem count_44200 : Nat.count Nat.Prime 44200 = 4599 := by
  have h := Nat.count_add Nat.Prime 44000 200
  rw [h, count_44000]
  decide
theorem count_44400 : Nat.count Nat.Prime 44400 = 4618 := by
  have h := Nat.count_add Nat.Prime 44200 200
  rw [h, count_44200]
  decide
theorem count_44600 : Nat.count Nat.Prime 44600 = 4635 := by
  have h := Nat.count_add Nat.Prime 44400 200
  rw [h, count_44400]
  decide
theorem count_44800 : Nat.count Nat.Prime 44800 = 4656 := by
  have h := Nat.count_add Nat.Prime 44600 200
  rw [h, count_44600]
  decide
theorem count_45000 : Nat.count Nat.Prime 45000 = 4675 := by
  have h := Nat.count_add Nat.Prime 44800 200
  rw [h, count_44800]
  decide
theorem count_45200 : Nat.count Nat.Prime 45200 = 4692 := by
  have h := Nat.count_add Nat.Prime 45000 200
  rw [h, count_45000]
  decide
theorem count_45400 : Nat.count Nat.Prime 45400 = 4709 := by
  have h := Nat.count_add Nat.Prime 45200 200
  rw [h, count_45200]
  decide
theorem count_45600 : Nat.count Nat.Prime 45600 = 4727 := by
  have h := Nat.count_add Nat.Prime 45400 200
  rw [h, count_45400]
  decide
theorem count_45800 : Nat.count Nat.Prime 45800 = 4743 := by
  have h := Nat.count_add Nat.Prime 45600 200
  rw [h, count_45600]
  decide
theorem count_46000 : Nat.count Nat.Prime 46000 = 4761 := by
  have h := Nat.count_add Nat.Prime 45800 200
  rw [h, count_45800]
  decide
theorem count_46200 : Nat.count Nat.Prime 46200 = 4780 := by
  have h := Nat.count_add Nat.Prime 46000 200
  rw [h, count_46000]
  decide
theorem count_46400 : Nat.count Nat.Prime 46400 = 4796 := by
  have h := Nat.count_add Nat.Prime 46200 200
  rw [h, count_46200]
  decide
theorem count_46600 : Nat.count Nat.Prime 46600 = 4815 := by
  have h := Nat.count_add Nat.Prime 46400 200
  rw [h, count_46400]
  decide
theorem count_46800 : Nat.count Nat.Prime 46800 = 4834 := by
  have h := Nat.count_add Nat.Prime 46600 200
  rw [h, count_46600]
  decide
theorem count_47000 : Nat.count Nat.Prime 47000 = 4851 := by
  have h := Nat.count_add Nat.Prime 46800 200
  rw [h, count_46800]
  decide
theorem count_47200 : Nat.count Nat.Prime 47200 = 4868 := by
  have h := Nat.count_add Nat.Prime 47000 200
  rw [h, count_47000]
  decide
theorem count_47400 : Nat.count Nat.Prime 47400 = 4887 := by
  have h := Nat.count_add Nat.Prime 47200 200
  rw [h, count_47200]
  decide
theorem count_47600 : Nat.count Nat.Prime 47600 = 4907 := by
  have h := Nat.count_add Nat.Prime 47400 200
  rw [h, count_47400]
  decide
theorem count_47800 : Nat.count Nat.Prime 47800 = 4927 := by
  have h := Nat.count_add Nat.Prime 47600 200
  rw [h, count_47600]
  decide
