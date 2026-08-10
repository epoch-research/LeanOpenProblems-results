import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \\sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \\operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\\operatorname{prime}(k) = \\text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : Nat) : Nat :=
  if n < 39 then
    let start_idx : Nat := (n * (n - 1)) / 2
    Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)
  else
    2

theorem nth_of_count {p : Nat → Prop} [DecidablePred p] {n c : Nat} (hp : p n) (hc : Nat.count p n = c) : Nat.nth p c = n := by
  subst hc
  exact Nat.nth_count hp

theorem count_50 : Nat.count Nat.Prime 50 = 15 := by decide
theorem count_100 : Nat.count Nat.Prime 100 = 25 := by
  have h := Nat.count_add Nat.Prime 50 50
  rw [h, count_50]
  decide

theorem count_150 : Nat.count Nat.Prime 150 = 35 := by
  have h := Nat.count_add Nat.Prime 100 50
  rw [h, count_100]
  decide

theorem count_200 : Nat.count Nat.Prime 200 = 46 := by
  have h := Nat.count_add Nat.Prime 150 50
  rw [h, count_150]
  decide

theorem count_250 : Nat.count Nat.Prime 250 = 53 := by
  have h := Nat.count_add Nat.Prime 200 50
  rw [h, count_200]
  decide

theorem count_300 : Nat.count Nat.Prime 300 = 62 := by
  have h := Nat.count_add Nat.Prime 250 50
  rw [h, count_250]
  decide

theorem count_350 : Nat.count Nat.Prime 350 = 70 := by
  have h := Nat.count_add Nat.Prime 300 50
  rw [h, count_300]
  decide

theorem count_400 : Nat.count Nat.Prime 400 = 78 := by
  have h := Nat.count_add Nat.Prime 350 50
  rw [h, count_350]
  decide

theorem count_450 : Nat.count Nat.Prime 450 = 87 := by
  have h := Nat.count_add Nat.Prime 400 50
  rw [h, count_400]
  decide

theorem count_500 : Nat.count Nat.Prime 500 = 95 := by
  have h := Nat.count_add Nat.Prime 450 50
  rw [h, count_450]
  decide

theorem count_550 : Nat.count Nat.Prime 550 = 101 := by
  have h := Nat.count_add Nat.Prime 500 50
  rw [h, count_500]
  decide

theorem count_600 : Nat.count Nat.Prime 600 = 109 := by
  have h := Nat.count_add Nat.Prime 550 50
  rw [h, count_550]
  decide

theorem count_650 : Nat.count Nat.Prime 650 = 118 := by
  have h := Nat.count_add Nat.Prime 600 50
  rw [h, count_600]
  decide

theorem count_700 : Nat.count Nat.Prime 700 = 125 := by
  have h := Nat.count_add Nat.Prime 650 50
  rw [h, count_650]
  decide

theorem count_750 : Nat.count Nat.Prime 750 = 132 := by
  have h := Nat.count_add Nat.Prime 700 50
  rw [h, count_700]
  decide

theorem count_800 : Nat.count Nat.Prime 800 = 139 := by
  have h := Nat.count_add Nat.Prime 750 50
  rw [h, count_750]
  decide

theorem count_850 : Nat.count Nat.Prime 850 = 146 := by
  have h := Nat.count_add Nat.Prime 800 50
  rw [h, count_800]
  decide

theorem count_900 : Nat.count Nat.Prime 900 = 154 := by
  have h := Nat.count_add Nat.Prime 850 50
  rw [h, count_850]
  decide

theorem count_950 : Nat.count Nat.Prime 950 = 161 := by
  have h := Nat.count_add Nat.Prime 900 50
  rw [h, count_900]
  decide

theorem count_1000 : Nat.count Nat.Prime 1000 = 168 := by
  have h := Nat.count_add Nat.Prime 950 50
  rw [h, count_950]
  decide

theorem count_1050 : Nat.count Nat.Prime 1050 = 176 := by
  have h := Nat.count_add Nat.Prime 1000 50
  rw [h, count_1000]
  decide

theorem count_1100 : Nat.count Nat.Prime 1100 = 184 := by
  have h := Nat.count_add Nat.Prime 1050 50
  rw [h, count_1050]
  decide

theorem count_1150 : Nat.count Nat.Prime 1150 = 189 := by
  have h := Nat.count_add Nat.Prime 1100 50
  rw [h, count_1100]
  decide

theorem count_1200 : Nat.count Nat.Prime 1200 = 196 := by
  have h := Nat.count_add Nat.Prime 1150 50
  rw [h, count_1150]
  decide

theorem count_1250 : Nat.count Nat.Prime 1250 = 204 := by
  have h := Nat.count_add Nat.Prime 1200 50
  rw [h, count_1200]
  decide

theorem count_1300 : Nat.count Nat.Prime 1300 = 211 := by
  have h := Nat.count_add Nat.Prime 1250 50
  rw [h, count_1250]
  decide

theorem count_1350 : Nat.count Nat.Prime 1350 = 217 := by
  have h := Nat.count_add Nat.Prime 1300 50
  rw [h, count_1300]
  decide

theorem count_1400 : Nat.count Nat.Prime 1400 = 222 := by
  have h := Nat.count_add Nat.Prime 1350 50
  rw [h, count_1350]
  decide

theorem count_1450 : Nat.count Nat.Prime 1450 = 229 := by
  have h := Nat.count_add Nat.Prime 1400 50
  rw [h, count_1400]
  decide

theorem count_1500 : Nat.count Nat.Prime 1500 = 239 := by
  have h := Nat.count_add Nat.Prime 1450 50
  rw [h, count_1450]
  decide

theorem count_1550 : Nat.count Nat.Prime 1550 = 244 := by
  have h := Nat.count_add Nat.Prime 1500 50
  rw [h, count_1500]
  decide

theorem count_1600 : Nat.count Nat.Prime 1600 = 251 := by
  have h := Nat.count_add Nat.Prime 1550 50
  rw [h, count_1550]
  decide

theorem count_1650 : Nat.count Nat.Prime 1650 = 259 := by
  have h := Nat.count_add Nat.Prime 1600 50
  rw [h, count_1600]
  decide

theorem count_1700 : Nat.count Nat.Prime 1700 = 266 := by
  have h := Nat.count_add Nat.Prime 1650 50
  rw [h, count_1650]
  decide

theorem count_1750 : Nat.count Nat.Prime 1750 = 272 := by
  have h := Nat.count_add Nat.Prime 1700 50
  rw [h, count_1700]
  decide

theorem count_1800 : Nat.count Nat.Prime 1800 = 278 := by
  have h := Nat.count_add Nat.Prime 1750 50
  rw [h, count_1750]
  decide

theorem count_1850 : Nat.count Nat.Prime 1850 = 283 := by
  have h := Nat.count_add Nat.Prime 1800 50
  rw [h, count_1800]
  decide

theorem count_1900 : Nat.count Nat.Prime 1900 = 290 := by
  have h := Nat.count_add Nat.Prime 1850 50
  rw [h, count_1850]
  decide

theorem count_1950 : Nat.count Nat.Prime 1950 = 296 := by
  have h := Nat.count_add Nat.Prime 1900 50
  rw [h, count_1900]
  decide

theorem count_2000 : Nat.count Nat.Prime 2000 = 303 := by
  have h := Nat.count_add Nat.Prime 1950 50
  rw [h, count_1950]
  decide

theorem count_2050 : Nat.count Nat.Prime 2050 = 309 := by
  have h := Nat.count_add Nat.Prime 2000 50
  rw [h, count_2000]
  decide

theorem count_2100 : Nat.count Nat.Prime 2100 = 317 := by
  have h := Nat.count_add Nat.Prime 2050 50
  rw [h, count_2050]
  decide

theorem count_2150 : Nat.count Nat.Prime 2150 = 324 := by
  have h := Nat.count_add Nat.Prime 2100 50
  rw [h, count_2100]
  decide

theorem count_2200 : Nat.count Nat.Prime 2200 = 327 := by
  have h := Nat.count_add Nat.Prime 2150 50
  rw [h, count_2150]
  decide

theorem count_2250 : Nat.count Nat.Prime 2250 = 334 := by
  have h := Nat.count_add Nat.Prime 2200 50
  rw [h, count_2200]
  decide

theorem count_2300 : Nat.count Nat.Prime 2300 = 342 := by
  have h := Nat.count_add Nat.Prime 2250 50
  rw [h, count_2250]
  decide

theorem count_2350 : Nat.count Nat.Prime 2350 = 348 := by
  have h := Nat.count_add Nat.Prime 2300 50
  rw [h, count_2300]
  decide

theorem count_2400 : Nat.count Nat.Prime 2400 = 357 := by
  have h := Nat.count_add Nat.Prime 2350 50
  rw [h, count_2350]
  decide

theorem count_2450 : Nat.count Nat.Prime 2450 = 363 := by
  have h := Nat.count_add Nat.Prime 2400 50
  rw [h, count_2400]
  decide

theorem count_2500 : Nat.count Nat.Prime 2500 = 367 := by
  have h := Nat.count_add Nat.Prime 2450 50
  rw [h, count_2450]
  decide

theorem count_2550 : Nat.count Nat.Prime 2550 = 373 := by
  have h := Nat.count_add Nat.Prime 2500 50
  rw [h, count_2500]
  decide

theorem count_2600 : Nat.count Nat.Prime 2600 = 378 := by
  have h := Nat.count_add Nat.Prime 2550 50
  rw [h, count_2550]
  decide

theorem count_2650 : Nat.count Nat.Prime 2650 = 383 := by
  have h := Nat.count_add Nat.Prime 2600 50
  rw [h, count_2600]
  decide

theorem count_2700 : Nat.count Nat.Prime 2700 = 393 := by
  have h := Nat.count_add Nat.Prime 2650 50
  rw [h, count_2650]
  decide

theorem count_2750 : Nat.count Nat.Prime 2750 = 401 := by
  have h := Nat.count_add Nat.Prime 2700 50
  rw [h, count_2700]
  decide

theorem count_2800 : Nat.count Nat.Prime 2800 = 407 := by
  have h := Nat.count_add Nat.Prime 2750 50
  rw [h, count_2750]
  decide

theorem count_2850 : Nat.count Nat.Prime 2850 = 413 := by
  have h := Nat.count_add Nat.Prime 2800 50
  rw [h, count_2800]
  decide

theorem count_2900 : Nat.count Nat.Prime 2900 = 419 := by
  have h := Nat.count_add Nat.Prime 2850 50
  rw [h, count_2850]
  decide

theorem count_2950 : Nat.count Nat.Prime 2950 = 424 := by
  have h := Nat.count_add Nat.Prime 2900 50
  rw [h, count_2900]
  decide

theorem count_3000 : Nat.count Nat.Prime 3000 = 430 := by
  have h := Nat.count_add Nat.Prime 2950 50
  rw [h, count_2950]
  decide

theorem count_3050 : Nat.count Nat.Prime 3050 = 437 := by
  have h := Nat.count_add Nat.Prime 3000 50
  rw [h, count_3000]
  decide

theorem count_3100 : Nat.count Nat.Prime 3100 = 442 := by
  have h := Nat.count_add Nat.Prime 3050 50
  rw [h, count_3050]
  decide

theorem count_3150 : Nat.count Nat.Prime 3150 = 446 := by
  have h := Nat.count_add Nat.Prime 3100 50
  rw [h, count_3100]
  decide

theorem count_3200 : Nat.count Nat.Prime 3200 = 452 := by
  have h := Nat.count_add Nat.Prime 3150 50
  rw [h, count_3150]
  decide

theorem count_3250 : Nat.count Nat.Prime 3250 = 457 := by
  have h := Nat.count_add Nat.Prime 3200 50
  rw [h, count_3200]
  decide

theorem count_3300 : Nat.count Nat.Prime 3300 = 463 := by
  have h := Nat.count_add Nat.Prime 3250 50
  rw [h, count_3250]
  decide

theorem count_3350 : Nat.count Nat.Prime 3350 = 472 := by
  have h := Nat.count_add Nat.Prime 3300 50
  rw [h, count_3300]
  decide

theorem count_3400 : Nat.count Nat.Prime 3400 = 478 := by
  have h := Nat.count_add Nat.Prime 3350 50
  rw [h, count_3350]
  decide

theorem count_3450 : Nat.count Nat.Prime 3450 = 482 := by
  have h := Nat.count_add Nat.Prime 3400 50
  rw [h, count_3400]
  decide

theorem count_3500 : Nat.count Nat.Prime 3500 = 489 := by
  have h := Nat.count_add Nat.Prime 3450 50
  rw [h, count_3450]
  decide

theorem count_3550 : Nat.count Nat.Prime 3550 = 497 := by
  have h := Nat.count_add Nat.Prime 3500 50
  rw [h, count_3500]
  decide

theorem count_3600 : Nat.count Nat.Prime 3600 = 503 := by
  have h := Nat.count_add Nat.Prime 3550 50
  rw [h, count_3550]
  decide

theorem count_3650 : Nat.count Nat.Prime 3650 = 510 := by
  have h := Nat.count_add Nat.Prime 3600 50
  rw [h, count_3600]
  decide

theorem count_3700 : Nat.count Nat.Prime 3700 = 516 := by
  have h := Nat.count_add Nat.Prime 3650 50
  rw [h, count_3650]
  decide

theorem count_3750 : Nat.count Nat.Prime 3750 = 522 := by
  have h := Nat.count_add Nat.Prime 3700 50
  rw [h, count_3700]
  decide

theorem count_3800 : Nat.count Nat.Prime 3800 = 528 := by
  have h := Nat.count_add Nat.Prime 3750 50
  rw [h, count_3750]
  decide

theorem count_3850 : Nat.count Nat.Prime 3850 = 533 := by
  have h := Nat.count_add Nat.Prime 3800 50
  rw [h, count_3800]
  decide

theorem count_3900 : Nat.count Nat.Prime 3900 = 539 := by
  have h := Nat.count_add Nat.Prime 3850 50
  rw [h, count_3850]
  decide

theorem count_3950 : Nat.count Nat.Prime 3950 = 548 := by
  have h := Nat.count_add Nat.Prime 3900 50
  rw [h, count_3900]
  decide

theorem count_4000 : Nat.count Nat.Prime 4000 = 550 := by
  have h := Nat.count_add Nat.Prime 3950 50
  rw [h, count_3950]
  decide

theorem count_4050 : Nat.count Nat.Prime 4050 = 558 := by
  have h := Nat.count_add Nat.Prime 4000 50
  rw [h, count_4000]
  decide

theorem count_4100 : Nat.count Nat.Prime 4100 = 565 := by
  have h := Nat.count_add Nat.Prime 4050 50
  rw [h, count_4050]
  decide

theorem count_4150 : Nat.count Nat.Prime 4150 = 570 := by
  have h := Nat.count_add Nat.Prime 4100 50
  rw [h, count_4100]
  decide

theorem count_4200 : Nat.count Nat.Prime 4200 = 574 := by
  have h := Nat.count_add Nat.Prime 4150 50
  rw [h, count_4150]
  decide

theorem count_4250 : Nat.count Nat.Prime 4250 = 582 := by
  have h := Nat.count_add Nat.Prime 4200 50
  rw [h, count_4200]
  decide

theorem count_4300 : Nat.count Nat.Prime 4300 = 590 := by
  have h := Nat.count_add Nat.Prime 4250 50
  rw [h, count_4250]
  decide

theorem count_4350 : Nat.count Nat.Prime 4350 = 594 := by
  have h := Nat.count_add Nat.Prime 4300 50
  rw [h, count_4300]
  decide

theorem count_4400 : Nat.count Nat.Prime 4400 = 599 := by
  have h := Nat.count_add Nat.Prime 4350 50
  rw [h, count_4350]
  decide

theorem count_4450 : Nat.count Nat.Prime 4450 = 604 := by
  have h := Nat.count_add Nat.Prime 4400 50
  rw [h, count_4400]
  decide

theorem count_4500 : Nat.count Nat.Prime 4500 = 610 := by
  have h := Nat.count_add Nat.Prime 4450 50
  rw [h, count_4450]
  decide

theorem count_4550 : Nat.count Nat.Prime 4550 = 617 := by
  have h := Nat.count_add Nat.Prime 4500 50
  rw [h, count_4500]
  decide

theorem count_4600 : Nat.count Nat.Prime 4600 = 622 := by
  have h := Nat.count_add Nat.Prime 4550 50
  rw [h, count_4550]
  decide

theorem count_4650 : Nat.count Nat.Prime 4650 = 628 := by
  have h := Nat.count_add Nat.Prime 4600 50
  rw [h, count_4600]
  decide

theorem count_4700 : Nat.count Nat.Prime 4700 = 634 := by
  have h := Nat.count_add Nat.Prime 4650 50
  rw [h, count_4650]
  decide

theorem count_4750 : Nat.count Nat.Prime 4750 = 639 := by
  have h := Nat.count_add Nat.Prime 4700 50
  rw [h, count_4700]
  decide

theorem count_4800 : Nat.count Nat.Prime 4800 = 646 := by
  have h := Nat.count_add Nat.Prime 4750 50
  rw [h, count_4750]
  decide

theorem count_4850 : Nat.count Nat.Prime 4850 = 650 := by
  have h := Nat.count_add Nat.Prime 4800 50
  rw [h, count_4800]
  decide

theorem count_4900 : Nat.count Nat.Prime 4900 = 654 := by
  have h := Nat.count_add Nat.Prime 4850 50
  rw [h, count_4850]
  decide

theorem count_4950 : Nat.count Nat.Prime 4950 = 661 := by
  have h := Nat.count_add Nat.Prime 4900 50
  rw [h, count_4900]
  decide

theorem count_5000 : Nat.count Nat.Prime 5000 = 669 := by
  have h := Nat.count_add Nat.Prime 4950 50
  rw [h, count_4950]
  decide

theorem count_5050 : Nat.count Nat.Prime 5050 = 675 := by
  have h := Nat.count_add Nat.Prime 5000 50
  rw [h, count_5000]
  decide

theorem count_5100 : Nat.count Nat.Prime 5100 = 681 := by
  have h := Nat.count_add Nat.Prime 5050 50
  rw [h, count_5050]
  decide

theorem count_5150 : Nat.count Nat.Prime 5150 = 686 := by
  have h := Nat.count_add Nat.Prime 5100 50
  rw [h, count_5100]
  decide

theorem count_5200 : Nat.count Nat.Prime 5200 = 692 := by
  have h := Nat.count_add Nat.Prime 5150 50
  rw [h, count_5150]
  decide

theorem count_5250 : Nat.count Nat.Prime 5250 = 697 := by
  have h := Nat.count_add Nat.Prime 5200 50
  rw [h, count_5200]
  decide

theorem count_5300 : Nat.count Nat.Prime 5300 = 702 := by
  have h := Nat.count_add Nat.Prime 5250 50
  rw [h, count_5250]
  decide

theorem count_5350 : Nat.count Nat.Prime 5350 = 707 := by
  have h := Nat.count_add Nat.Prime 5300 50
  rw [h, count_5300]
  decide

theorem count_5400 : Nat.count Nat.Prime 5400 = 712 := by
  have h := Nat.count_add Nat.Prime 5350 50
  rw [h, count_5350]
  decide

theorem count_5450 : Nat.count Nat.Prime 5450 = 721 := by
  have h := Nat.count_add Nat.Prime 5400 50
  rw [h, count_5400]
  decide

theorem count_5500 : Nat.count Nat.Prime 5500 = 725 := by
  have h := Nat.count_add Nat.Prime 5450 50
  rw [h, count_5450]
  decide

theorem count_5550 : Nat.count Nat.Prime 5550 = 732 := by
  have h := Nat.count_add Nat.Prime 5500 50
  rw [h, count_5500]
  decide

theorem count_5600 : Nat.count Nat.Prime 5600 = 738 := by
  have h := Nat.count_add Nat.Prime 5550 50
  rw [h, count_5550]
  decide

theorem count_5650 : Nat.count Nat.Prime 5650 = 741 := by
  have h := Nat.count_add Nat.Prime 5600 50
  rw [h, count_5600]
  decide

theorem nth_prime_0 : Nat.nth Nat.Prime 0 = 2 := nth_of_count (by decide) (by decide)