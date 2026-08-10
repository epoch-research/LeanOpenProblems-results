import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000
set_option kernel.maxMemory 0

open Nat Finset

/--
A130911: $a(n)$ is the number of primes with odd binary weight among the first $n$ primes minus the number with an even binary weight.
Primes with odd binary weight are called odious primes (A027697); primes with even binary weight are called evil primes (A027699).
$$a(n) = \sum_{k=1}^n \left( \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is odd}\}} - \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is even}\}} \right)$$
where $p_k$ is the $k$-th prime number.
-/
noncomputable def A130911 (n : ℕ) : ℤ :=
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ :=
    if (binary_weight p).bodd then 1 else -1
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

theorem A130911_step (n : ℕ) : A130911 (n+1) = A130911 n +
  (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
   let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
   weight_parity_sign (Nat.nth Nat.Prime n)) := by
  dsimp [A130911]
  rw [sum_range_succ]

theorem nth_prime_num_5 : nth Nat.Prime 5 = 13 := by
  have h : count Nat.Prime 13 = 5 := by decide
  have h2 := nth_count (by decide : Nat.Prime 13)
  rw [h] at h2; exact h2

theorem nth_prime_num_6 : nth Nat.Prime 6 = 17 := by
  have h : count Nat.Prime 17 = 6 := by decide
  have h2 := nth_count (by decide : Nat.Prime 17)
  rw [h] at h2; exact h2

theorem nth_prime_num_7 : nth Nat.Prime 7 = 19 := by
  have h : count Nat.Prime 19 = 7 := by decide
  have h2 := nth_count (by decide : Nat.Prime 19)
  rw [h] at h2; exact h2

theorem nth_prime_num_8 : nth Nat.Prime 8 = 23 := by
  have h : count Nat.Prime 23 = 8 := by decide
  have h2 := nth_count (by decide : Nat.Prime 23)
  rw [h] at h2; exact h2

theorem nth_prime_num_9 : nth Nat.Prime 9 = 29 := by
  have h : count Nat.Prime 29 = 9 := by decide
  have h2 := nth_count (by decide : Nat.Prime 29)
  rw [h] at h2; exact h2

theorem nth_prime_num_10 : nth Nat.Prime 10 = 31 := by
  have h : count Nat.Prime 31 = 10 := by decide
  have h2 := nth_count (by decide : Nat.Prime 31)
  rw [h] at h2; exact h2

theorem nth_prime_num_11 : nth Nat.Prime 11 = 37 := by
  have h : count Nat.Prime 37 = 11 := by decide
  have h2 := nth_count (by decide : Nat.Prime 37)
  rw [h] at h2; exact h2

theorem nth_prime_num_12 : nth Nat.Prime 12 = 41 := by
  have h : count Nat.Prime 41 = 12 := by decide
  have h2 := nth_count (by decide : Nat.Prime 41)
  rw [h] at h2; exact h2

theorem nth_prime_num_13 : nth Nat.Prime 13 = 43 := by
  have h : count Nat.Prime 43 = 13 := by decide
  have h2 := nth_count (by decide : Nat.Prime 43)
  rw [h] at h2; exact h2

theorem nth_prime_num_14 : nth Nat.Prime 14 = 47 := by
  have h : count Nat.Prime 47 = 14 := by decide
  have h2 := nth_count (by decide : Nat.Prime 47)
  rw [h] at h2; exact h2

theorem nth_prime_num_15 : nth Nat.Prime 15 = 53 := by
  have h : count Nat.Prime 53 = 15 := by decide
  have h2 := nth_count (by decide : Nat.Prime 53)
  rw [h] at h2; exact h2

theorem nth_prime_num_16 : nth Nat.Prime 16 = 59 := by
  have h : count Nat.Prime 59 = 16 := by decide
  have h2 := nth_count (by decide : Nat.Prime 59)
  rw [h] at h2; exact h2

theorem nth_prime_num_17 : nth Nat.Prime 17 = 61 := by
  have h : count Nat.Prime 61 = 17 := by decide
  have h2 := nth_count (by decide : Nat.Prime 61)
  rw [h] at h2; exact h2

theorem nth_prime_num_18 : nth Nat.Prime 18 = 67 := by
  have h : count Nat.Prime 67 = 18 := by decide
  have h2 := nth_count (by decide : Nat.Prime 67)
  rw [h] at h2; exact h2

theorem nth_prime_num_19 : nth Nat.Prime 19 = 71 := by
  have h : count Nat.Prime 71 = 19 := by decide
  have h2 := nth_count (by decide : Nat.Prime 71)
  rw [h] at h2; exact h2

theorem nth_prime_num_20 : nth Nat.Prime 20 = 73 := by
  have h : count Nat.Prime 73 = 20 := by decide
  have h2 := nth_count (by decide : Nat.Prime 73)
  rw [h] at h2; exact h2

theorem nth_prime_num_21 : nth Nat.Prime 21 = 79 := by
  have h : count Nat.Prime 79 = 21 := by decide
  have h2 := nth_count (by decide : Nat.Prime 79)
  rw [h] at h2; exact h2

theorem nth_prime_num_22 : nth Nat.Prime 22 = 83 := by
  have h : count Nat.Prime 83 = 22 := by decide
  have h2 := nth_count (by decide : Nat.Prime 83)
  rw [h] at h2; exact h2

theorem nth_prime_num_23 : nth Nat.Prime 23 = 89 := by
  have h : count Nat.Prime 89 = 23 := by decide
  have h2 := nth_count (by decide : Nat.Prime 89)
  rw [h] at h2; exact h2

theorem nth_prime_num_24 : nth Nat.Prime 24 = 97 := by
  have h : count Nat.Prime 97 = 24 := by decide
  have h2 := nth_count (by decide : Nat.Prime 97)
  rw [h] at h2; exact h2

theorem nth_prime_num_25 : nth Nat.Prime 25 = 101 := by
  have h : count Nat.Prime 101 = 25 := by decide
  have h2 := nth_count (by decide : Nat.Prime 101)
  rw [h] at h2; exact h2

theorem nth_prime_num_26 : nth Nat.Prime 26 = 103 := by
  have h : count Nat.Prime 103 = 26 := by decide
  have h2 := nth_count (by decide : Nat.Prime 103)
  rw [h] at h2; exact h2

theorem nth_prime_num_27 : nth Nat.Prime 27 = 107 := by
  have h : count Nat.Prime 107 = 27 := by decide
  have h2 := nth_count (by decide : Nat.Prime 107)
  rw [h] at h2; exact h2

theorem nth_prime_num_28 : nth Nat.Prime 28 = 109 := by
  have h : count Nat.Prime 109 = 28 := by decide
  have h2 := nth_count (by decide : Nat.Prime 109)
  rw [h] at h2; exact h2

theorem nth_prime_num_29 : nth Nat.Prime 29 = 113 := by
  have h : count Nat.Prime 113 = 29 := by decide
  have h2 := nth_count (by decide : Nat.Prime 113)
  rw [h] at h2; exact h2

theorem nth_prime_num_30 : nth Nat.Prime 30 = 127 := by
  have h : count Nat.Prime 127 = 30 := by decide
  have h2 := nth_count (by decide : Nat.Prime 127)
  rw [h] at h2; exact h2

theorem nth_prime_num_31 : nth Nat.Prime 31 = 131 := by
  have h : count Nat.Prime 131 = 31 := by decide
  have h2 := nth_count (by decide : Nat.Prime 131)
  rw [h] at h2; exact h2

theorem nth_prime_num_32 : nth Nat.Prime 32 = 137 := by
  have h : count Nat.Prime 137 = 32 := by decide
  have h2 := nth_count (by decide : Nat.Prime 137)
  rw [h] at h2; exact h2

theorem nth_prime_num_33 : nth Nat.Prime 33 = 139 := by
  have h : count Nat.Prime 139 = 33 := by decide
  have h2 := nth_count (by decide : Nat.Prime 139)
  rw [h] at h2; exact h2

theorem nth_prime_num_34 : nth Nat.Prime 34 = 149 := by
  have h : count Nat.Prime 149 = 34 := by decide
  have h2 := nth_count (by decide : Nat.Prime 149)
  rw [h] at h2; exact h2

theorem nth_prime_num_35 : nth Nat.Prime 35 = 151 := by
  have h : count Nat.Prime 151 = 35 := by decide
  have h2 := nth_count (by decide : Nat.Prime 151)
  rw [h] at h2; exact h2

theorem nth_prime_num_36 : nth Nat.Prime 36 = 157 := by
  have h : count Nat.Prime 157 = 36 := by decide
  have h2 := nth_count (by decide : Nat.Prime 157)
  rw [h] at h2; exact h2

theorem nth_prime_num_37 : nth Nat.Prime 37 = 163 := by
  have h : count Nat.Prime 163 = 37 := by decide
  have h2 := nth_count (by decide : Nat.Prime 163)
  rw [h] at h2; exact h2

theorem nth_prime_num_38 : nth Nat.Prime 38 = 167 := by
  have h : count Nat.Prime 167 = 38 := by decide
  have h2 := nth_count (by decide : Nat.Prime 167)
  rw [h] at h2; exact h2

theorem nth_prime_num_39 : nth Nat.Prime 39 = 173 := by
  have h : count Nat.Prime 173 = 39 := by decide
  have h2 := nth_count (by decide : Nat.Prime 173)
  rw [h] at h2; exact h2

theorem nth_prime_num_40 : nth Nat.Prime 40 = 179 := by
  have h : count Nat.Prime 179 = 40 := by decide
  have h2 := nth_count (by decide : Nat.Prime 179)
  rw [h] at h2; exact h2

theorem nth_prime_num_41 : nth Nat.Prime 41 = 181 := by
  have h : count Nat.Prime 181 = 41 := by decide
  have h2 := nth_count (by decide : Nat.Prime 181)
  rw [h] at h2; exact h2

