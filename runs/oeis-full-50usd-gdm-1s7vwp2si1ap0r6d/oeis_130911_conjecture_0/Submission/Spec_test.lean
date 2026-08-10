import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000

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

theorem nth_prime_num_42 : nth Nat.Prime 42 = 191 := by
  have h : count Nat.Prime 191 = 42 := by decide
  have h2 := nth_count (by decide : Nat.Prime 191)
  rw [h] at h2; exact h2

theorem nth_prime_num_43 : nth Nat.Prime 43 = 193 := by
  have h : count Nat.Prime 193 = 43 := by decide
  have h2 := nth_count (by decide : Nat.Prime 193)
  rw [h] at h2; exact h2

theorem nth_prime_num_44 : nth Nat.Prime 44 = 197 := by
  have h : count Nat.Prime 197 = 44 := by decide
  have h2 := nth_count (by decide : Nat.Prime 197)
  rw [h] at h2; exact h2

theorem nth_prime_num_45 : nth Nat.Prime 45 = 199 := by
  have h : count Nat.Prime 199 = 45 := by decide
  have h2 := nth_count (by decide : Nat.Prime 199)
  rw [h] at h2; exact h2

theorem nth_prime_num_46 : nth Nat.Prime 46 = 211 := by
  have h : count Nat.Prime 211 = 46 := by decide
  have h2 := nth_count (by decide : Nat.Prime 211)
  rw [h] at h2; exact h2

theorem nth_prime_num_47 : nth Nat.Prime 47 = 223 := by
  have h : count Nat.Prime 223 = 47 := by decide
  have h2 := nth_count (by decide : Nat.Prime 223)
  rw [h] at h2; exact h2

theorem nth_prime_num_48 : nth Nat.Prime 48 = 227 := by
  have h : count Nat.Prime 227 = 48 := by decide
  have h2 := nth_count (by decide : Nat.Prime 227)
  rw [h] at h2; exact h2

theorem nth_prime_num_49 : nth Nat.Prime 49 = 229 := by
  have h : count Nat.Prime 229 = 49 := by decide
  have h2 := nth_count (by decide : Nat.Prime 229)
  rw [h] at h2; exact h2

theorem nth_prime_num_50 : nth Nat.Prime 50 = 233 := by
  have h : count Nat.Prime 233 = 50 := by decide
  have h2 := nth_count (by decide : Nat.Prime 233)
  rw [h] at h2; exact h2

theorem nth_prime_num_51 : nth Nat.Prime 51 = 239 := by
  have h : count Nat.Prime 239 = 51 := by decide
  have h2 := nth_count (by decide : Nat.Prime 239)
  rw [h] at h2; exact h2

theorem nth_prime_num_52 : nth Nat.Prime 52 = 241 := by
  have h : count Nat.Prime 241 = 52 := by decide
  have h2 := nth_count (by decide : Nat.Prime 241)
  rw [h] at h2; exact h2

theorem nth_prime_num_53 : nth Nat.Prime 53 = 251 := by
  have h : count Nat.Prime 251 = 53 := by decide
  have h2 := nth_count (by decide : Nat.Prime 251)
  rw [h] at h2; exact h2

theorem nth_prime_num_54 : nth Nat.Prime 54 = 257 := by
  have h : count Nat.Prime 257 = 54 := by decide
  have h2 := nth_count (by decide : Nat.Prime 257)
  rw [h] at h2; exact h2

theorem nth_prime_num_55 : nth Nat.Prime 55 = 263 := by
  have h : count Nat.Prime 263 = 55 := by decide
  have h2 := nth_count (by decide : Nat.Prime 263)
  rw [h] at h2; exact h2

theorem nth_prime_num_56 : nth Nat.Prime 56 = 269 := by
  have h : count Nat.Prime 269 = 56 := by decide
  have h2 := nth_count (by decide : Nat.Prime 269)
  rw [h] at h2; exact h2

theorem nth_prime_num_57 : nth Nat.Prime 57 = 271 := by
  have h : count Nat.Prime 271 = 57 := by decide
  have h2 := nth_count (by decide : Nat.Prime 271)
  rw [h] at h2; exact h2

theorem nth_prime_num_58 : nth Nat.Prime 58 = 277 := by
  have h : count Nat.Prime 277 = 58 := by decide
  have h2 := nth_count (by decide : Nat.Prime 277)
  rw [h] at h2; exact h2

theorem nth_prime_num_59 : nth Nat.Prime 59 = 281 := by
  have h : count Nat.Prime 281 = 59 := by decide
  have h2 := nth_count (by decide : Nat.Prime 281)
  rw [h] at h2; exact h2

theorem nth_prime_num_60 : nth Nat.Prime 60 = 283 := by
  have h : count Nat.Prime 283 = 60 := by decide
  have h2 := nth_count (by decide : Nat.Prime 283)
  rw [h] at h2; exact h2

theorem nth_prime_num_61 : nth Nat.Prime 61 = 293 := by
  have h : count Nat.Prime 293 = 61 := by decide
  have h2 := nth_count (by decide : Nat.Prime 293)
  rw [h] at h2; exact h2

theorem nth_prime_num_62 : nth Nat.Prime 62 = 307 := by
  have h : count Nat.Prime 307 = 62 := by decide
  have h2 := nth_count (by decide : Nat.Prime 307)
  rw [h] at h2; exact h2

theorem nth_prime_num_63 : nth Nat.Prime 63 = 311 := by
  have h : count Nat.Prime 311 = 63 := by decide
  have h2 := nth_count (by decide : Nat.Prime 311)
  rw [h] at h2; exact h2

theorem nth_prime_num_64 : nth Nat.Prime 64 = 313 := by
  have h : count Nat.Prime 313 = 64 := by decide
  have h2 := nth_count (by decide : Nat.Prime 313)
  rw [h] at h2; exact h2

theorem nth_prime_num_65 : nth Nat.Prime 65 = 317 := by
  have h : count Nat.Prime 317 = 65 := by decide
  have h2 := nth_count (by decide : Nat.Prime 317)
  rw [h] at h2; exact h2

theorem nth_prime_num_66 : nth Nat.Prime 66 = 331 := by
  have h : count Nat.Prime 331 = 66 := by decide
  have h2 := nth_count (by decide : Nat.Prime 331)
  rw [h] at h2; exact h2

theorem nth_prime_num_67 : nth Nat.Prime 67 = 337 := by
  have h : count Nat.Prime 337 = 67 := by decide
  have h2 := nth_count (by decide : Nat.Prime 337)
  rw [h] at h2; exact h2

theorem nth_prime_num_68 : nth Nat.Prime 68 = 347 := by
  have h : count Nat.Prime 347 = 68 := by decide
  have h2 := nth_count (by decide : Nat.Prime 347)
  rw [h] at h2; exact h2

theorem nth_prime_num_69 : nth Nat.Prime 69 = 349 := by
  have h : count Nat.Prime 349 = 69 := by decide
  have h2 := nth_count (by decide : Nat.Prime 349)
  rw [h] at h2; exact h2

theorem nth_prime_num_70 : nth Nat.Prime 70 = 353 := by
  have h : count Nat.Prime 353 = 70 := by decide
  have h2 := nth_count (by decide : Nat.Prime 353)
  rw [h] at h2; exact h2

theorem nth_prime_num_71 : nth Nat.Prime 71 = 359 := by
  have h : count Nat.Prime 359 = 71 := by decide
  have h2 := nth_count (by decide : Nat.Prime 359)
  rw [h] at h2; exact h2

theorem nth_prime_num_72 : nth Nat.Prime 72 = 367 := by
  have h : count Nat.Prime 367 = 72 := by decide
  have h2 := nth_count (by decide : Nat.Prime 367)
  rw [h] at h2; exact h2

theorem nth_prime_num_73 : nth Nat.Prime 73 = 373 := by
  have h : count Nat.Prime 373 = 73 := by decide
  have h2 := nth_count (by decide : Nat.Prime 373)
  rw [h] at h2; exact h2

theorem nth_prime_num_74 : nth Nat.Prime 74 = 379 := by
  have h : count Nat.Prime 379 = 74 := by decide
  have h2 := nth_count (by decide : Nat.Prime 379)
  rw [h] at h2; exact h2

theorem nth_prime_num_75 : nth Nat.Prime 75 = 383 := by
  have h : count Nat.Prime 383 = 75 := by decide
  have h2 := nth_count (by decide : Nat.Prime 383)
  rw [h] at h2; exact h2

theorem nth_prime_num_76 : nth Nat.Prime 76 = 389 := by
  have h : count Nat.Prime 389 = 76 := by decide
  have h2 := nth_count (by decide : Nat.Prime 389)
  rw [h] at h2; exact h2

theorem nth_prime_num_77 : nth Nat.Prime 77 = 397 := by
  have h : count Nat.Prime 397 = 77 := by decide
  have h2 := nth_count (by decide : Nat.Prime 397)
  rw [h] at h2; exact h2

theorem nth_prime_num_78 : nth Nat.Prime 78 = 401 := by
  have h : count Nat.Prime 401 = 78 := by decide
  have h2 := nth_count (by decide : Nat.Prime 401)
  rw [h] at h2; exact h2

theorem nth_prime_num_79 : nth Nat.Prime 79 = 409 := by
  have h : count Nat.Prime 409 = 79 := by decide
  have h2 := nth_count (by decide : Nat.Prime 409)
  rw [h] at h2; exact h2

theorem nth_prime_num_80 : nth Nat.Prime 80 = 419 := by
  have h : count Nat.Prime 419 = 80 := by decide
  have h2 := nth_count (by decide : Nat.Prime 419)
  rw [h] at h2; exact h2

theorem nth_prime_num_81 : nth Nat.Prime 81 = 421 := by
  have h : count Nat.Prime 421 = 81 := by decide
  have h2 := nth_count (by decide : Nat.Prime 421)
  rw [h] at h2; exact h2

theorem A130911_0 : A130911 0 = 0 := by rfl

theorem A130911_1 : A130911 1 = 1 := by
  rw [A130911_step 0, A130911_0, nth_prime_zero_eq_two]
  simp

theorem A130911_2 : A130911 2 = 0 := by
  rw [A130911_step 1, A130911_1, nth_prime_one_eq_three]
  simp

theorem A130911_3 : A130911 3 = -1 := by
  rw [A130911_step 2, A130911_2, nth_prime_two_eq_five]
  simp

theorem A130911_4 : A130911 4 = 0 := by
  rw [A130911_step 3, A130911_3, nth_prime_three_eq_seven]
  simp

theorem A130911_5 : A130911 5 = 1 := by
  rw [A130911_step 4, A130911_4, nth_prime_four_eq_eleven]
  simp

theorem A130911_6 : A130911 6 = 2 := by
  rw [A130911_step 5, A130911_5, nth_prime_num_5]
  simp

theorem A130911_7 : A130911 7 = 1 := by
  rw [A130911_step 6, A130911_6, nth_prime_num_6]
  simp

theorem A130911_8 : A130911 8 = 2 := by
  rw [A130911_step 7, A130911_7, nth_prime_num_7]
  simp

theorem A130911_9 : A130911 9 = 1 := by
  rw [A130911_step 8, A130911_8, nth_prime_num_8]
  simp

theorem A130911_10 : A130911 10 = 0 := by
  rw [A130911_step 9, A130911_9, nth_prime_num_9]
  simp

theorem A130911_11 : A130911 11 = 1 := by
  rw [A130911_step 10, A130911_10, nth_prime_num_10]
  simp

theorem A130911_12 : A130911 12 = 2 := by
  rw [A130911_step 11, A130911_11, nth_prime_num_11]
  simp

theorem A130911_13 : A130911 13 = 3 := by
  rw [A130911_step 12, A130911_12, nth_prime_num_12]
  simp

theorem A130911_14 : A130911 14 = 2 := by
  rw [A130911_step 13, A130911_13, nth_prime_num_13]
  simp

theorem A130911_15 : A130911 15 = 3 := by
  rw [A130911_step 14, A130911_14, nth_prime_num_14]
  simp

theorem A130911_16 : A130911 16 = 2 := by
  rw [A130911_step 15, A130911_15, nth_prime_num_15]
  simp

theorem A130911_17 : A130911 17 = 3 := by
  rw [A130911_step 16, A130911_16, nth_prime_num_16]
  simp

theorem A130911_18 : A130911 18 = 4 := by
  rw [A130911_step 17, A130911_17, nth_prime_num_17]
  simp

theorem A130911_19 : A130911 19 = 5 := by
  rw [A130911_step 18, A130911_18, nth_prime_num_18]
  simp

theorem A130911_20 : A130911 20 = 4 := by
  rw [A130911_step 19, A130911_19, nth_prime_num_19]
  simp

theorem A130911_21 : A130911 21 = 5 := by
  rw [A130911_step 20, A130911_20, nth_prime_num_20]
  simp

theorem A130911_22 : A130911 22 = 6 := by
  rw [A130911_step 21, A130911_21, nth_prime_num_21]
  simp

theorem A130911_23 : A130911 23 = 5 := by
  rw [A130911_step 22, A130911_22, nth_prime_num_22]
  simp

theorem A130911_24 : A130911 24 = 4 := by
  rw [A130911_step 23, A130911_23, nth_prime_num_23]
  simp

theorem A130911_25 : A130911 25 = 5 := by
  rw [A130911_step 24, A130911_24, nth_prime_num_24]
  simp

theorem A130911_26 : A130911 26 = 4 := by
  rw [A130911_step 25, A130911_25, nth_prime_num_25]
  simp

theorem A130911_27 : A130911 27 = 5 := by
  rw [A130911_step 26, A130911_26, nth_prime_num_26]
  simp

theorem A130911_28 : A130911 28 = 6 := by
  rw [A130911_step 27, A130911_27, nth_prime_num_27]
  simp

theorem A130911_29 : A130911 29 = 7 := by
  rw [A130911_step 28, A130911_28, nth_prime_num_28]
  simp

theorem A130911_30 : A130911 30 = 6 := by
  rw [A130911_step 29, A130911_29, nth_prime_num_29]
  simp

theorem A130911_31 : A130911 31 = 7 := by
  rw [A130911_step 30, A130911_30, nth_prime_num_30]
  simp

theorem A130911_32 : A130911 32 = 8 := by
  rw [A130911_step 31, A130911_31, nth_prime_num_31]
  simp

theorem A130911_33 : A130911 33 = 9 := by
  rw [A130911_step 32, A130911_32, nth_prime_num_32]
  simp

theorem A130911_34 : A130911 34 = 8 := by
  rw [A130911_step 33, A130911_33, nth_prime_num_33]
  simp

theorem A130911_35 : A130911 35 = 7 := by
  rw [A130911_step 34, A130911_34, nth_prime_num_34]
  simp

theorem A130911_36 : A130911 36 = 8 := by
  rw [A130911_step 35, A130911_35, nth_prime_num_35]
  simp

theorem A130911_37 : A130911 37 = 9 := by
  rw [A130911_step 36, A130911_36, nth_prime_num_36]
  simp

theorem A130911_38 : A130911 38 = 8 := by
  rw [A130911_step 37, A130911_37, nth_prime_num_37]
  simp

theorem A130911_39 : A130911 39 = 9 := by
  rw [A130911_step 38, A130911_38, nth_prime_num_38]
  simp

theorem A130911_40 : A130911 40 = 10 := by
  rw [A130911_step 39, A130911_39, nth_prime_num_39]
  simp

theorem A130911_41 : A130911 41 = 11 := by
  rw [A130911_step 40, A130911_40, nth_prime_num_40]
  simp

theorem A130911_42 : A130911 42 = 12 := by
  rw [A130911_step 41, A130911_41, nth_prime_num_41]
  simp

theorem A130911_43 : A130911 43 = 13 := by
  rw [A130911_step 42, A130911_42, nth_prime_num_42]
  simp

theorem A130911_44 : A130911 44 = 14 := by
  rw [A130911_step 43, A130911_43, nth_prime_num_43]
  simp

theorem A130911_45 : A130911 45 = 13 := by
  rw [A130911_step 44, A130911_44, nth_prime_num_44]
  simp

theorem A130911_46 : A130911 46 = 14 := by
  rw [A130911_step 45, A130911_45, nth_prime_num_45]
  simp

theorem A130911_47 : A130911 47 = 15 := by
  rw [A130911_step 46, A130911_46, nth_prime_num_46]
  simp

theorem A130911_48 : A130911 48 = 16 := by
  rw [A130911_step 47, A130911_47, nth_prime_num_47]
  simp

theorem A130911_49 : A130911 49 = 17 := by
  rw [A130911_step 48, A130911_48, nth_prime_num_48]
  simp

theorem A130911_50 : A130911 50 = 18 := by
  rw [A130911_step 49, A130911_49, nth_prime_num_49]
  simp

theorem A130911_51 : A130911 51 = 19 := by
  rw [A130911_step 50, A130911_50, nth_prime_num_50]
  simp

theorem A130911_52 : A130911 52 = 20 := by
  rw [A130911_step 51, A130911_51, nth_prime_num_51]
  simp

theorem A130911_53 : A130911 53 = 21 := by
  rw [A130911_step 52, A130911_52, nth_prime_num_52]
  simp

theorem A130911_54 : A130911 54 = 22 := by
  rw [A130911_step 53, A130911_53, nth_prime_num_53]
  simp

theorem A130911_55 : A130911 55 = 21 := by
  rw [A130911_step 54, A130911_54, nth_prime_num_54]
  simp

theorem A130911_56 : A130911 56 = 20 := by
  rw [A130911_step 55, A130911_55, nth_prime_num_55]
  simp

theorem A130911_57 : A130911 57 = 19 := by
  rw [A130911_step 56, A130911_56, nth_prime_num_56]
  simp

theorem A130911_58 : A130911 58 = 20 := by
  rw [A130911_step 57, A130911_57, nth_prime_num_57]
  simp

theorem A130911_59 : A130911 59 = 19 := by
  rw [A130911_step 58, A130911_58, nth_prime_num_58]
  simp

theorem A130911_60 : A130911 60 = 18 := by
  rw [A130911_step 59, A130911_59, nth_prime_num_59]
  simp

theorem A130911_61 : A130911 61 = 19 := by
  rw [A130911_step 60, A130911_60, nth_prime_num_60]
  simp

theorem A130911_62 : A130911 62 = 18 := by
  rw [A130911_step 61, A130911_61, nth_prime_num_61]
  simp

theorem A130911_63 : A130911 63 = 19 := by
  rw [A130911_step 62, A130911_62, nth_prime_num_62]
  simp

theorem A130911_64 : A130911 64 = 18 := by
  rw [A130911_step 63, A130911_63, nth_prime_num_63]
  simp

theorem A130911_65 : A130911 65 = 19 := by
  rw [A130911_step 64, A130911_64, nth_prime_num_64]
  simp

theorem A130911_66 : A130911 66 = 18 := by
  rw [A130911_step 65, A130911_65, nth_prime_num_65]
  simp

theorem A130911_67 : A130911 67 = 19 := by
  rw [A130911_step 66, A130911_66, nth_prime_num_66]
  simp

theorem A130911_68 : A130911 68 = 18 := by
  rw [A130911_step 67, A130911_67, nth_prime_num_67]
  simp

theorem A130911_69 : A130911 69 = 17 := by
  rw [A130911_step 68, A130911_68, nth_prime_num_68]
  simp

theorem A130911_70 : A130911 70 = 16 := by
  rw [A130911_step 69, A130911_69, nth_prime_num_69]
  simp

theorem A130911_71 : A130911 71 = 15 := by
  rw [A130911_step 70, A130911_70, nth_prime_num_70]
  simp

theorem A130911_72 : A130911 72 = 14 := by
  rw [A130911_step 71, A130911_71, nth_prime_num_71]
  simp

theorem A130911_73 : A130911 73 = 15 := by
  rw [A130911_step 72, A130911_72, nth_prime_num_72]
  simp

theorem A130911_74 : A130911 74 = 14 := by
  rw [A130911_step 73, A130911_73, nth_prime_num_73]
  simp

theorem A130911_75 : A130911 75 = 15 := by
  rw [A130911_step 74, A130911_74, nth_prime_num_74]
  simp

theorem A130911_76 : A130911 76 = 14 := by
  rw [A130911_step 75, A130911_75, nth_prime_num_75]
  simp

theorem A130911_77 : A130911 77 = 13 := by
  rw [A130911_step 76, A130911_76, nth_prime_num_76]
  simp

theorem A130911_78 : A130911 78 = 14 := by
  rw [A130911_step 77, A130911_77, nth_prime_num_77]
  simp

theorem A130911_79 : A130911 79 = 13 := by
  rw [A130911_step 78, A130911_78, nth_prime_num_78]
  simp

theorem A130911_80 : A130911 80 = 14 := by
  rw [A130911_step 79, A130911_79, nth_prime_num_79]
  simp

theorem A130911_81 : A130911 81 = 15 := by
  rw [A130911_step 80, A130911_80, nth_prime_num_80]
  simp

theorem A130911_le_13_of_le_30 (n : ℕ) (h1 : n ≥ 11) (h2 : n ≤ 30) : A130911 n ≤ 13 := by
  interval_cases n
  · rw [A130911_11]; decide
  · rw [A130911_12]; decide
  · rw [A130911_13]; decide
  · rw [A130911_14]; decide
  · rw [A130911_15]; decide
  · rw [A130911_16]; decide
  · rw [A130911_17]; decide
  · rw [A130911_18]; decide
  · rw [A130911_19]; decide
  · rw [A130911_20]; decide
  · rw [A130911_21]; decide
  · rw [A130911_22]; decide
  · rw [A130911_23]; decide
  · rw [A130911_24]; decide
  · rw [A130911_25]; decide
  · rw [A130911_26]; decide
  · rw [A130911_27]; decide
  · rw [A130911_28]; decide
  · rw [A130911_29]; decide
  · rw [A130911_30]; decide

theorem A130911_le_13_of_le_50 (n : ℕ) (h1 : n ≥ 31) (h2 : n ≤ 50) : A130911 n ≤ 13 := by
  interval_cases n
  · rw [A130911_31]; decide
  · rw [A130911_32]; decide
  · rw [A130911_33]; decide
  · rw [A130911_34]; decide
  · rw [A130911_35]; decide
  · rw [A130911_36]; decide
  · rw [A130911_37]; decide
  · rw [A130911_38]; decide
  · rw [A130911_39]; decide
  · rw [A130911_40]; decide
  · rw [A130911_41]; decide
  · rw [A130911_42]; decide
  · rw [A130911_43]; decide
  · rw [A130911_44]; decide
  · rw [A130911_45]; decide
  · rw [A130911_46]; decide
  · rw [A130911_47]; decide
  · rw [A130911_48]; decide
  · rw [A130911_49]; decide
  · rw [A130911_50]; decide

theorem A130911_le_13_of_le_70 (n : ℕ) (h1 : n ≥ 51) (h2 : n ≤ 70) : A130911 n ≤ 13 := by
  interval_cases n
  · rw [A130911_51]; decide
  · rw [A130911_52]; decide
  · rw [A130911_53]; decide
  · rw [A130911_54]; decide
  · rw [A130911_55]; decide
  · rw [A130911_56]; decide
  · rw [A130911_57]; decide
  · rw [A130911_58]; decide
  · rw [A130911_59]; decide
  · rw [A130911_60]; decide
  · rw [A130911_61]; decide
  · rw [A130911_62]; decide
  · rw [A130911_63]; decide
  · rw [A130911_64]; decide
  · rw [A130911_65]; decide
  · rw [A130911_66]; decide
  · rw [A130911_67]; decide
  · rw [A130911_68]; decide
  · rw [A130911_69]; decide
  · rw [A130911_70]; decide

theorem A130911_le_13_of_le_78 (n : ℕ) (h1 : n ≥ 71) (h2 : n ≤ 78) : A130911 n ≤ 13 := by
  interval_cases n
  · rw [A130911_71]; decide
  · rw [A130911_72]; decide
  · rw [A130911_73]; decide
  · rw [A130911_74]; decide
  · rw [A130911_75]; decide
  · rw [A130911_76]; decide
  · rw [A130911_77]; decide
  · rw [A130911_78]; decide

theorem A130911_le_13_of_le_78_all (n : ℕ) (h1 : n ≥ 11) (h2 : n ≤ 78) : A130911 n ≤ 13 := by
  by_cases h3 : n ≤ 30
  · exact A130911_le_13_of_le_30 n h1 h3
  · by_cases h4 : n ≤ 50
    · have : n ≥ 31 := by omega
      exact A130911_le_13_of_le_50 n this h4
    · by_cases h5 : n ≤ 70
      · have : n ≥ 51 := by omega
        exact A130911_le_13_of_le_70 n this h5
      · have : n ≥ 71 := by omega
        exact A130911_le_13_of_le_78 n this h2

theorem sgn_not_minus_11 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 11 := by
  intro hn11; subst hn11
  have h_sgn11 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 11)) = 1 := by
    rw [nth_prime_num_11]; simp [digits_zero]
  rw [h_sgn11] at h_sgn; contradiction

theorem sgn_not_minus_12 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 12 := by
  intro hn12; subst hn12
  have h_sgn12 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 12)) = 1 := by
    rw [nth_prime_num_12]; simp [digits_zero]
  rw [h_sgn12] at h_sgn; contradiction

theorem sgn_not_minus_14 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 14 := by
  intro hn14; subst hn14
  have h_sgn14 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 14)) = 1 := by
    rw [nth_prime_num_14]; simp [digits_zero]
  rw [h_sgn14] at h_sgn; contradiction

theorem sgn_not_minus_16 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 16 := by
  intro hn16; subst hn16
  have h_sgn16 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 16)) = 1 := by
    rw [nth_prime_num_16]; simp [digits_zero]
  rw [h_sgn16] at h_sgn; contradiction

theorem sgn_not_minus_17 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 17 := by
  intro hn17; subst hn17
  have h_sgn17 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 17)) = 1 := by
    rw [nth_prime_num_17]; simp [digits_zero]
  rw [h_sgn17] at h_sgn; contradiction

theorem sgn_not_minus_18 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 18 := by
  intro hn18; subst hn18
  have h_sgn18 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 18)) = 1 := by
    rw [nth_prime_num_18]; simp [digits_zero]
  rw [h_sgn18] at h_sgn; contradiction

theorem sgn_not_minus_20 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 20 := by
  intro hn20; subst hn20
  have h_sgn20 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 20)) = 1 := by
    rw [nth_prime_num_20]; simp [digits_zero]
  rw [h_sgn20] at h_sgn; contradiction

theorem sgn_not_minus_21 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 21 := by
  intro hn21; subst hn21
  have h_sgn21 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 21)) = 1 := by
    rw [nth_prime_num_21]; simp [digits_zero]
  rw [h_sgn21] at h_sgn; contradiction

theorem sgn_not_minus_24 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 24 := by
  intro hn24; subst hn24
  have h_sgn24 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 24)) = 1 := by
    rw [nth_prime_num_24]; simp [digits_zero]
  rw [h_sgn24] at h_sgn; contradiction

theorem sgn_not_minus_26 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 26 := by
  intro hn26; subst hn26
  have h_sgn26 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 26)) = 1 := by
    rw [nth_prime_num_26]; simp [digits_zero]
  rw [h_sgn26] at h_sgn; contradiction

theorem sgn_not_minus_27 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 27 := by
  intro hn27; subst hn27
  have h_sgn27 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 27)) = 1 := by
    rw [nth_prime_num_27]; simp [digits_zero]
  rw [h_sgn27] at h_sgn; contradiction

theorem sgn_not_minus_28 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 28 := by
  intro hn28; subst hn28
  have h_sgn28 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 28)) = 1 := by
    rw [nth_prime_num_28]; simp [digits_zero]
  rw [h_sgn28] at h_sgn; contradiction

theorem sgn_not_minus_30 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 30 := by
  intro hn30; subst hn30
  have h_sgn30 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 30)) = 1 := by
    rw [nth_prime_num_30]; simp [digits_zero]
  rw [h_sgn30] at h_sgn; contradiction

theorem sgn_not_minus_31 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 31 := by
  intro hn31; subst hn31
  have h_sgn31 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 31)) = 1 := by
    rw [nth_prime_num_31]; simp [digits_zero]
  rw [h_sgn31] at h_sgn; contradiction

theorem sgn_not_minus_32 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 32 := by
  intro hn32; subst hn32
  have h_sgn32 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 32)) = 1 := by
    rw [nth_prime_num_32]; simp [digits_zero]
  rw [h_sgn32] at h_sgn; contradiction

theorem sgn_not_minus_35 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 35 := by
  intro hn35; subst hn35
  have h_sgn35 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 35)) = 1 := by
    rw [nth_prime_num_35]; simp [digits_zero]
  rw [h_sgn35] at h_sgn; contradiction

theorem sgn_not_minus_36 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 36 := by
  intro hn36; subst hn36
  have h_sgn36 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 36)) = 1 := by
    rw [nth_prime_num_36]; simp [digits_zero]
  rw [h_sgn36] at h_sgn; contradiction

theorem sgn_not_minus_38 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 38 := by
  intro hn38; subst hn38
  have h_sgn38 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 38)) = 1 := by
    rw [nth_prime_num_38]; simp [digits_zero]
  rw [h_sgn38] at h_sgn; contradiction

theorem sgn_not_minus_39 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 39 := by
  intro hn39; subst hn39
  have h_sgn39 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 39)) = 1 := by
    rw [nth_prime_num_39]; simp [digits_zero]
  rw [h_sgn39] at h_sgn; contradiction

theorem sgn_not_minus_40 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 40 := by
  intro hn40; subst hn40
  have h_sgn40 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 40)) = 1 := by
    rw [nth_prime_num_40]; simp [digits_zero]
  rw [h_sgn40] at h_sgn; contradiction

theorem sgn_not_minus_41 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 41 := by
  intro hn41; subst hn41
  have h_sgn41 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 41)) = 1 := by
    rw [nth_prime_num_41]; simp [digits_zero]
  rw [h_sgn41] at h_sgn; contradiction

theorem sgn_not_minus_42 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 42 := by
  intro hn42; subst hn42
  have h_sgn42 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 42)) = 1 := by
    rw [nth_prime_num_42]; simp [digits_zero]
  rw [h_sgn42] at h_sgn; contradiction

theorem sgn_not_minus_43 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 43 := by
  intro hn43; subst hn43
  have h_sgn43 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 43)) = 1 := by
    rw [nth_prime_num_43]; simp [digits_zero]
  rw [h_sgn43] at h_sgn; contradiction

theorem sgn_not_minus_45 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 45 := by
  intro hn45; subst hn45
  have h_sgn45 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 45)) = 1 := by
    rw [nth_prime_num_45]; simp [digits_zero]
  rw [h_sgn45] at h_sgn; contradiction

theorem sgn_not_minus_77 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 77 := by
  intro hn77; subst hn77
  have h_sgn77 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 77)) = 1 := by
    rw [nth_prime_num_77]; simp [digits_zero]
  rw [h_sgn77] at h_sgn; contradiction

theorem sgn_not_minus_79 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = -1) : n ≠ 79 := by
  intro hn79; subst hn79
  have h_sgn79 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 79)) = 1 := by
    rw [nth_prime_num_79]; simp [digits_zero]
  rw [h_sgn79] at h_sgn; contradiction

theorem sgn_not_plus_13 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 13 := by
  intro hn13; subst hn13
  have h_sgn13 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 13)) = -1 := by
    rw [nth_prime_num_13]; simp [digits_zero]
  rw [h_sgn13] at h_sgn; contradiction

theorem sgn_not_plus_15 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 15 := by
  intro hn15; subst hn15
  have h_sgn15 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 15)) = -1 := by
    rw [nth_prime_num_15]; simp [digits_zero]
  rw [h_sgn15] at h_sgn; contradiction

theorem sgn_not_plus_19 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 19 := by
  intro hn19; subst hn19
  have h_sgn19 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 19)) = -1 := by
    rw [nth_prime_num_19]; simp [digits_zero]
  rw [h_sgn19] at h_sgn; contradiction

theorem sgn_not_plus_22 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 22 := by
  intro hn22; subst hn22
  have h_sgn22 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 22)) = -1 := by
    rw [nth_prime_num_22]; simp [digits_zero]
  rw [h_sgn22] at h_sgn; contradiction

theorem sgn_not_plus_23 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 23 := by
  intro hn23; subst hn23
  have h_sgn23 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 23)) = -1 := by
    rw [nth_prime_num_23]; simp [digits_zero]
  rw [h_sgn23] at h_sgn; contradiction

theorem sgn_not_plus_25 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 25 := by
  intro hn25; subst hn25
  have h_sgn25 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 25)) = -1 := by
    rw [nth_prime_num_25]; simp [digits_zero]
  rw [h_sgn25] at h_sgn; contradiction

theorem sgn_not_plus_29 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 29 := by
  intro hn29; subst hn29
  have h_sgn29 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 29)) = -1 := by
    rw [nth_prime_num_29]; simp [digits_zero]
  rw [h_sgn29] at h_sgn; contradiction

theorem sgn_not_plus_33 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 33 := by
  intro hn33; subst hn33
  have h_sgn33 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 33)) = -1 := by
    rw [nth_prime_num_33]; simp [digits_zero]
  rw [h_sgn33] at h_sgn; contradiction

theorem sgn_not_plus_34 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 34 := by
  intro hn34; subst hn34
  have h_sgn34 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 34)) = -1 := by
    rw [nth_prime_num_34]; simp [digits_zero]
  rw [h_sgn34] at h_sgn; contradiction

theorem sgn_not_plus_37 (n : ℕ) (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime n)) = 1) : n ≠ 37 := by
  intro hn37; subst hn37
  have h_sgn37 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 37)) = -1 := by
    rw [nth_prime_num_37]; simp [digits_zero]
  rw [h_sgn37] at h_sgn; contradiction

