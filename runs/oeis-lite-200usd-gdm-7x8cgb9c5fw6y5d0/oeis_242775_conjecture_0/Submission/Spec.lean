import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Nat Set

/-- The number $b_k$, consisting of $k$ threes. $b_k = (10^k - 1)/3$. -/
def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3

/-- The number of decimal digits of $p$. -/
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length

/-- Concatenation of $b_k$ and $p$. -/
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p

/-- The $n$-th prime (1-indexed). -/
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/--
A242775: Let $b_k=3\dots3$ consist of $k\ge 1$ 3's. Then $a(n)$ is the smallest $k$ such that the concatenation $b_k$ and $\operatorname{prime}(n)$ is prime, or $a(n)=0$ if there is no such prime.
-/
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n

    -- The set S of all k >= 1 such that the concatenated number is prime.
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }

    -- Nat.sInf S is the minimum element of S. If S is empty, Nat.sInf S = 0 is the convention for ℕ.
    sInf S

theorem dvd_3_pow_10_sub_1 (k : ℕ) : 3 ∣ 10 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 10 ^ (k + 1) - 1 = 9 * 10 ^ k + (10 ^ k - 1) := by omega
    rw [h1]
    apply dvd_add
    · omega
    · exact ih

theorem rep_threes_spec (k : ℕ) : 3 * rep_threes k = 10 ^ k - 1 := by
  unfold rep_threes
  exact Nat.mul_div_cancel' (dvd_3_pow_10_sub_1 k)

theorem sub_one_mul_add (x y : ℕ) (hx : x ≥ 1) : (x - 1) * y + y = x * y := by
  have h : x - 1 + 1 = x := Nat.sub_add_cancel hx
  rw [← Nat.succ_mul]
  show (x - 1 + 1) * y = x * y
  rw [h]

theorem concat_spec (k : ℕ) : 3 * concatenate k 2593 + 2221 = 10 ^ (k + 4) := by
  unfold concatenate
  have h_num : num_digits 2593 = 4 := by
    unfold num_digits
    simp
  rw [h_num]
  have h_mul : 3 * (rep_threes k * 10 ^ 4 + 2593) + 2221 = (3 * rep_threes k) * 10000 + 10000 := by ring
  rw [h_mul, rep_threes_spec k]
  have h_pow_gt : 10 ^ k ≥ 1 := by
    have : 10 ^ k ≥ 10 ^ 0 := Nat.pow_le_pow_right (by omega) (by omega)
    exact this
  rw [sub_one_mul_add (10 ^ k) 10000 h_pow_gt]
  ring

theorem concat_sub_spec (k : ℕ) : 3 * concatenate k 2593 = 10 ^ (k + 4) - 2221 := by
  have h := concat_spec k
  omega

theorem not_prime_of_dvd_of_gt {a b : ℕ} (hb : b > 1) (h_dvd : b ∣ a) (h_gt : a > b) : ¬ Nat.Prime a := by
  intro h_prime
  have h_eq := h_prime.eq_one_or_self_of_dvd b h_dvd
  omega

theorem dvd_11_pow_10_2_1 (m : ℕ) : 11 ∣ 10 ^ (2 * m) * 100000 - 2221 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 10 ^ (2 * (m + 1)) * 100000 - 2221 = (10 ^ 2 - 1) * (10 ^ (2 * m) * 100000) + (10 ^ (2 * m) * 100000 - 2221) := by
      have h2 : 10 ^ (2 * (m + 1)) = 100 * 10 ^ (2 * m) := by ring
      rw [h2]
      omega
    rw [h1]
    apply dvd_add
    · apply dvd_mul_of_dvd_left; decide
    · exact ih

theorem dvd_of_11_mul_three (n : ℕ) (h : 11 ∣ 3 * n) : 11 ∣ n := by
  have h_coprime : Nat.Coprime 11 3 := by rfl
  have h_comm : 3 * n = n * 3 := Nat.mul_comm 3 n
  rw [h_comm] at h
  exact h_coprime.dvd_of_dvd_mul_right h

theorem div_11_of_odd (k : ℕ) (hk : k > 0) (hodd : k % 2 = 1) : 11 ∣ concatenate k 2593 := by
  have h_odd : ∃ m, k = 2 * m + 1 := by
    use k / 2
    omega
  rcases h_odd with ⟨m, hm⟩
  have h_div_3 : 11 ∣ 3 * (concatenate k 2593) := by
    rw [concat_sub_spec k, hm]
    have h_pow : 10 ^ (2 * m + 1 + 4) = 10 ^ (2 * m) * 100000 := by
      have : 2 * m + 1 + 4 = 2 * m + 5 := by omega
      rw [this, Nat.pow_add]
    rw [h_pow]
    exact dvd_11_pow_10_2_1 m
  exact dvd_of_11_mul_three (concatenate k 2593) h_div_3

theorem dvd_101_pow_10_4_2 (m : ℕ) : 101 ∣ 10 ^ (4 * m) * 1000000 - 2221 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 10 ^ (4 * (m + 1)) * 1000000 - 2221 = (10 ^ 4 - 1) * (10 ^ (4 * m) * 1000000) + (10 ^ (4 * m) * 1000000 - 2221) := by
      have h2 : 10 ^ (4 * (m + 1)) = 10000 * 10 ^ (4 * m) := by ring
      rw [h2]
      omega
    rw [h1]
    apply dvd_add
    · apply dvd_mul_of_dvd_left; decide
    · exact ih

theorem dvd_of_101_mul_three (n : ℕ) (h : 101 ∣ 3 * n) : 101 ∣ n := by
  have h_coprime : Nat.Coprime 101 3 := by rfl
  have h_comm : 3 * n = n * 3 := Nat.mul_comm 3 n
  rw [h_comm] at h
  exact h_coprime.dvd_of_dvd_mul_right h

theorem div_101_of_mod_4_2 (k : ℕ) (hk : k > 0) (h4 : k % 4 = 2) : 101 ∣ concatenate k 2593 := by
  have h_mod4 : ∃ m, k = 4 * m + 2 := by
    use k / 4
    omega
  rcases h_mod4 with ⟨m, hm⟩
  have h_div_3 : 101 ∣ 3 * (concatenate k 2593) := by
    rw [concat_sub_spec k, hm]
    have h_pow : 10 ^ (4 * m + 2 + 4) = 10 ^ (4 * m) * 1000000 := by
      have : 4 * m + 2 + 4 = 4 * m + 6 := by omega
      rw [this, Nat.pow_add]
    rw [h_pow]
    exact dvd_101_pow_10_4_2 m
  exact dvd_of_101_mul_three (concatenate k 2593) h_div_3

theorem dvd_7_pow_10_6_4 (m : ℕ) : 7 ∣ 10 ^ (6 * m) * 100000000 - 2221 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 10 ^ (6 * (m + 1)) * 100000000 - 2221 = (10 ^ 6 - 1) * (10 ^ (6 * m) * 100000000) + (10 ^ (6 * m) * 100000000 - 2221) := by
      have h2 : 10 ^ (6 * (m + 1)) = 1000000 * 10 ^ (6 * m) := by ring
      rw [h2]
      omega
    rw [h1]
    apply dvd_add
    · apply dvd_mul_of_dvd_left; decide
    · exact ih

theorem dvd_of_7_mul_three (n : ℕ) (h : 7 ∣ 3 * n) : 7 ∣ n := by
  have h_coprime : Nat.Coprime 7 3 := by rfl
  have h_comm : 3 * n = n * 3 := Nat.mul_comm 3 n
  rw [h_comm] at h
  exact h_coprime.dvd_of_dvd_mul_right h

theorem div_7_of_mod_6_4 (k : ℕ) (hk : k > 0) (h6 : k % 6 = 4) : 7 ∣ concatenate k 2593 := by
  have h_mod6 : ∃ m, k = 6 * m + 4 := by
    use k / 6
    omega
  rcases h_mod6 with ⟨m, hm⟩
  have h_div_3 : 7 ∣ 3 * (concatenate k 2593) := by
    rw [concat_sub_spec k, hm]
    have h_pow : 10 ^ (6 * m + 4 + 4) = 10 ^ (6 * m) * 100000000 := by
      have : 6 * m + 4 + 4 = 6 * m + 8 := by omega
      rw [this, Nat.pow_add]
    rw [h_pow]
    exact dvd_7_pow_10_6_4 m
  exact dvd_of_7_mul_three (concatenate k 2593) h_div_3

theorem dvd_37_pow_10_3_2 (m : ℕ) : 37 ∣ 10 ^ (3 * m) * 1000000 - 2221 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 10 ^ (3 * (m + 1)) * 1000000 - 2221 = (10 ^ 3 - 1) * (10 ^ (3 * m) * 1000000) + (10 ^ (3 * m) * 1000000 - 2221) := by
      have h2 : 10 ^ (3 * (m + 1)) = 1000 * 10 ^ (3 * m) := by ring
      rw [h2]
      omega
    rw [h1]
    apply dvd_add
    · apply dvd_mul_of_dvd_left; decide
    · exact ih

theorem dvd_of_37_mul_three (n : ℕ) (h : 37 ∣ 3 * n) : 37 ∣ n := by
  have h_coprime : Nat.Coprime 37 3 := by rfl
  have h_comm : 3 * n = n * 3 := Nat.mul_comm 3 n
  rw [h_comm] at h
  exact h_coprime.dvd_of_dvd_mul_right h

theorem div_37_of_mod_3_2 (k : ℕ) (hk : k > 0) (h3 : k % 3 = 2) : 37 ∣ concatenate k 2593 := by
  have h_mod3 : ∃ m, k = 3 * m + 2 := by
    use k / 3
    omega
  rcases h_mod3 with ⟨m, hm⟩
  have h_div_3 : 37 ∣ 3 * (concatenate k 2593) := by
    rw [concat_sub_spec k, hm]
    have h_pow : 10 ^ (3 * m + 2 + 4) = 10 ^ (3 * m) * 1000000 := by
      have : 3 * m + 2 + 4 = 3 * m + 6 := by omega
      rw [this, Nat.pow_add]
    rw [h_pow]
    exact dvd_37_pow_10_3_2 m
  exact dvd_of_37_mul_three (concatenate k 2593) h_div_3

theorem count_primes_100 : Nat.count Nat.Prime 100 = 25 := by decide
theorem count_primes_chunk_1 : Nat.count (fun x => Nat.Prime (100 + x)) 100 = 21 := by decide
theorem count_primes_200 : Nat.count Nat.Prime 200 = 46 := by
  have h_add : 200 = 100 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_100, count_primes_chunk_1]

theorem count_primes_chunk_2 : Nat.count (fun x => Nat.Prime (200 + x)) 100 = 16 := by decide
theorem count_primes_300 : Nat.count Nat.Prime 300 = 62 := by
  have h_add : 300 = 200 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_200, count_primes_chunk_2]

theorem count_primes_chunk_3 : Nat.count (fun x => Nat.Prime (300 + x)) 100 = 16 := by decide
theorem count_primes_400 : Nat.count Nat.Prime 400 = 78 := by
  have h_add : 400 = 300 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_300, count_primes_chunk_3]

theorem count_primes_chunk_4 : Nat.count (fun x => Nat.Prime (400 + x)) 100 = 17 := by decide
theorem count_primes_500 : Nat.count Nat.Prime 500 = 95 := by
  have h_add : 500 = 400 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_400, count_primes_chunk_4]

theorem count_primes_chunk_5 : Nat.count (fun x => Nat.Prime (500 + x)) 100 = 14 := by decide
theorem count_primes_600 : Nat.count Nat.Prime 600 = 109 := by
  have h_add : 600 = 500 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_500, count_primes_chunk_5]

theorem count_primes_chunk_6 : Nat.count (fun x => Nat.Prime (600 + x)) 100 = 16 := by decide
theorem count_primes_700 : Nat.count Nat.Prime 700 = 125 := by
  have h_add : 700 = 600 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_600, count_primes_chunk_6]

theorem count_primes_chunk_7 : Nat.count (fun x => Nat.Prime (700 + x)) 100 = 14 := by decide
theorem count_primes_800 : Nat.count Nat.Prime 800 = 139 := by
  have h_add : 800 = 700 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_700, count_primes_chunk_7]

theorem count_primes_chunk_8 : Nat.count (fun x => Nat.Prime (800 + x)) 100 = 15 := by decide
theorem count_primes_900 : Nat.count Nat.Prime 900 = 154 := by
  have h_add : 900 = 800 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_800, count_primes_chunk_8]

theorem count_primes_chunk_9 : Nat.count (fun x => Nat.Prime (900 + x)) 100 = 14 := by decide
theorem count_primes_1000 : Nat.count Nat.Prime 1000 = 168 := by
  have h_add : 1000 = 900 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_900, count_primes_chunk_9]

theorem count_primes_chunk_10 : Nat.count (fun x => Nat.Prime (1000 + x)) 100 = 16 := by decide
theorem count_primes_1100 : Nat.count Nat.Prime 1100 = 184 := by
  have h_add : 1100 = 1000 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1000, count_primes_chunk_10]

theorem count_primes_chunk_11 : Nat.count (fun x => Nat.Prime (1100 + x)) 100 = 12 := by decide
theorem count_primes_1200 : Nat.count Nat.Prime 1200 = 196 := by
  have h_add : 1200 = 1100 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1100, count_primes_chunk_11]

theorem count_primes_chunk_12 : Nat.count (fun x => Nat.Prime (1200 + x)) 100 = 15 := by decide
theorem count_primes_1300 : Nat.count Nat.Prime 1300 = 211 := by
  have h_add : 1300 = 1200 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1200, count_primes_chunk_12]

theorem count_primes_chunk_13 : Nat.count (fun x => Nat.Prime (1300 + x)) 100 = 11 := by decide
theorem count_primes_1400 : Nat.count Nat.Prime 1400 = 222 := by
  have h_add : 1400 = 1300 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1300, count_primes_chunk_13]

theorem count_primes_chunk_14 : Nat.count (fun x => Nat.Prime (1400 + x)) 100 = 17 := by decide
theorem count_primes_1500 : Nat.count Nat.Prime 1500 = 239 := by
  have h_add : 1500 = 1400 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1400, count_primes_chunk_14]

theorem count_primes_chunk_15 : Nat.count (fun x => Nat.Prime (1500 + x)) 100 = 12 := by decide
theorem count_primes_1600 : Nat.count Nat.Prime 1600 = 251 := by
  have h_add : 1600 = 1500 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1500, count_primes_chunk_15]

theorem count_primes_chunk_16 : Nat.count (fun x => Nat.Prime (1600 + x)) 100 = 15 := by decide
theorem count_primes_1700 : Nat.count Nat.Prime 1700 = 266 := by
  have h_add : 1700 = 1600 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1600, count_primes_chunk_16]

theorem count_primes_chunk_17 : Nat.count (fun x => Nat.Prime (1700 + x)) 100 = 12 := by decide
theorem count_primes_1800 : Nat.count Nat.Prime 1800 = 278 := by
  have h_add : 1800 = 1700 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1700, count_primes_chunk_17]

theorem count_primes_chunk_18 : Nat.count (fun x => Nat.Prime (1800 + x)) 100 = 12 := by decide
theorem count_primes_1900 : Nat.count Nat.Prime 1900 = 290 := by
  have h_add : 1900 = 1800 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1800, count_primes_chunk_18]

theorem count_primes_chunk_19 : Nat.count (fun x => Nat.Prime (1900 + x)) 100 = 13 := by decide
theorem count_primes_2000 : Nat.count Nat.Prime 2000 = 303 := by
  have h_add : 2000 = 1900 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_1900, count_primes_chunk_19]

theorem count_primes_chunk_20 : Nat.count (fun x => Nat.Prime (2000 + x)) 100 = 14 := by decide
theorem count_primes_2100 : Nat.count Nat.Prime 2100 = 317 := by
  have h_add : 2100 = 2000 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_2000, count_primes_chunk_20]

theorem count_primes_chunk_21 : Nat.count (fun x => Nat.Prime (2100 + x)) 100 = 10 := by decide
theorem count_primes_2200 : Nat.count Nat.Prime 2200 = 327 := by
  have h_add : 2200 = 2100 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_2100, count_primes_chunk_21]

theorem count_primes_chunk_22 : Nat.count (fun x => Nat.Prime (2200 + x)) 100 = 15 := by decide
theorem count_primes_2300 : Nat.count Nat.Prime 2300 = 342 := by
  have h_add : 2300 = 2200 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_2200, count_primes_chunk_22]

theorem count_primes_chunk_23 : Nat.count (fun x => Nat.Prime (2300 + x)) 100 = 15 := by decide
theorem count_primes_2400 : Nat.count Nat.Prime 2400 = 357 := by
  have h_add : 2400 = 2300 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_2300, count_primes_chunk_23]

theorem count_primes_chunk_24 : Nat.count (fun x => Nat.Prime (2400 + x)) 100 = 10 := by decide
theorem count_primes_2500 : Nat.count Nat.Prime 2500 = 367 := by
  have h_add : 2500 = 2400 + 100 := by omega
  rw [h_add, Nat.count_add, count_primes_2400, count_primes_chunk_24]

theorem count_primes_chunk_25 : Nat.count (fun x => Nat.Prime (2500 + x)) 93 = 10 := by decide
theorem count_primes_2593 : Nat.count Nat.Prime 2593 = 377 := by
  have h_add : 2593 = 2500 + 93 := by omega
  rw [h_add, Nat.count_add, count_primes_2500, count_primes_chunk_25]


theorem prime_of_index_378 : prime_of_index 378 = 2593 := by
  unfold prime_of_index
  have h_prime : Nat.Prime 2593 := by decide
  have h_count : Nat.count Nat.Prime 2593 = 377 := count_primes_2593
  have h_nth := Nat.nth_count h_prime
  rw [h_count] at h_nth
  exact h_nth


set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

theorem dvd_pow_sub_one (a m q : ℕ) (h : q ∣ a - 1) : q ∣ a ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : a ^ (m + 1) - 1 = (a - 1) * a ^ m + (a ^ m - 1) := by
      rw [Nat.pow_succ]
      omega
    rw [h1]
    apply dvd_add
    · apply dvd_mul_of_dvd_left h
    · exact ih

theorem dvd_pow_pow_sub_one (E m q : ℕ) (h : q ∣ 10 ^ E - 1) : q ∣ 10 ^ (E * m) - 1 := by
  have h_base : q ∣ (10 ^ E) ^ m - 1 := dvd_pow_sub_one (10 ^ E) m q h
  have h_eq : (10 ^ E) ^ m = 10 ^ (E * m) := by
    rw [← Nat.pow_mul]
    ring_nf
  rw [h_eq] at h_base
  exact h_base

theorem dvd_template (q E R m : ℕ) (hA : q ∣ 10 ^ E - 1) (hB : q ∣ 10 ^ R - 2221) (hR : 10 ^ R ≥ 2221) : q ∣ 10 ^ (E * m) * 10 ^ R - 2221 := by
  have h_div : q ∣ 10 ^ (E * m) - 1 := dvd_pow_pow_sub_one E m q hA
  have h_alg : 10 ^ (E * m) * 10 ^ R - 2221 = (10 ^ (E * m) - 1) * 10 ^ R + (10 ^ R - 2221) := by
    rw [Nat.sub_mul, one_mul]
    have h_le : 1 * 10 ^ R ≤ 10 ^ (E * m) * 10 ^ R := by
      have : 10 ^ (E * m) ≥ 1 := Nat.one_le_pow _ 10 (by decide)
      omega
    rw [one_mul] at h_le
    exact Nat.sub_add_cancel h_le
  rw [h_alg]
  apply dvd_add
  · apply dvd_mul_of_dvd_left h_div
  · exact hB

theorem dvd_of_coprime_3 (q : ℕ) (hq : Nat.Prime q) (hq3 : q ≠ 3) (n : ℕ) (h : q ∣ 3 * n) : q ∣ n := by
  have h_coprime : Nat.Coprime q 3 := by
    apply (Nat.Prime.coprime_iff_not_dvd hq).mpr
    intro hdvd
    have h_eq : q = 3 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three q hdvd) with h1 | h2
      · have h_prime_q := hq.ne_one
        omega
      · exact h2
    exact hq3 h_eq
  have h_comm : 3 * n = n * 3 := Nat.mul_comm 3 n
  rw [h_comm] at h
  exact h_coprime.dvd_of_dvd_mul_right h

theorem prime_2593 : Nat.Prime 2593 := by
  have h_nth : Nat.Prime (prime_of_index 378) := by
    unfold prime_of_index
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 377
  rw [prime_of_index_378] at h_nth
  exact h_nth

theorem dvd_23_pow_10_11_8 (m : ℕ) : 23 ∣ 10 ^ (132 * m) * 10 ^ 100 - 2221 :=
  dvd_template 23 132 100 m (by decide) (by decide) (by decide)

theorem div_23_of_mod_11_8 (m : ℕ) (h_mod : m % 11 = 8) : 23 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 23 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (132 * (m / 11)) * 10 ^ 100 := by
      have h_eq : 12 * m + 4 = 132 * (m / 11) + 100 := by
        have h_div : m = 11 * (m / 11) + (m % 11) := (Nat.div_add_mod m 11).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_23_pow_10_11_8 (m / 11)
  exact dvd_of_coprime_3 23 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_31_pow_10_5_4 (m : ℕ) : 31 ∣ 10 ^ (60 * m) * 10 ^ 52 - 2221 :=
  dvd_template 31 60 52 m (by decide) (by decide) (by decide)

theorem div_31_of_mod_5_4 (m : ℕ) (h_mod : m % 5 = 4) : 31 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 31 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (60 * (m / 5)) * 10 ^ 52 := by
      have h_eq : 12 * m + 4 = 60 * (m / 5) + 52 := by
        have h_div : m = 5 * (m / 5) + (m % 5) := (Nat.div_add_mod m 5).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_31_pow_10_5_4 (m / 5)
  exact dvd_of_coprime_3 31 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_61_pow_10_5_2 (m : ℕ) : 61 ∣ 10 ^ (60 * m) * 10 ^ 28 - 2221 :=
  dvd_template 61 60 28 m (by decide) (by decide) (by decide)

theorem div_61_of_mod_5_2 (m : ℕ) (h_mod : m % 5 = 2) : 61 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 61 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (60 * (m / 5)) * 10 ^ 28 := by
      have h_eq : 12 * m + 4 = 60 * (m / 5) + 28 := by
        have h_div : m = 5 * (m / 5) + (m % 5) := (Nat.div_add_mod m 5).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_61_pow_10_5_2 (m / 5)
  exact dvd_of_coprime_3 61 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_67_pow_10_11_8 (m : ℕ) : 67 ∣ 10 ^ (132 * m) * 10 ^ 100 - 2221 :=
  dvd_template 67 132 100 m (by decide) (by decide) (by decide)

theorem div_67_of_mod_11_8 (m : ℕ) (h_mod : m % 11 = 8) : 67 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 67 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (132 * (m / 11)) * 10 ^ 100 := by
      have h_eq : 12 * m + 4 = 132 * (m / 11) + 100 := by
        have h_div : m = 11 * (m / 11) + (m % 11) := (Nat.div_add_mod m 11).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_67_pow_10_11_8 (m / 11)
  exact dvd_of_coprime_3 67 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_71_pow_10_35_8 (m : ℕ) : 71 ∣ 10 ^ (420 * m) * 10 ^ 100 - 2221 :=
  dvd_template 71 420 100 m (by decide) (by decide) (by decide)

theorem div_71_of_mod_35_8 (m : ℕ) (h_mod : m % 35 = 8) : 71 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 71 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (420 * (m / 35)) * 10 ^ 100 := by
      have h_eq : 12 * m + 4 = 420 * (m / 35) + 100 := by
        have h_div : m = 35 * (m / 35) + (m % 35) := (Nat.div_add_mod m 35).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_71_pow_10_35_8 (m / 35)
  exact dvd_of_coprime_3 71 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_197_pow_10_49_43 (m : ℕ) : 197 ∣ 10 ^ (588 * m) * 10 ^ 520 - 2221 :=
  dvd_template 197 588 520 m (by decide) (by decide) (by decide)

theorem div_197_of_mod_49_43 (m : ℕ) (h_mod : m % 49 = 43) : 197 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 197 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (588 * (m / 49)) * 10 ^ 520 := by
      have h_eq : 12 * m + 4 = 588 * (m / 49) + 520 := by
        have h_div : m = 49 * (m / 49) + (m % 49) := (Nat.div_add_mod m 49).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_197_pow_10_49_43 (m / 49)
  exact dvd_of_coprime_3 197 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_257_pow_10_64_56 (m : ℕ) : 257 ∣ 10 ^ (768 * m) * 10 ^ 676 - 2221 :=
  dvd_template 257 768 676 m (by decide) (by decide) (by decide)

theorem div_257_of_mod_64_56 (m : ℕ) (h_mod : m % 64 = 56) : 257 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 257 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (768 * (m / 64)) * 10 ^ 676 := by
      have h_eq : 12 * m + 4 = 768 * (m / 64) + 676 := by
        have h_div : m = 64 * (m / 64) + (m % 64) := (Nat.div_add_mod m 64).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_257_pow_10_64_56 (m / 64)
  exact dvd_of_coprime_3 257 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_379_pow_10_63_20 (m : ℕ) : 379 ∣ 10 ^ (756 * m) * 10 ^ 244 - 2221 :=
  dvd_template 379 756 244 m (by decide) (by decide) (by decide)

theorem div_379_of_mod_63_20 (m : ℕ) (h_mod : m % 63 = 20) : 379 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 379 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (756 * (m / 63)) * 10 ^ 244 := by
      have h_eq : 12 * m + 4 = 756 * (m / 63) + 244 := by
        have h_div : m = 63 * (m / 63) + (m % 63) := (Nat.div_add_mod m 63).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_379_pow_10_63_20 (m / 63)
  exact dvd_of_coprime_3 379 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_491_pow_10_245_135 (m : ℕ) : 491 ∣ 10 ^ (2940 * m) * 10 ^ 1624 - 2221 :=
  dvd_template 491 2940 1624 m (by decide) (by decide) (by decide)

theorem div_491_of_mod_245_135 (m : ℕ) (h_mod : m % 245 = 135) : 491 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 491 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (2940 * (m / 245)) * 10 ^ 1624 := by
      have h_eq : 12 * m + 4 = 2940 * (m / 245) + 1624 := by
        have h_div : m = 245 * (m / 245) + (m % 245) := (Nat.div_add_mod m 245).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_491_pow_10_245_135 (m / 245)
  exact dvd_of_coprime_3 491 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_883_pow_10_147_69 (m : ℕ) : 883 ∣ 10 ^ (1764 * m) * 10 ^ 832 - 2221 :=
  dvd_template 883 1764 832 m (by decide) (by decide) (by decide)

theorem div_883_of_mod_147_69 (m : ℕ) (h_mod : m % 147 = 69) : 883 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 883 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (1764 * (m / 147)) * 10 ^ 832 := by
      have h_eq : 12 * m + 4 = 1764 * (m / 147) + 832 := by
        have h_div : m = 147 * (m / 147) + (m % 147) := (Nat.div_add_mod m 147).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_883_pow_10_147_69 (m / 147)
  exact dvd_of_coprime_3 883 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_1153_pow_10_96_70 (m : ℕ) : 1153 ∣ 10 ^ (1152 * m) * 10 ^ 844 - 2221 :=
  dvd_template 1153 1152 844 m (by decide) (by decide) (by decide)

theorem div_1153_of_mod_96_70 (m : ℕ) (h_mod : m % 96 = 70) : 1153 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 1153 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (1152 * (m / 96)) * 10 ^ 844 := by
      have h_eq : 12 * m + 4 = 1152 * (m / 96) + 844 := by
        have h_div : m = 96 * (m / 96) + (m % 96) := (Nat.div_add_mod m 96).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_1153_pow_10_96_70 (m / 96)
  exact dvd_of_coprime_3 1153 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_1321_pow_10_55_10 (m : ℕ) : 1321 ∣ 10 ^ (660 * m) * 10 ^ 124 - 2221 :=
  dvd_template 1321 660 124 m (by decide) (by decide) (by decide)

theorem div_1321_of_mod_55_10 (m : ℕ) (h_mod : m % 55 = 10) : 1321 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 1321 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (660 * (m / 55)) * 10 ^ 124 := by
      have h_eq : 12 * m + 4 = 660 * (m / 55) + 124 := by
        have h_div : m = 55 * (m / 55) + (m % 55) := (Nat.div_add_mod m 55).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_1321_pow_10_55_10 (m / 55)
  exact dvd_of_coprime_3 1321 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_4159_pow_10_231_120 (m : ℕ) : 4159 ∣ 10 ^ (2772 * m) * 10 ^ 1444 - 2221 :=
  dvd_template 4159 2772 1444 m (by decide) (by decide) (by decide)

theorem div_4159_of_mod_231_120 (m : ℕ) (h_mod : m % 231 = 120) : 4159 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 4159 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (2772 * (m / 231)) * 10 ^ 1444 := by
      have h_eq : 12 * m + 4 = 2772 * (m / 231) + 1444 := by
        have h_div : m = 231 * (m / 231) + (m % 231) := (Nat.div_add_mod m 231).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_4159_pow_10_231_120 (m / 231)
  exact dvd_of_coprime_3 4159 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_4951_pow_10_825_700 (m : ℕ) : 4951 ∣ 10 ^ (9900 * m) * 10 ^ 8404 - 2221 :=
  dvd_template 4951 9900 8404 m (by decide) (by decide) (by decide)

theorem div_4951_of_mod_825_700 (m : ℕ) (h_mod : m % 825 = 700) : 4951 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 4951 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (9900 * (m / 825)) * 10 ^ 8404 := by
      have h_eq : 12 * m + 4 = 9900 * (m / 825) + 8404 := by
        have h_div : m = 825 * (m / 825) + (m % 825) := (Nat.div_add_mod m 825).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_4951_pow_10_825_700 (m / 825)
  exact dvd_of_coprime_3 4951 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_7547_pow_10_3773_62 (m : ℕ) : 7547 ∣ 10 ^ (45276 * m) * 10 ^ 748 - 2221 :=
  dvd_template 7547 45276 748 m (by decide) (by decide) (by decide)

theorem div_7547_of_mod_3773_62 (m : ℕ) (h_mod : m % 3773 = 62) : 7547 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 7547 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (45276 * (m / 3773)) * 10 ^ 748 := by
      have h_eq : 12 * m + 4 = 45276 * (m / 3773) + 748 := by
        have h_div : m = 3773 * (m / 3773) + (m % 3773) := (Nat.div_add_mod m 3773).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_7547_pow_10_3773_62 (m / 3773)
  exact dvd_of_coprime_3 7547 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_9857_pow_10_2464_153 (m : ℕ) : 9857 ∣ 10 ^ (29568 * m) * 10 ^ 1840 - 2221 :=
  dvd_template 9857 29568 1840 m (by decide) (by decide) (by decide)

theorem div_9857_of_mod_2464_153 (m : ℕ) (h_mod : m % 2464 = 153) : 9857 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 9857 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (29568 * (m / 2464)) * 10 ^ 1840 := by
      have h_eq : 12 * m + 4 = 29568 * (m / 2464) + 1840 := by
        have h_div : m = 2464 * (m / 2464) + (m % 2464) := (Nat.div_add_mod m 2464).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_9857_pow_10_2464_153 (m / 2464)
  exact dvd_of_coprime_3 9857 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_12101_pow_10_3025_472 (m : ℕ) : 12101 ∣ 10 ^ (36300 * m) * 10 ^ 5668 - 2221 :=
  dvd_template 12101 36300 5668 m (by decide) (by decide) (by decide)

theorem div_12101_of_mod_3025_472 (m : ℕ) (h_mod : m % 3025 = 472) : 12101 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 12101 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (36300 * (m / 3025)) * 10 ^ 5668 := by
      have h_eq : 12 * m + 4 = 36300 * (m / 3025) + 5668 := by
        have h_div : m = 3025 * (m / 3025) + (m % 3025) := (Nat.div_add_mod m 3025).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_12101_pow_10_3025_472 (m / 3025)
  exact dvd_of_coprime_3 12101 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_15877_pow_10_189_36 (m : ℕ) : 15877 ∣ 10 ^ (2268 * m) * 10 ^ 436 - 2221 :=
  dvd_template 15877 2268 436 m (by decide) (by decide) (by decide)

theorem div_15877_of_mod_189_36 (m : ℕ) (h_mod : m % 189 = 36) : 15877 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 15877 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (2268 * (m / 189)) * 10 ^ 436 := by
      have h_eq : 12 * m + 4 = 2268 * (m / 189) + 436 := by
        have h_div : m = 189 * (m / 189) + (m % 189) := (Nat.div_add_mod m 189).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_15877_pow_10_189_36 (m / 189)
  exact dvd_of_coprime_3 15877 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_17497_pow_10_1458_365 (m : ℕ) : 17497 ∣ 10 ^ (17496 * m) * 10 ^ 4384 - 2221 :=
  dvd_template 17497 17496 4384 m (by decide) (by decide) (by decide)

theorem div_17497_of_mod_1458_365 (m : ℕ) (h_mod : m % 1458 = 365) : 17497 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 17497 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (17496 * (m / 1458)) * 10 ^ 4384 := by
      have h_eq : 12 * m + 4 = 17496 * (m / 1458) + 4384 := by
        have h_div : m = 1458 * (m / 1458) + (m % 1458) := (Nat.div_add_mod m 1458).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_17497_pow_10_1458_365 (m / 1458)
  exact dvd_of_coprime_3 17497 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_22639_pow_10_3773_2075 (m : ℕ) : 22639 ∣ 10 ^ (45276 * m) * 10 ^ 24904 - 2221 :=
  dvd_template 22639 45276 24904 m (by decide) (by decide) (by decide)

theorem div_22639_of_mod_3773_2075 (m : ℕ) (h_mod : m % 3773 = 2075) : 22639 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 22639 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (45276 * (m / 3773)) * 10 ^ 24904 := by
      have h_eq : 12 * m + 4 = 45276 * (m / 3773) + 24904 := by
        have h_div : m = 3773 * (m / 3773) + (m % 3773) := (Nat.div_add_mod m 3773).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_22639_pow_10_3773_2075 (m / 3773)
  exact dvd_of_coprime_3 22639 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_25411_pow_10_4235_774 (m : ℕ) : 25411 ∣ 10 ^ (50820 * m) * 10 ^ 9292 - 2221 :=
  dvd_template 25411 50820 9292 m (by decide) (by decide) (by decide)

theorem div_25411_of_mod_4235_774 (m : ℕ) (h_mod : m % 4235 = 774) : 25411 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 25411 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (50820 * (m / 4235)) * 10 ^ 9292 := by
      have h_eq : 12 * m + 4 = 50820 * (m / 4235) + 9292 := by
        have h_div : m = 4235 * (m / 4235) + (m % 4235) := (Nat.div_add_mod m 4235).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_25411_pow_10_4235_774 (m / 4235)
  exact dvd_of_coprime_3 25411 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_26731_pow_10_4455_2491 (m : ℕ) : 26731 ∣ 10 ^ (53460 * m) * 10 ^ 29896 - 2221 :=
  dvd_template 26731 53460 29896 m (by decide) (by decide) (by decide)

theorem div_26731_of_mod_4455_2491 (m : ℕ) (h_mod : m % 4455 = 2491) : 26731 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 26731 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (53460 * (m / 4455)) * 10 ^ 29896 := by
      have h_eq : 12 * m + 4 = 53460 * (m / 4455) + 29896 := by
        have h_div : m = 4455 * (m / 4455) + (m % 4455) := (Nat.div_add_mod m 4455).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_26731_pow_10_4455_2491 (m / 4455)
  exact dvd_of_coprime_3 26731 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_30493_pow_10_2541_974 (m : ℕ) : 30493 ∣ 10 ^ (30492 * m) * 10 ^ 11692 - 2221 :=
  dvd_template 30493 30492 11692 m (by decide) (by decide) (by decide)

theorem div_30493_of_mod_2541_974 (m : ℕ) (h_mod : m % 2541 = 974) : 30493 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 30493 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (30492 * (m / 2541)) * 10 ^ 11692 := by
      have h_eq : 12 * m + 4 = 30492 * (m / 2541) + 11692 := by
        have h_div : m = 2541 * (m / 2541) + (m % 2541) := (Nat.div_add_mod m 2541).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_30493_pow_10_2541_974 (m / 2541)
  exact dvd_of_coprime_3 30493 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_32341_pow_10_2695_1324 (m : ℕ) : 32341 ∣ 10 ^ (32340 * m) * 10 ^ 15892 - 2221 :=
  dvd_template 32341 32340 15892 m (by decide) (by decide) (by decide)

theorem div_32341_of_mod_2695_1324 (m : ℕ) (h_mod : m % 2695 = 1324) : 32341 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 32341 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (32340 * (m / 2695)) * 10 ^ 15892 := by
      have h_eq : 12 * m + 4 = 32340 * (m / 2695) + 15892 := by
        have h_div : m = 2695 * (m / 2695) + (m % 2695) := (Nat.div_add_mod m 2695).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_32341_pow_10_2695_1324 (m / 2695)
  exact dvd_of_coprime_3 32341 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_45361_pow_10_945_444 (m : ℕ) : 45361 ∣ 10 ^ (11340 * m) * 10 ^ 5332 - 2221 :=
  dvd_template 45361 11340 5332 m (by decide) (by decide) (by decide)

theorem div_45361_of_mod_945_444 (m : ℕ) (h_mod : m % 945 = 444) : 45361 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 45361 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (11340 * (m / 945)) * 10 ^ 5332 := by
      have h_eq : 12 * m + 4 = 11340 * (m / 945) + 5332 := by
        have h_div : m = 945 * (m / 945) + (m % 945) := (Nat.div_add_mod m 945).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_45361_pow_10_945_444 (m / 945)
  exact dvd_of_coprime_3 45361 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_122501_pow_10_1225_783 (m : ℕ) : 122501 ∣ 10 ^ (14700 * m) * 10 ^ 9400 - 2221 :=
  dvd_template 122501 14700 9400 m (by decide) (by decide) (by decide)

theorem div_122501_of_mod_1225_783 (m : ℕ) (h_mod : m % 1225 = 783) : 122501 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 122501 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (14700 * (m / 1225)) * 10 ^ 9400 := by
      have h_eq : 12 * m + 4 = 14700 * (m / 1225) + 9400 := by
        have h_div : m = 1225 * (m / 1225) + (m % 1225) := (Nat.div_add_mod m 1225).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_122501_pow_10_1225_783 (m / 1225)
  exact dvd_of_coprime_3 122501 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_181501_pow_10_3025_1758 (m : ℕ) : 181501 ∣ 10 ^ (36300 * m) * 10 ^ 21100 - 2221 :=
  dvd_template 181501 36300 21100 m (by decide) (by decide) (by decide)

theorem div_181501_of_mod_3025_1758 (m : ℕ) (h_mod : m % 3025 = 1758) : 181501 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 181501 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (36300 * (m / 3025)) * 10 ^ 21100 := by
      have h_eq : 12 * m + 4 = 36300 * (m / 3025) + 21100 := by
        have h_div : m = 3025 * (m / 3025) + (m % 3025) := (Nat.div_add_mod m 3025).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_181501_pow_10_3025_1758 (m / 3025)
  exact dvd_of_coprime_3 181501 (by decide) (by decide) (concatenate (12 * m) 2593) h_div_3

theorem dvd_2593_pow_10_216_0 (m : ℕ) : 2593 ∣ 10 ^ (2592 * m) * 10 ^ 4 - 2221 :=
  dvd_template 2593 2592 4 m (by decide) (by decide) (by decide)

theorem div_2593_of_mod_216_0 (m : ℕ) (h_mod : m % 216 = 0) : 2593 ∣ concatenate (12 * m) 2593 := by
  have h_div_3 : 2593 ∣ 3 * concatenate (12 * m) 2593 := by
    rw [concat_sub_spec (12 * m)]
    have h_pow : 10 ^ (12 * m + 4) = 10 ^ (2592 * (m / 216)) * 10 ^ 4 := by
      have h_eq : 12 * m + 4 = 2592 * (m / 216) + 4 := by
        have h_div : m = 216 * (m / 216) + (m % 216) := (Nat.div_add_mod m 216).symm
        rw [h_mod] at h_div
        omega
      rw [h_eq, Nat.pow_add]
    rw [h_pow]
    exact dvd_2593_pow_10_216_0 (m / 216)
  exact dvd_of_coprime_3 2593 prime_2593 (by decide) (concatenate (12 * m) 2593) h_div_3

/-- OEIS A242775 Conjecture Disproof -/
theorem oeis_242775_conjecture_0.disproof : ¬ (∀ n, 4 ≤ n → A242775 n > 0) := by
  intro h
  have h2 : A242775 378 > 0 := h 378 (by omega)
  have h3 : A242775 378 = 0 := by
    unfold A242775
    simp
    have h_p : prime_of_index 378 = 2593 := prime_of_index_378
    rw [h_p]
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hk
    by_cases h_odd : k % 2 = 1
    · have h_div := div_11_of_odd k hk h_odd
      have h_gt : concatenate k 2593 > 11 := by
        unfold concatenate
        omega
      exact not_prime_of_dvd_of_gt (by decide : 11 > 1) h_div h_gt
    · by_cases h_4 : k % 4 = 2
      · have h_div := div_101_of_mod_4_2 k hk h_4
        have h_gt : concatenate k 2593 > 101 := by
          unfold concatenate
          omega
        exact not_prime_of_dvd_of_gt (by decide : 101 > 1) h_div h_gt
      · by_cases h_6 : k % 6 = 4
        · have h_div := div_7_of_mod_6_4 k hk h_6
          have h_gt : concatenate k 2593 > 7 := by
            unfold concatenate
            omega
          exact not_prime_of_dvd_of_gt (by decide : 7 > 1) h_div h_gt
        · by_cases h_3 : k % 3 = 2
          · have h_div := div_37_of_mod_3_2 k hk h_3
            have h_gt : concatenate k 2593 > 37 := by
              unfold concatenate
              omega
            exact not_prime_of_dvd_of_gt (by decide : 37 > 1) h_div h_gt
          · have hk12 : k % 12 = 0 := by omega
            have hk12_m : ∃ m, k = 12 * m := by
              use k / 12
              omega
            rcases hk12_m with ⟨m, hm⟩
            have hm_gt : m > 0 := by omega
            rw [hm]
            by_cases h_mod_0 : m % 11 = 8
            · have h_div := div_23_of_mod_11_8 m h_mod_0
              have h_gt : concatenate (12 * m) 2593 > 23 := by
                unfold concatenate
                omega
              exact not_prime_of_dvd_of_gt (by decide : 23 > 1) h_div h_gt
            ·               by_cases h_mod_1 : m % 5 = 4
              · have h_div := div_31_of_mod_5_4 m h_mod_1
                have h_gt : concatenate (12 * m) 2593 > 31 := by
                  unfold concatenate
                  omega
                exact not_prime_of_dvd_of_gt (by decide : 31 > 1) h_div h_gt
              ·                 by_cases h_mod_2 : m % 5 = 2
                · have h_div := div_61_of_mod_5_2 m h_mod_2
                  have h_gt : concatenate (12 * m) 2593 > 61 := by
                    unfold concatenate
                    omega
                  exact not_prime_of_dvd_of_gt (by decide : 61 > 1) h_div h_gt
                ·                   by_cases h_mod_3 : m % 11 = 8
                  · have h_div := div_67_of_mod_11_8 m h_mod_3
                    have h_gt : concatenate (12 * m) 2593 > 67 := by
                      unfold concatenate
                      omega
                    exact not_prime_of_dvd_of_gt (by decide : 67 > 1) h_div h_gt
                  ·                     by_cases h_mod_4 : m % 35 = 8
                    · have h_div := div_71_of_mod_35_8 m h_mod_4
                      have h_gt : concatenate (12 * m) 2593 > 71 := by
                        unfold concatenate
                        omega
                      exact not_prime_of_dvd_of_gt (by decide : 71 > 1) h_div h_gt
                    ·                       by_cases h_mod_5 : m % 49 = 43
                      · have h_div := div_197_of_mod_49_43 m h_mod_5
                        have h_gt : concatenate (12 * m) 2593 > 197 := by
                          unfold concatenate
                          omega
                        exact not_prime_of_dvd_of_gt (by decide : 197 > 1) h_div h_gt
                      ·                         by_cases h_mod_6 : m % 64 = 56
                        · have h_div := div_257_of_mod_64_56 m h_mod_6
                          have h_gt : concatenate (12 * m) 2593 > 257 := by
                            unfold concatenate
                            omega
                          exact not_prime_of_dvd_of_gt (by decide : 257 > 1) h_div h_gt
                        ·                           by_cases h_mod_7 : m % 63 = 20
                          · have h_div := div_379_of_mod_63_20 m h_mod_7
                            have h_gt : concatenate (12 * m) 2593 > 379 := by
                              unfold concatenate
                              omega
                            exact not_prime_of_dvd_of_gt (by decide : 379 > 1) h_div h_gt
                          ·                             by_cases h_mod_8 : m % 245 = 135
                            · have h_div := div_491_of_mod_245_135 m h_mod_8
                              have h_gt : concatenate (12 * m) 2593 > 491 := by
                                unfold concatenate
                                omega
                              exact not_prime_of_dvd_of_gt (by decide : 491 > 1) h_div h_gt
                            ·                               by_cases h_mod_9 : m % 147 = 69
                              · have h_div := div_883_of_mod_147_69 m h_mod_9
                                have h_gt : concatenate (12 * m) 2593 > 883 := by
                                  unfold concatenate
                                  omega
                                exact not_prime_of_dvd_of_gt (by decide : 883 > 1) h_div h_gt
                              ·                                 by_cases h_mod_10 : m % 96 = 70
                                · have h_div := div_1153_of_mod_96_70 m h_mod_10
                                  have h_gt : concatenate (12 * m) 2593 > 1153 := by
                                    unfold concatenate
                                    omega
                                  exact not_prime_of_dvd_of_gt (by decide : 1153 > 1) h_div h_gt
                                ·                                   by_cases h_mod_11 : m % 55 = 10
                                  · have h_div := div_1321_of_mod_55_10 m h_mod_11
                                    have h_gt : concatenate (12 * m) 2593 > 1321 := by
                                      unfold concatenate
                                      omega
                                    exact not_prime_of_dvd_of_gt (by decide : 1321 > 1) h_div h_gt
                                  ·                                     by_cases h_mod_12 : m % 231 = 120
                                    · have h_div := div_4159_of_mod_231_120 m h_mod_12
                                      have h_gt : concatenate (12 * m) 2593 > 4159 := by
                                        unfold concatenate
                                        omega
                                      exact not_prime_of_dvd_of_gt (by decide : 4159 > 1) h_div h_gt
                                    ·                                       by_cases h_mod_13 : m % 825 = 700
                                      · have h_div := div_4951_of_mod_825_700 m h_mod_13
                                        have h_gt : concatenate (12 * m) 2593 > 4951 := by
                                          unfold concatenate
                                          omega
                                        exact not_prime_of_dvd_of_gt (by decide : 4951 > 1) h_div h_gt
                                      ·                                         by_cases h_mod_14 : m % 3773 = 62
                                        · have h_div := div_7547_of_mod_3773_62 m h_mod_14
                                          have h_gt : concatenate (12 * m) 2593 > 7547 := by
                                            unfold concatenate
                                            omega
                                          exact not_prime_of_dvd_of_gt (by decide : 7547 > 1) h_div h_gt
                                        ·                                           by_cases h_mod_15 : m % 2464 = 153
                                          · have h_div := div_9857_of_mod_2464_153 m h_mod_15
                                            have h_gt : concatenate (12 * m) 2593 > 9857 := by
                                              unfold concatenate
                                              omega
                                            exact not_prime_of_dvd_of_gt (by decide : 9857 > 1) h_div h_gt
                                          ·                                             by_cases h_mod_16 : m % 3025 = 472
                                            · have h_div := div_12101_of_mod_3025_472 m h_mod_16
                                              have h_gt : concatenate (12 * m) 2593 > 12101 := by
                                                unfold concatenate
                                                omega
                                              exact not_prime_of_dvd_of_gt (by decide : 12101 > 1) h_div h_gt
                                            ·                                               by_cases h_mod_17 : m % 189 = 36
                                              · have h_div := div_15877_of_mod_189_36 m h_mod_17
                                                have h_gt : concatenate (12 * m) 2593 > 15877 := by
                                                  unfold concatenate
                                                  omega
                                                exact not_prime_of_dvd_of_gt (by decide : 15877 > 1) h_div h_gt
                                              ·                                                 by_cases h_mod_18 : m % 1458 = 365
                                                · have h_div := div_17497_of_mod_1458_365 m h_mod_18
                                                  have h_gt : concatenate (12 * m) 2593 > 17497 := by
                                                    unfold concatenate
                                                    omega
                                                  exact not_prime_of_dvd_of_gt (by decide : 17497 > 1) h_div h_gt
                                                ·                                                   by_cases h_mod_19 : m % 3773 = 2075
                                                  · have h_div := div_22639_of_mod_3773_2075 m h_mod_19
                                                    have h_gt : concatenate (12 * m) 2593 > 22639 := by
                                                      unfold concatenate
                                                      omega
                                                    exact not_prime_of_dvd_of_gt (by decide : 22639 > 1) h_div h_gt
                                                  ·                                                     by_cases h_mod_20 : m % 4235 = 774
                                                    · have h_div := div_25411_of_mod_4235_774 m h_mod_20
                                                      have h_gt : concatenate (12 * m) 2593 > 25411 := by
                                                        unfold concatenate
                                                        omega
                                                      exact not_prime_of_dvd_of_gt (by decide : 25411 > 1) h_div h_gt
                                                    ·                                                       by_cases h_mod_21 : m % 4455 = 2491
                                                      · have h_div := div_26731_of_mod_4455_2491 m h_mod_21
                                                        have h_gt : concatenate (12 * m) 2593 > 26731 := by
                                                          unfold concatenate
                                                          omega
                                                        exact not_prime_of_dvd_of_gt (by decide : 26731 > 1) h_div h_gt
                                                      ·                                                         by_cases h_mod_22 : m % 2541 = 974
                                                        · have h_div := div_30493_of_mod_2541_974 m h_mod_22
                                                          have h_gt : concatenate (12 * m) 2593 > 30493 := by
                                                            unfold concatenate
                                                            omega
                                                          exact not_prime_of_dvd_of_gt (by decide : 30493 > 1) h_div h_gt
                                                        ·                                                           by_cases h_mod_23 : m % 2695 = 1324
                                                          · have h_div := div_32341_of_mod_2695_1324 m h_mod_23
                                                            have h_gt : concatenate (12 * m) 2593 > 32341 := by
                                                              unfold concatenate
                                                              omega
                                                            exact not_prime_of_dvd_of_gt (by decide : 32341 > 1) h_div h_gt
                                                          ·                                                             by_cases h_mod_24 : m % 945 = 444
                                                            · have h_div := div_45361_of_mod_945_444 m h_mod_24
                                                              have h_gt : concatenate (12 * m) 2593 > 45361 := by
                                                                unfold concatenate
                                                                omega
                                                              exact not_prime_of_dvd_of_gt (by decide : 45361 > 1) h_div h_gt
                                                            ·                                                               by_cases h_mod_25 : m % 1225 = 783
                                                              · have h_div := div_122501_of_mod_1225_783 m h_mod_25
                                                                have h_gt : concatenate (12 * m) 2593 > 122501 := by
                                                                  unfold concatenate
                                                                  omega
                                                                exact not_prime_of_dvd_of_gt (by decide : 122501 > 1) h_div h_gt
                                                              ·                                                                 by_cases h_mod_26 : m % 3025 = 1758
                                                                · have h_div := div_181501_of_mod_3025_1758 m h_mod_26
                                                                  have h_gt : concatenate (12 * m) 2593 > 181501 := by
                                                                    unfold concatenate
                                                                    omega
                                                                  exact not_prime_of_dvd_of_gt (by decide : 181501 > 1) h_div h_gt
                                                                · by_cases h_mod_27 : m % 216 = 0
                                                                  · have h_div := div_2593_of_mod_216_0 m h_mod_27
                                                                    have h_gt : concatenate (12 * m) 2593 > 2593 := by
                                                                      unfold concatenate
                                                                      omega
                                                                    exact not_prime_of_dvd_of_gt (by decide : 2593 > 1) h_div h_gt
                                                                  · -- Contradiction: m % H_i != s_i for all i, and m % 216 != 0. omega can prove False!
                                                                    omega
  omega
