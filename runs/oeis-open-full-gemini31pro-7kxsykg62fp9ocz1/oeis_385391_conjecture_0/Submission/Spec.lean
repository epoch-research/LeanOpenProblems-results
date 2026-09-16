import FormalConjectures.Util.ProblemImports

open Nat Set Finset

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

/--
A385391: $a(n)$ is the smallest integer $k$ such that $A384237(k) = n$.
This is formalized using the set infimum ($\mathrm{sInf}$) of the preimage of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial $p_n\#$. Product of the first $n$ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (Finset.range n).prod fun i => Nat.nth Nat.Prime i

lemma a_eq (n m : ℕ) (h1 : A384237 m = n) (h2 : ∀ k < m, A384237 k ≠ n) : a n = m := by
  dsimp [a]
  apply IsLeast.csInf_eq
  constructor
  · exact h1
  · intro k hk
    by_contra hlt
    exact h2 k (not_le.mp hlt) hk

lemma A384237_cond_eq (n d : ℕ) (hd : d ∣ n) (hd0 : d > 0) :
    (d ^ d) % n = d % n ↔ ((d % (n / d)) ^ (d - 1)) % (n / d) = 1 % (n / d) := by
  generalize h_m : n / d = m
  have hn : n = m * d := by rw [← h_m, Nat.div_mul_cancel hd]
  have hd_pow : d ^ d = d ^ (d - 1) * d := by
    calc d ^ d = d ^ (d - 1 + 1) := by rw [Nat.sub_add_cancel hd0]
      _ = d ^ (d - 1) * d := by rw [pow_succ]
  subst hn
  rw [hd_pow]
  have h1 : d % (m * d) = (1 % m) * d := by
    calc d % (m * d) = (1 * d) % (m * d) := by rw [Nat.one_mul]
      _ = (1 % m) * d := Nat.mul_mod_mul_right d 1 m
  rw [Nat.mul_mod_mul_right, h1]
  rw [← Nat.pow_mod]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_right hd0 h
  · intro h
    rw [h]
lemma prime_0 : Nat.nth Nat.Prime 0 = 2 := by
  rw [Nat.nth_zero]
  apply IsLeast.csInf_eq
  exact ⟨Nat.prime_two, fun k hk => Nat.Prime.two_le hk⟩

lemma prime_n (n val : ℕ) (hval_prime : Nat.Prime val)
    (h_gt : ∀ m < n, Nat.nth Nat.Prime m < val)
    (h_le : ∀ k, Nat.Prime k → (∀ m < n, Nat.nth Nat.Prime m < k) → val ≤ k) :
    Nat.nth Nat.Prime n = val := by
  rw [Nat.nth_eq_sInf]
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨hval_prime, h_gt⟩
  · intro k hk
    exact h_le k hk.1 hk.2

lemma prime_1 : Nat.nth Nat.Prime 1 = 3 := by
  apply prime_n 1 3 (by decide)
  · intro m hm
    have : m = 0 := by omega
    subst this
    rw [prime_0]
    decide
  · intro k hk h_gt
    have h1 := h_gt 0 (by decide)
    rw [prime_0] at h1
    clear h_gt
    by_contra h_not
    have : k < 3 := not_le.mp h_not
    have h2 : k = 2 := by omega
    subst h2
    omega

lemma prime_2 : Nat.nth Nat.Prime 2 = 5 := by
  apply prime_n 2 5 (by decide)
  · intro m hm
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl
    · rw [prime_0]; decide
    · rw [prime_1]; decide
  · intro k hk h_gt
    have h1 := h_gt 1 (by decide)
    rw [prime_1] at h1
    clear h_gt
    by_contra h_not
    have : k < 5 := not_le.mp h_not
    have : k = 4 := by omega
    subst this
    revert hk; decide

lemma prime_3 : Nat.nth Nat.Prime 3 = 7 := by
  apply prime_n 3 7 (by decide)
  · intro m hm
    have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [prime_0]; decide
    · rw [prime_1]; decide
    · rw [prime_2]; decide
  · intro k hk h_gt
    have h1 := h_gt 2 (by decide)
    rw [prime_2] at h1
    clear h_gt
    by_contra h_not
    have : k < 7 := not_le.mp h_not
    have : k = 6 := by omega
    subst this
    revert hk; decide

lemma prime_4 : Nat.nth Nat.Prime 4 = 11 := by
  apply prime_n 4 11 (by decide)
  · intro m hm
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [prime_0]; decide
    · rw [prime_1]; decide
    · rw [prime_2]; decide
    · rw [prime_3]; decide
  · intro k hk h_gt
    have h1 := h_gt 3 (by decide)
    rw [prime_3] at h1
    clear h_gt
    by_contra h_not
    have : k < 11 := not_le.mp h_not
    have : k = 8 ∨ k = 9 ∨ k = 10 := by omega
    rcases this with rfl | rfl | rfl
    · revert hk; decide
    · revert hk; decide
    · revert hk; decide

lemma prime_5 : Nat.nth Nat.Prime 5 = 13 := by
  apply prime_n 5 13 (by decide)
  · intro m hm
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · rw [prime_0]; decide
    · rw [prime_1]; decide
    · rw [prime_2]; decide
    · rw [prime_3]; decide
    · rw [prime_4]; decide
  · intro k hk h_gt
    have h1 := h_gt 4 (by decide)
    rw [prime_4] at h1
    clear h_gt
    by_contra h_not
    have : k < 13 := not_le.mp h_not
    have : k = 12 := by omega
    subst this
    revert hk; decide

lemma a002110_0 : A002110 0 = 1 := rfl
lemma a002110_1 : A002110 1 = 2 := by
  have h : 1 ≠ 0 := by decide
  rw [A002110, if_neg h, prod_range_succ, prod_range_zero, one_mul, prime_0]
lemma a002110_2 : A002110 2 = 6 := by
  have h : 2 ≠ 0 := by decide
  rw [A002110, if_neg h, prod_range_succ, prod_range_succ, prod_range_zero, one_mul, prime_0, prime_1]
  rfl
lemma a002110_3 : A002110 3 = 30 := by
  have h : 3 ≠ 0 := by decide
  rw [A002110, if_neg h, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero, one_mul, prime_0, prime_1, prime_2]
  rfl
lemma a002110_4 : A002110 4 = 210 := by
  have h : 4 ≠ 0 := by decide
  rw [A002110, if_neg h, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero, one_mul, prime_0, prime_1, prime_2, prime_3]
  rfl
lemma a002110_5 : A002110 5 = 2310 := by
  have h : 5 ≠ 0 := by decide
  rw [A002110, if_neg h, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero, one_mul, prime_0, prime_1, prime_2, prime_3, prime_4]
  rfl



def fastA384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => ((d % (n / d)) ^ (d - 1)) % (n / d) = 1 % (n / d)).card

lemma A384237_eq_fastA384237 (n : ℕ) : A384237 n = fastA384237 n := by
  dsimp [A384237, fastA384237]
  congr 1
  apply Finset.filter_congr
  intro d hd
  have hd_div : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd_pos : d > 0 := by
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    exact Nat.pos_of_ne_zero (fun h => by subst h; exact hn0 (eq_zero_of_zero_dvd hd_div))
  exact A384237_cond_eq n d hd_div hd_pos

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 3000

lemma test1 : ∀ k, 1 ≤ k → k < 300 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test2 : ∀ k, 300 ≤ k → k < 600 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test3 : ∀ k, 600 ≤ k → k < 900 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test4 : ∀ k, 900 ≤ k → k < 1200 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test5 : ∀ k, 1200 ≤ k → k < 1500 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test6 : ∀ k, 1500 ≤ k → k < 1800 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test7 : ∀ k, 1800 ≤ k → k < 2100 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide
lemma test8 : ∀ k, 2100 ≤ k → k < 2310 → fastA384237 k ≠ 10 := by intro k _ hk; revert hk k; decide

lemma a_10_2 : ∀ k < 2310, A384237 k ≠ 10 := by
  intro k hk
  rw [A384237_eq_fastA384237]
  if hk0 : k = 0 then
    subst hk0
    decide
  else
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    if h1 : k < 300 then exact test1 k hk1 h1
    else if h2 : k < 600 then exact test2 k (not_lt.mp h1) h2
    else if h3 : k < 900 then exact test3 k (not_lt.mp h2) h3
    else if h4 : k < 1200 then exact test4 k (not_lt.mp h3) h4
    else if h5 : k < 1500 then exact test5 k (not_lt.mp h4) h5
    else if h6 : k < 1800 then exact test6 k (not_lt.mp h5) h6
    else if h7 : k < 2100 then exact test7 k (not_lt.mp h6) h7
    else exact test8 k (not_lt.mp h7) hk

theorem oeis_385391_conjecture_0 :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a002110_0]
    apply a_eq
    · decide
    · intro k hk; revert hk k; decide
  · rw [a002110_1]
    apply a_eq
    · decide
    · intro k hk; revert hk k; decide
  · rw [a002110_2]
    apply a_eq
    · decide
    · intro k hk;
      if hk0 : k = 0 then subst hk0; decide
      else if hk1 : k = 1 then subst hk1; decide
      else if hk2 : k = 2 then subst hk2; decide
      else if hk3 : k = 3 then subst hk3; decide
      else if hk4 : k = 4 then subst hk4; decide
      else if hk5 : k = 5 then subst hk5; decide
      else omega
  · rw [a002110_3]
    apply a_eq
    · decide
    · intro k hk;
      if hk0 : k < 10 then revert hk0 hk k; decide
      else if hk1 : k < 20 then revert hk1 hk k; decide
      else if hk2 : k < 30 then revert hk2 hk k; decide
      else omega
  · rw [a002110_4]
    apply a_eq
    · decide
    · intro k hk;
      if h1 : k < 70 then revert h1 hk k; decide
      else if h2 : k < 140 then revert h2 hk k; decide
      else if h3 : k < 210 then revert h3 hk k; decide
      else omega
  · rw [a002110_5]
    apply a_eq
    · rw [A384237_eq_fastA384237]
      decide
    · exact a_10_2

theorem oeis_385391_conjecture_0.disproof : ¬ (type_of% @oeis_385391_conjecture_0) := sorry
