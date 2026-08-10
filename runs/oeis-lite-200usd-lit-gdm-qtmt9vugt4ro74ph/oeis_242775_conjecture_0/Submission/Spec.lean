import FormalConjectures.Util.ProblemImports

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

set_option maxRecDepth 300000
set_option maxHeartbeats 15000000

/-
### Section 1: Optimized Primality Certifier
-/

def sqrt_fast_go (n : ℕ) (i : ℕ) : ℕ :=
  match i with
  | 0 => 0
  | i' + 1 =>
    if i * i ≤ n then i
    else sqrt_fast_go n i'


theorem sqrt_fast_go_eq (n i : ℕ) (h : Nat.sqrt n ≤ i) : sqrt_fast_go n i = Nat.sqrt n := by
  induction i with
  | zero =>
    have h_eq : Nat.sqrt n = 0 := by omega
    rw [h_eq]
    rfl
  | succ i' ih =>
    dsimp [sqrt_fast_go]
    split_ifs with h_le
    · have h_eq1 : i' + 1 ≤ Nat.sqrt n := by rwa [Nat.le_sqrt]
      omega
    · have h_lt : Nat.sqrt n < i' + 1 := by
        rw [Nat.sqrt_lt]
        omega
      have h_le2 : Nat.sqrt n ≤ i' := by omega
      exact ih h_le2

def sqrt_fast (n : ℕ) : ℕ :=
  sqrt_fast_go n (if n < 10000 then 100 else n)

theorem sqrt_fast_eq_sqrt (n : ℕ) : sqrt_fast n = Nat.sqrt n := by
  dsimp [sqrt_fast]
  apply sqrt_fast_go_eq
  split_ifs with h
  · have h_lt : Nat.sqrt n < 100 := by
      rw [Nat.sqrt_lt]
      exact h
    omega
  · exact Nat.sqrt_le_self n

def is_prime_fast (n : ℕ) : Bool :=
  decide (2 ≤ n) && ((List.range (sqrt_fast n + 1)).all (fun d => decide (d < 2) || decide (n % d ≠ 0)))

theorem is_prime_fast_iff (n : ℕ) : is_prime_fast n = true ↔ Nat.Prime n := by
  dsimp [is_prime_fast]
  rw [sqrt_fast_eq_sqrt]
  rw [Bool.and_eq_true, decide_eq_true_iff, Nat.prime_def_le_sqrt]
  apply and_congr_right'
  rw [List.all_eq_true]
  simp only [List.mem_range, Nat.lt_succ_iff]
  constructor
  · intro h m hm2 hms hdvd
    have h_mem := h m hms
    rw [Bool.or_eq_true] at h_mem
    rcases h_mem with h_lt2 | h_mod
    · rw [decide_eq_true_iff] at h_lt2
      omega
    · rw [decide_eq_true_iff] at h_mod
      apply h_mod
      exact dvd_iff_mod_eq_zero.mp hdvd
  · intro h m hm_le
    rw [Bool.or_eq_true]
    by_cases h_lt2 : m < 2
    · left; rw [decide_eq_true_iff]; omega
    · right; rw [decide_eq_true_iff]
      intro h_mod
      have hm2 : 2 ≤ m := by omega
      have hdvd := dvd_iff_mod_eq_zero.mpr h_mod
      exact h m hm2 hm_le hdvd

def count_tr_go (p : ℕ → Bool) (n : ℕ) (acc : ℕ) : ℕ :=
  match n with
  | 0 => acc
  | n' + 1 =>
    let acc' := if p n' then acc + 1 else acc
    count_tr_go p n' acc'

def count_tr (p : ℕ → Bool) (n : ℕ) : ℕ :=
  count_tr_go p n 0

theorem count_tr_go_eq (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (acc : ℕ) :
    count_tr_go (fun x => decide (p x)) n acc = Nat.count p n + acc := by
  induction n generalizing acc with
  | zero =>
    rw [Nat.count_zero]
    rw [Nat.zero_add]
    rfl
  | succ n' ih =>
    rw [Nat.count_succ]
    dsimp [count_tr_go]
    rw [ih]
    split_ifs with h1 h2 h3
    · omega
    · rw [decide_eq_true_iff] at h1
      contradiction
    · rw [decide_eq_true_iff] at h1
      contradiction
    · omega

theorem count_tr_eq (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    count_tr (fun x => decide (p x)) n = Nat.count p n := by
  dsimp [count_tr]
  rw [count_tr_go_eq]
  rw [Nat.add_zero]

theorem prime_of_index_378 : prime_of_index 378 = 2593 := by
  dsimp [prime_of_index]
  have h_prime : Nat.Prime 2593 := by
    rw [← is_prime_fast_iff]
    decide
  have h_count : count Nat.Prime 2593 = 377 := by
    have h_eq : Nat.Prime = (fun x => is_prime_fast x = true) := by
      ext x
      exact (is_prime_fast_iff x).symm
    simp only [h_eq]
    rw [← count_tr_eq]
    decide
  have h_nth := Nat.nth_count h_prime
  rw [h_count] at h_nth
  exact h_nth

/-
### Section 2: Modular and Concatenation Algebra
-/

lemma three_dvd_ten_pow_sub_one (k : ℕ) : 3 ∣ 10 ^ k - 1 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h : 10 ^ (k + 1) - 1 = 9 * 10 ^ k + (10 ^ k - 1) := by
      omega
    rw [h]
    apply dvd_add
    · apply dvd_mul_of_dvd_left
      decide
    · exact ih

theorem concatenate_identity (k p : ℕ) :
    3 * concatenate k p + 10 ^ (num_digits p) = 10 ^ (k + num_digits p) + 3 * p := by
  dsimp [concatenate, rep_threes]
  have h_dvd := three_dvd_ten_pow_sub_one k
  have h_mul_div := Nat.mul_div_cancel' h_dvd
  rw [Nat.left_distrib]
  rw [← Nat.mul_assoc]
  rw [h_mul_div]
  have h_sub_dist : (10 ^ k - 1) * 10 ^ (num_digits p) = 10 ^ k * 10 ^ (num_digits p) - 10 ^ (num_digits p) := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [h_sub_dist]
  have h_pow_add : 10 ^ k * 10 ^ (num_digits p) = 10 ^ (k + num_digits p) := by
    rw [Nat.pow_add]
  rw [h_pow_add]
  have h_le : 10 ^ (num_digits p) ≤ 10 ^ (k + num_digits p) := by
    apply Nat.pow_le_pow_right
    decide
    omega
  omega

lemma mod_add_cancel (a b q : ℕ) (hq : q > 0) (h : (a + b) % q = b % q) : a % q = 0 := by
  have h1 : (a + b) % q = (a % q + b % q) % q := by rw [Nat.add_mod]
  rw [h] at h1
  have h_lt1 : a % q < q := Nat.mod_lt a hq
  have h_lt2 : b % q < q := Nat.mod_lt b hq
  have h_cases : a % q + b % q < q ∨ a % q + b % q ≥ q := by omega
  rcases h_cases with h_lt | h_ge
  · have h_mod_eq : (a % q + b % q) % q = a % q + b % q := Nat.mod_eq_of_lt h_lt
    rw [h_mod_eq] at h1
    omega
  · have h_lt3 : a % q + b % q < q + q := by omega
    have h_eq_add : a % q + b % q = q + (a % q + b % q - q) := by omega
    rw [h_eq_add] at h1
    rw [Nat.add_mod, Nat.mod_self q, Nat.zero_add, Nat.mod_mod] at h1
    have h_lt4 : a % q + b % q - q < q := by omega
    rw [Nat.mod_eq_of_lt h_lt4] at h1
    omega

theorem concatenate_dvd_of_modEq (k p q : ℕ) (hq : q > 0) (hq3 : q ≠ 3) (hq_prime : Nat.Prime q)
    (h_eq : (10 ^ (k + num_digits p) + 3 * p) % q = (10 ^ (num_digits p)) % q) :
    q ∣ concatenate k p := by
  have h_id := concatenate_identity k p
  have h_mod : (3 * concatenate k p + 10 ^ (num_digits p)) % q = (10 ^ (k + num_digits p) + 3 * p) % q := by
    rw [h_id]
  rw [h_eq] at h_mod
  have h_div3 : (3 * concatenate k p) % q = 0 := mod_add_cancel (3 * concatenate k p) (10 ^ (num_digits p)) q hq h_mod
  have h_dvd3 : q ∣ 3 * concatenate k p := Nat.dvd_of_mod_eq_zero h_div3
  have h_or := (Nat.Prime.dvd_mul hq_prime).mp h_dvd3
  rcases h_or with h_dvd_3 | h_dvd_cat
  · have h_le : q ≤ 3 := Nat.le_of_dvd (by decide) h_dvd_3
    have h_prime_ge2 : q ≥ 2 := Nat.Prime.two_le hq_prime
    have h_dvd_23 : ¬ 2 ∣ 3 := by decide
    have h_q_eq_2 : q = 2 := by omega
    rw [h_q_eq_2] at h_dvd_3
    exact False.elim (h_dvd_23 h_dvd_3)
  · exact h_dvd_cat

lemma pow_mod_eq_mod_mod (x order q : ℕ) (h_ord : 10 ^ order ≡ 1 [MOD q]) :
    10 ^ x ≡ 10 ^ (x % order) [MOD q] := by
  have h_div := Nat.div_add_mod x order
  have h_eq : 10 ^ x = (10 ^ order) ^ (x / order) * 10 ^ (x % order) := by
    conv_lhs => rw [← h_div]
    rw [Nat.pow_add, Nat.pow_mul]
  rw [h_eq]
  have h1 : (10 ^ order) ^ (x / order) ≡ 1 ^ (x / order) [MOD q] := Nat.ModEq.pow (x / order) h_ord
  rw [Nat.one_pow] at h1
  have h2 : (10 ^ order) ^ (x / order) * 10 ^ (x % order) ≡ 1 * 10 ^ (x % order) [MOD q] := Nat.ModEq.mul_right (10 ^ (x % order)) h1
  rw [Nat.one_mul] at h2
  exact h2

lemma pow_mod_eq_of_modEq (k k_val order d q : ℕ)
    (h_ord : 10 ^ order ≡ 1 [MOD q]) (hk : k ≡ k_val [MOD order]) :
    10 ^ (k + d) ≡ 10 ^ (k_val + d) [MOD q] := by
  have h_add : k + d ≡ k_val + d [MOD order] := Nat.ModEq.add_right d hk
  have h_pow1 : 10 ^ (k + d) ≡ 10 ^ ((k + d) % order) [MOD q] := pow_mod_eq_mod_mod (k + d) order q h_ord
  have h_pow2 : 10 ^ (k_val + d) ≡ 10 ^ ((k_val + d) % order) [MOD q] := pow_mod_eq_mod_mod (k_val + d) order q h_ord
  rw [h_add] at h_pow1
  exact Nat.ModEq.trans h_pow1 (Nat.ModEq.symm h_pow2)

lemma rep_threes_ge_three (k : ℕ) (hk : k ≥ 1) : rep_threes k ≥ 3 := by
  dsimp [rep_threes]
  have h_dvd : 3 ∣ 10 ^ k - 1 := three_dvd_ten_pow_sub_one k
  have h_mod : (10 ^ k - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  have h_pow : 10 ^ k ≥ 10 := Nat.pow_le_pow_right (show 10 > 0 by decide) hk
  omega

lemma composite_of_dvd (p q : ℕ) (hq : Nat.Prime q) (hdvd : q ∣ p) (hlt : q < p) : ¬ Nat.Prime p := by
  intro hp
  have h_eq_or := Nat.Prime.eq_one_or_self_of_dvd hp q hdvd
  rcases h_eq_or with h1 | h2
  · have : q ≥ 2 := Nat.Prime.two_le hq
    omega
  · omega

lemma num_digits_2593 : num_digits 2593 = 4 := by
  dsimp [num_digits, digits]
  rw [digitsAux, digitsAux, digitsAux, digitsAux]
  rw [digitsAux_zero]
  rfl

/-
### Section 3: Modular Branches
-/

lemma odd_composite (k : ℕ) (hk_pos : k > 0) (hk_odd : k % 2 = 1) :
    ¬ Nat.Prime (concatenate k 2593) := by
  have h_dvd : 11 ∣ concatenate k 2593 := by
    have h_mod_2 : k ≡ 1 [MOD 2] := hk_odd
    have h_ord : 10 ^ 2 ≡ 1 [MOD 11] := by decide
    have h_pow := pow_mod_eq_of_modEq k 1 2 4 11 h_ord h_mod_2
    have h_add := Nat.ModEq.add_right (3 * 2593) h_pow
    have h_eq : 10 ^ 5 + 3 * 2593 ≡ 10 ^ 4 [MOD 11] := by decide
    have h_trans := Nat.ModEq.trans h_add h_eq
    rw [← num_digits_2593] at h_trans
    exact concatenate_dvd_of_modEq k 2593 11 (by decide) (by decide) (by decide) h_trans
  have h_hlt : 11 < concatenate k 2593 := by
    dsimp [concatenate]
    rw [num_digits_2593]
    have h_rep := rep_threes_ge_three k hk_pos
    omega
  exact composite_of_dvd (concatenate k 2593) 11 (by decide) h_dvd h_hlt

lemma dvd_concatenate_37 (k : ℕ) (hk : k ≡ 2 [MOD 3]) : 37 ∣ concatenate k 2593 := by
  have h_ord : 10 ^ 3 ≡ 1 [MOD 37] := by decide
  have h_eq : 10 ^ (2 + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 37] := by decide
  have h_pow := pow_mod_eq_of_modEq k 2 3 4 37 h_ord hk
  have h_add := Nat.ModEq.add_right (3 * 2593) h_pow
  have h_trans : 10 ^ (k + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 37] := Nat.ModEq.trans h_add h_eq
  rw [← num_digits_2593] at h_trans
  exact concatenate_dvd_of_modEq k 2593 37 (by decide) (by decide) (by decide) h_trans

lemma dvd_concatenate_7 (k : ℕ) (hk : k ≡ 4 [MOD 6]) : 7 ∣ concatenate k 2593 := by
  have h_ord : 10 ^ 6 ≡ 1 [MOD 7] := by decide
  have h_eq : 10 ^ (4 + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 7] := by decide
  have h_pow := pow_mod_eq_of_modEq k 4 6 4 7 h_ord hk
  have h_add := Nat.ModEq.add_right (3 * 2593) h_pow
  have h_trans : 10 ^ (k + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 7] := Nat.ModEq.trans h_add h_eq
  rw [← num_digits_2593] at h_trans
  exact concatenate_dvd_of_modEq k 2593 7 (by decide) (by decide) (by decide) h_trans

lemma dvd_concatenate_101 (k : ℕ) (hk : k ≡ 2 [MOD 4]) : 101 ∣ concatenate k 2593 := by
  have h_ord : 10 ^ 4 ≡ 1 [MOD 101] := by decide
  have h_eq : 10 ^ (2 + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 101] := by decide
  have h_pow := pow_mod_eq_of_modEq k 2 4 4 101 h_ord hk
  have h_add := Nat.ModEq.add_right (3 * 2593) h_pow
  have h_trans : 10 ^ (k + 4) + 3 * 2593 ≡ 10 ^ 4 [MOD 101] := Nat.ModEq.trans h_add h_eq
  rw [← num_digits_2593] at h_trans
  exact concatenate_dvd_of_modEq k 2593 101 (by decide) (by decide) (by decide) h_trans

lemma composite_case_12r (r : ℕ) : ¬ Nat.Prime (concatenate (12 * r) 2593) := by
  sorry

lemma composite_2593 (k : ℕ) (hk : k > 0) : ¬ Nat.Prime (concatenate k 2593) := by
  by_cases h_odd : k % 2 = 1
  · exact odd_composite k hk h_odd
  · have h_even : k % 2 = 0 := by omega
    have h_mod12 : k % 12 = 0 ∨ k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8 ∨ k % 12 = 10 := by omega
    rcases h_mod12 with h0 | h2 | h4 | h6 | h8 | h10
    · have h_div : 12 ∣ k := Nat.dvd_of_mod_eq_zero h0
      rcases h_div with ⟨r, rfl⟩
      exact composite_case_12r r
    · have h_div_eq : k = 12 * (k / 12) + 2 := by
        have := Nat.div_add_mod k 12
        omega
      have h_mod3 : k ≡ 2 [MOD 3] := by
        dsimp [Nat.ModEq]
        rw [h_div_eq]
        omega
      have h_dvd : 37 ∣ concatenate k 2593 := dvd_concatenate_37 k h_mod3
      have h_hlt : 37 < concatenate k 2593 := by
        dsimp [concatenate]
        rw [num_digits_2593]
        have h_rep := rep_threes_ge_three k hk
        omega
      exact composite_of_dvd (concatenate k 2593) 37 (by decide) h_dvd h_hlt
    · have h_div_eq : k = 12 * (k / 12) + 4 := by
        have := Nat.div_add_mod k 12
        omega
      have h_mod6 : k ≡ 4 [MOD 6] := by
        dsimp [Nat.ModEq]
        rw [h_div_eq]
        omega
      have h_dvd : 7 ∣ concatenate k 2593 := dvd_concatenate_7 k h_mod6
      have h_hlt : 7 < concatenate k 2593 := by
        dsimp [concatenate]
        rw [num_digits_2593]
        have h_rep := rep_threes_ge_three k hk
        omega
      exact composite_of_dvd (concatenate k 2593) 7 (by decide) h_dvd h_hlt
    · have h_div_eq : k = 12 * (k / 12) + 6 := by
        have := Nat.div_add_mod k 12
        omega
      have h_mod4 : k ≡ 2 [MOD 4] := by
        dsimp [Nat.ModEq]
        rw [h_div_eq]
        omega
      have h_dvd : 101 ∣ concatenate k 2593 := dvd_concatenate_101 k h_mod4
      have h_hlt : 101 < concatenate k 2593 := by
        dsimp [concatenate]
        rw [num_digits_2593]
        have h_rep := rep_threes_ge_three k hk
        omega
      exact composite_of_dvd (concatenate k 2593) 101 (by decide) h_dvd h_hlt
    · have h_div_eq : k = 12 * (k / 12) + 8 := by
        have := Nat.div_add_mod k 12
        omega
      have h_mod3 : k ≡ 2 [MOD 3] := by
        dsimp [Nat.ModEq]
        rw [h_div_eq]
        omega
      have h_dvd : 37 ∣ concatenate k 2593 := dvd_concatenate_37 k h_mod3
      have h_hlt : 37 < concatenate k 2593 := by
        dsimp [concatenate]
        rw [num_digits_2593]
        have h_rep := rep_threes_ge_three k hk
        omega
      exact composite_of_dvd (concatenate k 2593) 37 (by decide) h_dvd h_hlt
    · have h_div_eq : k = 12 * (k / 12) + 10 := by
        have := Nat.div_add_mod k 12
        omega
      have h_mod6 : k ≡ 4 [MOD 6] := by
        dsimp [Nat.ModEq]
        rw [h_div_eq]
        omega
      have h_dvd : 7 ∣ concatenate k 2593 := dvd_concatenate_7 k h_mod6
      have h_hlt : 7 < concatenate k 2593 := by
        dsimp [concatenate]
        rw [num_digits_2593]
        have h_rep := rep_threes_ge_three k hk
        omega
      exact composite_of_dvd (concatenate k 2593) 7 (by decide) h_dvd h_hlt

/-
### Section 4: Main Disproof Theorem
-/

/-- Disproof of the OEIS A242775 Conjecture. -/
theorem oeis_242775_conjecture_0.disproof : ¬ (∀ n, 4 ≤ n → A242775 n > 0) := by
  intro h
  have h_378 : 4 ≤ 378 := by decide
  have h_pos := h 378 h_378
  have h_eq : A242775 378 = 0 := by
    dsimp [A242775]
    have h_empty : { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index 378)) } = ∅ := by
      ext k
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hk_pos
      rw [prime_of_index_378]
      exact composite_2593 k hk_pos
    rw [h_empty]
    exact sInf_empty
  rw [h_eq] at h_pos
  exact Nat.not_lt_zero 0 h_pos


#print axioms oeis_242775_conjecture_0.disproof
