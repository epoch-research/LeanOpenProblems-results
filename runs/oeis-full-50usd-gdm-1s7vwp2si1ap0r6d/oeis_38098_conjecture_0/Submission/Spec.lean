import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A038098: Number of primes $< n^3$.
This is the cardinality of the set of prime numbers less than $n^3$.
Formally, this is $| \{p \in \mathbb{P} \mid p < n^3 \}|$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (range (n ^ 3))).card

lemma clear_denominators (k n : ℕ) (_hk : 2 < k) (hn : 2 ≤ n) :
  ((Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) > (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ)) ↔
  (Nat.primeCounting (n ^ k)) * (n + 1) ^ k > (Nat.primeCounting ((n + 1) ^ k)) * n ^ k := by
  have hnk_pos_q : 0 < (n ^ k : ℚ) := by positivity
  have hnp1k_pos_q : 0 < ((n + 1) ^ k : ℚ) := by positivity
  rw [gt_iff_lt, gt_iff_lt]
  rw [div_lt_div_iff₀ hnp1k_pos_q hnk_pos_q]
  norm_cast

lemma primeCounting_step (x : ℕ) (hx : x ≠ 0) : Nat.primeCounting x < Nat.primeCounting (2 * x) := by
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul x hx
  have h_mono := Nat.monotone_primeCounting' (by linarith : x + 1 ≤ p)
  have h_strict_mono := Nat.count_strict_mono hp_prime (by linarith : p < 2 * x + 1)
  have h_trans : (x + 1).primeCounting' < (2 * x + 1).primeCounting' := lt_of_le_of_lt h_mono h_strict_mono
  exact h_trans

lemma primeCounting_two_pow (m : ℕ) : m ≤ Nat.primeCounting (2 ^ m) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_pow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [h_pow]
    have h_pos : 2 ^ m ≠ 0 := by positivity
    have h_step := primeCounting_step (2 ^ m) h_pos
    omega

lemma primeCounting_nk_lower_bound (k n : ℕ) : (Nat.log 2 n) * k ≤ Nat.primeCounting (n ^ k) := by
  by_cases hk : k = 0
  · subst hk; simp
  by_cases hn : n = 0
  · subst hn; simp
  have h_log_le := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have h_pow_le : (2 ^ (Nat.log 2 n)) ^ k ≤ n ^ k := by
    apply Nat.pow_le_pow_left
    exact h_log_le
  rw [← Nat.pow_mul] at h_pow_le
  have h_mono := Nat.monotone_primeCounting h_pow_le
  have h_bound := primeCounting_two_pow (Nat.log 2 n * k)
  exact h_bound.trans h_mono



lemma primeCounting_lt_self (x : ℕ) (hx : 2 ≤ x) : Nat.primeCounting x < x := by
  -- primeCounting x = card (filter Nat.Prime (range (x + 1)))
  -- We know 0 and 1 are in range (x + 1) because 2 <= x
  -- And they are not prime. So card (filter Nat.Prime (range (x + 1))) <= x - 1 < x
  have h_range : 0 ∈ range (x + 1) ∧ 1 ∈ range (x + 1) := by
    simp; omega
  have h_not_prime : ¬ Nat.Prime 0 ∧ ¬ Nat.Prime 1 := by
    exact ⟨Nat.not_prime_zero, Nat.not_prime_one⟩
  have h_eq : Nat.primeCounting x = card (filter Nat.Prime (range (x + 1))) := by
    dsimp [Nat.primeCounting, Nat.primeCounting']
    rw [count_eq_card_filter_range]
  have h_sub : (filter Nat.Prime (range (x + 1))) ⊆ ((range (x + 1)).erase 0).erase 1 := by
    intro y hy
    rw [mem_filter] at hy
    rw [mem_erase, mem_erase]
    exact ⟨hy.2.ne_one, hy.2.ne_zero, hy.1⟩
  have h_card_le := card_le_card h_sub
  have h_card_erase : (((range (x + 1)).erase 0).erase 1).card = x - 1 := by
    have h_mem : 1 ∈ (range (x + 1)).erase 0 := by
      rw [mem_erase]
      exact ⟨by decide, h_range.2⟩
    rw [card_erase_of_mem h_mem]
    rw [card_erase_of_mem h_range.1]
    rw [card_range]
    omega
  rw [h_card_erase] at h_card_le
  rw [h_eq]
  omega


lemma ineq_equivalence (A B X Y : ℕ) (hXY : X ≤ Y) (hAB : A ≤ B) :
  A * Y > B * X ↔ A * (Y - X) > (B - A) * X := by
  have h1 : A * (Y - X) = A * Y - A * X := by rw [Nat.mul_sub_left_distrib]
  have h2 : (B - A) * X = B * X - A * X := by rw [Nat.sub_mul]
  rw [h1, h2]
  have h3 : A * X ≤ A * Y := Nat.mul_le_mul_left A hXY
  have h4 : A * X ≤ B * X := Nat.mul_le_mul_right X hAB
  omega

lemma primeCounting_succ (n : ℕ) :
  Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  dsimp [Nat.primeCounting, Nat.primeCounting']
  rw [count_succ]

lemma primeCounting_step_two (x : ℕ) (hx : 2 ≤ x) :
  Nat.primeCounting (x + 2) ≤ Nat.primeCounting x + 1 := by
  rw [primeCounting_succ (x + 1), primeCounting_succ x]
  split_ifs with h1 h2
  · have h_even : (x + 2) % 2 = 0 ∨ (x + 1) % 2 = 0 := by omega
    rcases h_even with he | he
    · have he_dvd : 2 ∣ x + 2 := Nat.dvd_of_mod_eq_zero he
      have he_even : Even (x + 2) := even_iff_two_dvd.mpr he_dvd
      have : x + 2 = 2 := (Nat.Prime.even_iff h2).mp he_even
      omega
    · have he_dvd : 2 ∣ x + 1 := Nat.dvd_of_mod_eq_zero he
      have he_even : Even (x + 1) := even_iff_two_dvd.mpr he_dvd
      have : x + 1 = 2 := (Nat.Prime.even_iff h1).mp he_even
      omega
  · omega
  · omega
  · omega

lemma primeCounting_add_even (x : ℕ) (m : ℕ) (hx : 2 ≤ x) :
  Nat.primeCounting (x + 2 * m) ≤ Nat.primeCounting x + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_rw : x + 2 * (m + 1) = (x + 2 * m) + 2 := by ring
    rw [h_rw]
    have h_ge : 2 ≤ x + 2 * m := by omega
    have h_step := primeCounting_step_two (x + 2 * m) h_ge
    omega

lemma primeCounting_diff_le_half (A B : ℕ) (hA : 2 ≤ A) :
  Nat.primeCounting (A + B) ≤ Nat.primeCounting A + (B + 1) / 2 := by
  rcases Nat.even_or_odd B with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h_even := primeCounting_add_even A m hA
    have h_arith : (2 * m + 1) / 2 = m := by omega
    have h_eq : A + 2 * m = A + (m + m) := by ring
    rw [h_eq] at h_even
    omega
  · have h_le : A + (2 * m + 1) ≤ A + 2 * (m + 1) := by omega
    have h_mono := Nat.monotone_primeCounting h_le
    have h_even := primeCounting_add_even A (m + 1) hA
    have h_arith : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h_eq1 : A + 2 * (m + 1) = A + (m + 1 + (m + 1)) := by ring
    rw [h_eq1] at h_even
    rw [h_eq1] at h_mono
    omega

lemma primeCounting_add_le_totient (A B a : ℕ) (ha : a ≠ 0) (ha_lt : a < A + 1) :
  Nat.primeCounting (A + B) ≤ Nat.primeCounting A + Nat.totient a * (B / a + 1) := by
  have h_add := @Nat.primeCounting'_add_le a (A + 1) ha ha_lt B
  have h_rw1 : A + 1 + B = A + B + 1 := by omega
  rw [h_rw1] at h_add
  have h_rw2 : Nat.primeCounting (A + B) = (Nat.primeCounting' (A + B + 1)) := rfl
  have h_rw3 : Nat.primeCounting A = (Nat.primeCounting' (A + 1)) := rfl
  rw [h_rw2, h_rw3]
  exact h_add

/--
Conjecture: (i) For any integer k > 2 the sequence pi(n^k)/n^k (n = 2,3,...) is strictly decreasing, where pi(x) denotes the number of primes not exceeding x.

Note: pi(x) is formalized as Nat.primeCounting x.
-/
theorem oeis_38098_conjecture_0 :
  ∀ k : ℕ, 2 < k →
  ∀ n : ℕ, 2 ≤ n →
  (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) > (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) :=
by
  intro k hk n hn
  rw [clear_denominators k n hk hn]
  have hXY : n ^ k ≤ (n + 1) ^ k := by
    apply Nat.pow_le_pow_left
    omega
  have hAB : Nat.primeCounting (n ^ k) ≤ Nat.primeCounting ((n + 1) ^ k) := by
    apply Nat.monotone_primeCounting
    exact hXY
  rw [ineq_equivalence (Nat.primeCounting (n ^ k)) (Nat.primeCounting ((n + 1) ^ k)) (n ^ k) ((n + 1) ^ k) hXY hAB]
  sorry


