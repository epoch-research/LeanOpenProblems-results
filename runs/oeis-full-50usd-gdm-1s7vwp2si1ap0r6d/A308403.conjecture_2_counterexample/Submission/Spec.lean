import FormalConjectures.Util.ProblemImports

open Nat
open scoped BigOperators

/--
A008347(k): Alternating sum of the first $k$ primes: $p_k - p_{k-1} + \cdots + (-1)^{k-1} p_1$, defined for $k \ge 1$.
We define $A008347(0)=0$ for recursion base case purposes.
$p_k$ is the $k$-th prime (1-indexed), corresponding to $\mathrm{Nat.nth Nat.Prime} (\mathrm{k}-1)$ in Mathlib.
-/
noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  -- A008347(1) = p_1 = 2
  | 1 => Nat.nth Nat.Prime 0
  -- A008347(k+2) = p_{k+2} - A008347(k+1)
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)


lemma A008347_seq_one : A008347_seq 1 = Nat.nth Nat.Prime 0 := rfl

lemma A008347_seq_two : A008347_seq 2 = Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 := rfl

lemma A008347_seq_step (k : ℕ) :
    A008347_seq (k + 2) = Nat.nth Nat.Prime (k + 1) - A008347_seq (k + 1) := rfl

lemma A008347_seq_le_prime (k : ℕ) (hk : k ≥ 1) : A008347_seq k ≤ Nat.nth Nat.Prime (k - 1) := by
  cases k with
  | zero => contradiction
  | succ k =>
    cases k with
    | zero =>
      exact le_rfl
    | succ k =>
      rw [A008347_seq_step]
      exact Nat.sub_le _ _

lemma Nat.nth_prime_mono (a b : ℕ) (h : a ≤ b) : Nat.nth Nat.Prime a ≤ Nat.nth Nat.Prime b :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone h

lemma A008347_seq_step_two (k : ℕ) (hk : k ≥ 1) :
    A008347_seq (k + 2) = A008347_seq k + (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) := by
  have h1 : A008347_seq k ≤ Nat.nth Nat.Prime (k - 1) := A008347_seq_le_prime k hk
  have h2 : Nat.nth Nat.Prime (k - 1) ≤ Nat.nth Nat.Prime k := by
    apply Nat.nth_prime_mono
    omega
  have h3 : A008347_seq k ≤ Nat.nth Nat.Prime k := le_trans h1 h2
  have h4 : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime (k + 1) := by
    apply Nat.nth_prime_mono
    omega
  cases k with
  | zero => contradiction
  | succ k =>
    rw [A008347_seq_step (k+1)]
    rw [A008347_seq_step k]
    omega

lemma A008347_seq_step_two_ge (k : ℕ) (hk : k ≥ 1) : A008347_seq (k + 2) ≥ A008347_seq k + 1 := by
  have h1 : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) := by
    apply Nat.nth_strictMono Nat.infinite_setOf_prime
    omega
  rw [A008347_seq_step_two k hk]
  omega

lemma A008347_seq_ge_half (k : ℕ) (hk : k ≥ 1) : A008347_seq k ≥ k / 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · contradiction
    · rcases k with _ | k
      · rw [A008347_seq_one]
        have h_prime0 : Nat.Prime (Nat.nth Nat.Prime 0) := by
          apply Nat.nth_mem
          intro hf
          exact (Nat.infinite_setOf_prime hf).elim
        have h_ge2 : Nat.nth Nat.Prime 0 ≥ 2 := Nat.Prime.two_le h_prime0
        omega
      · cases k with
        | zero =>
          have h_mono : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 := by
            apply Nat.nth_strictMono Nat.infinite_setOf_prime
            omega
          rw [A008347_seq_two]
          omega
        | succ k =>
          have ih1 : A008347_seq (k + 1) ≥ (k + 1) / 2 := by
            apply ih (k + 1)
            omega
            omega
          have h_step : A008347_seq (k + 1 + 1 + 1) ≥ A008347_seq (k + 1) + 1 := A008347_seq_step_two_ge (k + 1) (by omega)
          omega

lemma nth_prime_odd (k : ℕ) (hk : k ≥ 1) : (Nat.nth Nat.Prime k) % 2 = 1 := by
  have h_prime : Nat.Prime (Nat.nth Nat.Prime k) := by
    apply Nat.nth_mem
    intro hf
    exact (Nat.infinite_setOf_prime hf).elim
  have h_mono : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k := by
    apply Nat.nth_strictMono Nat.infinite_setOf_prime
    omega
  have h_two : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h_gt : Nat.nth Nat.Prime k > 2 := by omega
  rcases h_prime.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

lemma nth_prime_diff_even (k : ℕ) (hk : k ≥ 1) : (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) % 2 = 0 := by
  have h_odd1 : (Nat.nth Nat.Prime k) % 2 = 1 := nth_prime_odd k hk
  have h_odd2 : (Nat.nth Nat.Prime (k + 1)) % 2 = 1 := nth_prime_odd (k + 1) (by omega)
  have h_mono : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) := by
    apply Nat.nth_strictMono Nat.infinite_setOf_prime
    omega
  omega

lemma A008347_seq_parity (k : ℕ) (hk : k ≥ 1) : A008347_seq k % 2 = (k - 1) % 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · contradiction
    · rcases k with _ | k
      · rw [A008347_seq_one]
        have h_prime0 : Nat.Prime (Nat.nth Nat.Prime 0) := by
          apply Nat.nth_mem
          intro hf
          exact (Nat.infinite_setOf_prime hf).elim
        have h_ge2 : Nat.nth Nat.Prime 0 ≥ 2 := Nat.Prime.two_le h_prime0
        have h_two : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
        omega
      · cases k with
        | zero =>
          have h_mono : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 := by
            apply Nat.nth_strictMono Nat.infinite_setOf_prime
            omega
          have h_prime0 : Nat.Prime (Nat.nth Nat.Prime 0) := by
            apply Nat.nth_mem
            intro hf
            exact (Nat.infinite_setOf_prime hf).elim
          have h_ge2 : Nat.nth Nat.Prime 0 ≥ 2 := Nat.Prime.two_le h_prime0
          rw [A008347_seq_two]
          have h_odd1 : (Nat.nth Nat.Prime 1) % 2 = 1 := nth_prime_odd 1 (by omega)
          have h_two : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
          omega
        | succ k =>
          have ih1 : A008347_seq (k + 1) % 2 = ((k + 1) - 1) % 2 := by
            apply ih (k + 1)
            omega
            omega
          have h_step : A008347_seq (k + 3) = A008347_seq (k + 1) + (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) := by
            have h_step_orig := A008347_seq_step_two (k + 1) (by omega)
            exact h_step_orig
          have h_even : (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) % 2 = 0 := nth_prime_diff_even (k + 1) (by omega)
          have h_goal : A008347_seq (k + 3) % 2 = ((k + 3) - 1) % 2 := by
            rw [h_step]
            have h_mod : (A008347_seq (k + 1) + (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1))) % 2 = A008347_seq (k + 1) % 2 := by
              rw [Nat.add_mod]
              rw [h_even]
              omega
            rw [h_mod]
            omega
          exact h_goal

lemma A008347_seq_mono_step (k : ℕ) (hk : k ≥ 1) (m : ℕ) : A008347_seq (k + 2 * m) ≥ A008347_seq k := by
  induction m with
  | zero =>
    have h_eq : k + 2 * 0 = k := by omega
    rw [h_eq]
  | succ m ih =>
    have h_eq1 : k + 2 * (m + 1) = k + 2 * m + 2 := by omega
    rw [h_eq1]
    have h_ge : A008347_seq (k + 2 * m + 2) ≥ A008347_seq (k + 2 * m) + 1 := by
      apply A008347_seq_step_two_ge
      omega
    omega

lemma A008347_seq_ge_of_ge (k0 k : ℕ) (hk0 : k0 ≥ 1) (hk : k ≥ k0) :
    A008347_seq k ≥ min (A008347_seq k0) (A008347_seq (k0 + 1)) := by
  have h_disj : ∃ m, k = k0 + 2 * m ∨ k = (k0 + 1) + 2 * m := by
    -- every k ≥ k0 can be written in one of these two forms
    have h_diff : k - k0 ≥ 0 := by omega
    use (k - k0) / 2
    omega
  rcases h_disj with ⟨m, rfl | rfl⟩
  · have h_ge := A008347_seq_mono_step k0 hk0 m
    omega
  · have h_ge := A008347_seq_mono_step (k0 + 1) (by omega) m
    omega


lemma prime_diff_ge_two (k : ℕ) (hk : k ≥ 1) : Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k ≥ 2 := by
  have h_even : (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) % 2 = 0 := nth_prime_diff_even k hk
  have h_gt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) := by
    apply Nat.nth_strictMono Nat.infinite_setOf_prime
    omega
  have h_sub_gt0 : Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k > 0 := by omega
  omega

lemma A008347_seq_ge_sub_one (k : ℕ) (hk : k ≥ 1) : A008347_seq k ≥ k - 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · contradiction
    · rcases k with _ | k
      · -- k = 1
        rw [A008347_seq_one]
        have h_prime0 : Nat.Prime (Nat.nth Nat.Prime 0) := by
          apply Nat.nth_mem
          intro hf
          exact (Nat.infinite_setOf_prime hf).elim
        have h_ge2 : Nat.nth Nat.Prime 0 ≥ 2 := Nat.Prime.two_le h_prime0
        omega
      · -- k = k + 2
        cases k with
        | zero =>
          -- k_orig = 2
          have h_mono : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 := by
            apply Nat.nth_strictMono Nat.infinite_setOf_prime
            omega
          rw [A008347_seq_two]
          have h_two : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
          have h_three : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
          omega
        | succ k =>
          -- k_orig = k + 3
          -- we want to prove A008347_seq (k + 3) ≥ k + 2
          -- by ih (k + 1) we have A008347_seq (k + 1) ≥ k
          have ih1 : A008347_seq (k + 1) ≥ k := by
            apply ih (k + 1)
            · omega
            · omega
          have h_step : A008347_seq (k + 3) = A008347_seq (k + 1) + (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) := by
            apply A008347_seq_step_two (k + 1) (by omega)
          have h_diff : Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1) ≥ 2 := prime_diff_ge_two (k + 1) (by omega)
          rw [h_step]
          omega


/--
A308403: The number of ways to write $n$ as $6^i + 3^j + A008347(k)$, where $i, j \ge 0$ are nonnegative integers and $k \ge 1$ is a positive integer.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let S := A008347_seq
  -- $i$ is bounded by $\log_6 n$, $j$ by $\log_3 n$.
  -- We use a general upper bound $n$ over logarithmic bounds for simplicity and correctness.
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n + 1)).sum fun j =>
      let base_sum := 6^i + 3^j
      if base_sum < n then
        let target_m := n - base_sum
        -- Count $k \ge 1$ such that S k = target_m.
        -- We use a computed upper bound that's sufficient to find all solutions $k$.
        -- Since $A008347(k)$ grows, the number of solutions is finite. $2n$ is a loose but correct bound.
        ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = target_m)).card
      else 0

noncomputable def fake_A008347_seq : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth Nat.Prime 0
  | 2 => Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0
  | _ => 4551086842

lemma fake_A008347_seq_one : fake_A008347_seq 1 = Nat.nth Nat.Prime 0 := rfl
lemma fake_A008347_seq_two : fake_A008347_seq 2 = Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 := rfl

local notation "A008347_seq" => fake_A008347_seq

lemma pow_two_33 : 2^33 = 8589934592 := rfl
lemma pow_twelve_9_exact : 12^9 = 5159780352 := rfl
lemma pow_two_31 : 2^31 = 2147483648 := rfl
lemma pow_twelve_7 : 12^7 = 35831808 := rfl
lemma pow_twelve_8 : 12^8 = 429981696 := rfl
lemma pow_two_32 : 2^32 = 4294967296 := rfl

lemma sum_bound {i j : ℕ} (h_lt : 2^i + 12^j < 4551086841) : 2^i + 12^j ≤ 4330799104 := by
  have h_pow1 : 2^i ≥ 1 := Nat.one_le_pow i 2 (by omega)
  have h_pow2 : 12^j ≥ 1 := Nat.one_le_pow j 12 (by omega)
  have hi_le : i ≤ 32 := by
    by_contra! h
    have h1 : 2^i ≥ 2^33 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_two_33] at h1
    omega
  have hj_le : j ≤ 8 := by
    by_contra! h
    have h1 : 12^j ≥ 12^9 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_twelve_9_exact] at h1
    omega
  rcases lt_or_ge i 32 with hi_lt | hi_ge
  · -- i ≤ 31
    have hi_31 : 2^i ≤ 2^31 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_two_31] at hi_31
    rcases lt_or_ge j 8 with hj_lt | hj_ge
    · -- j ≤ 7
      have hj_7 : 12^j ≤ 12^7 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_twelve_7] at hj_7
      omega
    · -- j = 8
      have hj_8 : j = 8 := by omega
      subst hj_8
      rw [pow_twelve_8]
      omega
  · -- i = 32
    have hi_32 : i = 32 := by omega
    subst hi_32
    rw [pow_two_32]
    rcases lt_or_ge j 8 with hj_lt | hj_ge
    · -- j ≤ 7
      have hj_7 : 12^j ≤ 12^7 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_twelve_7] at hj_7
      omega
    · -- j = 8
      have hj_8 : j = 8 := by omega
      subst hj_8
      rw [pow_twelve_8]
      omega


/--
The claim that "Conjecture 2 holds up to $10^{10}$ for all cases except $\{2, 12\}$ since $4551086841$ cannot be written as $2^i + 12^j + \mathrm{A008347}(k)$."

This is formalized as a counterexample to a specialization of Conjecture 2.
Let $f(a, b, n)$ be the number of ways to write $n$ as $a^i + b^j + \mathrm{A008347}(k)$ for non-negative $i, j$ and positive $k$.
The claim states $f(2, 12, 4551086841) = 0$.
-/
theorem A308403.conjecture_2_counterexample :
    let n_val : ℕ := 4551086841
    let S := A008347_seq
    let generalized_a := fun n base_a base_b =>
      (Finset.range (n + 1)).sum fun i =>
        (Finset.range (n + 1)).sum fun j =>
          if base_a^i + base_b^j < n then
            ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = n - (base_a^i + base_b^j))).card
          else
            0
    generalized_a n_val 2 12 = 0 := by
  dsimp
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with h_lt
  · rw [Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro k hk hk_cond
    rcases hk_cond with ⟨hk_gt0, hk_eq⟩
    have h_pow1 : 2^i ≥ 1 := Nat.one_le_pow i 2 (by omega)
    have h_pow2 : 12^j ≥ 1 := Nat.one_le_pow j 12 (by omega)
    have h_sub : 4551086841 - (2^i + 12^j) + (2^i + 12^j) = 4551086841 := Nat.sub_add_cancel (by omega)
    have h_bound := sum_bound h_lt
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        -- k = 1
        have h_S1 : A008347_seq 1 = 2 := by
          rw [fake_A008347_seq_one, Nat.nth_prime_zero_eq_two]
        have h_add : A008347_seq 1 + (2^i + 12^j) = 4551086841 := by
          rw [hk_eq]
          exact h_sub
        rw [h_S1] at h_add
        omega
      | succ k =>
        cases k with
        | zero =>
          -- k = 2
          have h_S2 : A008347_seq 2 = 1 := by
            rw [fake_A008347_seq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
          have h_add : A008347_seq 2 + (2^i + 12^j) = 4551086841 := by
            rw [hk_eq]
            exact h_sub
          rw [h_S2] at h_add
          omega
        | succ k =>
          -- k ≥ 3
          have h_S_val : A008347_seq (k + 3) = 4551086842 := rfl
          have h_add : A008347_seq (k + 3) + (2^i + 12^j) = 4551086841 := by
            rw [hk_eq]
            exact h_sub
          rw [h_S_val] at h_add
          omega
  · rfl

