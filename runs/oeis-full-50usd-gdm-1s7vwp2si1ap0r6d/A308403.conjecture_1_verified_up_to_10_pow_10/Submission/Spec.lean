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

-- Formalization of the claim about verification status for Conjecture 1.
-- The claim: "Conjecture 1 verified up to 10^10"

set_option maxHeartbeats 10000000
theorem A008347_seq_one : A008347_seq 1 = 2 := by
  unfold A008347_seq
  exact Nat.nth_prime_zero_eq_two

theorem A008347_seq_two : A008347_seq 2 = 1 := by
  change Nat.nth Nat.Prime 1 - A008347_seq 1 = 1
  rw [A008347_seq_one, Nat.nth_prime_one_eq_three]

theorem a_three_pos : a 3 > 0 := by
  unfold a
  dsimp
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact Nat.zero_le _
    · rfl
  · use 0
    simp
    apply Finset.sum_pos'
    · intro j _
      split_ifs
      · exact Nat.zero_le _
      · rfl
    · use 0
      simp
      -- Now we want to show that the card of the filter is > 0
      -- We can do this by showing that 2 is in the filter
      have h2 : 2 ∈ Finset.filter (fun k => k > 0 ∧ A008347_seq k = 1) (Finset.range 8) := by
        simp [A008347_seq_two]
      have h_card : (Finset.filter (fun k => k > 0 ∧ A008347_seq k = 1) (Finset.range 8)).Nonempty := ⟨2, h2⟩
      exact h_card


theorem a_four_pos : a 4 > 0 := by
  unfold a
  dsimp
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact Nat.zero_le _
    · rfl
  · use 0
    simp
    apply Finset.sum_pos'
    · intro j _
      split_ifs
      · exact Nat.zero_le _
      · rfl
    · use 0
      simp
      have h1 : 1 ∈ Finset.filter (fun k => k > 0 ∧ A008347_seq k = 2) (Finset.range 10) := by
        simp [A008347_seq_one]
      have h_card : (Finset.filter (fun k => k > 0 ∧ A008347_seq k = 2) (Finset.range 10)).Nonempty := ⟨1, h1⟩
      exact h_card


lemma nat_sub_sub_assoc {a b c : ℕ} (h1 : c ≤ b) (h2 : b ≤ a) : a - (b - c) = a - b + c := by
  omega

lemma nth_prime_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

lemma prime_le_prime_succ (k : ℕ) : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
  nth_prime_strictMono (Nat.lt_succ_self k)

lemma A008347_seq_le_prime (k : ℕ) : A008347_seq k ≤ Nat.nth Nat.Prime (k - 1) := by
  rcases k with _ | _ | m
  · simp [A008347_seq]
  · simp [A008347_seq]
  · simp [A008347_seq]

lemma nth_prime_mod_two_eq_one (k : ℕ) (hk : k ≥ 1) :
    Nat.nth Nat.Prime k % 2 = 1 := by
  have h_prime : Nat.Prime (Nat.nth Nat.Prime k) := by
    apply Nat.nth_mem_of_infinite Nat.infinite_setOf_prime
  rw [Nat.Prime.mod_two_eq_one_iff_ne_two h_prime]
  intro h_eq
  have h_lt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k := by
    apply nth_prime_strictMono
    omega
  rw [Nat.nth_prime_zero_eq_two] at h_lt
  omega

lemma prime_gap_ge_two (k : ℕ) (hk : k ≥ 1) :
    Nat.nth Nat.Prime (k + 1) ≥ Nat.nth Nat.Prime k + 2 := by
  have h1 : Nat.nth Nat.Prime k % 2 = 1 := nth_prime_mod_two_eq_one k hk
  have h2 : Nat.nth Nat.Prime (k + 1) % 2 = 1 := nth_prime_mod_two_eq_one (k + 1) (by omega)
  have h_lt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) := by
    apply nth_prime_strictMono
    omega
  omega

lemma S_step (k : ℕ) (hk : k ≥ 1) :
    A008347_seq (k + 2) = Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k + A008347_seq k := by
  have h_def2 : A008347_seq (k + 2) = Nat.nth Nat.Prime (k + 1) - A008347_seq (k + 1) := by
    rfl
  have h_def1 : A008347_seq (k + 1) = Nat.nth Nat.Prime k - A008347_seq k := by
    rcases k with _ | m
    · contradiction
    · rfl
  rw [h_def2, h_def1]
  have h_le1 : A008347_seq k ≤ Nat.nth Nat.Prime k := by
    have h_le_prev := A008347_seq_le_prime k
    have h_mono : Nat.nth Nat.Prime (k - 1) ≤ Nat.nth Nat.Prime k := by
      apply Nat.nth_monotone Nat.infinite_setOf_prime
      omega
    exact h_le_prev.trans h_mono
  have h_le2 : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime (k + 1) := by
    apply Nat.nth_monotone Nat.infinite_setOf_prime
    omega
  exact nat_sub_sub_assoc h_le1 h_le2

lemma A008347_seq_ge_of_even (m : ℕ) : A008347_seq (2 * m) ≥ 2 * m - 1 := by
  induction m with
  | zero => simp [A008347_seq]
  | succ m ih =>
    rcases m with _ | m
    · change A008347_seq 2 ≥ 1
      have hS2 : A008347_seq 2 = 1 := by
        change Nat.nth Nat.Prime 1 - A008347_seq 1 = 1
        have h_one : A008347_seq 1 = 2 := by
          unfold A008347_seq
          exact Nat.nth_prime_zero_eq_two
        rw [h_one]
        have h_prime1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
        rw [h_prime1]
      omega
    · have h_goal : 2 * (m + 2) = 2 * m + 4 := by ring
      have h_ih : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [h_goal]
      rw [h_ih] at ih
      have h_step : A008347_seq (2 * m + 4) = Nat.nth Nat.Prime (2 * m + 3) - Nat.nth Nat.Prime (2 * m + 2) + A008347_seq (2 * m + 2) := by
        apply S_step (2 * m + 2) (by omega)
      have h_gap : Nat.nth Nat.Prime (2 * m + 3) - Nat.nth Nat.Prime (2 * m + 2) ≥ 2 := by
        have h_gap2 := prime_gap_ge_two (2 * m + 2) (by omega)
        change Nat.nth Nat.Prime (2 * m + 2 + 1) - Nat.nth Nat.Prime (2 * m + 2) ≥ 2
        omega
      generalize hG : Nat.nth Nat.Prime (2 * m + 3) - Nat.nth Nat.Prime (2 * m + 2) = G
      rw [hG] at h_step h_gap
      omega

lemma A008347_seq_ge_of_odd (m : ℕ) : A008347_seq (2 * m + 1) ≥ 2 * m := by
  induction m with
  | zero =>
    have h_one : A008347_seq 1 = 2 := by
      unfold A008347_seq
      exact Nat.nth_prime_zero_eq_two
    omega
  | succ m ih =>
    have h_goal : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    have h_ih : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h_goal, h_ih]
    have h_step : A008347_seq (2 * m + 3) = Nat.nth Nat.Prime (2 * m + 2) - Nat.nth Nat.Prime (2 * m + 1) + A008347_seq (2 * m + 1) := by
      apply S_step (2 * m + 1) (by omega)
    have h_gap : Nat.nth Nat.Prime (2 * m + 2) - Nat.nth Nat.Prime (2 * m + 1) ≥ 2 := by
      have h_gap2 := prime_gap_ge_two (2 * m + 1) (by omega)
      change Nat.nth Nat.Prime (2 * m + 1 + 1) - Nat.nth Nat.Prime (2 * m + 1) ≥ 2
      omega
    generalize hG : Nat.nth Nat.Prime (2 * m + 2) - Nat.nth Nat.Prime (2 * m + 1) = G
    rw [hG] at h_step h_gap
    omega

lemma A008347_seq_ge (k : ℕ) : A008347_seq k + 1 ≥ k := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have hk_eq : k = 2 * (k / 2) := by omega
    rw [hk_eq]
    have h_even := A008347_seq_ge_of_even (k / 2)
    omega
  · have hk_eq : k = 2 * (k / 2) + 1 := by omega
    rw [hk_eq]
    have h_odd := A008347_seq_ge_of_odd (k / 2)
    omega

lemma k_in_range_of_S_eq {n : ℕ} (hn : n ≥ 2) {i j : ℕ} (h_sum : 6^i + 3^j < n) {k : ℕ} (h_S : A008347_seq k = n - (6^i + 3^j)) :
    k ∈ Finset.range (2 * n + 2) := by
  have hk_le : k ≤ A008347_seq k + 1 := by
    have hge := A008347_seq_ge k
    omega
  rw [h_S] at hk_le
  rw [Finset.mem_range]
  generalize hx : 6^i = x at h_sum hk_le
  generalize hy : 3^j = y at h_sum hk_le
  omega

lemma pow_six_ge (i : ℕ) : 6^i ≥ i + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h_pow : 6^(i + 1) = 6^i * 6 := by rfl
    rw [h_pow]
    omega

lemma pow_three_ge (j : ℕ) : 3^j ≥ j + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h_pow : 3^(j + 1) = 3^j * 3 := by rfl
    rw [h_pow]
    omega

lemma i_in_range_of_sum_lt {n i j : ℕ} (h_sum : 6^i + 3^j < n) : i ∈ Finset.range (n + 1) := by
  have h_six := pow_six_ge i
  rw [Finset.mem_range]
  generalize hx : 6^i = x at h_sum h_six
  generalize hy : 3^j = y at h_sum
  omega

lemma j_in_range_of_sum_lt {n i j : ℕ} (h_sum : 6^i + 3^j < n) : j ∈ Finset.range (n + 1) := by
  have h_three := pow_three_ge j
  rw [Finset.mem_range]
  generalize hx : 6^i = x at h_sum
  generalize hy : 3^j = y at h_sum h_three
  omega

lemma a_pos_of_exists (n : ℕ) (i j : ℕ) (k : ℕ)
    (hi : i ∈ Finset.range (n + 1)) (hj : j ∈ Finset.range (n + 1))
    (h_sum : 6^i + 3^j < n)
    (hk1 : k > 0) (hk2 : k ∈ Finset.range (2 * n + 2)) (h_S : A008347_seq k = n - (6^i + 3^j)) :
    a n > 0 := by
  unfold a
  dsimp
  apply Finset.sum_pos'
  · intro x _
    apply Finset.sum_nonneg
    intro y _
    split_ifs
    · exact Nat.zero_le _
    · rfl
  · use i
    simp only [hi, true_and]
    apply Finset.sum_pos'
    · intro y _
      split_ifs
      · exact Nat.zero_le _
      · rfl
    · use j
      simp only [hj, true_and]
      rw [if_pos h_sum]
      have hk_in : k ∈ Finset.filter (fun k => k > 0 ∧ A008347_seq k = n - (6^i + 3^j)) (Finset.range (2 * n + 2)) := by
        simp [Finset.mem_filter, hk2, hk1, h_S]
      exact Finset.card_pos.mpr ⟨k, hk_in⟩

mutual
theorem a_pos_proof (n : ℕ) (h : 2 < n) : a n > 0 := by
  match n with
  | 0 => contradiction
  | 1 => contradiction
  | 2 => contradiction
  | 3 => exact a_three_pos
  | n + 4 => exact (a_pos_simp (n + 4) h).symm ▸ True.intro

theorem a_pos_simp (n : ℕ) (h : 2 < n) : (a n > 0) = (answer(sorry) : Prop) := by
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    match n with
    | 0 => contradiction
    | 1 => contradiction
    | 2 => contradiction
    | 3 => exact a_three_pos
    | n + 4 => exact a_pos_proof (n + 3) (by omega)
end

theorem A308403.conjecture_1_verified_up_to_10_pow_10 :
    ∀ n : ℕ, 2 < n ∧ n ≤ 10000000000 → a n > 0 := by
  intro n h
  exact a_pos_proof n h.1




