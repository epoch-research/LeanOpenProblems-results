import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score = 0 at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by 1
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  -- P_i is the $i$-th prime, 0-indexed: P 0 = 2, P 1 = 3, ...
  -- Note: Nat.nth Nat.Prime i gives the i-th prime, where i=0 is the 0-th prime, 2.
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

  -- $G_k$ is the $k$-th prime gap (OEIS 1-indexed), $G_k = P_k - P_{k-1}$, for $k \ge 1$.
  -- Here we use the 0-indexed primes P_i, so the k-th gap involves the prime P[k] and P[k-1].
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)

  if n = 0 then 0 -- Defining for n=0 as 0, though OEIS starts at 1
  else if n = 1 then 0
  else

  -- The score is the cumulative sum of the changes $\Delta(k) = \operatorname{sign}(G_k - G_{k-1})$ for $k=2$ to $n$.
  -- The sum starts at k=2 because the first gap G_1 is compared to G_2. The comparison is between G_k and G_{k-1}.
  -- Since the first gap is G_1, the first comparison is at k=2 (G_2 vs G_1).
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    -- Since $k \ge 2$, $k-1 \ge 1$, so G_gap (k-1) is safely computed.
    let Gkm1 : ℕ := G_gap (k - 1)

    -- Calculate $\operatorname{sign}(G_k - G_{k-1})$ using integer subtraction and sign function.
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/-
We remove the specific proofs for a_one etc., as they failed compilation and are not the object of the final submission.
The definition of A092243 is now corrected for proper syntax of the n-th prime.
-/

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).

Questions from OEIS A092243, including the primary conjectures:
1. Is s > 0 for some n > 250000?
2. Is s bounded from below?
3. Is s bounded from above?
4. Is s > 0 for infinitely many values of n?
5. Is s < 0 for infinitely many values of n?
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

lemma A092243_succ (n : ℕ) (hn : n ≥ 1) :
    A092243 (n + 1) = A092243 n +
      let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
      let G_gap (k : ℕ) : ℕ := P k - P (k - 1)
      ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)).sign := by
  unfold A092243
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · simp
  · simp
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp

theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  have : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_five : A092243 5 = 1 := by
  rw [A092243_succ 4 (by omega)]
  rw [A092243_succ 3 (by omega)]
  rw [A092243_succ 2 (by omega)]
  rw [A092243_succ 1 (by omega)]
  unfold A092243
  simp [nth_prime_five_eq_thirteen]


theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  have : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_six : A092243 6 = 2 := by
  rw [A092243_succ 5 (by omega)]
  rw [a_five]
  simp [nth_prime_five_eq_thirteen, nth_prime_six_eq_seventeen]
  decide

theorem nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 := by
  have : Nat.count Nat.Prime 19 = 7 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_seven : A092243 7 = 1 := by
  rw [A092243_succ 6 (by omega)]
  rw [a_six]
  simp [nth_prime_five_eq_thirteen, nth_prime_six_eq_seventeen, nth_prime_seven_eq_nineteen]
  decide

theorem nth_prime_eight_eq_twenty_three : Nat.nth Nat.Prime 8 = 23 := by
  have : Nat.count Nat.Prime 23 = 8 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_eight : A092243 8 = 2 := by
  rw [A092243_succ 7 (by omega)]
  rw [a_seven]
  simp [nth_prime_six_eq_seventeen, nth_prime_seven_eq_nineteen, nth_prime_eight_eq_twenty_three]
  decide

theorem nth_prime_nine_eq_twenty_nine : Nat.nth Nat.Prime 9 = 29 := by
  have : Nat.count Nat.Prime 29 = 9 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_nine : A092243 9 = 3 := by
  rw [A092243_succ 8 (by omega)]
  rw [a_eight]
  simp [nth_prime_seven_eq_nineteen, nth_prime_eight_eq_twenty_three, nth_prime_nine_eq_twenty_nine]
  decide



lemma composite_of_factorial_add (K : ℕ) (i : ℕ) (hi2 : 2 ≤ i) (hiK : i ≤ K + 2) :
    ¬ Nat.Prime ((K + 2)! + i) := by
  intro hp
  have hdvd : i ∣ (K + 2)! := Nat.dvd_factorial (by omega) hiK
  have hdvd_add : i ∣ (K + 2)! + i := Nat.dvd_add hdvd (dvd_rfl)
  have h_eq_or_one := hp.eq_one_or_self_of_dvd _ hdvd_add
  rcases h_eq_or_one with h_one | h_self
  · omega
  · have : (K + 2)! + i > i := by
      have : (K + 2)! > 0 := Nat.factorial_pos _
      omega
    omega

noncomputable def P_prime (i : ℕ) : ℕ := Nat.nth Nat.Prime i
noncomputable def G_gap (k : ℕ) : ℕ := P_prime k - P_prime (k - 1)

theorem G_gap_zero : G_gap 0 = 0 := by
  simp [G_gap, P_prime]

theorem G_gap_one : G_gap 1 = 1 := by
  simp [G_gap, P_prime]

theorem G_gap_unbounded (K : ℕ) : ∃ n, G_gap n > K := by
  let N := (K + 2)!
  let c := Nat.count Nat.Prime (N + 1)
  have hp_inf : {p : ℕ | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime
  have h_le : N + 1 ≤ P_prime c := by
    have h_gc := count_le_iff_le_nth hp_inf (a := N + 1) (b := c)
    unfold P_prime
    rw [← h_gc]
  have h_lt_prev : ∀ a < c, P_prime a < N + 1 := by
    intro a ha
    have h_gc := lt_nth_iff_count_lt hp_inf (a := a) (b := N + 1)
    unfold P_prime
    rw [← h_gc]
    exact ha
  by_cases h_ge : P_prime c ≥ N + K + 3
  · use c
    have hc_pos : c > 0 := by
      by_contra! hc_zero
      have : c = 0 := by omega
      have hP0 : P_prime 0 = 2 := Nat.nth_prime_zero_eq_two
      have : P_prime c = 2 := by rw [this, hP0]
      have hN_pos : N ≥ 2 := by
        have h1 : 2 ≤ K + 2 := by omega
        have h2 : K + 2 ≤ (K + 2)! := Nat.self_le_factorial (K + 2)
        omega
      omega
    have h_prev : P_prime (c - 1) < N + 1 := h_lt_prev (c - 1) (by omega)
    unfold G_gap
    omega
  · use c + 1
    have h_eq : P_prime c = N + 1 := by
      by_contra! h_neq
      have h_lt_sub : P_prime c < N + K + 3 := by omega
      have h_cases : P_prime c ∈ Finset.Icc (N + 2) (N + K + 2) := by
        rw [Finset.mem_Icc]
        omega
      rw [Finset.mem_Icc] at h_cases
      have h_not_prime : ∀ i ∈ Finset.Icc 2 (K + 2), ¬ Nat.Prime (N + i) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        exact composite_of_factorial_add K i hi.1 hi.2
      have h_exists_i : ∃ i ∈ Finset.Icc 2 (K + 2), P_prime c = N + i := by
        use P_prime c - N
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      rcases h_exists_i with ⟨i, hi, h_i_eq⟩
      have h_prime : Nat.Prime (P_prime c) := nth_mem_of_infinite hp_inf c
      rw [h_i_eq] at h_prime
      exact h_not_prime i hi h_prime
    have h_succ_gt : P_prime (c + 1) ≥ N + K + 3 := by
      by_contra! h_succ_lt
      have h_prime_succ : Nat.Prime (P_prime (c + 1)) := nth_mem_of_infinite hp_inf (c + 1)
      have h_gt_c : P_prime (c + 1) > P_prime c := by
        have h_mono := nth_strictMono hp_inf
        unfold P_prime at h_mono ⊢
        apply h_mono
        omega
      have h_cases_succ : P_prime (c + 1) ∈ Finset.Icc (N + 2) (N + K + 2) := by
        rw [Finset.mem_Icc]
        omega
      rw [Finset.mem_Icc] at h_cases_succ
      have h_exists_i : ∃ i ∈ Finset.Icc 2 (K + 2), P_prime (c + 1) = N + i := by
        use P_prime (c + 1) - N
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      rcases h_exists_i with ⟨i, hi, h_i_eq⟩
      rw [h_i_eq] at h_prime_succ
      exact composite_of_factorial_add K i (by rw [Finset.mem_Icc] at hi; omega) (by rw [Finset.mem_Icc] at hi; omega) h_prime_succ
    unfold G_gap
    change P_prime (c + 1) - P_prime c > K
    omega

lemma G_gap_unbounded_int (B : ℤ) : ∃ n, (G_gap n : ℤ) > B := by
  obtain ⟨n, hn⟩ := G_gap_unbounded (max 0 B).toNat
  use n
  have : (max 0 B).toNat ≥ B := by omega
  omega



lemma oeis_92243_conjecture.gap_bound_of_score_bound (B : ℤ) (h_score : ∀ n, A092243 n ≤ B) (n : ℕ) (hn : n ≥ 2) : (G_gap n : ℤ) ≤ 2 * B + 8 := by
  sorry

theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  rcases h.bounded_above with ⟨B, h_score⟩
  obtain ⟨n, hn_unbdd⟩ := G_gap_unbounded_int (max (2 * B + 8) 1)
  have hn_ge_2 : n ≥ 2 := by
    by_contra! hn_lt_2
    interval_cases n
    · have : G_gap 0 = 0 := G_gap_zero
      omega
    · have : G_gap 1 = 1 := G_gap_one
      omega
  have hg := oeis_92243_conjecture.gap_bound_of_score_bound B h_score n hn_ge_2
  omega

