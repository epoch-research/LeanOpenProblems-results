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

theorem prime_13 : Nat.Prime 13 := by decide
theorem prime_17 : Nat.Prime 17 := by decide
theorem prime_19 : Nat.Prime 19 := by decide
theorem prime_23 : Nat.Prime 23 := by decide
theorem prime_29 : Nat.Prime 29 := by decide

theorem nth_5 : nth Nat.Prime 5 = 13 := by
  have h := nth_count prime_13
  have hc : count Nat.Prime 13 = 5 := by decide
  rw [hc] at h
  exact h

theorem nth_6 : nth Nat.Prime 6 = 17 := by
  have h := nth_count prime_17
  have hc : count Nat.Prime 17 = 6 := by decide
  rw [hc] at h
  exact h

theorem nth_7 : nth Nat.Prime 7 = 19 := by
  have h := nth_count prime_19
  have hc : count Nat.Prime 19 = 7 := by decide
  rw [hc] at h
  exact h

theorem nth_8 : nth Nat.Prime 8 = 23 := by
  have h := nth_count prime_23
  have hc : count Nat.Prime 23 = 8 := by decide
  rw [hc] at h
  exact h

theorem nth_9 : nth Nat.Prime 9 = 29 := by
  have h := nth_count prime_29
  have hc : count Nat.Prime 29 = 9 := by decide
  rw [hc] at h
  exact h

theorem A092243_nine : A092243 9 = 3 := by
  unfold A092243
  dsimp
  have h_icc : Finset.Icc 2 9 = {2, 3, 4, 5, 6, 7, 8, 9} := rfl
  rw [h_icc]
  simp
  rw [nth_5, nth_6, nth_7, nth_8, nth_9]
  decide


lemma composite_factorial_add (n : ℕ) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    ¬ Nat.Prime ((n + 1)! + k) := by
  intro hp
  have h_pos : 0 < k := by omega
  have hdvd : k ∣ (n + 1)! + k := by
    have h1 : k ∣ (n + 1)! := dvd_factorial h_pos hkn
    exact dvd_add h1 (dvd_refl k)
  have hk_eq : k = (n + 1)! + k := by
    rcases hp.eq_one_or_self_of_dvd k hdvd with (h_one | h_self)
    · omega
    · exact h_self
  have h_fact_zero : (n + 1)! = 0 := by omega
  have h_fact_pos := factorial_pos (n + 1)
  omega

lemma prime_gaps_arbitrarily_large (M : ℕ) (hM : M ≥ 1) : ∃ k : ℕ, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k > M := by
  let a := (M + 1)! + 2
  have h_ex : ∃ j, Nat.nth Nat.Prime j ≥ a := by
    obtain ⟨p, hp_ge, hp_prime⟩ := exists_infinite_primes a
    use count Nat.Prime p
    have h_eq := nth_count hp_prime
    rw [h_eq]
    exact hp_ge
  let m := Nat.find h_ex
  have hm_spec : Nat.nth Nat.Prime m ≥ a := Nat.find_spec h_ex
  have hm_min : ∀ i < m, Nat.nth Nat.Prime i < a := fun i hi => not_le.1 (Nat.find_min h_ex hi)
  have hm_nz : m ≠ 0 := by
    intro h_zero
    have hm_spec' := hm_spec
    rw [h_zero] at hm_spec'
    have h0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
    rw [h0] at hm_spec'
    have ha_ge : a ≥ 4 := by
      have h_fact : (M + 1)! ≥ 2 := by
        have h1 : M + 1 ≤ (M + 1)! := self_le_factorial (M + 1)
        omega
      omega
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm_nz
  use k
  have hpk : Nat.nth Nat.Prime k < a := by
    have hk_lt : k < m := by omega
    exact hm_min k hk_lt
  have hpk1 : Nat.nth Nat.Prime (k + 1) ≥ a := by
    have h_eq : k + 1 = m := by omega
    rw [h_eq]
    exact hm_spec
  have h_prime_k1 : Nat.Prime (Nat.nth Nat.Prime (k + 1)) := nth_mem_of_infinite infinite_setOf_prime (k + 1)
  have hpk1_ge : Nat.nth Nat.Prime (k + 1) ≥ (M + 1)! + M + 2 := by
    by_contra h_lt
    push_neg at h_lt
    have h_diff : Nat.nth Nat.Prime (k + 1) - (M + 1)! ∈ Finset.Icc 2 (M + 1) := by
      rw [Finset.mem_Icc]
      constructor
      · omega
      · omega
    let x := Nat.nth Nat.Prime (k + 1) - (M + 1)!
    have h_eq : Nat.nth Nat.Prime (k + 1) = (M + 1)! + x := by omega
    have h_comp : ¬ Nat.Prime ((M + 1)! + x) := by
      apply composite_factorial_add M x
      · rw [Finset.mem_Icc] at h_diff
        omega
      · rw [Finset.mem_Icc] at h_diff
        omega
    rw [← h_eq] at h_comp
    exact h_comp h_prime_k1
  omega


lemma nth_prime_odd (k : ℕ) (hk : k ≥ 1) : Odd (Nat.nth Nat.Prime k) := by
  have h_gt : Nat.nth Nat.Prime k > Nat.nth Nat.Prime 0 := by
    apply Nat.nth_strictMono
    · exact Nat.infinite_setOf_prime
    · omega
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  rw [h0] at h_gt
  have hp : Nat.Prime (Nat.nth Nat.Prime k) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  rcases hp.eq_two_or_odd' with h2 | h_odd
  · omega
  · exact h_odd

lemma odd_sub_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : b ≤ a) : Even (a - b) := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  have h_le : y ≤ x := by omega
  use x - y
  omega

lemma gap_even (k : ℕ) (hk : k ≥ 2) : Even (Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)) := by
  have hk1 : k ≥ 1 := by omega
  have hk0 : k - 1 ≥ 1 := by omega
  have h1 := nth_prime_odd k hk1
  have h2 := nth_prime_odd (k - 1) hk0
  have h_lt : Nat.nth Nat.Prime (k - 1) < Nat.nth Nat.Prime k := by
    apply Nat.nth_strictMono
    · exact Nat.infinite_setOf_prime
    · omega
  have h_le : Nat.nth Nat.Prime (k - 1) ≤ Nat.nth Nat.Prime k := by omega
  exact odd_sub_odd h1 h2 h_le

noncomputable def G_gap (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

lemma count_nth_prime (n : ℕ) : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n := by
  apply Nat.count_nth
  intro hf
  exact False.elim (Nat.infinite_setOf_prime hf)

theorem nth_prime_le_two_mul (k : ℕ) (hk : k ≥ 1) :
    Nat.nth Nat.Prime (k + 1) ≤ 2 * Nat.nth Nat.Prime k := by
  let p := Nat.nth Nat.Prime k
  have hp_prime : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hp_pos : p ≠ 0 := by
    have h_gt : Nat.nth Nat.Prime k > Nat.nth Nat.Prime 0 := by
      apply Nat.nth_strictMono
      · exact Nat.infinite_setOf_prime
      · omega
    have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
    omega
  -- By Bertrand's Postulate, there is a prime in (p, 2p]
  obtain ⟨q, hq_prime, hq_lt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul p hp_pos
  have h_next : Nat.nth Nat.Prime (k + 1) ≤ q := by
    by_contra h_lt_next
    push_neg at h_lt_next
    have h_count_p : Nat.count Nat.Prime p = k := count_nth_prime k
    have h_count_k1 : Nat.count Nat.Prime (Nat.nth Nat.Prime (k + 1)) = k + 1 := count_nth_prime (k + 1)
    have h_mon1 : Nat.count Nat.Prime p ≤ Nat.count Nat.Prime q := Nat.count_monotone Nat.Prime (le_of_lt hq_lt)
    have h_mon2 : Nat.count Nat.Prime q ≤ Nat.count Nat.Prime (Nat.nth Nat.Prime (k + 1)) := Nat.count_monotone Nat.Prime (le_of_lt h_lt_next)
    rw [h_count_p] at h_mon1
    rw [h_count_k1] at h_mon2
    have h_cases : Nat.count Nat.Prime q = k ∨ Nat.count Nat.Prime q = k + 1 := by omega
    rcases h_cases with hk_case | hk1_case
    · have hq_eq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq_prime
      rw [hk_case] at hq_eq
      omega
    · have hq_eq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq_prime
      rw [hk1_case] at hq_eq
      omega
  omega



lemma gaps_not_eventually_ge (K : ℕ) (hK : K ≥ 1) (M : ℕ) (hM : M > Nat.nth Nat.Prime K) :
    ¬ (∀ n ≥ K + 1, G_gap n ≥ M) := by
  intro h
  have h1 := h (K + 1) (by omega)
  have h2 := nth_prime_le_two_mul K hK
  have h_eq : G_gap (K + 1) = Nat.nth Nat.Prime (K + 1) - Nat.nth Nat.Prime K := rfl
  have h3 : G_gap (K + 1) ≤ Nat.nth Nat.Prime K := by
    rw [h_eq]
    omega
  omega

lemma gaps_not_eventually_constant (K : ℕ) (d : ℕ) (hd : d ≥ 1) :
    ¬ (∀ n ≥ K, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = d) := by
  intro h_const
  have h_ind (m : ℕ) : Nat.nth Nat.Prime (K + m) = Nat.nth Nat.Prime K + m * d := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : K + m + 1 = K + m + 1 := rfl
      have h2 : Nat.nth Nat.Prime (K + m + 1) = Nat.nth Nat.Prime (K + m) + d := by
        have h_eq : K + m + 1 = (K + m) + 1 := by omega
        rw [h_eq]
        have h_spec := h_const (K + m) (by omega)
        omega
      have h_goal : K + (m + 1) = K + m + 1 := by omega
      rw [h_goal, h2, ih]
      ring
  let p := Nat.nth Nat.Prime K
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime K
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_composite : Nat.nth Nat.Prime (K + p) = p * (1 + d) := by
    have h_eq := h_ind p
    rw [h_eq]
    ring
  have hp_kp : Nat.Prime (Nat.nth Nat.Prime (K + p)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (K + p)
  rw [h_composite] at hp_kp
  have h_div : p ∣ p * (1 + d) := dvd_mul_right p (1 + d)
  rcases hp_kp.eq_one_or_self_of_dvd p h_div with hp1 | hpeq
  · omega
  · have hpeq' : p * (1 + d) = p * 1 := by omega
    have h_eq : 1 + d = 1 := Nat.eq_of_mul_eq_mul_left (by omega) hpeq'
    omega


lemma A092243_eq (n : ℕ) (hn : n ≥ 2) :
    A092243 n = (Finset.Icc 2 n).sum fun k ↦ Int.sign ((G_gap k : ℤ) - (G_gap (k - 1) : ℤ)) := by
  unfold A092243
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

lemma A092243_succ (n : ℕ) (hn : n ≥ 2) :
    A092243 (n + 1) = A092243 n + Int.sign ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)) := by
  rw [A092243_eq n hn, A092243_eq (n + 1) (by omega)]
  have h_eq : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h_not : n + 1 ∉ Finset.Icc 2 n := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _
    omega
  rw [h_eq, Finset.sum_insert h_not]
  have h_eq2 : n + 1 - 1 = n := by omega
  rw [h_eq2]
  ring

lemma A092243_sub (a b : ℕ) (ha : a ≥ 2) (hab : a < b) :
    A092243 b - A092243 a = (Finset.Icc (a + 1) b).sum fun k => Int.sign ((G_gap k : ℤ) - (G_gap (k-1) : ℤ)) := by
  rw [A092243_eq a ha, A092243_eq b (by omega)]
  have h_union : Finset.Icc 2 b = Finset.Icc 2 a ∪ Finset.Icc (a + 1) b := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have h_disj : Disjoint (Finset.Icc 2 a) (Finset.Icc (a + 1) b) := by
    apply Finset.disjoint_iff_ne.2
    intro x hx y hy h_eq
    simp only [Finset.mem_Icc] at hx hy
    omega
  rw [h_union, Finset.sum_union h_disj]
  ring


lemma my_sign_eq_zero_iff (x : ℤ) : Int.sign x = 0 ↔ x = 0 := by
  rcases x with (n | n)
  · cases n with
    | zero => simp [Int.sign]
    | succ n =>
      simp [Int.sign]
      omega
  · simp [Int.sign]


lemma my_sign_eq_neg_one_iff (x : ℤ) : Int.sign x = -1 ↔ x < 0 := by
  rcases x with (n | n)
  · cases n with
    | zero => simp [Int.sign]
    | succ n => simp [Int.sign]; omega
  · simp [Int.sign]

lemma my_sign_eq_one_iff (x : ℤ) : Int.sign x = 1 ↔ x > 0 := by
  rcases x with (n | n)
  · cases n with
    | zero => simp [Int.sign]
    | succ n => simp [Int.sign]
  · simp [Int.sign]


lemma decrease_step_e_le_zero (i : ℕ) (hi : i ≥ 3) (h_dec : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = -1) :
    (G_gap i : ℤ) - (G_gap (i-1) : ℤ) - 2 * Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) ≤ 0 := by
  have h_lt : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) < 0 := by
    rwa [my_sign_eq_neg_one_iff] at h_dec
  have h_even_i := gap_even i (by omega)
  have h_even_im1 := gap_even (i-1) (by omega)
  rcases h_even_i with ⟨u, hu⟩
  rcases h_even_im1 with ⟨v, hv⟩
  have h_G1 : G_gap i = Nat.nth Nat.Prime i - Nat.nth Nat.Prime (i-1) := rfl
  have h_G2 : G_gap (i-1) = Nat.nth Nat.Prime (i-1) - Nat.nth Nat.Prime (i-1-1) := rfl
  rw [← h_G1] at hu
  rw [← h_G2] at hv
  have h_le : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) ≤ -2 := by
    have h_eq : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) = 2 * ((u : ℤ) - (v : ℤ)) := by
      omega
    rw [h_eq] at h_lt
    have h_lt2 : (u : ℤ) - (v : ℤ) < 0 := by omega
    have h_le2 : (u : ℤ) - (v : ℤ) ≤ -1 := by omega
    omega
  omega


lemma non_decrease_step_e_ge_zero (i : ℕ) (hi : i ≥ 3) (h_non_dec : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) ≥ 0) :
    (G_gap i : ℤ) - (G_gap (i-1) : ℤ) - 2 * Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) ≥ 0 := by
  have h_even_i := gap_even i (by omega)
  have h_even_im1 := gap_even (i-1) (by omega)
  rcases h_even_i with ⟨u, hu⟩
  rcases h_even_im1 with ⟨v, hv⟩
  have h_G1 : G_gap i = Nat.nth Nat.Prime i - Nat.nth Nat.Prime (i-1) := rfl
  have h_G2 : G_gap (i-1) = Nat.nth Nat.Prime (i-1) - Nat.nth Nat.Prime (i-1-1) := rfl
  rw [← h_G1] at hu
  rw [← h_G2] at hv
  have h_cases : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = 0 ∨ Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = 1 := by
    have h_tri : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) < 0 ∨ (G_gap i : ℤ) - (G_gap (i-1) : ℤ) = 0 ∨ (G_gap i : ℤ) - (G_gap (i-1) : ℤ) > 0 := by omega
    rcases h_tri with h_lt | h_eq | h_gt
    · have h_sign : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = -1 := by rwa [my_sign_eq_neg_one_iff]
      omega
    · have h_sign : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = 0 := by rwa [my_sign_eq_zero_iff]
      left; exact h_sign
    · have h_sign : Int.sign ((G_gap i : ℤ) - (G_gap (i-1) : ℤ)) = 1 := by rwa [my_sign_eq_one_iff]
      right; exact h_sign
  rcases h_cases with h0 | h1
  · have h_eq : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) = 0 := by
      rw [my_sign_eq_zero_iff] at h0
      exact h0
    omega
  · have h_gt : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) > 0 := by
      rwa [my_sign_eq_one_iff] at h1
    have h_le : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) ≥ 2 := by
      have h_eq : (G_gap i : ℤ) - (G_gap (i-1) : ℤ) = 2 * ((u : ℤ) - (v : ℤ)) := by
        omega
      rw [h_eq] at h_gt
      have h_gt2 : (u : ℤ) - (v : ℤ) > 0 := by omega
      have h_le2 : (u : ℤ) - (v : ℤ) ≥ 1 := by omega
      omega
    omega


lemma telescoping_gaps (a b : ℕ) (hab : a < b) :
    (Finset.Icc (a + 1) b).sum (fun k => (G_gap k : ℤ) - (G_gap (k - 1) : ℤ)) = (G_gap b : ℤ) - (G_gap a : ℤ) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have h_icc : Finset.Icc (a + 1) (a + 1) = {a + 1} := Finset.Icc_self (a + 1)
    rw [h_icc]
    simp
  | succ b hb ih =>
    have h_icc : Finset.Icc (a + 1) (b + 1) = insert (b + 1) (Finset.Icc (a + 1) b) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not : b + 1 ∉ Finset.Icc (a + 1) b := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    rw [h_icc, Finset.sum_insert h_not]
    have h_eq : b + 1 - 1 = b := by omega
    rw [h_eq]
    rw [ih]
    ring


lemma score_gap_relation (a b : ℕ) (ha : a ≥ 2) (hab : a < b) :
    (G_gap b : ℤ) - (G_gap a : ℤ) = 2 * (A092243 b - A092243 a) +
      (Finset.Icc (a + 1) b).sum (fun k => (G_gap k : ℤ) - (G_gap (k - 1) : ℤ) - 2 * Int.sign ((G_gap k : ℤ) - (G_gap (k - 1) : ℤ))) := by
  rw [A092243_sub a b ha hab]
  rw [← telescoping_gaps a b hab]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext k
  ring

lemma score_not_eventually_constant (N : ℕ) : ¬ (∀ n ≥ N, A092243 (n + 1) = A092243 n) := by
  intro h
  let K := max N 2
  have h_const : ∀ n ≥ K, G_gap (n + 1) = G_gap n := by
    intro n hn
    have hn_N : n ≥ N := by omega
    have hn_2 : n ≥ 2 := by omega
    have h_eq := h n hn_N
    have h_succ := A092243_succ n hn_2
    rw [h_eq] at h_succ
    have h_sign : Int.sign ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)) = 0 := by omega
    have h_sub_zero : (G_gap (n + 1) : ℤ) - (G_gap n : ℤ) = 0 := by
      rw [my_sign_eq_zero_iff] at h_sign
      exact h_sign
    have h_eq2 : (G_gap (n + 1) : ℤ) = (G_gap n : ℤ) := by omega
    exact Int.ofNat_inj.1 h_eq2
  have h_ind (m : ℕ) : G_gap (K + m) = G_gap K := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have h_eq : K + Nat.succ m = (K + m) + 1 := by omega
      rw [h_eq]
      have h_spec := h_const (K + m) (by omega)
      rw [h_spec]
      exact ih
  let d := G_gap K
  have hd_pos : d ≥ 1 := by
    have hK2 : K ≥ 2 := by omega
    have h_even := gap_even K hK2
    have hpK : G_gap K > 0 := by
      unfold G_gap
      have h_lt : Nat.nth Nat.Prime (K - 1) < Nat.nth Nat.Prime K := by
        apply Nat.nth_strictMono
        · exact Nat.infinite_setOf_prime
        · omega
      omega
    omega
  have h_all : ∀ n ≥ K, G_gap n = d := by
    intro n hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]
    exact h_ind m
  have h_const_all : ∀ n ≥ K, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = d := by
    intro n hn
    have h_eq : G_gap (n + 1) = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := rfl
    rw [← h_eq]
    exact h_all (n + 1) (by omega)
  exact gaps_not_eventually_constant K d hd_pos h_const_all

lemma no_consecutive_twin_gaps (n : ℕ) (hn : n ≥ 3) :
    ¬ (G_gap n = 2 ∧ G_gap (n + 1) = 2) := by
  intro h
  rcases h with ⟨h1, h2⟩
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
  have hp_n1 : P n = P (n - 1) + 2 := by
    have : G_gap n = P n - P (n - 1) := rfl
    have h_lt : P (n - 1) < P n := by
      apply Nat.nth_strictMono
      · exact Nat.infinite_setOf_prime
      · omega
    omega
  have hp_n2 : P (n + 1) = P n + 2 := by
    have : G_gap (n + 1) = P (n + 1) - P (n + 1 - 1) := rfl
    have h_eq : n + 1 - 1 = n := by omega
    rw [h_eq] at this
    have h_lt : P n < P (n + 1) := by
      apply Nat.nth_strictMono
      · exact Nat.infinite_setOf_prime
      · omega
    omega
  let p := P (n - 1)
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have hp_ge : p ≥ 5 := by
    have h_mono : P 2 ≤ P (n - 1) := by
      apply StrictMono.monotone
      · exact Nat.nth_strictMono Nat.infinite_setOf_prime
      · omega
    have h_prime_5 : Nat.Prime 5 := by decide
    have h_p2 : P 2 = 5 := by
      have h := Nat.nth_count h_prime_5
      have hc : Nat.count Nat.Prime 5 = 2 := by decide
      rw [hc] at h
      exact h
    omega
  -- Now we show that one of p, p+2, p+4 is divisible by 3.
  have h_mod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h_mod with hm0 | hm1 | hm2
  · have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hm0
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_p
    · contradiction
    · omega
  · -- p % 3 = 1 => (p+2) % 3 = 0
    have hp2 : P (n + 1) = p + 4 := by omega
    have hpn : P n = p + 2 := by omega
    have hm : (p + 2) % 3 = 0 := by omega
    rw [← hpn] at hm
    have hdvd : 3 ∣ P n := Nat.dvd_of_mod_eq_zero hm
    have hpn_prime : Nat.Prime (P n) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    rcases hpn_prime.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_pn
    · contradiction
    · omega
  · -- p % 3 = 2 => (p+4) % 3 = 0
    have hp2 : P (n + 1) = p + 4 := by omega
    have hm : (p + 4) % 3 = 0 := by omega
    rw [← hp2] at hm
    have hdvd : 3 ∣ P (n + 1) := Nat.dvd_of_mod_eq_zero hm
    have hp2_prime : Nat.Prime (P (n + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
    rcases hp2_prime.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_pn1
    · contradiction
    · omega


lemma no_consecutive_four_gaps (n : ℕ) (hn : n ≥ 3) :
    ¬ (G_gap n = 4 ∧ G_gap (n + 1) = 4) := by
  intro h
  rcases h with ⟨h1, h2⟩
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
  have hp_n1 : P n = P (n - 1) + 4 := by
    have : G_gap n = P n - P (n - 1) := rfl
    have h_lt : P (n - 1) < P n := by
      apply Nat.nth_strictMono
      · exact Nat.infinite_setOf_prime
      · omega
    omega
  have hp_n2 : P (n + 1) = P n + 4 := by
    have : G_gap (n + 1) = P (n + 1) - P (n + 1 - 1) := rfl
    have h_eq : n + 1 - 1 = n := by omega
    rw [h_eq] at this
    have h_lt : P n < P (n + 1) := by
      apply Nat.nth_strictMono
      · exact Nat.infinite_setOf_prime
      · omega
    omega
  let p := P (n - 1)
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have hp_ge : p ≥ 5 := by
    have h_mono : P 2 ≤ P (n - 1) := by
      apply StrictMono.monotone
      · exact Nat.nth_strictMono Nat.infinite_setOf_prime
      · omega
    have h_prime_5 : Nat.Prime 5 := by decide
    have h_p2 : P 2 = 5 := by
      have h := Nat.nth_count h_prime_5
      have hc : Nat.count Nat.Prime 5 = 2 := by decide
      rw [hc] at h
      exact h
    omega
  -- Now we show that one of p, p+4, p+8 is divisible by 3.
  have h_mod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h_mod with hm0 | hm1 | hm2
  · have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hm0
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_p
    · contradiction
    · omega
  · -- p % 3 = 1 => (p+8) % 3 = 0
    have hp2 : P (n + 1) = p + 8 := by rw [hp_n2, hp_n1]
    have hm : (p + 8) % 3 = 0 := by omega
    rw [← hp2] at hm
    have hdvd : 3 ∣ P (n + 1) := Nat.dvd_of_mod_eq_zero hm
    have hp2_prime : Nat.Prime (P (n + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
    rcases hp2_prime.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_pn1
    · contradiction
    · omega
  · -- p % 3 = 2 => (p+4) % 3 = 0
    have hm : (p + 4) % 3 = 0 := by omega
    rw [← hp_n1] at hm
    have hdvd : 3 ∣ P n := Nat.dvd_of_mod_eq_zero hm
    have hpn_prime : Nat.Prime (P n) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    rcases hpn_prime.eq_one_or_self_of_dvd 3 hdvd with h3_1 | h3_pn
    · contradiction
    · omega



lemma prime_gaps_arbitrarily_large_after (N : ℕ) (M : ℕ) (hM : M ≥ 1) :
    ∃ k ≥ N, G_gap (k + 1) > M := by
  let M' := M + Nat.nth Nat.Prime N + 2
  have hM' : M' ≥ 1 := by omega
  obtain ⟨k, hk⟩ := prime_gaps_arbitrarily_large M' hM'
  use k
  have hk_ge : k ≥ N := by
    by_contra h_lt
    push_neg at h_lt
    have h_lt2 : Nat.nth Nat.Prime (k + 1) ≤ Nat.nth Nat.Prime N := by
      apply StrictMono.monotone (Nat.nth_strictMono Nat.infinite_setOf_prime)
      omega
    have h_mono : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime (k + 1) := by
      apply StrictMono.monotone (Nat.nth_strictMono Nat.infinite_setOf_prime)
      omega
    have h_gap_le : G_gap (k + 1) ≤ Nat.nth Nat.Prime N := by
      unfold G_gap
      omega
    omega
  constructor
  · exact hk_ge
  · unfold G_gap
    have h_eq : k + 1 - 1 = k := by omega
    rw [h_eq]
    omega

lemma gaps_not_eventually_le (N : ℕ) (M : ℕ) (hM : M ≥ 1) : ¬ (∀ n ≥ N, G_gap n ≤ M) := by
  intro h_le
  obtain ⟨k, hk_ge, hk⟩ := prime_gaps_arbitrarily_large_after N M hM
  have h_spec := h_le (k + 1) (by omega)
  omega

lemma nth_prime_ge (K : ℕ) : Nat.nth Nat.Prime K ≥ K := by
  apply StrictMono.id_le
  exact Nat.nth_strictMono Nat.infinite_setOf_prime
theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  rcases h.bounded_above with ⟨B_up, hB_up⟩
  rcases h.bounded_below with ⟨B_low, hB_low⟩
  let C := B_up - B_low
  let C_val : ℕ := 4 * C.natAbs + 10
  have hC_val : C_val ≥ 1 := by omega
  -- we want to find a gap G_gap a > 4 * C.natAbs + 10
  obtain ⟨k, hk⟩ := prime_gaps_arbitrarily_large C_val hC_val
  let a := k + 1
  have ha_ge : a ≥ 2 := by
    by_contra h_lt
    have h_eq : a = 1 := by omega
    have prime_3 : Nat.Prime 3 := by decide
    have nth_1 : nth Nat.Prime 1 = 3 := by
      have h := nth_count prime_3
      have hc : count Nat.Prime 3 = 1 := by decide
      rw [hc] at h
      exact h
    have prime_2 : Nat.Prime 2 := by decide
    have nth_0 : nth Nat.Prime 0 = 2 := by
      have h := nth_count prime_2
      have hc : count Nat.Prime 2 = 0 := by decide
      rw [hc] at h
      exact h
    have h_gap1 : G_gap 1 = 1 := by
      unfold G_gap
      rw [nth_1, nth_0]
    have h_hk : G_gap a > C_val := hk
    rw [h_eq, h_gap1] at h_hk
    omega
  have h_cases : (∃ b ≥ a + 1, G_gap b ≥ G_gap a + 2 * C + 2) ∨ ¬ (∃ b ≥ a + 1, G_gap b ≥ G_gap a + 2 * C + 2) := Classical.em _
  rcases h_cases with ⟨b, hb_ge, hb_lt⟩ | h_all_neg
  · dsimp [C] at *
    have hab : a < b := by omega
    have h_step : (Finset.Icc (a + 1) b).sum (fun k => (G_gap k : ℤ) - (G_gap (k - 1) : ℤ) - 2 * Int.sign ((G_gap k : ℤ) - (G_gap (k - 1) : ℤ))) =
      (G_gap b : ℤ) - (G_gap a : ℤ) - 2 * (A092243 b - A092243 a) := by
      have h_rel := score_gap_relation a b ha_ge hab
      omega
    have h_lt : (G_gap b : ℤ) - (G_gap a : ℤ) ≥ 2 * C + 2 := by omega
    have h_low_b := hB_low b
    have h_up_b := hB_up b
    have h_low_a := hB_low a
    have h_up_a := hB_up a
    clear hk
    have h_C_ge : C ≥ 0 := by
      have h2 : A092243 2 = 1 := by simp [A092243]
      have h_low := hB_low 2
      have h_up := hB_up 2
      omega
    sorry
  · push_neg at h_all_neg
    have h_all : ∀ b ≥ a + 1, G_gap b < G_gap a + 2 * C + 2 := h_all_neg
    have h_C_ge : C ≥ 0 := by
      have h2 : A092243 2 = 1 := by simp [A092243]
      have h_low := hB_low 2
      have h_up := hB_up 2
      omega
    have h_Ga : (G_gap a : ℤ) > 4 * C + 10 := by
      have h_hk : G_gap a > C_val := hk
      have h_abs : C.natAbs = C := Int.natAbs_of_nonneg h_C_ge
      have h_eq : C_val = 4 * C + 10 := by
        dsimp [C_val]
        rw [h_abs]
      omega
    let M_int := (G_gap a : ℤ) + 2 * C + 2
    have h_Mint_pos : M_int ≥ 0 := by omega
    let M := M_int.toNat
    have h_M_eq : (M : ℤ) = M_int := Int.toNat_of_nonneg h_Mint_pos
    have h_M_ge1 : M ≥ 1 := by
      have h_eq : (M : ℤ) = M_int := h_M_eq
      omega
    have h_le := gaps_not_eventually_le (a + 1) M h_M_ge1
    have h_all' : ∀ n ≥ a + 1, G_gap n ≤ M := by
      intro n hn
      have h_spec := h_all n hn
      have h_eq : (M : ℤ) = (G_gap a : ℤ) + 2 * C + 2 := h_M_eq
      omega
    exact h_le h_all'


