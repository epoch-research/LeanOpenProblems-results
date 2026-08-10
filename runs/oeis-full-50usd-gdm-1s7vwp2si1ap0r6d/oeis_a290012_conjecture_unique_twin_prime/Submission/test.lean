import FormalConjectures.Util.ProblemImports

open Nat Set Finset


noncomputable def A290012 (n : ℕ) : ℕ :=
  let S_n : ℕ := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  -- sInf finds the smallest element of the set of primes p that satisfy the condition.
  sInf { p : ℕ | p.Prime ∧ S_n ≤ p ^ 2 }

lemma prime_nth_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

lemma prime_nth_ge_add_two (k : ℕ) (hk : 1 ≤ k) :
  Nat.nth Nat.Prime (k + 1) ≥ Nat.nth Nat.Prime k + 2 := by
  have h_mono : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
    prime_nth_strictMono (Nat.lt_succ_self k)
  have hk_prime : (Nat.nth Nat.Prime k).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hk1_prime : (Nat.nth Nat.Prime (k + 1)).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k + 1)
  have hk_ge3 : 3 ≤ Nat.nth Nat.Prime k := by
    have h_le : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime k :=
      prime_nth_strictMono.monotone hk
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    omega
  by_contra! h_lt
  have h_eq : Nat.nth Nat.Prime (k + 1) = Nat.nth Nat.Prime k + 1 := by omega
  have hk1_even : Even (Nat.nth Nat.Prime (k + 1)) := by
    rw [h_eq]
    have hk_odd : Odd (Nat.nth Nat.Prime k) := hk_prime.odd_of_ne_two (by omega)
    exact Odd.add_odd hk_odd (by decide)
  have hk1_eq2 : Nat.nth Nat.Prime (k + 1) = 2 := by
    rwa [hk1_prime.even_iff] at hk1_even
  omega

lemma p_sq_add_8_le_next (k : ℕ) (hk : 3 ≤ k) :
  (Nat.nth Nat.Prime k) ^ 2 + 8 ≤ (Nat.nth Nat.Prime (k + 1)) ^ 2 := by
  have hk_ge1 : 1 ≤ k := by omega
  have hp_gt : Nat.nth Nat.Prime (k + 1) ≥ Nat.nth Nat.Prime k + 2 :=
    prime_nth_ge_add_two k hk_ge1
  have hk_ge7 : 7 ≤ Nat.nth Nat.Prime k := by
    have h_le : Nat.nth Nat.Prime 3 ≤ Nat.nth Nat.Prime k :=
      prime_nth_strictMono.monotone hk
    have h1 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
    omega
  have h_mono : (Nat.nth Nat.Prime k + 2) ^ 2 ≤ (Nat.nth Nat.Prime (k + 1)) ^ 2 := by
    gcongr
  have : (Nat.nth Nat.Prime k + 2) ^ 2 = (Nat.nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k + 4 := by ring
  nlinarith

lemma S_le_p_sq_sub_four_sq (n : ℕ) (hn : 3 ≤ n) :
  16 * (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ ((Nat.nth Nat.Prime n) ^ 2 - 4) ^ 2 := by
  induction' n, hn using Nat.le_induction with k hk ih
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  · rw [Finset.sum_range_succ]
    have h1 : 16 * ((Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + nth Nat.Prime k ^ 2) =
      16 * (Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + 16 * nth Nat.Prime k ^ 2 := by ring
    rw [h1]
    have hk_ge7 : 7 ≤ Nat.nth Nat.Prime k := by
      have h_le : Nat.nth Nat.Prime 3 ≤ Nat.nth Nat.Prime k :=
        prime_nth_strictMono.monotone hk
      have h1 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
      omega
    have h_sub_four_ge : (Nat.nth Nat.Prime k) ^ 2 ≥ 4 := by nlinarith
    have h2 : 16 * (Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + 16 * nth Nat.Prime k ^ 2 ≤
      ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 16 * nth Nat.Prime k ^ 2 := by linarith [ih]
    refine h2.trans ?_
    have h_calc : ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 16 * nth Nat.Prime k ^ 2 = ((nth Nat.Prime k) ^ 2 + 4) ^ 2 := by
      have h_id : ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 16 * (nth Nat.Prime k) ^ 2 = ((nth Nat.Prime k) ^ 2 + 4) ^ 2 := by
        have h_cast : (((nth Nat.Prime k) ^ 2 - 4 : ℕ) : ℤ) = (nth Nat.Prime k : ℤ) ^ 2 - 4 := Nat.cast_sub h_sub_four_ge
        zify
        rw [h_cast]
        ring
      exact h_id
    rw [h_calc]
    have h_next : (nth Nat.Prime k) ^ 2 + 4 ≤ (nth Nat.Prime (k + 1)) ^ 2 - 4 := by
      have : (nth Nat.Prime k) ^ 2 + 8 ≤ (nth Nat.Prime (k + 1)) ^ 2 := p_sq_add_8_le_next k hk
      have hk1_ge1 : 1 ≤ k + 1 := by omega
      have hk1_ge3 : 3 ≤ Nat.nth Nat.Prime (k + 1) := by
        have h_le : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (k + 1) :=
          prime_nth_strictMono.monotone hk1_ge1
        have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
        omega
      have : (Nat.nth Nat.Prime (k + 1)) ^ 2 ≥ 4 := by nlinarith
      omega
    have h_mono : ((nth Nat.Prime k) ^ 2 + 4) ^ 2 ≤ ((nth Nat.Prime (k + 1)) ^ 2 - 4) ^ 2 := by
      gcongr
    exact h_mono

lemma four_sqrt_S_add_four_le_p_sq (n : ℕ) (hn : 3 ≤ n) :
  4 * Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 4 ≤ (Nat.nth Nat.Prime n) ^ 2 := by
  set S_n := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  have h_le := S_le_p_sq_sub_four_sq n hn
  have h_sqrt : Nat.sqrt (16 * S_n) ≤ Nat.sqrt (((Nat.nth Nat.Prime n) ^ 2 - 4) ^ 2) :=
    Nat.sqrt_le_sqrt h_le
  have h_id : Nat.sqrt (((Nat.nth Nat.Prime n) ^ 2 - 4) ^ 2) = (Nat.nth Nat.Prime n) ^ 2 - 4 :=
    Nat.sqrt_eq' ((Nat.nth Nat.Prime n) ^ 2 - 4)
  rw [h_id] at h_sqrt
  have h_le' : 4 * Nat.sqrt S_n ≤ Nat.sqrt (16 * S_n) := by
    rw [Nat.le_sqrt']
    have : (4 * Nat.sqrt S_n) ^ 2 = 16 * (Nat.sqrt S_n) ^ 2 := by ring
    rw [this]
    gcongr
    exact Nat.sqrt_le' S_n
  have hp_ge7 : 7 ≤ Nat.nth Nat.Prime n := by
    have h_le : Nat.nth Nat.Prime 3 ≤ Nat.nth Nat.Prime n :=
      prime_nth_strictMono.monotone hn
    have h1 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
    omega
  have h_p_sq_ge4 : 4 ≤ (Nat.nth Nat.Prime n) ^ 2 := by nlinarith
  omega










lemma A_le_two_sqrt (n : ℕ) (hn : 2 ≤ n) :
  A290012 n ≤ 2 * Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) := by
  unfold A290012
  dsimp only
  generalize hS : (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = S_n
  have hS_ge : 13 ≤ S_n := by
    have hn_ge : (Finset.range 2).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ S_n := by
      rw [← hS]
      apply Finset.sum_le_sum_of_subset
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hS2 : (Finset.range 2).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 13 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
      simp
    omega
  have h_sqrt_pos : Nat.sqrt S_n ≠ 0 := by
    have : 9 ≤ S_n := by omega
    have h_sqrt : 3 ≤ Nat.sqrt S_n := by
      have h9 : Nat.sqrt 9 ≤ Nat.sqrt S_n := Nat.sqrt_le_sqrt this
      have h_nine : Nat.sqrt 9 = 3 := by norm_num
      omega
    omega
  obtain ⟨p, hp_prime, h_gt, h_le⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt S_n) h_sqrt_pos
  have h_mem : p ∈ { q : ℕ | q.Prime ∧ S_n ≤ q ^ 2 } := by
    simp only [Set.mem_setOf_eq]
    refine ⟨hp_prime, ?_⟩
    have : Nat.sqrt S_n + 1 ≤ p := h_gt
    have h_sq : (Nat.sqrt S_n + 1) ^ 2 ≤ p ^ 2 := by gcongr
    have h_lt : S_n < (Nat.sqrt S_n + 1) ^ 2 := by
      have h_lt_mul : S_n < (Nat.sqrt S_n + 1) * (Nat.sqrt S_n + 1) := Nat.lt_succ_sqrt S_n
      rwa [← sq] at h_lt_mul
    omega
  have h_le_sInf : sInf { q : ℕ | q.Prime ∧ S_n ≤ q ^ 2 } ≤ p := Nat.sInf_le h_mem
  exact h_le_sInf.trans h_le

lemma S_le_p_sq_sub_four_sq_sixty_four (n : ℕ) (hn : 4 ≤ n) :
  64 * (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ ((Nat.nth Nat.Prime n) ^ 2 - 4) ^ 2 := by
  induction' n, hn using Nat.le_induction with k hk ih
  · -- Base case n = 4
    have hS4 : (Finset.range 4).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 87 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
      decide
    have hp4 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
    rw [hS4, hp4]
    decide
  · -- Induction step
    rw [Finset.sum_range_succ]
    have h1 : 64 * ((Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + nth Nat.Prime k ^ 2) =
      64 * (Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + 64 * nth Nat.Prime k ^ 2 := by ring
    rw [h1]
    have hk_ge11 : 11 ≤ Nat.nth Nat.Prime k := by
      have h_le : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime k :=
        prime_nth_strictMono.monotone hk
      have h1 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
      omega
    have h_sub_four_ge : (Nat.nth Nat.Prime k) ^ 2 ≥ 4 := by nlinarith
    have h2 : 64 * (Finset.range k).sum (fun k_1 => nth Nat.Prime k_1 ^ 2) + 64 * nth Nat.Prime k ^ 2 ≤
      ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 64 * nth Nat.Prime k ^ 2 := by linarith [ih]
    refine h2.trans ?_
    have h_calc : ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 64 * nth Nat.Prime k ^ 2 = ((nth Nat.Prime k) ^ 2 + 28) ^ 2 - 768 := by
      have h_id : ((nth Nat.Prime k) ^ 2 - 4) ^ 2 + 64 * (nth Nat.Prime k) ^ 2 + 768 = ((nth Nat.Prime k) ^ 2 + 28) ^ 2 := by
        have h_cast : (((nth Nat.Prime k) ^ 2 - 4 : ℕ) : ℤ) = (nth Nat.Prime k : ℤ) ^ 2 - 4 := Nat.cast_sub h_sub_four_ge
        zify
        rw [h_cast]
        ring
      omega
    rw [h_calc]
    have h_next : ((nth Nat.Prime k) ^ 2 + 28) ^ 2 - 768 ≤ ((nth Nat.Prime (k + 1)) ^ 2 - 4) ^ 2 := by
      have h_prime_step : Nat.nth Nat.Prime (k + 1) ≥ Nat.nth Nat.Prime k + 2 := by
        apply prime_nth_ge_add_two
        omega
      have h_next_sq_ge : (Nat.nth Nat.Prime (k + 1)) ^ 2 - 4 ≥ (Nat.nth Nat.Prime k + 2) ^ 2 - 4 := by
        have : (Nat.nth Nat.Prime (k + 1)) ^ 2 ≥ (Nat.nth Nat.Prime k + 2) ^ 2 := by gcongr
        omega
      have h_id2 : (Nat.nth Nat.Prime k + 2) ^ 2 - 4 = (Nat.nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k := by
        have h_ring : (Nat.nth Nat.Prime k + 2) ^ 2 = (Nat.nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k + 4 := by ring
        omega
      rw [h_id2] at h_next_sq_ge
      have h_mono : ((nth Nat.Prime k) ^ 2 + 28) ^ 2 ≤ ((nth Nat.Prime (k + 1)) ^ 2 - 4) ^ 2 + 768 := by
        have h_goal : ((nth Nat.Prime k) ^ 2 + 28) ^ 2 ≤ ((nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k) ^ 2 + 768 := by
          have : 4 * Nat.nth Nat.Prime k ≥ 44 := by omega
          have h_base : (nth Nat.Prime k) ^ 2 + 28 ≤ (nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k := by omega
          have h_sq : ((nth Nat.Prime k) ^ 2 + 28) ^ 2 ≤ ((nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k) ^ 2 := by gcongr
          omega
        have h_trans : ((nth Nat.Prime k) ^ 2 + 4 * Nat.nth Nat.Prime k) ^ 2 ≤ ((nth Nat.Prime (k + 1)) ^ 2 - 4) ^ 2 := by gcongr
        omega
      omega
    exact h_next







lemma four_A_add_four_le_p_sq (n : ℕ) (hn : 4 ≤ n) :
  4 * A290012 n + 4 ≤ (Nat.nth Nat.Prime n) ^ 2 := by
  have h1 := A_le_two_sqrt n (by omega)
  have h2 := S_le_p_sq_sub_four_sq_sixty_four n hn
  have h_sqrt := Nat.sqrt_le_sqrt h2
  have h_id : Nat.sqrt (((Nat.nth Nat.Prime n) ^ 2 - 4) ^ 2) = (Nat.nth Nat.Prime n) ^ 2 - 4 :=
    Nat.sqrt_eq' ((Nat.nth Nat.Prime n) ^ 2 - 4)
  rw [h_id] at h_sqrt
  have h_le' : 8 * Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) ≤ Nat.sqrt (64 * (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) := by
    rw [Nat.le_sqrt']
    have : (8 * Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2))) ^ 2 = 64 * (Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2))) ^ 2 := by ring
    rw [this]
    gcongr
    exact Nat.sqrt_le' _
  have h_trans : 8 * Nat.sqrt ((Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) ≤ (Nat.nth Nat.Prime n) ^ 2 - 4 := h_le'.trans h_sqrt
  have hp_ge11 : 11 ≤ Nat.nth Nat.Prime n := by
    have h_le : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime n :=
      prime_nth_strictMono.monotone hn
    have h_four : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
    omega
  have hp_sq_ge4 : 4 ≤ (Nat.nth Nat.Prime n) ^ 2 := by nlinarith
  omega


theorem A_four : A290012 4 = 11 := by
  unfold A290012; dsimp only
  have hS : (Finset.range 4).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 87 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
    decide
  rw [hS]
  have h_mem : 11 ∈ { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 } := by
    refine ⟨Nat.prime_eleven, by norm_num⟩
  have h_le : sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 } ≤ 11 := Nat.sInf_le h_mem
  have h_nonempty : { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 }.Nonempty := ⟨11, h_mem⟩
  have h_in : sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 } ∈ { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 } := Nat.sInf_mem h_nonempty
  have h_ge : 11 ≤ sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 } := by
    by_contra! h_lt
    have h_p : (sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 }).Prime := h_in.1
    have h_sq : 87 ≤ (sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 }) ^ 2 := h_in.2
    interval_cases sInf { p : ℕ | p.Prime ∧ 87 ≤ p ^ 2 }
    · exact Nat.not_prime_zero h_p
    · exact Nat.not_prime_one h_p
    · revert h_sq; decide
    · revert h_sq; decide
    · revert h_p; decide
    · revert h_sq; decide
    · revert h_p; decide
    · revert h_sq; decide
    · revert h_p; decide
    · revert h_p; decide
    · revert h_p; decide
  exact le_antisymm h_le h_ge

lemma A_succ_ne_A_add_two_helper (n : ℕ) (hn : 3 ≤ n) (U : ℕ) (h_prime : Nat.Prime U)
  (hS : (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ U ^ 2)
  (h_lt : (U + 2) ^ 2 < (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) :
  A290012 (n + 1) ≠ A290012 n + 2 := by
  have h_mem : U ∈ { q : ℕ | q.Prime ∧ (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ q ^ 2 } := by
    simp [h_prime, hS]
  have h_le : A290012 n ≤ U := by
    unfold A290012
    exact Nat.sInf_le h_mem
  have h_sq : (A290012 n + 2) ^ 2 ≤ (U + 2) ^ 2 := by gcongr
  have h_lt' : (A290012 n + 2) ^ 2 < (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) := h_sq.trans_lt h_lt
  have h_An1_mem : A290012 (n + 1) ∈ { q : ℕ | q.Prime ∧ (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ q ^ 2 } := by
    unfold A290012
    have h_nonempty : { q : ℕ | q.Prime ∧ (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ q ^ 2 }.Nonempty := by
      have h_sum_pos : (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≥ 4 := by
        have h_le_sum : (Finset.range 1).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) := by
          apply Finset.sum_le_sum_of_subset
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        have h1 : (Finset.range 1).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 4 := by
          rw [Finset.sum_range_one]
          rw [Nat.nth_prime_zero_eq_two]
          rfl
        omega
      have h_pos : (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≠ 0 := by omega
      have h_sqrt : 2 ≤ Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) := by
        have h_sqrt_4 := Nat.sqrt_le_sqrt h_sum_pos
        have h_four : Nat.sqrt 4 = 2 := by norm_num
        omega
      have h_sqrt_pos : Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) ≠ 0 := by omega
      obtain ⟨p, hp_prime, h_gt, h_le'⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2))) h_sqrt_pos
      refine ⟨p, hp_prime, ?_⟩
      have : Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 1 ≤ p := h_gt
      have h_sq' : (Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 1) ^ 2 ≤ p ^ 2 := by gcongr
      have h_lt'' : (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) < (Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 1) ^ 2 := by
        have h_lt_mul : (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) < (Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 1) * (Nat.sqrt ((Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)) + 1) := Nat.lt_succ_sqrt _
        rwa [← sq] at h_lt_mul
      omega
    exact Nat.sInf_mem h_nonempty
  have h_An1_sq : (Finset.range (n + 1)).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) ≤ (A290012 (n + 1)) ^ 2 := h_An1_mem.2
  have h_strict : (A290012 n + 2) ^ 2 < (A290012 (n + 1)) ^ 2 := h_lt'.trans_le h_An1_sq
  have h_lt_final : A290012 n + 2 < A290012 (n + 1) := by
    zify at h_strict ⊢
    nlinarith
  omega





lemma test_n_3 : A290012 4 ≠ A290012 3 + 2 := by
  apply A_succ_ne_A_add_two_helper 3 (by omega) 7 Nat.prime_seven
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
    decide
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
    decide


lemma test_nth_five : Nat.nth Nat.Prime 5 = 13 :=
  Nat.nth_count (show Nat.Prime 13 by decide)


