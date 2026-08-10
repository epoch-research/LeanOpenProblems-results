import FormalConjectures.Util.ProblemImports





open Nat Finset

/--
A080101: Number of prime powers in all composite numbers between $n$-th prime and next prime.
Let $p_n$ be the $n$-th prime. $a(n)$ is the number of prime powers $k$ such that $p_n < k < p_{n+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    -- $p_n$ (the n-th prime in OEIS 1-indexing) corresponds to Nat.nth Nat.Prime (n - 1) in Mathlib's 0-indexing.
    let p_n := Nat.nth Nat.Prime (n - 1)
    -- $p_{n+1}$ is Nat.nth Nat.Prime n.
    let p_succ_n := Nat.nth Nat.Prime n

    -- We count the number of prime powers in the open interval (p_n, p_{n+1}).
    -- IsPrimePow is the correct predicate, globally available through Mathlib.
    (Ioo p_n p_succ_n).filter IsPrimePow |>.card
  else
    0

/--
A080101: The maximum value of terms in the sequence is conjectured to be 2.
This is a formalization of the OEIS conjecture: "The maximum value of terms in the sequence, through the (10^5)th term, is 2. - Harvey P. Dale, Aug 24 2014 This is conjectured to be the maximum, see also A366833. - Gus Wiseman, Nov 06 2024"
-/
theorem IsPrimePow_four : IsPrimePow 4 := by decide
theorem not_IsPrimePow_six : ¬ IsPrimePow 6 := by decide
theorem IsPrimePow_eight : IsPrimePow 8 := by decide

theorem IsPrimePow_nine : IsPrimePow 9 := by
  rw [isPrimePow_nat_iff]
  refine ⟨3, 2, prime_three, by decide, by rfl⟩

theorem not_IsPrimePow_ten : ¬ IsPrimePow 10 := by decide

theorem a_zero : a 0 = 0 := by
  unfold a
  split
  · contradiction
  · rfl

theorem a_one : a 1 = 0 := by
  unfold a
  split
  · have h_p0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
    have h_p1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_one_eq_three
    dsimp only
    rw [h_p0, h_p1]
    have h_empty : Ioo 2 3 = ∅ := by rfl
    rw [h_empty]
    rfl
  · contradiction

theorem a_two : a 2 = 1 := by
  unfold a
  split
  · have h_p1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_one_eq_three
    have h_p2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_two_eq_five
    dsimp only
    rw [h_p1, h_p2]
    have h_Ioo : Ioo 3 5 = {4} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {4} = {4} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨rfl, h⟩; rfl
      · rintro rfl
        exact ⟨rfl, IsPrimePow_four⟩
    rw [h_filter]
    rfl
  · contradiction

theorem a_three : a 3 = 0 := by
  unfold a
  split
  · have h_p2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_two_eq_five
    have h_p3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_three_eq_seven
    dsimp only
    rw [h_p2, h_p3]
    have h_Ioo : Ioo 5 7 = {6} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {6} = ∅ := by
      ext x
      simp
      rintro rfl
      exact not_IsPrimePow_six
    rw [h_filter]
    rfl
  · contradiction

theorem a_four : a 4 = 2 := by
  unfold a
  split
  · have h_p3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_three_eq_seven
    have h_p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
    dsimp only
    rw [h_p3, h_p4]
    have h_Ioo : Ioo 7 11 = {8, 9, 10} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {8, 9, 10} = {8, 9} := by
      ext x
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, h⟩
        · left; rfl
        · right; rfl
        · contradiction
      · rintro (rfl | rfl)
        · exact ⟨by simp, IsPrimePow_eight⟩
        · exact ⟨by simp, IsPrimePow_nine⟩
    rw [h_filter]
    rfl
  · contradiction


theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 13 by decide)
theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 17 by decide)
theorem nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 19 by decide)
theorem nth_prime_eight_eq_twenty_three : Nat.nth Nat.Prime 8 = 23 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 23 by decide)
theorem nth_prime_nine_eq_twenty_nine : Nat.nth Nat.Prime 9 = 29 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 29 by decide)
theorem nth_prime_ten_eq_thirty_one : Nat.nth Nat.Prime 10 = 31 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 31 by decide)

theorem IsPrimePow_sixteen : IsPrimePow 16 := by
  rw [isPrimePow_nat_iff]
  refine ⟨2, 4, prime_two, by decide, by rfl⟩

theorem IsPrimePow_twenty_five : IsPrimePow 25 := by
  rw [isPrimePow_nat_iff]
  refine ⟨5, 2, prime_five, by decide, by rfl⟩

theorem IsPrimePow_twenty_seven : IsPrimePow 27 := by
  rw [isPrimePow_nat_iff]
  refine ⟨3, 3, prime_three, by decide, by rfl⟩

theorem not_IsPrimePow_twelve : ¬ IsPrimePow 12 := by decide
theorem not_IsPrimePow_fourteen : ¬ IsPrimePow 14 := by decide

theorem not_IsPrimePow_fifteen : ¬ IsPrimePow 15 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, h_eq⟩
  have h_dvd : p ∣ 15 := by
    rw [← h_eq]
    exact dvd_pow_self p (by omega)
  have hp_le : p ≤ 15 := Nat.le_of_dvd (by decide) h_dvd
  have hp_prime : p.Prime := hp
  have hp_cases : p = 3 ∨ p = 5 := by
    interval_cases p
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · left; rfl
    · revert hp_prime; decide
    · right; rfl
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
  rcases hp_cases with rfl | rfl
  · -- p = 3
    rcases le_or_gt k 2 with hk_le | hk_gt
    · interval_cases k
      · rw [pow_one] at h_eq; omega
      · have : 3 ^ 2 = 9 := by rfl
        omega
    · have h_gt : 3 ^ k > 15 := by
        calc 15 < 27 := by decide
             _ ≤ 3 ^ k := Nat.pow_le_pow_right (show 1 ≤ 3 by decide) hk_gt
      omega
  · -- p = 5
    rcases le_or_gt k 1 with hk_le | hk_gt
    · interval_cases k
      · rw [pow_one] at h_eq; omega
    · have h_gt : 5 ^ k > 15 := by
        calc 15 < 25 := by decide
             _ ≤ 5 ^ k := Nat.pow_le_pow_right (show 1 ≤ 5 by decide) hk_gt
      omega

theorem not_IsPrimePow_eighteen : ¬ IsPrimePow 18 := by decide
theorem not_IsPrimePow_twenty : ¬ IsPrimePow 20 := by decide

theorem not_IsPrimePow_twenty_one : ¬ IsPrimePow 21 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, h_eq⟩
  have h_dvd : p ∣ 21 := by
    rw [← h_eq]
    exact dvd_pow_self p (by omega)
  have hp_le : p ≤ 21 := Nat.le_of_dvd (by decide) h_dvd
  have hp_prime : p.Prime := hp
  have hp_cases : p = 3 ∨ p = 7 := by
    interval_cases p
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · left; rfl
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · right; rfl
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert h_dvd; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
  rcases hp_cases with rfl | rfl
  · -- p = 3
    rcases le_or_gt k 2 with hk_le | hk_gt
    · interval_cases k
      · rw [pow_one] at h_eq; omega
      · have : 3 ^ 2 = 9 := by rfl
        omega
    · have h_gt : 3 ^ k > 21 := by
        calc 21 < 27 := by decide
             _ ≤ 3 ^ k := Nat.pow_le_pow_right (show 1 ≤ 3 by decide) hk_gt
      omega
  · -- p = 7
    rcases le_or_gt k 1 with hk_le | hk_gt
    · interval_cases k
      · rw [pow_one] at h_eq; omega
    · have h_gt : 7 ^ k > 21 := by
        calc 21 < 49 := by decide
             _ ≤ 7 ^ k := Nat.pow_le_pow_right (show 1 ≤ 7 by decide) hk_gt
      omega

theorem not_IsPrimePow_twenty_two : ¬ IsPrimePow 22 := by decide
theorem not_IsPrimePow_twenty_four : ¬ IsPrimePow 24 := by decide
theorem not_IsPrimePow_twenty_six : ¬ IsPrimePow 26 := by decide
theorem not_IsPrimePow_twenty_eight : ¬ IsPrimePow 28 := by decide
theorem not_IsPrimePow_thirty : ¬ IsPrimePow 30 := by decide

theorem a_five : a 5 = 0 := by
  unfold a
  split
  · have h_p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
    have h_p5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_five_eq_thirteen
    dsimp only
    rw [h_p4, h_p5]
    have h_Ioo : Ioo 11 13 = {12} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {12} = ∅ := by
      ext x
      simp
      rintro rfl
      exact not_IsPrimePow_twelve
    rw [h_filter]
    rfl
  · contradiction

theorem a_six : a 6 = 1 := by
  unfold a
  split
  · have h_p5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_five_eq_thirteen
    have h_p6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_six_eq_seventeen
    dsimp only
    rw [h_p5, h_p6]
    have h_Ioo : Ioo 13 17 = {14, 15, 16} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {14, 15, 16} = {16} := by
      ext x
      simp
      constructor
      · rintro ⟨rfl | rfl | rfl, h⟩
        · exact False.elim (not_IsPrimePow_fourteen h)
        · exact False.elim (not_IsPrimePow_fifteen h)
        · rfl
      · rintro rfl
        exact ⟨by simp, IsPrimePow_sixteen⟩
    rw [h_filter]
    rfl
  · contradiction

theorem a_seven : a 7 = 0 := by
  unfold a
  split
  · have h_p6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_six_eq_seventeen
    have h_p7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_seven_eq_nineteen
    dsimp only
    rw [h_p6, h_p7]
    have h_Ioo : Ioo 17 19 = {18} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {18} = ∅ := by
      ext x
      simp
      rintro rfl
      exact not_IsPrimePow_eighteen
    rw [h_filter]
    rfl
  · contradiction

theorem a_eight : a 8 = 0 := by
  unfold a
  split
  · have h_p7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_seven_eq_nineteen
    have h_p8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_eight_eq_twenty_three
    dsimp only
    rw [h_p7, h_p8]
    have h_Ioo : Ioo 19 23 = {20, 21, 22} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {20, 21, 22} = ∅ := by
      ext x
      simp
      rintro (rfl | rfl | rfl) h
      · exact not_IsPrimePow_twenty h
      · exact not_IsPrimePow_twenty_one h
      · exact not_IsPrimePow_twenty_two h
    rw [h_filter]
    rfl
  · contradiction

theorem a_nine : a 9 = 2 := by
  unfold a
  split
  · have h_p8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_eight_eq_twenty_three
    have h_p9 : Nat.nth Nat.Prime 9 = 29 := nth_prime_nine_eq_twenty_nine
    dsimp only
    rw [h_p8, h_p9]
    have h_Ioo : Ioo 23 29 = {24, 25, 26, 27, 28} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {24, 25, 26, 27, 28} = {25, 27} := by
      ext x
      simp
      constructor
      · rintro ⟨rfl | rfl | rfl | rfl | rfl, h⟩
        · exact False.elim (not_IsPrimePow_twenty_four h)
        · left; rfl
        · exact False.elim (not_IsPrimePow_twenty_six h)
        · right; rfl
        · exact False.elim (not_IsPrimePow_twenty_eight h)
      · rintro (rfl | rfl)
        · exact ⟨by simp, IsPrimePow_twenty_five⟩
        · exact ⟨by simp, IsPrimePow_twenty_seven⟩
    rw [h_filter]
    rfl
  · contradiction

theorem a_ten : a 10 = 0 := by
  unfold a
  split
  · have h_p9 : Nat.nth Nat.Prime 9 = 29 := nth_prime_nine_eq_twenty_nine
    have h_p10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_ten_eq_thirty_one
    dsimp only
    rw [h_p9, h_p10]
    have h_Ioo : Ioo 29 31 = {30} := by rfl
    rw [h_Ioo]
    have h_filter : filter IsPrimePow {30} = ∅ := by
      ext x
      simp
      rintro rfl
      exact not_IsPrimePow_thirty
    rw [h_filter]
    rfl
  · contradiction

lemma card_le_two_of_triple (S : Finset ℕ) (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → False) : S.card ≤ 2 := by
  by_contra hc
  have hc' : S.card ≥ 3 := by omega
  have h_len : S.toList.length ≥ 3 := by
    rwa [Finset.length_toList]
  rcases h_eq : S.toList with _ | ⟨x, _ | ⟨y, _ | ⟨z, L⟩⟩⟩
  · rw [h_eq] at h_len; contradiction
  · rw [h_eq] at h_len; contradiction
  · rw [h_eq] at h_len; contradiction
  · have hx : x ∈ S := by
      rw [← Finset.mem_toList, h_eq]
      simp
    have hy : y ∈ S := by
      rw [← Finset.mem_toList, h_eq]
      simp
    have hz : z ∈ S := by
      rw [← Finset.mem_toList, h_eq]
      simp
    have h_nodup : S.toList.Nodup := S.nodup_toList
    rw [h_eq] at h_nodup
    simp only [List.nodup_cons, List.mem_cons, not_or] at h_nodup
    rcases h_nodup with ⟨⟨hxy, hxz, _⟩, ⟨hyz, _⟩, _⟩
    rcases lt_or_gt_of_ne hxy with h_lt1 | h_gt1
    · rcases lt_or_gt_of_ne hyz with h_lt2 | h_gt2
      · exact h x hx y hy z hz h_lt1 h_lt2
      · rcases lt_or_gt_of_ne hxz with h_lt3 | h_gt3
        · exact h x hx z hz y hy h_lt3 h_gt2
        · exact h z hz x hx y hy h_gt3 h_lt1
    · rcases lt_or_gt_of_ne hyz with h_lt2 | h_gt2
      · rcases lt_or_gt_of_ne hxz with h_lt3 | h_gt3
        · exact h y hy x hx z hz h_gt1 h_lt3
        · exact h y hy z hz x hx h_lt2 h_gt3
      · exact h z hz y hy x hx h_gt2 h_gt1

lemma test_nth_ge_two (n : ℕ) (x : ℕ)
    (hx : Nat.nth Nat.Prime (n - 1) < x) : 1 < x := by
  have h_prime_zero : Nat.nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
  have h_le : Nat.nth Nat.Prime 0 ≤ Nat.nth Nat.Prime (n - 1) := by
    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
    omega
  rw [h_prime_zero] at h_le
  omega

lemma no_prime_between (n : ℕ) (hn : 0 < n) (p : ℕ) (h_prime : p.Prime)
    (h1 : Nat.nth Nat.Prime (n - 1) < p) (h2 : p < Nat.nth Nat.Prime n) : False := by
  have h_succ : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  have h2' : p < Nat.nth Nat.Prime ((n - 1) + 1) := by
    rwa [← h_succ]
  have h_le := Nat.le_nth_of_lt_nth_succ h2' h_prime
  omega

lemma no_triple_if_two_mul_le (n : ℕ) (hn : 0 < n) (x z : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hz : z ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (h_le : 2 * x ≤ z) : False := by
  simp only [mem_filter, mem_Ioo] at hx hz
  rcases hx with ⟨⟨hp_n_lt_x, _⟩, _⟩
  rcases hz with ⟨⟨_, hz_lt_p_succ⟩, _⟩
  have hx_gt_one : 1 < x := test_nth_ge_two n x hp_n_lt_x
  obtain ⟨p, hp_prime, hx_lt_p, hp_le_two_x⟩ := Nat.bertrand x (by omega)
  have hp_lt_p_succ : p < Nat.nth Nat.Prime n := by
    calc p ≤ 2 * x := hp_le_two_x
         _ ≤ z := h_le
         _ < Nat.nth Nat.Prime n := hz_lt_p_succ
  exact no_prime_between n hn p hp_prime (by omega) hp_lt_p_succ


lemma test_bound_z (n : ℕ) (hn : 4 < n) (x z : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hz : z ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow) :
    z ≤ 2 * Nat.nth Nat.Prime (n - 1) - 1 := by
  have hn_pos : 0 < n := by omega
  simp only [mem_filter, mem_Ioo] at hx hz
  rcases hx with ⟨⟨hp_n_lt_x, _⟩, _⟩
  rcases hz with ⟨⟨_, hz_lt_p_succ⟩, _⟩
  have hp_n_ge_eleven : 11 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h_le : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime (n - 1) := by
      rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
      omega
    have h_p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
    omega
  obtain ⟨p, hp_prime, h_gt_pn, h_le_two_pn⟩ := Nat.bertrand (Nat.nth Nat.Prime (n - 1)) (by omega)
  have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
    by_contra hc
    push_neg at hc
    exact no_prime_between n hn_pos p hp_prime h_gt_pn hc
  have hz_lt_p : z < p := by omega
  omega

lemma same_base_eq (n : ℕ) (hn : 0 < n) (x y : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hy : y ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (q u1 u2 : ℕ) (hq : q.Prime) (hx_eq : x = q ^ u1) (hy_eq : y = q ^ u2) : x = y := by
  by_contra h_ne
  simp only [mem_filter, mem_Ioo] at hx hy
  rcases hx with ⟨⟨hp_n_lt_x, hx_lt_p_succ⟩, _⟩
  rcases hy with ⟨⟨hp_n_lt_y, hy_lt_p_succ⟩, _⟩
  have hq_ge_two : 2 ≤ q := hq.two_le
  have hp_n_ge_two : 2 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h_le : Nat.nth Nat.Prime 0 ≤ Nat.nth Nat.Prime (n - 1) := by
      rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
      omega
    have h_p0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_zero_eq_two
    omega
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · -- x < y
    have hu_lt : u1 < u2 := by
      by_contra hc
      push_neg at hc
      have h_le : y ≤ x := by
        rw [hx_eq, hy_eq]
        exact Nat.pow_le_pow_right hq.one_le hc
      omega
    have hu_succ : u1 + 1 ≤ u2 := hu_lt
    have hy_ge : q ^ (u1 + 1) ≤ y := by
      rw [hy_eq]
      exact Nat.pow_le_pow_right hq.one_le hu_succ
    have hy_ge_2x : 2 * x ≤ y := by
      calc 2 * x = 2 * q ^ u1 := by rw [hx_eq]
           _ ≤ q * q ^ u1 := Nat.mul_le_mul_right _ hq_ge_two
           _ = q ^ u1 * q := by rw [mul_comm]
           _ = q ^ (u1 + 1) := by rw [← pow_succ]
           _ ≤ y := hy_ge
    have hp_succ_le_two_pn : Nat.nth Nat.Prime n ≤ 2 * Nat.nth Nat.Prime (n - 1) := by
      obtain ⟨p, hp_prime, h_gt_pn, h_le_two_pn⟩ := Nat.bertrand (Nat.nth Nat.Prime (n - 1)) (by omega)
      have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
        by_contra hc
        push_neg at hc
        exact no_prime_between n hn p hp_prime h_gt_pn hc
      omega
    omega
  · -- y < x
    have hu_lt : u2 < u1 := by
      by_contra hc
      push_neg at hc
      have h_le : x ≤ y := by
        rw [hx_eq, hy_eq]
        exact Nat.pow_le_pow_right hq.one_le hc
      omega
    have hu_succ : u2 + 1 ≤ u1 := hu_lt
    have hx_ge : q ^ (u2 + 1) ≤ x := by
      rw [hx_eq]
      exact Nat.pow_le_pow_right hq.one_le hu_succ
    have hx_ge_2y : 2 * y ≤ x := by
      calc 2 * y = 2 * q ^ u2 := by rw [hy_eq]
           _ ≤ q * q ^ u2 := Nat.mul_le_mul_right _ hq_ge_two
           _ = q ^ u2 * q := by rw [mul_comm]
           _ = q ^ (u2 + 1) := by rw [← pow_succ]
           _ ≤ x := hx_ge
    have hp_succ_le_two_pn : Nat.nth Nat.Prime n ≤ 2 * Nat.nth Nat.Prime (n - 1) := by
      obtain ⟨p, hp_prime, h_gt_pn, h_le_two_pn⟩ := Nat.bertrand (Nat.nth Nat.Prime (n - 1)) (by omega)
      have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
        by_contra hc
        push_neg at hc
        exact no_prime_between n hn p hp_prime h_gt_pn hc
      omega
    omega

lemma base_lt_pn (n : ℕ) (hn : 4 < n) (x : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (q u : ℕ) (hq : q.Prime) (hx_eq : x = q ^ u) : q < Nat.nth Nat.Prime (n - 1) := by
  have hn_pos : 0 < n := by omega
  simp only [mem_filter, mem_Ioo] at hx
  rcases hx with ⟨⟨hp_n_lt_x, hx_lt_p_succ⟩, _⟩
  have hp_n_ge_eleven : 11 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h_le : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime (n - 1) := by
      rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
      omega
    have h_p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
    omega
  by_contra hc
  push_neg at hc
  have h_cases : q = Nat.nth Nat.Prime (n - 1) ∨ Nat.nth Nat.Prime (n - 1) < q := by omega
  rcases h_cases with rfl | h_gt
  · -- q = p_n
    have hu_ge_two : 2 ≤ u := by
      by_contra hc2
      have hu_le : u ≤ 1 := by omega
      interval_cases u
      · rw [pow_zero] at hx_eq; omega
      · rw [pow_one] at hx_eq; omega
    have h_x_ge_pn2 : (Nat.nth Nat.Prime (n - 1)) ^ 2 ≤ x := by
      rw [hx_eq]
      exact Nat.pow_le_pow_right (by omega) hu_ge_two
    have h_p_succ_le_two_pn : Nat.nth Nat.Prime n ≤ 2 * Nat.nth Nat.Prime (n - 1) := by
      obtain ⟨p, hp_prime, h_gt_pn, h_le_two_pn⟩ := Nat.bertrand (Nat.nth Nat.Prime (n - 1)) (by omega)
      have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
        by_contra hc
        push_neg at hc
        exact no_prime_between n hn_pos p hp_prime h_gt_pn hc
      omega
    have h_pn2 : 2 * Nat.nth Nat.Prime (n - 1) < (Nat.nth Nat.Prime (n - 1)) ^ 2 := by
      calc 2 * Nat.nth Nat.Prime (n - 1) < 11 * Nat.nth Nat.Prime (n - 1) := by nlinarith
           _ ≤ (Nat.nth Nat.Prime (n - 1)) * Nat.nth Nat.Prime (n - 1) := Nat.mul_le_mul_right _ hp_n_ge_eleven
           _ = (Nat.nth Nat.Prime (n - 1)) ^ 2 := by ring
    omega
  · -- q > p_n
    have h_q_ge_p_succ : Nat.nth Nat.Prime n ≤ q := by
      by_contra hc2
      push_neg at hc2
      exact no_prime_between n hn_pos q hq h_gt hc2
    have h_x_ge_q : q ≤ x := by
      rw [hx_eq]
      have hu_pos : 1 ≤ u := by
        by_contra hc2
        have : u = 0 := by omega
        subst this
        rw [pow_zero] at hx_eq
        have h_x_gt_one : 1 < x := test_nth_ge_two n x hp_n_lt_x
        omega
      exact Nat.le_self_pow (by omega) q
    omega


lemma bertrand_bound_k (n : ℕ) (hn : 4 < n) (x z k : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hz : z ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hxy : x < z) (hk1 : 1 ≤ k) (hk_le : k ≤ x - Nat.nth Nat.Prime (n - 1)) :
    z ≤ 2 * x - 2 * k - 1 := by
  have hn_pos : 0 < n := by omega
  simp only [mem_filter, mem_Ioo] at hx hz
  rcases hx with ⟨⟨hp_n_lt_x, hx_lt_p_succ⟩, _⟩
  rcases hz with ⟨⟨_, hz_lt_p_succ⟩, _⟩
  have hp_n_ge_eleven : 11 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h_le : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime (n - 1) := by
      rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
      omega
    have h_p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_four_eq_eleven
    omega
  have h_xk_gt_one : 1 < x - k := by omega
  obtain ⟨p, hp_prime, h_gt, h_le⟩ := Nat.bertrand (x - k) (by omega)
  have hp_gt_x : x < p := by
    by_contra hc
    push_neg at hc
    have h_pn_le_xk : Nat.nth Nat.Prime (n - 1) ≤ x - k := by omega
    have hp_gt_pn : Nat.nth Nat.Prime (n - 1) < p := by omega
    have hp_lt_p_succ : p < Nat.nth Nat.Prime n := by omega
    exact no_prime_between n hn_pos p hp_prime hp_gt_pn hp_lt_p_succ
  have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
    by_contra hc
    push_neg at hc
    have hp_gt_pn : Nat.nth Nat.Prime (n - 1) < p := by omega
    exact no_prime_between n hn_pos p hp_prime hp_gt_pn hc
  have hz_lt_p : z < p := by omega
  omega

lemma at_least_one_ge_five (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
    (h12 : q1 ≠ q2) (h23 : q2 ≠ q3) (h13 : q1 ≠ q3) :
    5 ≤ q1 ∨ 5 ≤ q2 ∨ 5 ≤ q3 := by
  have h_val (q : ℕ) (hq : q.Prime) : q = 2 ∨ q = 3 ∨ 5 ≤ q := by
    have h_ge : 2 ≤ q := hq.two_le
    rcases le_or_gt 5 q with h5 | h5
    · right; right; exact h5
    · have hq4 : q ≠ 4 := by
        rintro rfl
        revert hq
        decide
      omega
  have h1 := h_val q1 hq1
  have h2 := h_val q2 hq2
  have h3 := h_val q3 hq3
  omega


lemma u_eq_two_of_ge_three (pn q u : ℕ) (hpn : 2 ≤ pn) (hq : 3 ≤ q) (h_sq : pn < q ^ 2) (h_le : q ^ u ≤ 2 * pn - 1) : u ≤ 2 := by
  by_contra hc
  push_neg at hc
  have hu : 3 ≤ u := hc
  have h_le3 : q ^ 3 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
  have h_q3 : q ^ 3 = q * q ^ 2 := by ring
  have h_ge : 2 * pn - 1 < q ^ 3 := by
    calc 2 * pn - 1 < 3 * pn := by omega
         _ ≤ 3 * q ^ 2 := by
           have h_mul := Nat.mul_le_mul_left 3 h_sq
           omega
         _ ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
         _ = q ^ 3 := h_q3.symm
  omega

lemma at_least_two_ge_three (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
    (h12 : q1 ≠ q2) (h23 : q2 ≠ q3) (h13 : q1 ≠ q3) :
    (3 ≤ q1 ∧ 3 ≤ q2) ∨ (3 ≤ q2 ∧ 3 ≤ q3) ∨ (3 ≤ q1 ∧ 3 ≤ q3) := by
  have h_val (q : ℕ) (hq : q.Prime) : q = 2 ∨ 3 ≤ q := by
    have h_ge : 2 ≤ q := hq.two_le
    omega
  have h1 := h_val q1 hq1
  have h2 := h_val q2 hq2
  have h3 := h_val q3 hq3
  omega

/--
A080101: The maximum value of terms in the sequence is conjectured to be 2.
This is a formalization of the OEIS conjecture: "The maximum value of terms in the sequence, through the (10^5)th term, is 2. - Harvey P. Dale, Aug 24 2014 This is conjectured to be the maximum, see also A366833. - Gus Wiseman, Nov 06 2024"
-/





lemma n_eq_of_nth_eq (n : ℕ) (hn : 0 < n) (k : ℕ) (h : Nat.nth Nat.Prime (n - 1) = Nat.nth Nat.Prime k) : n = k + 1 := by
  have h_eq : n - 1 = k := Nat.nth_injective Nat.infinite_setOf_prime h
  omega

lemma not_IsPrimePow_of_two_prime_divisors (n : ℕ) (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hd1 : p1 ∣ n) (hd2 : p2 ∣ n) (hne : p1 ≠ p2) : ¬ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, rfl⟩
  have hd1' : p1 ∣ p := hp1.dvd_of_dvd_pow hd1
  have hd2' : p2 ∣ p := hp2.dvd_of_dvd_pow hd2
  have heq1 : p = p1 := (hp.dvd_iff_eq hp1.ne_one).mp hd1'
  have heq2 : p = p2 := (hp.dvd_iff_eq hp2.ne_one).mp hd2'
  subst heq1 heq2
  exact hne rfl

lemma odd_prime_power_ge_121 (P q u : ℕ) (hP : 83 ≤ P) (hq : q.Prime) (hu : 2 ≤ u) (hq_ge3 : 3 ≤ q) (h_gt : P < q ^ u) : 121 ≤ q ^ u := by
  rcases le_or_gt 11 q with hq11 | hq11
  · have hq_sq : 121 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq11 hq11
    have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
    omega
  · have hq_cases : q = 3 ∨ q = 5 ∨ q = 7 := by
      interval_cases q <;> { try { revert hq; decide }; try { decide } }
    rcases hq_cases with rfl | rfl | rfl
    · have hu_ge5 : 5 ≤ u := by
        by_contra hc
        have : u ≤ 4 := by omega
        have : 3 ^ u ≤ 81 := by
          interval_cases u
          · decide
          · decide
          · decide
        omega
      calc 121 ≤ 243 := by decide
           _ ≤ 3 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hu_ge5
    · have hu_ge3 : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 5 ^ u ≤ 25 := by
          interval_cases u
          · decide
        omega
      calc 121 ≤ 125 := by decide
           _ ≤ 5 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 5) hu_ge3
    · have hu_ge3 : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 7 ^ u ≤ 49 := by
          interval_cases u
          · decide
        omega
      calc 121 ≤ 343 := by decide
           _ ≤ 7 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 7) hu_ge3

lemma odd_prime_power_ge_243 (P q u : ℕ) (hP : 83 ≤ P) (hq : q.Prime) (hu : 2 ≤ u) (hq_ge3 : 3 ≤ q) (h_gt : P < q ^ u) : 243 ≤ q ^ u := by
  rcases le_or_gt 11 q with hq11 | hq11
  · have hq_sq : 121 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq11 hq11
    have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
    rcases le_or_gt 17 q with hq17 | hq17
    · have hq_sq2 : 289 ≤ q ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul hq17 hq17
      have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
      omega
    · have hq_cases : q = 11 ∨ q = 13 := by
        interval_cases q <;> { try { revert hq; decide }; try { decide } }
      rcases hq_cases with rfl | rfl
      · have : 3 ≤ u := by
          by_contra hc
          have : u ≤ 2 := by omega
          have : 11 ^ u ≤ 121 := by interval_cases u <;> decide
          omega
        calc 243 ≤ 1331 := by decide
             _ ≤ 11 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 11) this
      · have : 3 ≤ u := by
          by_contra hc
          have : u ≤ 2 := by omega
          have : 13 ^ u ≤ 169 := by interval_cases u <;> decide
          omega
        calc 243 ≤ 2197 := by decide
             _ ≤ 13 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 13) this
  · have hq_cases : q = 3 ∨ q = 5 ∨ q = 7 := by
      interval_cases q <;> { try { revert hq; decide }; try { decide } }
    rcases hq_cases with rfl | rfl | rfl
    · have : 5 ≤ u := by
        by_contra hc
        have : u ≤ 4 := by omega
        have : 3 ^ u ≤ 81 := by interval_cases u <;> decide
        omega
      calc 243 ≤ 243 := by decide
           _ ≤ 3 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 3) this
    · have : 4 ≤ u := by
        by_contra hc
        have : u ≤ 3 := by omega
        have : 5 ^ u ≤ 125 := by interval_cases u <;> decide
        omega
      calc 243 ≤ 625 := by decide
           _ ≤ 5 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 5) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 7 ^ u ≤ 49 := by interval_cases u <;> decide
        omega
      calc 243 ≤ 343 := by decide
           _ ≤ 7 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 7) this

lemma odd_prime_power_ge_512 (P q u : ℕ) (hP : 251 ≤ P) (hq : q.Prime) (hu : 2 ≤ u) (hq_ge3 : 3 ≤ q) (h_gt : P < q ^ u) : 512 ≤ q ^ u := by
  rcases le_or_gt 23 q with hq23 | hq23
  · have hq_sq : 529 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq23 hq23
    have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
    omega
  · have hq_cases : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 := by
      interval_cases q <;> { try { revert hq; decide }; try { decide } }
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : 6 ≤ u := by
        by_contra hc
        have : u ≤ 5 := by omega
        have : 3 ^ u ≤ 243 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 729 := by decide
           _ ≤ 3 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 3) this
    · have : 5 ≤ u := by
        by_contra hc
        have : u ≤ 4 := by omega
        have : 5 ^ u ≤ 625 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 3125 := by decide
           _ ≤ 5 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 5) this
    · have : 4 ≤ u := by
        by_contra hc
        have : u ≤ 3 := by omega
        have : 7 ^ u ≤ 343 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 2401 := by decide
           _ ≤ 7 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 7) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 11 ^ u ≤ 121 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 1331 := by decide
           _ ≤ 11 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 11) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 13 ^ u ≤ 169 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 2197 := by decide
           _ ≤ 13 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 13) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 17 ^ u ≤ 289 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 4913 := by decide
           _ ≤ 17 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 17) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 19 ^ u ≤ 361 := by interval_cases u <;> decide
        omega
      calc 512 ≤ 6859 := by decide
           _ ≤ 19 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 19) this

lemma odd_prime_power_ge_841 (P q u : ℕ) (hP : 509 ≤ P) (hq : q.Prime) (hu : 2 ≤ u) (hq_ge3 : 3 ≤ q) (h_gt : P < q ^ u) : 841 ≤ q ^ u := by
  rcases le_or_gt 29 q with hq29 | hq29
  · have hq_sq : 841 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq29 hq29
    have : q ^ 2 ≤ q ^ u := Nat.pow_le_pow_right (by omega) hu
    omega
  · have hq_cases : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 := by
      interval_cases q <;> { try { revert hq; decide }; try { decide } }
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : 7 ≤ u := by
        by_contra hc
        have : u ≤ 6 := by omega
        have : 3 ^ u ≤ 729 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 2187 := by decide
           _ ≤ 3 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 3) this
    · have : 5 ≤ u := by
        by_contra hc
        have : u ≤ 4 := by omega
        have : 5 ^ u ≤ 625 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 3125 := by decide
           _ ≤ 5 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 5) this
    · have : 4 ≤ u := by
        by_contra hc
        have : u ≤ 3 := by omega
        have : 7 ^ u ≤ 343 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 2401 := by decide
           _ ≤ 7 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 7) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 11 ^ u ≤ 121 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 1331 := by decide
           _ ≤ 11 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 11) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 13 ^ u ≤ 169 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 2197 := by decide
           _ ≤ 13 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 13) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 17 ^ u ≤ 289 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 4913 := by decide
           _ ≤ 17 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 17) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 19 ^ u ≤ 361 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 6859 := by decide
           _ ≤ 19 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 19) this
    · have : 3 ≤ u := by
        by_contra hc
        have : u ≤ 2 := by omega
        have : 23 ^ u ≤ 529 := by interval_cases u <;> decide
        omega
      calc 841 ≤ 12167 := by decide
           _ ≤ 23 ^ u := Nat.pow_le_pow_right (by decide : 1 ≤ 23) this

lemma no_triple_for_small_P (n : ℕ) (hn : 0 < n) (hk_range : 10 ≤ n - 1 ∧ n - 1 < 22)
    (x y z : ℕ)
    (hx : x ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hy : y ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hz : z ∈ (Ioo (Nat.nth Nat.Prime (n - 1)) (Nat.nth Nat.Prime n)).filter IsPrimePow)
    (hxy : x < y) (hyz : y < z) : False := by
  have hk_val : n - 1 = 10 ∨ n - 1 = 11 ∨ n - 1 = 12 ∨ n - 1 = 13 ∨ n - 1 = 14 ∨ n - 1 = 15 ∨ n - 1 = 16 ∨ n - 1 = 17 ∨ n - 1 = 18 ∨ n - 1 = 19 ∨ n - 1 = 20 ∨ n - 1 = 21 := by omega
  rcases hk_val with h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq
  · -- P = 31, k = 10, next = 37
    have h_eq2 : n = 10 + 1 := by omega
    subst h_eq2
    have hp_10 : Nat.nth Nat.Prime 10 = 31 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 31 by decide)
    have hp_11 : Nat.nth Nat.Prime 11 = 37 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 37 by decide)
    simp only [hp_10, hp_11, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h33 : ¬ IsPrimePow 33 := not_IsPrimePow_of_two_prime_divisors 33 3 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h34 : ¬ IsPrimePow 34 := not_IsPrimePow_of_two_prime_divisors 34 2 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h35 : ¬ IsPrimePow 35 := not_IsPrimePow_of_two_prime_divisors 35 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h36 : ¬ IsPrimePow 36 := not_IsPrimePow_of_two_prime_divisors 36 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 37, k = 11, next = 41
    have h_eq2 : n = 11 + 1 := by omega
    subst h_eq2
    have hp_11 : Nat.nth Nat.Prime 11 = 37 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 37 by decide)
    have hp_12 : Nat.nth Nat.Prime 12 = 41 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 41 by decide)
    simp only [hp_11, hp_12, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h38 : ¬ IsPrimePow 38 := not_IsPrimePow_of_two_prime_divisors 38 2 19 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h39 : ¬ IsPrimePow 39 := not_IsPrimePow_of_two_prime_divisors 39 3 13 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h40 : ¬ IsPrimePow 40 := not_IsPrimePow_of_two_prime_divisors 40 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 41, k = 12, next = 43
    have h_eq2 : n = 12 + 1 := by omega
    subst h_eq2
    have hp_12 : Nat.nth Nat.Prime 12 = 41 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 41 by decide)
    have hp_13 : Nat.nth Nat.Prime 13 = 43 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 43 by decide)
    simp only [hp_12, hp_13, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h42 : ¬ IsPrimePow 42 := not_IsPrimePow_of_two_prime_divisors 42 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 43, k = 13, next = 47
    have h_eq2 : n = 13 + 1 := by omega
    subst h_eq2
    have hp_13 : Nat.nth Nat.Prime 13 = 43 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 43 by decide)
    have hp_14 : Nat.nth Nat.Prime 14 = 47 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 47 by decide)
    simp only [hp_13, hp_14, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h44 : ¬ IsPrimePow 44 := not_IsPrimePow_of_two_prime_divisors 44 2 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h45 : ¬ IsPrimePow 45 := not_IsPrimePow_of_two_prime_divisors 45 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h46 : ¬ IsPrimePow 46 := not_IsPrimePow_of_two_prime_divisors 46 2 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 47, k = 14, next = 53
    have h_eq2 : n = 14 + 1 := by omega
    subst h_eq2
    have hp_14 : Nat.nth Nat.Prime 14 = 47 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 47 by decide)
    have hp_15 : Nat.nth Nat.Prime 15 = 53 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 53 by decide)
    simp only [hp_14, hp_15, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h48 : ¬ IsPrimePow 48 := not_IsPrimePow_of_two_prime_divisors 48 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h50 : ¬ IsPrimePow 50 := not_IsPrimePow_of_two_prime_divisors 50 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h51 : ¬ IsPrimePow 51 := not_IsPrimePow_of_two_prime_divisors 51 3 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h52 : ¬ IsPrimePow 52 := not_IsPrimePow_of_two_prime_divisors 52 2 13 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 53, k = 15, next = 59
    have h_eq2 : n = 15 + 1 := by omega
    subst h_eq2
    have hp_15 : Nat.nth Nat.Prime 15 = 53 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 53 by decide)
    have hp_16 : Nat.nth Nat.Prime 16 = 59 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 59 by decide)
    simp only [hp_15, hp_16, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h54 : ¬ IsPrimePow 54 := not_IsPrimePow_of_two_prime_divisors 54 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h55 : ¬ IsPrimePow 55 := not_IsPrimePow_of_two_prime_divisors 55 5 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h56 : ¬ IsPrimePow 56 := not_IsPrimePow_of_two_prime_divisors 56 2 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h57 : ¬ IsPrimePow 57 := not_IsPrimePow_of_two_prime_divisors 57 3 19 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h58 : ¬ IsPrimePow 58 := not_IsPrimePow_of_two_prime_divisors 58 2 29 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 59, k = 16, next = 61
    have h_eq2 : n = 16 + 1 := by omega
    subst h_eq2
    have hp_16 : Nat.nth Nat.Prime 16 = 59 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 59 by decide)
    have hp_17 : Nat.nth Nat.Prime 17 = 61 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 61 by decide)
    simp only [hp_16, hp_17, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h60 : ¬ IsPrimePow 60 := not_IsPrimePow_of_two_prime_divisors 60 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 61, k = 17, next = 67
    have h_eq2 : n = 17 + 1 := by omega
    subst h_eq2
    have hp_17 : Nat.nth Nat.Prime 17 = 61 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 61 by decide)
    have hp_18 : Nat.nth Nat.Prime 18 = 67 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 67 by decide)
    simp only [hp_17, hp_18, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h62 : ¬ IsPrimePow 62 := not_IsPrimePow_of_two_prime_divisors 62 2 31 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h63 : ¬ IsPrimePow 63 := not_IsPrimePow_of_two_prime_divisors 63 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h65 : ¬ IsPrimePow 65 := not_IsPrimePow_of_two_prime_divisors 65 5 13 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h66 : ¬ IsPrimePow 66 := not_IsPrimePow_of_two_prime_divisors 66 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 67, k = 18, next = 71
    have h_eq2 : n = 18 + 1 := by omega
    subst h_eq2
    have hp_18 : Nat.nth Nat.Prime 18 = 67 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 67 by decide)
    have hp_19 : Nat.nth Nat.Prime 19 = 71 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 71 by decide)
    simp only [hp_18, hp_19, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h68 : ¬ IsPrimePow 68 := not_IsPrimePow_of_two_prime_divisors 68 2 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h69 : ¬ IsPrimePow 69 := not_IsPrimePow_of_two_prime_divisors 69 3 23 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h70 : ¬ IsPrimePow 70 := not_IsPrimePow_of_two_prime_divisors 70 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 71, k = 19, next = 73
    have h_eq2 : n = 19 + 1 := by omega
    subst h_eq2
    have hp_19 : Nat.nth Nat.Prime 19 = 71 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 71 by decide)
    have hp_20 : Nat.nth Nat.Prime 20 = 73 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 73 by decide)
    simp only [hp_19, hp_20, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h72 : ¬ IsPrimePow 72 := not_IsPrimePow_of_two_prime_divisors 72 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 73, k = 20, next = 79
    have h_eq2 : n = 20 + 1 := by omega
    subst h_eq2
    have hp_20 : Nat.nth Nat.Prime 20 = 73 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 73 by decide)
    have hp_21 : Nat.nth Nat.Prime 21 = 79 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 79 by decide)
    simp only [hp_20, hp_21, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h74 : ¬ IsPrimePow 74 := not_IsPrimePow_of_two_prime_divisors 74 2 37 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h75 : ¬ IsPrimePow 75 := not_IsPrimePow_of_two_prime_divisors 75 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h76 : ¬ IsPrimePow 76 := not_IsPrimePow_of_two_prime_divisors 76 2 19 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h77 : ¬ IsPrimePow 77 := not_IsPrimePow_of_two_prime_divisors 77 7 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h78 : ¬ IsPrimePow 78 := not_IsPrimePow_of_two_prime_divisors 78 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)
  · -- P = 79, k = 21, next = 83
    have h_eq2 : n = 21 + 1 := by omega
    subst h_eq2
    have hp_21 : Nat.nth Nat.Prime 21 = 79 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 79 by decide)
    have hp_22 : Nat.nth Nat.Prime 22 = 83 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 83 by decide)
    simp only [hp_21, hp_22, mem_filter, mem_Ioo] at hx hy hz
    rcases hx with ⟨⟨hx1, hx2⟩, hx_pp⟩
    rcases hy with ⟨⟨hy1, hy2⟩, hy_pp⟩
    rcases hz with ⟨⟨hz1, hz2⟩, hz_pp⟩
    have h80 : ¬ IsPrimePow 80 := not_IsPrimePow_of_two_prime_divisors 80 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h82 : ¬ IsPrimePow 82 := not_IsPrimePow_of_two_prime_divisors 82 2 41 (by decide) (by decide) (by decide) (by decide) (by decide)
    interval_cases x <;> (try contradiction) <;> interval_cases y <;> (try contradiction) <;> interval_cases z <;> (try contradiction)

theorem oeis_80101_conjecture : ∀ (n : ℕ), a n ≤ 2 := by
  intro n
  rcases le_or_gt n 10 with hn | hn
  · interval_cases n
    · rw [a_zero]; omega
    · rw [a_one]; omega
    · rw [a_two]; omega
    · rw [a_three]; omega
    · rw [a_four]
    · rw [a_five]; omega
    · rw [a_six]; omega
    · rw [a_seven]; omega
    · rw [a_eight]; omega
    · rw [a_nine]
    · rw [a_ten]; omega
  · unfold a
    split
    · apply card_le_two_of_triple
      intro x hx y hy z hz hxy hyz
      have hp_n_ge_thirty_one : 31 ≤ Nat.nth Nat.Prime (n - 1) := by
        have h_le : Nat.nth Nat.Prime 10 ≤ Nat.nth Nat.Prime (n - 1) := by
          rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
          omega
        have h_p10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_ten_eq_thirty_one
        omega
      have h_cases : Nat.nth Nat.Prime (n - 1) < 83 ∨ 83 ≤ Nat.nth Nat.Prime (n - 1) := by omega
      rcases h_cases with h_lt | h_ge
      · -- n - 1 must fall into k ∈ [10, 21]
        have h_n_bounds : 10 ≤ n - 1 ∧ n - 1 < 22 := by
          constructor
          · by_contra hc
            push_neg at hc
            have h_lt' : Nat.nth Nat.Prime (n - 1) < Nat.nth Nat.Prime 10 := by
              rw [Nat.nth_lt_nth Nat.infinite_setOf_prime]
              omega
            have h_p10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_ten_eq_thirty_one
            omega
          · by_contra hc
            push_neg at hc
            have h_le : Nat.nth Nat.Prime 21 ≤ Nat.nth Nat.Prime (n - 1) := by
              rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
              omega
            have h_p21 : Nat.nth Nat.Prime 21 = 79 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 79 by decide)
            omega
        exact no_triple_for_small_P n (by omega) h_n_bounds x y z hx hy hz hxy hyz
      · -- P ≥ 83
        have hx_copy := hx
        have hy_copy := hy
        have hz_copy := hz
        simp only [mem_filter, mem_Ioo] at hx hy hz
        rcases hx with ⟨⟨hp_n_lt_x, hx_lt_p_succ⟩, h_x_pp⟩
        rcases hy with ⟨⟨hp_n_lt_y, hy_lt_p_succ⟩, h_y_pp⟩
        rcases hz with ⟨⟨hp_n_lt_z, hz_lt_p_succ⟩, h_z_pp⟩
        rw [isPrimePow_nat_iff] at h_x_pp
        rcases h_x_pp with ⟨q1, u1, ⟨hq1, hu1, hx_eq⟩⟩
        rw [isPrimePow_nat_iff] at h_y_pp
        rcases h_y_pp with ⟨q2, u2, ⟨hq2, hu2, hy_eq⟩⟩
        rw [isPrimePow_nat_iff] at h_z_pp
        rcases h_z_pp with ⟨q3, u3, ⟨hq3, hu3, hz_eq⟩⟩
        have h_u1 : 2 ≤ u1 := by
          by_contra hc
          have : u1 = 1 := by omega
          subst this
          rw [pow_one] at hx_eq
          have hx_eq' : x = q1 := hx_eq.symm
          subst hx_eq'
          exact no_prime_between n (by omega) x hq1 hp_n_lt_x hx_lt_p_succ
        have h_u2 : 2 ≤ u2 := by
          by_contra hc
          have : u2 = 1 := by omega
          subst this
          rw [pow_one] at hy_eq
          have hy_eq' : y = q2 := hy_eq.symm
          subst hy_eq'
          exact no_prime_between n (by omega) y hq2 hp_n_lt_y hy_lt_p_succ
        have h_u3 : 2 ≤ u3 := by
          by_contra hc
          have : u3 = 1 := by omega
          subst this
          rw [pow_one] at hz_eq
          have hz_eq' : z = q3 := hz_eq.symm
          subst hz_eq'
          exact no_prime_between n (by omega) z hq3 hp_n_lt_z hz_lt_p_succ
        have hq12 : q1 ≠ q2 := by
          rintro rfl
          have : x = y := same_base_eq n (by omega) x y hx_copy hy_copy q1 u1 u2 hq1 hx_eq.symm hy_eq.symm
          omega
        have hq23 : q2 ≠ q3 := by
          rintro rfl
          have : y = z := same_base_eq n (by omega) y z hy_copy hz_copy q2 u2 u3 hq2 hy_eq.symm hz_eq.symm
          omega
        have hq13 : q1 ≠ q3 := by
          rintro rfl
          have : x = z := same_base_eq n (by omega) x z hx_copy hz_copy q1 u1 u3 hq1 hx_eq.symm hz_eq.symm
          omega
        have h_bases := at_least_two_ge_three q1 q2 q3 hq1 hq2 hq3 hq12 hq23 hq13
        rcases h_bases with ⟨hq1_ge3, hq2_ge3⟩ | ⟨hq2_ge3, hq3_ge3⟩ | ⟨hq1_ge3, hq3_ge3⟩
        · have hx_ge121 : 121 ≤ x := by
            rw [← hx_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge hq1 h_u1 hq1_ge3 hp_n_lt_x
          have hy_ge121 : 121 ≤ y := by
            rw [← hy_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge hq2 h_u2 hq2_ge3 hp_n_lt_y
          have h_distinct : q1 ≠ 3 ∨ q2 ≠ 3 := by
            by_contra hc
            push_neg at hc
            rcases hc with ⟨rfl, rfl⟩
            exact hq12 rfl
          have h_one_base_ge243 : 243 ≤ x ∨ 243 ≤ y := by
            rcases h_distinct with hne1 | hne2
            · right
              rw [← hy_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge hq2 h_u2 hq2_ge3 hp_n_lt_y
            · left
              rw [← hx_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge hq1 h_u1 hq1_ge3 hp_n_lt_x
          have hz_ge244 : 244 ≤ z := by
            rcases h_one_base_ge243 with hx_ge_val | hy_ge_val
            · omega
            · omega
          have hz_ge256 : 256 ≤ z := by
            rcases eq_or_ne q3 2 with rfl | hq3_ne2
            · have : 2 ^ u3 ≥ 244 := by omega
              have : u3 ≥ 8 := by
                by_contra hc
                have : u3 ≤ 7 := by omega
                have : 2 ^ u3 ≤ 128 := by interval_cases u3 <;> decide
                omega
              calc 256 ≤ 2 ^ u3 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) this
            · have hq3_ge3 : 3 ≤ q3 := by
                have : 2 ≤ q3 := hq3.two_le
                omega
              have : 243 ≤ z := by
                rw [← hz_eq]
                exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
              omega
          rcases le_or_gt 251 (Nat.nth Nat.Prime (n - 1)) with h_ge251 | h_lt251
          · have hx_ge512 : 512 ≤ x := by
              rw [← hx_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge251 hq1 h_u1 hq1_ge3 hp_n_lt_x
            have hy_ge512 : 512 ≤ y := by
              rw [← hy_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge251 hq2 h_u2 hq2_ge3 hp_n_lt_y
            have hz_ge512 : 512 ≤ z := by
              rcases eq_or_ne q3 2 with rfl | hq3_ne2
              · have : 2 ^ u3 ≥ 513 := by omega
                have : u3 ≥ 10 := by
                  by_contra hc
                  have : u3 ≤ 9 := by omega
                  have : 2 ^ u3 ≤ 512 := by interval_cases u3 <;> decide
                  omega
                calc 512 ≤ 2 ^ u3 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) this
              · have hq3_ge3 : 3 ≤ q3 := by
                  have : 2 ≤ q3 := hq3.two_le
                  omega
                have : 512 ≤ z := by
                  rw [← hz_eq]
                  exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge251 hq3 h_u3 hq3_ge3 hp_n_lt_z
                omega
            rcases le_or_gt 509 (Nat.nth Nat.Prime (n - 1)) with h_ge509 | h_lt509
            · have hz_ge841 : 841 ≤ z := by
                rcases eq_or_ne q3 2 with rfl | hq3_ne2
                · have : 2 ^ u3 ≥ 730 := by omega
                  have : u3 ≥ 10 := by
                    by_contra hc
                    have : u3 ≤ 9 := by omega
                    have : 2 ^ u3 ≤ 512 := by interval_cases u3 <;> decide
                    omega
                  calc 841 ≤ 1024 := by decide
                       _ ≤ 2 ^ u3 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) this
                · have hq3_ge3 : 3 ≤ q3 := by
                    have : 2 ≤ q3 := hq3.two_le
                    omega
                  have : 841 ≤ z := by
                    rw [← hz_eq]
                    exact odd_prime_power_ge_841 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge509 hq3 h_u3 hq3_ge3 hp_n_lt_z
                  omega
              have hp_succ_le_two_pn : Nat.nth Nat.Prime n ≤ 2 * Nat.nth Nat.Prime (n - 1) := by
                obtain ⟨p, hp_prime, h_gt_pn, h_le_two_pn⟩ := Nat.bertrand (Nat.nth Nat.Prime (n - 1)) (by omega)
                have hp_ge_p_succ : Nat.nth Nat.Prime n ≤ p := by
                  by_contra hc
                  push_neg at hc
                  exact no_prime_between n (by omega) p hp_prime h_gt_pn hc
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              -- now P is in [509, 829). The next prime must be ≤ 839.
              have hp_succ_le_839 : Nat.nth Nat.Prime n ≤ 839 := by
                -- since P < 829, n - 1 < 144
                have : n - 1 < 144 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 144 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                  omega
                have : n ≤ 144 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 144 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                omega
              omega
            · have hp_succ_le_509 : Nat.nth Nat.Prime n ≤ 509 := by
                have : n - 1 < 97 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 97 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                  omega
                have : n ≤ 97 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 97 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              omega
          · have hp_succ_le_251 : Nat.nth Nat.Prime n ≤ 251 := by
              have : n - 1 < 54 := by
                by_contra hc
                have : Nat.nth Nat.Prime 54 ≤ Nat.nth Nat.Prime (n - 1) := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
                omega
              have : n ≤ 54 := by omega
              have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 54 := by
                rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                omega
              have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
              omega
            have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
            omega
        · -- q2, q3 ≥ 3
          have hy_ge121 : 121 ≤ y := by
            rw [← hy_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge hq2 h_u2 hq2_ge3 hp_n_lt_y
          have hz_ge121 : 121 ≤ z := by
            rw [← hz_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
          have h_distinct : q2 ≠ 3 ∨ q3 ≠ 3 := by
            by_contra hc
            push_neg at hc
            rcases hc with ⟨rfl, rfl⟩
            exact hq23 rfl
          have h_one_base_ge243 : 243 ≤ y ∨ 243 ≤ z := by
            rcases h_distinct with hne1 | hne2
            · right
              rw [← hz_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
            · left
              rw [← hy_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge hq2 h_u2 hq2_ge3 hp_n_lt_y
          have hz_ge243 : 243 ≤ z := by
            rcases h_one_base_ge243 with hy_ge_val | hz_ge_val
            · omega
            · omega
          have hz_ge256 : 256 ≤ z := by
            have : 244 ≤ z := by omega
            rcases eq_or_ne q3 2 with rfl | hq3_ne2
            · revert hq3; decide
            · have hq3_ge3 : 3 ≤ q3 := by
                have : 2 ≤ q3 := hq3.two_le
                omega
              have : 243 ≤ z := by
                rw [← hz_eq]
                exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
              omega
          rcases le_or_gt 251 (Nat.nth Nat.Prime (n - 1)) with h_ge251 | h_lt251
          · have hy_ge512 : 512 ≤ y := by
              rw [← hy_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n - 1)) q2 u2 h_ge251 hq2 h_u2 hq2_ge3 hp_n_lt_y
            have hz_ge512 : 512 ≤ z := by
              have hq3_ge3 : 3 ≤ q3 := by
                have : 2 ≤ q3 := hq3.two_le
                omega
              rw [← hz_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge251 hq3 h_u3 hq3_ge3 hp_n_lt_z
            rcases le_or_gt 509 (Nat.nth Nat.Prime (n - 1)) with h_ge509 | h_lt509
            · have hz_ge841 : 841 ≤ z := by
                have hq3_ge3 : 3 ≤ q3 := by
                  have : 2 ≤ q3 := hq3.two_le
                  omega
                rw [← hz_eq]
                exact odd_prime_power_ge_841 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge509 hq3 h_u3 hq3_ge3 hp_n_lt_z
              have hp_succ_le_839 : Nat.nth Nat.Prime n ≤ 839 := by
                have : n - 1 < 144 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 144 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                  omega
                have : n ≤ 144 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 144 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              omega
            · have hp_succ_le_509 : Nat.nth Nat.Prime n ≤ 509 := by
                have : n - 1 < 97 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 97 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                  omega
                have : n ≤ 97 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 97 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              omega
          · have hp_succ_le_251 : Nat.nth Nat.Prime n ≤ 251 := by
              have : n - 1 < 54 := by
                by_contra hc
                have : Nat.nth Nat.Prime 54 ≤ Nat.nth Nat.Prime (n - 1) := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
                omega
              have : n ≤ 54 := by omega
              have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 54 := by
                rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                omega
              have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
                omega
            have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
            omega
        · -- q1, q3 ≥ 3
          have hx_ge121 : 121 ≤ x := by
            rw [← hx_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge hq1 h_u1 hq1_ge3 hp_n_lt_x
          have hz_ge121 : 121 ≤ z := by
            rw [← hz_eq]
            exact odd_prime_power_ge_121 (Nat.nth Nat.Prime (n - 1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
          have h_distinct : q1 ≠ 3 ∨ q3 ≠ 3 := by
            by_contra hc
            push_neg at hc
            rcases hc with ⟨rfl, rfl⟩
            exact hq13 rfl
          have h_one_base_ge243 : 243 ≤ x ∨ 243 ≤ z := by
            rcases h_distinct with hne1 | hne2
            · right
              rw [← hz_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
            · left
              rw [← hx_eq]
              exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge hq1 h_u1 hq1_ge3 hp_n_lt_x
          have hz_ge243 : 243 ≤ z := by
            rcases h_one_base_ge243 with hx_ge_val | hz_ge_val
            · have : 2187 ≤ y := by omega
              omega
            · omega
          have hz_ge256 : 256 ≤ z := by
            have : 244 ≤ z := by omega
            rcases eq_or_ne q3 2 with rfl | hq3_ne2
            · revert hq3; decide
            · have hq3_ge3 : 3 ≤ q3 := by
                have : 2 ≤ q3 := hq3.two_le
                omega
              have : 243 ≤ z := by
                rw [← hz_eq]
                exact odd_prime_power_ge_243 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge hq3 h_u3 hq3_ge3 hp_n_lt_z
              omega
          rcases le_or_gt 251 (Nat.nth Nat.Prime (n - 1)) with h_ge251 | h_lt251
          · have hx_ge512 : 512 ≤ x := by
              rw [← hx_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n - 1)) q1 u1 h_ge251 hq1 h_u1 hq1_ge3 hp_n_lt_x
            have hz_ge512 : 512 ≤ z := by
              have hq3_ge3 : 3 ≤ q3 := by
                have : 2 ≤ q3 := hq3.two_le
                omega
              rw [← hz_eq]
              exact odd_prime_power_ge_512 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge251 hq3 h_u3 hq3_ge3 hp_n_lt_z
            rcases le_or_gt 509 (Nat.nth Nat.Prime (n - 1)) with h_ge509 | h_lt509
            · have hz_ge841 : 841 ≤ z := by
                have hq3_ge3 : 3 ≤ q3 := by
                  have : 2 ≤ q3 := hq3.two_le
                  omega
                rw [← hz_eq]
                exact odd_prime_power_ge_841 (Nat.nth Nat.Prime (n-1)) q3 u3 h_ge509 hq3 h_u3 hq3_ge3 hp_n_lt_z
              have hp_succ_le_839 : Nat.nth Nat.Prime n ≤ 839 := by
                have : n - 1 < 144 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 144 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                  omega
                have : n ≤ 144 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 144 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 144 = 829 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 829 by decide)
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              omega
            · have hp_succ_le_509 : Nat.nth Nat.Prime n ≤ 509 := by
                have : n - 1 < 97 := by
                  by_contra hc
                  have : Nat.nth Nat.Prime 97 ≤ Nat.nth Nat.Prime (n - 1) := by
                    rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                    omega
                  have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                  omega
                have : n ≤ 97 := by omega
                have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 97 := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 97 = 509 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 509 by decide)
                omega
              have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
              omega
          · have hp_succ_le_251 : Nat.nth Nat.Prime n ≤ 251 := by
              have : n - 1 < 54 := by
                by_contra hc
                have : Nat.nth Nat.Prime 54 ≤ Nat.nth Nat.Prime (n - 1) := by
                  rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                  omega
                have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
                omega
              have : n ≤ 54 := by omega
              have : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime 54 := by
                rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
                omega
              have : Nat.nth Nat.Prime 54 = 251 := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 251 by decide)
                omega
            have : z < Nat.nth Nat.Prime n := hz_lt_p_succ
            omega
    · omega
