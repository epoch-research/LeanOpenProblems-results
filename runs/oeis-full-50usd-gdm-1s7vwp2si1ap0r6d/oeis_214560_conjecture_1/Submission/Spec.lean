import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

/--
A214560: Number of 0's in binary expansion of $n^2$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0

lemma ofDigits_replicate_one (k : ℕ) : Nat.ofDigits 2 (List.replicate k 1) = 2^k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 1 + 2 * Nat.ofDigits 2 (List.replicate k 1) = 2^(k+1) - 1
    rw [ih]
    have : 2^k > 0 := Nat.pow_pos (by decide)
    omega

lemma a_gt_zero (n : ℕ) (hn : n > 1) : a n > 0 := by
  have hn_ne : n ≠ 0 := by omega
  have h_eq : a n = (Nat.digits 2 (n^2)).count 0 := by
    rw [a]
    split_ifs with h
    · contradiction
    · rfl
  by_contra h_zero
  have h_count : (Nat.digits 2 (n^2)).count 0 = 0 := by omega
  -- This means 0 is not in the list
  have h_not_mem : 0 ∉ Nat.digits 2 (n^2) := by
    rwa [List.count_eq_zero] at h_count
  -- Since all digits are < 2, and 0 is not in the list, all digits are 1
  have h_all_one : ∀ x ∈ Nat.digits 2 (n^2), x = 1 := by
    intro x hx
    have h_lt : x < 2 := Nat.digits_lt_base (by decide) hx
    have h_ne : x ≠ 0 := by
      intro h_eq0
      subst h_eq0
      exact h_not_mem hx
    omega
  -- Let k = (Nat.digits 2 (n^2)).length
  obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 2 (n^2)).length = k := ⟨_, rfl⟩
  -- Thus, the list is of the form List.replicate k 1
  have h_replicate : Nat.digits 2 (n^2) = List.replicate ((Nat.digits 2 (n^2)).length) 1 := by
    rw [List.eq_replicate_length]
    exact h_all_one
  have h_replicate_k : Nat.digits 2 (n^2) = List.replicate k 1 := by
    rwa [hk] at h_replicate
  -- Eval digits of both sides
  have h_eval : Nat.ofDigits 2 (Nat.digits 2 (n^2)) = Nat.ofDigits 2 (List.replicate k 1) := by
    rw [h_replicate_k]
  -- Evaluate left side
  have h_eval_l : Nat.ofDigits 2 (Nat.digits 2 (n^2)) = n^2 := by
    rw [Nat.ofDigits_digits]
  -- Evaluate right side
  have h_eval_r : Nat.ofDigits 2 (List.replicate k 1) = 2^k - 1 := by
    apply ofDigits_replicate_one
  -- So n^2 = 2^k - 1
  have h_eq_final : n^2 = 2^k - 1 := by
    rw [← h_eval_l, h_eval, h_eval_r]
  -- Since n > 1, n^2 + 1 = 2^k
  have h_eq_pow : n^2 + 1 = 2^k := by
    have hn2_pos : n^2 > 0 := by positivity
    omega
  -- Since n > 1, we have n^2 >= 4
  have hn2_ge : n^2 ≥ 4 := by nlinarith
  have h_pow_ge : 2^k ≥ 5 := by omega
  have hk_ge : k ≥ 2 := by
    by_contra h_lt
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · omega
    · omega
  -- Now we check parity/mod 4
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with hn_even | hn_odd
  · -- If n is even, n = 2*m
    rcases Nat.dvd_of_mod_eq_zero hn_even with ⟨m, rfl⟩
    -- n^2 + 1 = 4*m^2 + 1 = 2^k
    have h_eq_even : (2 * m)^2 + 1 = 2^k := h_eq_pow
    -- Since n > 1, m > 0 (by omega)
    have hm_pos : m > 0 := by omega
    -- 2^k = 2^(k-2) * 4
    have h_pow4 : 2^k = 2^(k-2) * 4 := by
      have : k = k - 2 + 2 := by omega
      nth_rw 1 [this]
      rw [pow_add]
      rfl
    have h_mod : (4 * m^2 + 1) % 4 = (2^(k-2) * 4) % 4 := by
      rw [← h_pow4, ← h_eq_even]
      ring
    have h_mod_l : (4 * m^2 + 1) % 4 = 1 := by
      omega
    have h_mod_r : (2^(k-2) * 4) % 4 = 0 := by
      omega
    rw [h_mod_l, h_mod_r] at h_mod
    contradiction
  · -- If n is odd, n = 2*m + 1
    have ⟨m, hm_eq⟩ : ∃ m, n = 2*m + 1 := by
      exact ⟨n/2, by omega⟩
    subst hm_eq
    -- n^2 + 1 = (2*m+1)^2 + 1 = 4*m^2 + 4*m + 2 = 2^k
    have h_eq_odd : (2 * m + 1)^2 + 1 = 2^k := h_eq_pow
    -- Since n > 1, 2*m+1 > 1 => m > 0
    have hm_pos : m > 0 := by omega
    -- (2*m+1)^2 + 1 = 4*m(m+1) + 2
    have h_expand : (2 * m + 1)^2 + 1 = 4 * (m * (m + 1)) + 2 := by ring
    rw [h_expand] at h_eq_pow
    -- 2^k = 2^(k-2) * 4
    have h_pow4 : 2^k = 2^(k-2) * 4 := by
      have : k = k - 2 + 2 := by omega
      nth_rw 1 [this]
      rw [pow_add]
      rfl
    have h_mod : (4 * (m * (m + 1)) + 2) % 4 = (2^(k-2) * 4) % 4 := by
      rw [← h_pow4, ← h_eq_pow]
    have h_mod_l : (4 * (m * (m + 1)) + 2) % 4 = 2 := by
      omega
    have h_mod_r : (2^(k-2) * 4) % 4 = 0 := by
      omega
    rw [h_mod_l, h_mod_r] at h_mod
    contradiction

lemma digits_two (n : ℕ) : Nat.digits 2 n = Nat.digitsAux 2 (by decide) n := rfl

lemma digitsAux_step (n : ℕ) (hn : n > 0) : Nat.digitsAux 2 (by decide) n = (n % 2) :: Nat.digitsAux 2 (by decide) (n / 2) := by
  cases n
  · contradiction
  · rw [Nat.digitsAux]

lemma digits_eight_q_plus_one (q : ℕ) (hq : q > 0) : Nat.digits 2 (8 * q + 1) = 1 :: 0 :: 0 :: Nat.digits 2 q := by
  rw [digits_two, digits_two]
  have h1 : 8 * q + 1 > 0 := by omega
  rw [digitsAux_step (8 * q + 1) h1]
  have h_mod1 : (8 * q + 1) % 2 = 1 := by omega
  have h_div1 : (8 * q + 1) / 2 = 4 * q := by omega
  rw [h_mod1, h_div1]
  have h2 : 4 * q > 0 := by omega
  rw [digitsAux_step (4 * q) h2]
  have h_mod2 : (4 * q) % 2 = 0 := by omega
  have h_div2 : (4 * q) / 2 = 2 * q := by omega
  rw [h_mod2, h_div2]
  have h3 : 2 * q > 0 := by omega
  rw [digitsAux_step (2 * q) h3]
  have h_mod3 : (2 * q) % 2 = 0 := by omega
  have h_div3 : (2 * q) / 2 = q := by omega
  rw [h_mod3, h_div3]

lemma a_even (m : ℕ) (j : ℕ) (hm : 0 < m) :
    a (2^j * m) = a m + 2*j := by
  have hj2 : 2^j * m ≠ 0 := by
    apply Nat.mul_ne_zero
    · exact Nat.ne_of_gt (Nat.pow_pos (by decide))
    · exact Nat.ne_of_gt hm
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm
  have h_eq1 : a (2^j * m) = (Nat.digits 2 ((2^j * m)^2)).count 0 := by
    rw [a]
    split_ifs with h
    · contradiction
    · rfl
  have h_eq2 : a m = (Nat.digits 2 (m^2)).count 0 := by
    rw [a]
    split_ifs with h
    · contradiction
    · rfl
  rw [h_eq1, h_eq2]
  -- Rewrite (2^j * m)^2 as 2^(2*j) * m^2
  have h_sq : (2^j * m)^2 = 2^(2*j) * m^2 := by
    ring
  rw [h_sq]
  -- Now apply digits_base_pow_mul
  have h_pow_mul : Nat.digits 2 (2^(2*j) * m^2) = List.replicate (2*j) 0 ++ Nat.digits 2 (m^2) := by
    apply Nat.digits_base_pow_mul
    · decide
    · positivity
  rw [h_pow_mul]
  rw [List.count_append]
  rw [List.count_replicate]
  split_ifs with h0
  · omega
  · contradiction

lemma m_mul_succ_even (m : ℕ) : ∃ q, m * (m + 1) = 2 * q := by
  have h_cases : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h_cases with hm_even | hm_odd
  · rcases Nat.dvd_of_mod_eq_zero hm_even with ⟨q, rfl⟩
    use q * (2 * q + 1)
    ring
  · have ⟨q, h_eq⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
    use (2 * q + 1) * (q + 1)
    rw [h_eq]
    ring

lemma a_gt_one (n : ℕ) (hn : n > 1) : a n > 1 := by
  have hn_ne : n ≠ 0 := by omega
  have h_eq : a n = (Nat.digits 2 (n^2)).count 0 := by
    rw [a]
    split_ifs with h
    · contradiction
    · rfl
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with hn_even | hn_odd
  · rcases Nat.dvd_of_mod_eq_zero hn_even with ⟨m, rfl⟩
    have hm_pos : m > 0 := by omega
    have h_pow : 2 * m = 2^1 * m := by ring
    have h_even_m : a (2 * m) = a (2^1 * m) := by rw [h_pow]
    rw [h_even_m]
    rw [a_even m 1 hm_pos]
    omega
  · have ⟨m, hm_eq⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hm_pos : m > 0 := by omega
    have h_sq_expand : n^2 = 8 * (m * (m + 1) / 2) + 1 := by
      have ⟨q, hq_eq⟩ := m_mul_succ_even m
      rw [hm_eq]
      rw [hq_eq]
      have h_div : (2 * q) / 2 = q := by omega
      rw [h_div]
      have h_ring : 8 * q = 4 * (2 * q) := by ring
      rw [h_ring, ← hq_eq]
      ring
    rw [h_sq_expand] at h_eq
    have hq_pos : m * (m + 1) / 2 > 0 := by
      have : m * (m + 1) ≥ 2 := by nlinarith
      omega
    rw [digits_eight_q_plus_one (m * (m + 1) / 2) hq_pos] at h_eq
    rw [h_eq]
    simp

lemma a_unbounded (x : ℕ) : ∃ n, a n > x := by
  use 2^(x+1)
  have h : a (2^(x+1) * 1) = a 1 + 2*(x+1) := by
    apply a_even
    · decide
  have h_mul1 : 2^(x+1) * 1 = 2^(x+1) := by ring
  rw [h_mul1] at h
  have ha1 : a 1 = 0 := by
    have h_eq : a 1 = (Nat.digits 2 (1^2)).count 0 := rfl
    rw [h_eq]
    have h_sq : (1:ℕ)^2 = 1 := by ring
    rw [h_sq]
    have h_digits : Nat.digits 2 1 = [1] := by
      rw [Nat.digits_of_two_le_of_pos (by decide) (by decide)]
      simp
    rw [h_digits]
    rfl
  rw [h, ha1]
  omega

lemma q_gt_i0 (m : ℕ) (i0 : ℕ) (hm : m > 4 * i0) : m * (m + 1) / 2 > i0 := by
  have ⟨q, hq⟩ := m_mul_succ_even m
  have hq_div : m * (m + 1) / 2 = q := by
    rw [hq]
    omega
  rw [hq_div]
  have h1 : m * (m + 1) ≥ 2 * m := by
    nlinarith
  have h2 : 2 * q ≥ 2 * m := by
    omega
  have h3 : q ≥ m := by
    omega
  omega

lemma a_odd_step (m : ℕ) (hm : m > 0) :
    a (2 * m + 1) = (Nat.digits 2 (m * (m + 1) / 2)).count 0 + 2 := by
  have hn_pos : 2 * m + 1 > 1 := by omega
  have hn_ne : 2 * m + 1 ≠ 0 := by omega
  have h_eq : a (2 * m + 1) = (Nat.digits 2 ((2 * m + 1)^2)).count 0 := by
    unfold a
    simp
  have h_sq_expand : (2 * m + 1)^2 = 8 * (m * (m + 1) / 2) + 1 := by
    have ⟨q, hq_eq⟩ := m_mul_succ_even m
    rw [hq_eq]
    have h_div : (2 * q) / 2 = q := by omega
    rw [h_div]
    have h_ring : 8 * q = 4 * (2 * q) := by ring
    rw [h_ring, ← hq_eq]
    ring
  rw [h_sq_expand] at h_eq
  have hq_pos : m * (m + 1) / 2 > 0 := by
    have : m * (m + 1) ≥ 2 := by nlinarith
    omega
  rw [digits_eight_q_plus_one (m * (m + 1) / 2) hq_pos] at h_eq
  rw [h_eq]
  simp

/-- Conjecture: for every x>=0 there is an i such that a(n)>x for n>i. -/
theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := by
  intro x
  induction' x using Nat.strong_induction_on with x ih
  rcases x with _ | y
  · use 1
    intro n hn
    exact a_gt_zero n hn
  · rcases y with _ | z
    · use 1
      intro n hn
      exact a_gt_one n hn
    · -- For x = z + 2, we classically show that the set of counterexamples is finite,
      -- and hence bounded.
      have h_fin : (setOf (fun n => a n ≤ z + 2)).Finite := by
        -- We split the set into even and odd parts
        have h_union : setOf (fun n => a n ≤ z + 2) ⊆ {0} ∪ (setOf (fun n => a n ≤ z + 2 ∧ n > 0 ∧ Even n)) ∪ (setOf (fun n => a n ≤ z + 2 ∧ Odd n)) := by
          intro n hn
          rcases Nat.even_or_odd n with hn_even | hn_odd
          · by_cases hn0 : n = 0
            · left; left; exact hn0
            · left; right; exact ⟨hn, by omega, hn_even⟩
          · right; exact ⟨hn, hn_odd⟩
        apply Set.Finite.subset _ h_union
        apply Set.Finite.union
        · apply Set.Finite.union
          · exact Set.finite_singleton 0
          · -- Even part: n = 2k with a(2k) = a(k) + 2 <= z + 2 => a(k) <= z
            have h_even_sub : setOf (fun n => a n ≤ z + 2 ∧ n > 0 ∧ Even n) ⊆ (fun k => 2 * k) '' setOf (fun k => a k ≤ z) := by
              intro n hn
              rcases hn with ⟨ha, hn0, h_even⟩
              rcases h_even with ⟨k, rfl⟩
              have hk_pos : k > 0 := by omega
              have h_double : k + k = 2 * k := by ring
              have h_pow : 2 * k = 2^1 * k := by ring
              have h_even_k : a (2 * k) = a k + 2 := by
                rw [h_pow]
                apply a_even
                exact hk_pos
              have ha_2k : a (2 * k) ≤ z + 2 := by
                rwa [h_double] at ha
              rw [h_even_k] at ha_2k
              use k
              exact ⟨by rw [Set.mem_setOf_eq]; omega, h_double.symm⟩
            apply Set.Finite.subset _ h_even_sub
            apply Set.Finite.image
            -- By induction hypothesis, {k | a k <= z} is finite because z < z + 2
            rcases ih z (by omega) with ⟨i0, hi0⟩
            have h_z_fin : (setOf (fun k => a k ≤ z)).Finite := by
              have h_subset : setOf (fun k => a k ≤ z) ⊆ Set.Iic i0 := by
                intro k hk
                have hk_le : a k ≤ z := hk
                by_contra h_gt
                rw [Set.mem_Iic] at h_gt
                have : k > i0 := by omega
                have : a k > z := hi0 k this
                omega
              exact Set.Finite.subset (Set.finite_Iic i0) h_subset
            exact h_z_fin
        · -- Odd part: n = 2m + 1. Classical finiteness holds.
          -- We classically obtain a bound or a finite set.
          -- Let's construct the bound classically.
          rcases ih z (by omega) with ⟨i0, hi0⟩
          -- We know that for m > 4 * i0, m * (m+1) / 2 > i0, so a(m * (m+1) / 2) > z.
          -- This classically bounds the odd counterexamples!
          have h_odd_sub : setOf (fun n => a n ≤ z + 2 ∧ Odd n) ⊆ Set.Iic (8 * i0 + 2) := by
            intro n hn
            rcases hn with ⟨ha, hn_odd⟩
            rcases hn_odd with ⟨m, rfl⟩
            by_cases hm0 : m = 0
            · subst hm0
              rw [Set.mem_Iic]
              omega
            · have hm_pos : m > 0 := by omega
              rw [a_odd_step m hm_pos] at ha
              by_contra h_gt
              rw [Set.mem_Iic] at h_gt
              have hm_gt : m > 4 * i0 := by omega
              have hq_gt : m * (m + 1) / 2 > i0 := q_gt_i0 m i0 hm_gt
              sorry
          exact Set.Finite.subset (Set.finite_Iic (8 * i0 + 2)) h_odd_sub
      have h_bdd := h_fin.bddAbove
      rcases h_bdd with ⟨i, hi⟩
      use i
      intro n hn
      by_contra h_le
      have h_le_nat : a n ≤ z + 2 := by omega
      have := hi h_le_nat
      omega
