import FormalConjectures.Util.ProblemImports

open Nat

lemma sqrt_succ_eq_sqrt_of_not_sq (x : ℕ) (hnot : x + 1 ≠ (sqrt (x + 1)) * (sqrt (x + 1))) : sqrt (x + 1) = sqrt x := by
  have h1 : sqrt x * sqrt x ≤ x := sqrt_le x
  have h2 : x < (sqrt x + 1) * (sqrt x + 1) := lt_succ_sqrt x
  have h3 : x + 1 ≤ (sqrt x + 1) * (sqrt x + 1) := by omega
  have h4 : x + 1 < (sqrt x + 1) * (sqrt x + 1) := by
    by_contra hc
    have hc' : x + 1 = (sqrt x + 1) * (sqrt x + 1) := by omega
    have h_sq : x + 1 = sqrt (x + 1) * sqrt (x + 1) := by
      have : sqrt (x + 1) = sqrt x + 1 := by
        rw [hc']
        exact sqrt_eq (sqrt x + 1)
      rw [this, ← hc']
    exact hnot h_sq
  have h5 : sqrt x * sqrt x ≤ x + 1 := by omega
  exact (eq_sqrt.mpr ⟨h5, h4⟩).symm

lemma sqrt_sq_sub_one (Q : ℕ) (hQ : Q ≥ 1) : sqrt (Q * Q - 1) = Q - 1 := by
  have h_eq : Q * Q - 1 = (Q - 1) * (Q - 1) + 2 * (Q - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hQ)
    simp [succ_mul, mul_succ]
    omega
  rw [h_eq]
  exact sqrt_add_eq (Q - 1) (by omega)

lemma sq_sub_one_sq (S : ℕ) (hS : S ≥ 2) : (S - 1) * (S - 1) = S * S - 2 * S + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [succ_mul, mul_succ]
  omega


lemma sq_sub_one_sq_add (S : ℕ) (hS : S ≥ 1) : (S - 1) * (S - 1) + 2 * S = S * S + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S ≠ 0)
  simp [succ_mul, mul_succ]
  omega


def P (n : ℕ) : Prop :=
  ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime ∧ p ≤ 16 * (sqrt (n + p)) + 1 ∧
    (p ≤ 11 → sqrt (n + p) ≤ 7)

lemma P_3 : P 3 := by
  use 2
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma P_step (n : ℕ) (hn : n ≥ 3) (h : P n) : P (n + 1) := by
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, hp_le, h_cond⟩ := h
  let S := sqrt (n + 1 + p)
  by_cases hsq : n + 1 + p = S * S
  · -- Case B: perfect square
    have hp_ge : p ≥ 2 := hp_prime.two_le
    have h_S_ge : S ≥ 2 := by
      have h1 : n + 1 + p ≥ 6 := by omega
      rw [hsq] at h1
      by_contra hc
      have : S ≤ 1 := by omega
      interval_cases S
      · omega
      · omega
    have h_sqrt_eq : sqrt (n + p) = S - 1 := by
      have : n + p = S * S - 1 := by omega
      rw [this]
      exact sqrt_sq_sub_one S (by omega)
    have hS_prime : (S - 1).Prime := by
      rw [← h_sqrt_eq]
      exact hsqrt_prime
    have hp_le_S : p ≤ 16 * S - 15 := by
      rw [h_sqrt_eq] at hp_le
      have : 16 * (S - 1) + 1 = 16 * S - 15 := by omega
      omega
    by_cases h_B1 : p ≤ 2 * S - 1
    · -- Subcase B1: p <= 2 * S - 1
      by_cases hS8 : S ≤ 8
      · interval_cases S
        · have : (S - 1).Prime := hS_prime
          contradiction
        · interval_cases p
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
        · interval_cases p
          · use 11; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
        · have : (S - 1).Prime := hS_prime
          contradiction
        · interval_cases p
          · use 17; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
        · have : (S - 1).Prime := hS_prime
          contradiction
        · interval_cases p
          · use 59; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
          · use 2; refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · have h_S_ge9 : S ≥ 9 := by omega
        have h_S_ge12 : S ≥ 12 := by
          by_contra hc
          have : S = 9 ∨ S = 10 ∨ S = 11 := by omega
          rcases this with rfl | rfl | rfl
          · have : (8 : ℕ).Prime := hS_prime
            contradiction
          · have : (9 : ℕ).Prime := hS_prime
            contradiction
          · have : (10 : ℕ).Prime := hS_prime
            contradiction
        have hp_ge13 : p ≥ 13 := by
          by_contra hc
          have : p ≤ 11 := by omega
          have : sqrt (n + p) ≤ 7 := h_cond this
          rw [h_sqrt_eq] at this
          omega
        by_cases hp13 : p = 13
        · use 17
          refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
          · omega
          · have h_eq : sqrt (n + 1 + 17) = S - 1 := by
              have h_id : (S - 1) * (S - 1) + 2 * S = S * S + 1 := sq_sub_one_sq_add S (by omega)
              have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
              refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
              · omega
              · rw [hS_eq]; omega
            rw [h_eq]
            exact hS_prime
          · have h_eq : sqrt (n + 1 + 17) = S - 1 := by
              have h_id : (S - 1) * (S - 1) + 2 * S = S * S + 1 := sq_sub_one_sq_add S (by omega)
              have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
              refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
              · omega
              · rw [hS_eq]; omega
            rw [h_eq]
            omega
          · intro hc
            contradiction
        · have hp_ge17 : p ≥ 17 := by
            by_contra hc
            have : p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 := by omega
            rcases this with rfl | rfl | rfl | rfl
            · contradiction
            · norm_num at hp_prime
            · norm_num at hp_prime
            · norm_num at hp_prime
          use 13
          refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
          · omega
          · have h_eq : sqrt (n + 1 + 13) = S - 1 := by
              have h_id : (S - 1) * (S - 1) + 2 * S = S * S + 1 := sq_sub_one_sq_add S (by omega)
              have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
              refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
              · omega
              · rw [hS_eq]; omega
            rw [h_eq]
            exact hS_prime
          · have h_eq : sqrt (n + 1 + 13) = S - 1 := by
              have h_id : (S - 1) * (S - 1) + 2 * S = S * S + 1 := sq_sub_one_sq_add S (by omega)
              have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
              refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
              · omega
              · rw [hS_eq]; omega
            rw [h_eq]
            omega
          · intro hc
            contradiction
    · -- Subcase B2: p > 2 * S - 1
      have hp_gt : p > 2 * S - 1 := by omega
      have hk_ne_zero : (p - 1) / 2 ≠ 0 := by omega
      obtain ⟨p', hp'_prime, hp'1, hp'_le⟩ := exists_prime_lt_and_le_two_mul ((p - 1) / 2) hk_ne_zero
      use p'
      have hp'_lt_n1 : p' < n + 1 := by omega
      have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
      have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
      have h_eq : sqrt (n + 1 + p') = S - 1 := by
        have h_sqrt : S - 1 = sqrt (n + 1 + p') := by
          refine eq_sqrt.mpr ⟨?_, ?_⟩
          · -- (S - 1) * (S - 1) <= n + 1 + p'
            rw [sq_sub_one_sq S (by omega)]
            have : n + 1 = S * S - p := by omega
            omega
          · -- n + 1 + p' < S * S
            have h_cancel : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
            rw [h_cancel]
            have : n + 1 = S * S - p := by omega
            omega
        exact h_sqrt.symm
      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_⟩
      · rwa [h_eq]
      · rw [h_eq]
        have h_arith : 16 * (S - 1) + 1 = 16 * S - 15 := by omega
        rw [h_arith]
        omega
      · intro hp'11
        rw [h_eq]
        -- S - 1 <= 7
        -- We show S <= 8
        -- If S >= 9 => S >= 12.
        -- Since p > 2S - 1 => p > 23 => p >= 29.
        -- So (p - 1) / 2 >= 14.
        -- So p' >= 17, which contradicts p' <= 11!
        have h_S_ge12 : S ≥ 12 := by
          by_contra hc
          have : S = 9 ∨ S = 10 ∨ S = 11 := by omega
          rcases this with rfl | rfl | rfl
          · have : (8 : ℕ).Prime := hS_prime
            contradiction
          · have : (9 : ℕ).Prime := hS_prime
            contradiction
          · have : (10 : ℕ).Prime := hS_prime
            contradiction
        have hp_ge29 : p ≥ 29 := by omega
        have hp'_ge17 : p' ≥ 17 := by omega
        omega
  · -- Case A: not a perfect square
    use p
    have h_not : n + p + 1 ≠ (sqrt (n + p + 1)) * (sqrt (n + p + 1)) := by
      have h_assoc : n + p + 1 = n + 1 + p := by omega
      rwa [h_assoc]
    have h_eq : sqrt (n + 1 + p) = sqrt (n + p) := by
      have h_assoc : n + 1 + p = n + p + 1 := by omega
      rw [h_assoc]
      exact sqrt_succ_eq_sqrt_of_not_sq (n + p) h_not
    refine ⟨hp_prime, by omega, ?_, ?_, ?_⟩
    · rwa [h_eq]
    · rwa [h_eq]
    · intro hp11
      rw [h_eq]
      exact h_cond hp11

lemma P_all (n : ℕ) (hn : n ≥ 3) : P n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n < 3
    · have : n = 2 := by omega
      subst this
      exact P_3
    · have hn3 : n ≥ 3 := by omega
      exact P_step n hn3 (ih hn3)




