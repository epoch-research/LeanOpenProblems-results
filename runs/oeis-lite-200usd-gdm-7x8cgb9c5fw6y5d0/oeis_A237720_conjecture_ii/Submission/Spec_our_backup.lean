import FormalConjectures.Util.ProblemImports
open Nat Finset
open scoped Nat.Prime
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt Nat.sqrt.iter

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 \rfloor$ with \\lfloor \sqrt298 \\rfloor prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

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
    (p ≤ 11 ∧ n ≤ 182 → sqrt (n + p) ≤ 7) ∧
    (p = 2 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 3 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧
    (p = 5 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 7 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 11 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧
    (p = 13 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 17 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 19 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧
    (p = 23 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 29 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧ (p = 31 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧
    (p = 37 ∧ sqrt (n + p) ≤ 316 → n ≤ 300) ∧
    (sqrt (n + p) ≥ 18 → p ≤ 4 * (sqrt (n + p)) - 2)

lemma P_3 : P 3 := by
  use 2
  decide

lemma P_step (n : ℕ) (hn : n ≥ 301) (h : P n) : P (n + 1) := by
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, hp_le, h_cond1, h_cond2, h_cond3, h_cond5, h_cond6, h_cond7, h_cond8, h_cond9, h_cond10, h_cond11, h_cond12, h_cond13, h_cond14, h_cond4⟩ := h
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
      have : n + p = S * S - 1 := by
        generalize h_S_sq : S * S = S_sq at hsq ⊢
        omega
      rw [this]
      exact sqrt_sq_sub_one S (by omega)
    have hS_prime : (S - 1).Prime := by
      rw [← h_sqrt_eq]
      exact hsqrt_prime
    have hp_le_S : p ≤ 16 * S - 15 := by
      rw [h_sqrt_eq] at hp_le
      have : 16 * (S - 1) + 1 = 16 * S - 15 := by omega
      omega
    -- Since n >= 301, n + 1 >= 302.
    -- n + 1 + p >= 304.
    -- S * S = n + 1 + p >= 304.
    -- So S >= 18.
    have h_S_ge18 : S ≥ 18 := by
      by_contra hc
      have : S ≤ 17 := by omega
      have : S * S ≤ 289 := by nlinarith
      omega
    have h_S_sq : S * S ≥ 324 := by nlinarith
    have h_S_sq2 : S * S - 2 * S + 1 ≥ 289 := by
      have h1 : (S - 1) * (S - 1) ≥ 289 := by
        have : S - 1 ≥ 17 := by omega
        nlinarith
      rwa [sq_sub_one_sq S (by omega)] at h1
    have hS_ge1 : S ≥ 1 := by omega
    have hS_ge2 : S ≥ 2 := by omega
    have h_S_sq_ge_2S : S * S ≥ 2 * S := Nat.mul_le_mul_right S hS_ge2
    have h_S_sq_ge_p : S * S ≥ p := by omega
    by_cases h_S_317 : S ≤ 317
    · have h_sqrt_le316 : sqrt (n + p) ≤ 316 := by
        rw [h_sqrt_eq]
        omega
      have hp_gt37 : p > 37 := by
        by_contra hc
        have : p ≤ 37 := by omega
        have h_cond_case : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 := by
          interval_cases p
          · decide
          · decide
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · decide
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
          · decide
        rcases h_cond_case with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have : n ≤ 300 := h_cond2 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond3 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond5 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond6 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond7 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond8 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond9 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond10 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond11 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond12 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond13 ⟨by decide, h_sqrt_le316⟩
          omega
        · have : n ≤ 300 := h_cond14 ⟨by decide, h_sqrt_le316⟩
          omega
      -- Since p > 37, we can use Bertrand's postulate!
      have hk_ne_zero : (p - 1) / 2 ≠ 0 := by omega
      obtain ⟨p', hp'_prime, hp'1, hp'_le⟩ := exists_prime_lt_and_le_two_mul ((p - 1) / 2) hk_ne_zero
      use p'
      have hp'_lt_n1 : p' < n + 1 := by omega
      have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
      have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
      have h_S_ge19 : S ≥ 19 := by
        by_contra hc
        have : S ≤ 18 := by omega
        have : S * S ≤ 324 := by nlinarith
        omega
      have hp_le_S_cond : p ≤ 4 * S - 6 := by
        have h_sqrt_ge18 : sqrt (n + p) ≥ 18 := by omega
        have := h_cond4 h_sqrt_ge18
        omega
      have hp_odd : p % 2 = 1 := by
        rcases hp_prime.eq_two_or_odd with rfl | hp_odd
        · omega
        · exact hp_odd
      have h_eq : sqrt (n + 1 + p') = S - 1 := by
        have h_sqrt : S - 1 = sqrt (n + 1 + p') := by
          refine eq_sqrt.mpr ⟨?_, ?_⟩
          · -- (S - 1) * (S - 1) <= n + 1 + p'
            rw [sq_sub_one_sq S hS_ge2]
            have : n + 1 = S * S - p := by
              generalize h_S_sq : S * S = S_sq at hsq ⊢
              omega
            rw [this]
            generalize h_S_sq_eq : S * S = S_sq at h_S_sq_ge_2S h_S_sq_ge_p ⊢
            omega
          · -- n + 1 + p' < S * S
            have h_cancel : S - 1 + 1 = S := Nat.sub_add_cancel hS_ge1
            rw [h_cancel]
            have : n + 1 = S * S - p := by
              generalize h_S_sq : S * S = S_sq at hsq ⊢
              omega
            rw [this]
            generalize h_S_sq_eq : S * S = S_sq at h_S_sq_ge_2S h_S_sq_ge_p ⊢
            omega
        exact h_sqrt.symm
      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_eq]; exact hS_prime
      · rw [h_eq]; omega
      · intro hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; rw [h_eq]; omega
    · -- Now we know S >= 318!
      have h_eq : sqrt (n + 1 + 2) = S - 1 := by
        have h_sqrt : S - 1 = sqrt (n + 1 + 2) := by
          refine eq_sqrt.mpr ⟨?_, ?_⟩
          · -- (S - 1) * (S - 1) <= n + 1 + 2
            rw [sq_sub_one_sq S hS_ge2]
            have : n + 1 = S * S - p := by
              generalize h_S_sq : S * S = S_sq at hsq ⊢
              omega
            rw [this]
            generalize h_S_sq_eq : S * S = S_sq at h_S_sq_ge_2S h_S_sq_ge_p ⊢
            omega
          · -- n + 1 + 2 < S * S
            have h_cancel : S - 1 + 1 = S := Nat.sub_add_cancel hS_ge1
            rw [h_cancel]
            have : n + 1 = S * S - p := by
              generalize h_S_sq : S * S = S_sq at hsq ⊢
              omega
            rw [this]
            generalize h_S_sq_eq : S * S = S_sq at h_S_sq_ge_2S h_S_sq_ge_p ⊢
            omega
        exact h_sqrt.symm
      use 2
      refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · rw [h_eq]; exact hS_prime
      · rw [h_eq]; omega
      · intro hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; omega
      · intro hc; rw [h_eq] at hc; rw [h_eq]; omega
  · -- Case A: not a perfect square
    use p
    have h_not : n + p + 1 ≠ (sqrt (n + p + 1)) * (sqrt (n + p + 1)) := by
      have h_assoc : n + p + 1 = n + 1 + p := by omega
      rwa [h_assoc]
    have h_eq : sqrt (n + 1 + p) = sqrt (n + p) := by
      have h_assoc : n + 1 + p = n + p + 1 := by omega
      rw [h_assoc]
      exact sqrt_succ_eq_sqrt_of_not_sq (n + p) h_not
    refine ⟨hp_prime, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 3
      rwa [h_eq]
    · -- 4
      rwa [h_eq]
    · -- 5
      intro hc
      rw [h_eq]
      exact h_cond1 ⟨hc.1, by omega⟩
    · -- 6
      intro hc; rw [h_eq] at hc
      have h_premise : p = 2 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond2 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 7
      intro hc; rw [h_eq] at hc
      have h_premise : p = 3 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond3 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 8
      intro hc; rw [h_eq] at hc
      have h_premise : p = 5 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond5 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 9
      intro hc; rw [h_eq] at hc
      have h_premise : p = 7 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond6 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 10
      intro hc; rw [h_eq] at hc
      have h_premise : p = 11 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond7 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 11
      intro hc; rw [h_eq] at hc
      have h_premise : p = 13 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond8 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 12
      intro hc; rw [h_eq] at hc
      have h_premise : p = 17 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond9 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 13
      intro hc; rw [h_eq] at hc
      have h_premise : p = 19 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond10 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 14
      intro hc; rw [h_eq] at hc
      have h_premise : p = 23 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond11 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 15
      intro hc; rw [h_eq] at hc
      have h_premise : p = 29 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond12 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 16
      intro hc; rw [h_eq] at hc
      have h_premise : p = 31 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond13 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 17
      intro hc; rw [h_eq] at hc
      have h_premise : p = 37 ∧ sqrt (n + p) ≤ 316 := hc
      have hn_le := h_cond14 h_premise
      by_cases hn_eq : n = 300
      · subst hn_eq; revert hsqrt_prime h_not; decide
      · omega
    · -- 18
      intro hc
      rw [h_eq] at hc
      rw [h_eq]
      exact h_cond4 hc

lemma P_large (n : ℕ) (hn : n ≥ 300) : P n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n < 300
    · have : n + 1 = 300 := by omega
      rw [this]
      use 2
      decide
    · have hn_ge : n ≥ 300 := by omega
      exact P_step n hn_ge (ih hn_ge)

lemma P_all (n : ℕ) (hn : n ≥ 3) : P n := by
  by_cases h_lt : n < 300
  · interval_cases n
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 7; decide
    · use 7; decide
    · use 5; decide
    · use 5; decide
    · use 3; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 17; decide
    · use 17; decide
    · use 13; decide
    · use 13; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 7; decide
    · use 7; decide
    · use 5; decide
    · use 5; decide
    · use 3; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 47; decide
    · use 47; decide
    · use 47; decide
    · use 47; decide
    · use 43; decide
    · use 43; decide
    · use 41; decide
    · use 41; decide
    · use 41; decide
    · use 41; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 31; decide
    · use 31; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 19; decide
    · use 19; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 41; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 31; decide
    · use 31; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 19; decide
    · use 19; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 13; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 97; decide
    · use 97; decide
    · use 97; decide
    · use 97; decide
    · use 97; decide
    · use 97; decide
    · use 89; decide
    · use 89; decide
    · use 89; decide
    · use 89; decide
    · use 89; decide
    · use 89; decide
    · use 83; decide
    · use 83; decide
    · use 83; decide
    · use 83; decide
    · use 79; decide
    · use 79; decide
    · use 79; decide
    · use 79; decide
    · use 79; decide
    · use 79; decide
    · use 73; decide
    · use 73; decide
    · use 71; decide
    · use 71; decide
    · use 71; decide
    · use 71; decide
    · use 67; decide
    · use 67; decide
    · use 67; decide
    · use 67; decide
    · use 67; decide
    · use 67; decide
    · use 61; decide
    · use 61; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 59; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 53; decide
    · use 47; decide
    · use 47; decide
    · use 47; decide
    · use 47; decide
    · use 43; decide
    · use 43; decide
    · use 41; decide
    · use 41; decide
    · use 41; decide
    · use 41; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 37; decide
    · use 31; decide
    · use 31; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 29; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 23; decide
    · use 19; decide
    · use 19; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 17; decide
    · use 13; decide
    · use 13; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 11; decide
    · use 7; decide
    · use 7; decide
    · use 5; decide
    · use 5; decide
    · use 3; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
    · use 2; decide
  · have hn_ge : n ≥ 300 := by omega
    exact P_large n hn_ge

theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  have hn3 : n ≥ 3 := by omega
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, _⟩ := P_all n hn3
  exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
