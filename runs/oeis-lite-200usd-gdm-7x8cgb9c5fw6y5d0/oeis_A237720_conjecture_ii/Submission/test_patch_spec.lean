import FormalConjectures.Util.ProblemImports
open Nat

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt Nat.sqrt.iter

def P (n : ℕ) : Prop :=
  ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime ∧ p ≤ 16 * (sqrt (n + p)) + 1 ∧
    (p = 2 → n ≤ 193) ∧ (p = 3 → n ≤ 192) ∧
    (p = 5 → n ≤ 191) ∧ (p = 7 → n ≤ 190) ∧ (p = 11 → n ≤ 189) ∧
    (p = 13 → n ≤ 188) ∧ (p = 17 → n ≤ 187) ∧ (p = 19 → n ≤ 186) ∧
    (p = 23 → n ≤ 185) ∧ (p = 29 → n ≤ 184) ∧ (p = 31 → n ≤ 183) ∧
    (p = 37 → n ≤ 182) ∧
    (sqrt (n + p) ≥ 18 → p ≤ 4 * (sqrt (n + p)) - 2)

lemma P_100000 : P 100000 := by
  use 491
  decide

lemma sq_sub_one_sq (S : ℕ) (hS : S ≥ 2) : (S - 1) * (S - 1) = S * S - 2 * S + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [succ_mul, mul_succ]
  omega

lemma sqrt_sq_sub_one (Q : ℕ) (hQ : Q ≥ 1) : sqrt (Q * Q - 1) = Q - 1 := by
  have h_eq : Q * Q - 1 = (Q - 1) * (Q - 1) + 2 * (Q - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hQ)
    simp [succ_mul, mul_succ]
    omega
  rw [h_eq]
  exact sqrt_add_eq (Q - 1) (by omega)

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

lemma P_step (n : ℕ) (hn : n ≥ 100000) (h : P n) : P (n + 1) := by
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, hp_le, h_cond2, h_cond3, h_cond5, h_cond6, h_cond7, h_cond8, h_cond9, h_cond10, h_cond11, h_cond12, h_cond13, h_cond14, h_cond4⟩ := h
  let S := sqrt (n + 1 + p)
  by_cases hsq : n + 1 + p = S * S
  · -- Case B: perfect square
    have h_S_eq : sqrt (n + 1 + p) = S := rfl
    have hp_ge2 : p ≥ 2 := hp_prime.two_le
    have h_S_ge : S ≥ 316 := by
      have : n + 1 + p ≥ 100003 := by omega
      have h_sq : 99856 ≤ n + 1 + p := by omega
      rw [← h_S_eq]
      exact Nat.le_sqrt.mpr h_sq
    have h_S_sq_ge1 : S * S ≥ 1 := by omega
    have h_sqrt_eq : sqrt (n + p) = S - 1 := by
      have : n + p = S * S - 1 := by omega
      rw [this]
      exact sqrt_sq_sub_one S (by omega)
    have hS_prime : (S - 1).Prime := by
      rw [← h_sqrt_eq]
      exact hsqrt_prime
    have hS_ge1 : S ≥ 1 := by omega
    have hS_ge2 : S ≥ 2 := by omega
    have h_S_sq_ge_2S : S * S ≥ 2 * S := Nat.mul_le_mul_right S hS_ge2
    have hp_ge13 : p ≥ 13 := by
      by_contra hc
      have : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · have : n ≤ 193 := h_cond2 rfl
        omega
      · have : n ≤ 192 := h_cond3 rfl
        omega
      · have : n ≤ 191 := h_cond5 rfl
        omega
      · have : n ≤ 190 := h_cond6 rfl
        omega
      · have : n ≤ 189 := h_cond7 rfl
        omega
    by_cases hp_gt : p > 2 * S - 1
    · -- Case B2: p > 2 * S - 1
      have hk_ne_zero : (p - 1) / 2 ≠ 0 := by omega
      have hp_le_4S : p ≤ 4 * (S - 1) - 2 := by
        have : sqrt (n + p) = S - 1 := h_sqrt_eq
        have h_cond_premise : sqrt (n + p) ≥ 18 := by omega
        have h_val := h_cond4 h_cond_premise
        rwa [this] at h_val
      obtain ⟨p', hp'_prime, hp'1, hp'_le⟩ := exists_prime_lt_and_le_two_mul ((p - 1) / 2) hk_ne_zero
      use p'
      have hp'_lt_n1 : p' < n + 1 := by omega
      have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
      have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
      have h_eq : sqrt (n + 1 + p') = S - 1 := by
        have h_sqrt : S - 1 = sqrt (n + 1 + p') := by
          refine eq_sqrt.mpr ⟨?_, ?_⟩
          · -- (S - 1) * (S - 1) <= n + 1 + p'
            have hp_odd : p % 2 = 1 := by
              rcases hp_prime.eq_two_or_odd with rfl | hp_odd
              · omega
              · exact hp_odd
            calc (S - 1) * (S - 1)
              _ = S * S - 2 * S + 1 := by rw [sq_sub_one_sq S hS_ge2]
              _ = n + 1 + p - 2 * S + 1 := by rw [← hsq]
              _ ≤ n + 1 + p' := by omega
          · -- n + 1 + p' < S * S
            have h_cancel : S - 1 + 1 = S := Nat.sub_add_cancel hS_ge1
            rw [h_cancel]
            have : n + 1 = S * S - p := by omega
            omega
        exact h_sqrt.symm
      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [h_eq]
      · rw [h_eq]
        omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc; omega
      · intro hc
        rw [h_eq] at hc
        omega
    · -- Case B1: p <= 2 * S - 1
      have hp_le_2S : p ≤ 2 * S - 1 := by omega
      by_cases hp13 : p = 13
      · subst hp13
        have h_eq : sqrt (n + 1 + 11) = S - 1 := by
          have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel hS_ge1
          generalize h_S_sq_eq : S * S = S_sq at *
          have hn_eq : n + 1 = S_sq - 13 := by omega
          refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
          · calc (S - 1) * (S - 1)
              _ = S * S - 2 * S + 1 := by rw [sq_sub_one_sq S hS_ge2]
              _ = n + 1 + p - 2 * S + 1 := by rw [← hsq]
              _ ≤ n + 1 + 11 := by omega
          · rw [hS_eq, hn_eq]
            omega
        use 11
        refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · rw [h_eq]
          exact hS_prime
        · rw [h_eq]
          omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc
          rw [h_eq]
          omega
      · have hp_ge17 : p ≥ 17 := by
          by_contra hc
          have : p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · contradiction
          · norm_num at hp_prime
          · norm_num at hp_prime
          · norm_num at hp_prime
        have h_eq : sqrt (n + 1 + 13) = S - 1 := by
          have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel hS_ge1
          generalize h_S_sq_eq : S * S = S_sq at *
          have hn_eq : n + 1 = S_sq - p := by omega
          refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
          · calc (S - 1) * (S - 1)
              _ = S * S - 2 * S + 1 := by rw [sq_sub_one_sq S hS_ge2]
              _ = n + 1 + p - 2 * S + 1 := by rw [← hsq]
              _ ≤ n + 1 + 13 := by omega
          · rw [hS_eq, hn_eq]
            omega
        use 13
        refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · rw [h_eq]
          exact hS_prime
        · rw [h_eq]
          omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc; omega
        · intro hc
          rw [h_eq]
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
    refine ⟨hp_prime, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [h_eq]
    · rwa [h_eq]
    · intro hc
      have h_cond_p : n ≤ 193 := h_cond2 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 192 := h_cond3 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 191 := h_cond5 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 190 := h_cond6 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 189 := h_cond7 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 188 := h_cond8 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 187 := h_cond9 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 186 := h_cond10 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 185 := h_cond11 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 184 := h_cond12 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 183 := h_cond13 hc
      omega
    · intro hc
      have h_cond_p : n ≤ 182 := h_cond14 hc
      omega
    · intro hc
      rw [h_eq] at hc
      have := h_cond4 hc
      rwa [h_eq]

lemma P_all (n : ℕ) (hn : n ≥ 100000) : P n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n < 100000
    · have : n + 1 = 100000 := by omega
      rw [this]
      exact P_100000
    · have hn_ge : n ≥ 100000 := by omega
      exact P_step n hn_ge (ih hn_ge)
