import FormalConjectures.Util.ProblemImports
open Nat Finset
open scoped Nat.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

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
    (p = 2 → n ≤ 61) ∧ (sqrt (n + p) ≥ 12 → p ≤ 4 * (sqrt (n + p)) - 2)

lemma P_3 : P 3 := by
  use 2
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · have h_n : 3 + 2 = 5 := by omega
    rw [h_n]; norm_num
  · have h_n : 3 + 2 = 5 := by omega
    rw [h_n]; norm_num
  · intro hc; omega
  · have h_n : 3 + 2 = 5 := by omega
    intro hc; rw [h_n]; norm_num

lemma P_step (n : ℕ) (hn : n ≥ 3) (h : P n) : P (n + 1) := by
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, hp_le, h_cond, h_cond2⟩ := h
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
    have hp_le_S_sq : p ≤ S * S - 4 := by omega

    by_cases hS12 : S ≤ 12
    · interval_cases S
      · -- S = 2
        have h_S_prime : (2 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 3
        interval_cases p
        · -- p = 2
          use 2
          have h_n : n + 1 + 2 = 9 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 3
          use 2
          have h_n : n + 1 + 2 = 8 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 4
          norm_num at hp_prime
        · -- p = 5
          use 2
          have h_n : n + 1 + 2 = 6 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
      · -- S = 4
        interval_cases p
        · -- p = 2
          use 11
          have h_n : n + 1 + 11 = 25 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 3
          use 2
          have h_n : n + 1 + 2 = 15 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 4
          norm_num at hp_prime
        · -- p = 5
          use 2
          have h_n : n + 1 + 2 = 13 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 6
          norm_num at hp_prime
        · -- p = 7
          use 2
          have h_n : n + 1 + 2 = 11 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 8
          norm_num at hp_prime
        · -- p = 9
          norm_num at hp_prime
        · -- p = 10
          norm_num at hp_prime
        · -- p = 11
          use 2
          have h_n : n + 1 + 2 = 7 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 12
          norm_num at hp_prime
      · -- S = 5
        have h_S_prime : (5 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 6
        interval_cases p
        · -- p = 2
          use 17
          have h_n : n + 1 + 17 = 51 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 3
          use 2
          have h_n : n + 1 + 2 = 35 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 4
          norm_num at hp_prime
        · -- p = 5
          use 2
          have h_n : n + 1 + 2 = 33 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 6
          norm_num at hp_prime
        · -- p = 7
          use 2
          have h_n : n + 1 + 2 = 31 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 8
          norm_num at hp_prime
        · -- p = 9
          norm_num at hp_prime
        · -- p = 10
          norm_num at hp_prime
        · -- p = 11
          use 2
          have h_n : n + 1 + 2 = 27 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 12
          norm_num at hp_prime
        · -- p = 13
          use 2
          have h_n : n + 1 + 2 = 25 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 14
          norm_num at hp_prime
        · -- p = 15
          norm_num at hp_prime
        · -- p = 16
          norm_num at hp_prime
        · -- p = 17
          use 7
          have h_n : n + 1 + 7 = 26 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 18
          norm_num at hp_prime
        · -- p = 19
          use 11
          have h_n : n + 1 + 11 = 28 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 20
          norm_num at hp_prime
        · -- p = 21
          norm_num at hp_prime
        · -- p = 22
          norm_num at hp_prime
        · -- p = 23
          use 2
          have h_n : n + 1 + 2 = 15 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 24
          norm_num at hp_prime
        · -- p = 25
          norm_num at hp_prime
        · -- p = 26
          norm_num at hp_prime
        · -- p = 27
          norm_num at hp_prime
        · -- p = 28
          norm_num at hp_prime
        · -- p = 29
          use 2
          have h_n : n + 1 + 2 = 9 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 30
          norm_num at hp_prime
        · -- p = 31
          use 2
          have h_n : n + 1 + 2 = 7 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 32
          norm_num at hp_prime
      · -- S = 7
        have h_S_prime : (7 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 8
        interval_cases p
        · -- p = 2
          use 59
          have h_n : n + 1 + 59 = 121 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 3
          use 2
          have h_n : n + 1 + 2 = 63 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 4
          norm_num at hp_prime
        · -- p = 5
          use 2
          have h_n : n + 1 + 2 = 61 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 6
          norm_num at hp_prime
        · -- p = 7
          use 2
          have h_n : n + 1 + 2 = 59 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 8
          norm_num at hp_prime
        · -- p = 9
          norm_num at hp_prime
        · -- p = 10
          norm_num at hp_prime
        · -- p = 11
          use 2
          have h_n : n + 1 + 2 = 55 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 12
          norm_num at hp_prime
        · -- p = 13
          use 2
          have h_n : n + 1 + 2 = 53 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 14
          norm_num at hp_prime
        · -- p = 15
          norm_num at hp_prime
        · -- p = 16
          norm_num at hp_prime
        · -- p = 17
          use 2
          have h_n : n + 1 + 2 = 49 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 18
          norm_num at hp_prime
        · -- p = 19
          use 5
          have h_n : n + 1 + 5 = 50 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 20
          norm_num at hp_prime
        · -- p = 21
          norm_num at hp_prime
        · -- p = 22
          norm_num at hp_prime
        · -- p = 23
          use 11
          have h_n : n + 1 + 11 = 52 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 24
          norm_num at hp_prime
        · -- p = 25
          norm_num at hp_prime
        · -- p = 26
          norm_num at hp_prime
        · -- p = 27
          norm_num at hp_prime
        · -- p = 28
          norm_num at hp_prime
        · -- p = 29
          use 17
          have h_n : n + 1 + 17 = 52 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 30
          norm_num at hp_prime
        · -- p = 31
          use 2
          have h_n : n + 1 + 2 = 35 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 32
          norm_num at hp_prime
        · -- p = 33
          norm_num at hp_prime
        · -- p = 34
          norm_num at hp_prime
        · -- p = 35
          norm_num at hp_prime
        · -- p = 36
          norm_num at hp_prime
        · -- p = 37
          use 2
          have h_n : n + 1 + 2 = 29 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 38
          norm_num at hp_prime
        · -- p = 39
          norm_num at hp_prime
        · -- p = 40
          norm_num at hp_prime
        · -- p = 41
          use 2
          have h_n : n + 1 + 2 = 25 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 42
          norm_num at hp_prime
        · -- p = 43
          use 5
          have h_n : n + 1 + 5 = 26 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 44
          norm_num at hp_prime
        · -- p = 45
          norm_num at hp_prime
        · -- p = 46
          norm_num at hp_prime
        · -- p = 47
          use 11
          have h_n : n + 1 + 11 = 28 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 48
          norm_num at hp_prime
        · -- p = 49
          norm_num at hp_prime
        · -- p = 50
          norm_num at hp_prime
        · -- p = 51
          norm_num at hp_prime
        · -- p = 52
          norm_num at hp_prime
        · -- p = 53
          use 2
          have h_n : n + 1 + 2 = 13 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 54
          norm_num at hp_prime
        · -- p = 55
          norm_num at hp_prime
        · -- p = 56
          norm_num at hp_prime
        · -- p = 57
          norm_num at hp_prime
        · -- p = 58
          norm_num at hp_prime
        · -- p = 59
          use 2
          have h_n : n + 1 + 2 = 7 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 60
          norm_num at hp_prime
      · -- S = 9
        have h_S_prime : (9 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 10
        have h_S_prime : (10 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 11
        have h_S_prime : (11 - 1).Prime := hS_prime
        norm_num at h_S_prime
      · -- S = 12
        interval_cases p
        · -- p = 2
          use 29
          have h_n : n + 1 + 29 = 171 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 3
          use 29
          have h_n : n + 1 + 29 = 170 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 4
          norm_num at hp_prime
        · -- p = 5
          use 3
          have h_n : n + 1 + 3 = 142 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 6
          norm_num at hp_prime
        · -- p = 7
          use 3
          have h_n : n + 1 + 3 = 140 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 8
          norm_num at hp_prime
        · -- p = 9
          norm_num at hp_prime
        · -- p = 10
          norm_num at hp_prime
        · -- p = 11
          use 3
          have h_n : n + 1 + 3 = 136 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 12
          norm_num at hp_prime
        · -- p = 13
          use 3
          have h_n : n + 1 + 3 = 134 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 14
          norm_num at hp_prime
        · -- p = 15
          norm_num at hp_prime
        · -- p = 16
          norm_num at hp_prime
        · -- p = 17
          use 3
          have h_n : n + 1 + 3 = 130 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 18
          norm_num at hp_prime
        · -- p = 19
          use 3
          have h_n : n + 1 + 3 = 128 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 20
          norm_num at hp_prime
        · -- p = 21
          norm_num at hp_prime
        · -- p = 22
          norm_num at hp_prime
        · -- p = 23
          use 3
          have h_n : n + 1 + 3 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 24
          norm_num at hp_prime
        · -- p = 25
          norm_num at hp_prime
        · -- p = 26
          norm_num at hp_prime
        · -- p = 27
          norm_num at hp_prime
        · -- p = 28
          norm_num at hp_prime
        · -- p = 29
          use 7
          have h_n : n + 1 + 7 = 122 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 30
          norm_num at hp_prime
        · -- p = 31
          use 11
          have h_n : n + 1 + 11 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 32
          norm_num at hp_prime
        · -- p = 33
          norm_num at hp_prime
        · -- p = 34
          norm_num at hp_prime
        · -- p = 35
          norm_num at hp_prime
        · -- p = 36
          norm_num at hp_prime
        · -- p = 37
          use 17
          have h_n : n + 1 + 17 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 38
          norm_num at hp_prime
        · -- p = 39
          norm_num at hp_prime
        · -- p = 40
          norm_num at hp_prime
        · -- p = 41
          use 19
          have h_n : n + 1 + 19 = 122 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 42
          norm_num at hp_prime
        · -- p = 43
          use 23
          have h_n : n + 1 + 23 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 44
          norm_num at hp_prime
        · -- p = 45
          norm_num at hp_prime
        · -- p = 46
          norm_num at hp_prime
        · -- p = 47
          use 29
          have h_n : n + 1 + 29 = 126 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 48
          norm_num at hp_prime
        · -- p = 49
          norm_num at hp_prime
        · -- p = 50
          norm_num at hp_prime
        · -- p = 51
          norm_num at hp_prime
        · -- p = 52
          norm_num at hp_prime
        · -- p = 53
          use 31
          have h_n : n + 1 + 31 = 122 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 54
          norm_num at hp_prime
        · -- p = 55
          norm_num at hp_prime
        · -- p = 56
          norm_num at hp_prime
        · -- p = 57
          norm_num at hp_prime
        · -- p = 58
          norm_num at hp_prime
        · -- p = 59
          use 37
          have h_n : n + 1 + 37 = 122 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 60
          norm_num at hp_prime
        · -- p = 61
          use 41
          have h_n : n + 1 + 41 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 62
          norm_num at hp_prime
        · -- p = 63
          norm_num at hp_prime
        · -- p = 64
          norm_num at hp_prime
        · -- p = 65
          norm_num at hp_prime
        · -- p = 66
          norm_num at hp_prime
        · -- p = 67
          use 47
          have h_n : n + 1 + 47 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 68
          norm_num at hp_prime
        · -- p = 69
          norm_num at hp_prime
        · -- p = 70
          norm_num at hp_prime
        · -- p = 71
          use 53
          have h_n : n + 1 + 53 = 126 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 72
          norm_num at hp_prime
        · -- p = 73
          use 53
          have h_n : n + 1 + 53 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 74
          norm_num at hp_prime
        · -- p = 75
          norm_num at hp_prime
        · -- p = 76
          norm_num at hp_prime
        · -- p = 77
          norm_num at hp_prime
        · -- p = 78
          norm_num at hp_prime
        · -- p = 79
          use 59
          have h_n : n + 1 + 59 = 124 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 80
          norm_num at hp_prime
        · -- p = 81
          norm_num at hp_prime
        · -- p = 82
          norm_num at hp_prime
        · -- p = 83
          use 2
          have h_n : n + 1 + 2 = 63 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 84
          norm_num at hp_prime
        · -- p = 85
          norm_num at hp_prime
        · -- p = 86
          norm_num at hp_prime
        · -- p = 87
          norm_num at hp_prime
        · -- p = 88
          norm_num at hp_prime
        · -- p = 89
          use 2
          have h_n : n + 1 + 2 = 57 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 90
          norm_num at hp_prime
        · -- p = 91
          norm_num at hp_prime
        · -- p = 92
          norm_num at hp_prime
        · -- p = 93
          norm_num at hp_prime
        · -- p = 94
          norm_num at hp_prime
        · -- p = 95
          norm_num at hp_prime
        · -- p = 96
          norm_num at hp_prime
        · -- p = 97
          use 2
          have h_n : n + 1 + 2 = 49 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 98
          norm_num at hp_prime
        · -- p = 99
          norm_num at hp_prime
        · -- p = 100
          norm_num at hp_prime
        · -- p = 101
          use 7
          have h_n : n + 1 + 7 = 50 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 102
          norm_num at hp_prime
        · -- p = 103
          use 11
          have h_n : n + 1 + 11 = 52 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 104
          norm_num at hp_prime
        · -- p = 105
          norm_num at hp_prime
        · -- p = 106
          norm_num at hp_prime
        · -- p = 107
          use 13
          have h_n : n + 1 + 13 = 50 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 108
          norm_num at hp_prime
        · -- p = 109
          use 17
          have h_n : n + 1 + 17 = 52 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 110
          norm_num at hp_prime
        · -- p = 111
          norm_num at hp_prime
        · -- p = 112
          norm_num at hp_prime
        · -- p = 113
          use 2
          have h_n : n + 1 + 2 = 33 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 114
          norm_num at hp_prime
        · -- p = 115
          norm_num at hp_prime
        · -- p = 116
          norm_num at hp_prime
        · -- p = 117
          norm_num at hp_prime
        · -- p = 118
          norm_num at hp_prime
        · -- p = 119
          norm_num at hp_prime
        · -- p = 120
          norm_num at hp_prime
        · -- p = 121
          norm_num at hp_prime
        · -- p = 122
          norm_num at hp_prime
        · -- p = 123
          norm_num at hp_prime
        · -- p = 124
          norm_num at hp_prime
        · -- p = 125
          norm_num at hp_prime
        · -- p = 126
          norm_num at hp_prime
        · -- p = 127
          use 11
          have h_n : n + 1 + 11 = 28 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 128
          norm_num at hp_prime
        · -- p = 129
          norm_num at hp_prime
        · -- p = 130
          norm_num at hp_prime
        · -- p = 131
          use 2
          have h_n : n + 1 + 2 = 15 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 132
          norm_num at hp_prime
        · -- p = 133
          norm_num at hp_prime
        · -- p = 134
          norm_num at hp_prime
        · -- p = 135
          norm_num at hp_prime
        · -- p = 136
          norm_num at hp_prime
        · -- p = 137
          use 2
          have h_n : n + 1 + 2 = 9 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 138
          norm_num at hp_prime
        · -- p = 139
          use 2
          have h_n : n + 1 + 2 = 7 := by omega
          refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
          · rw [h_n]; norm_num
          · rw [h_n]; norm_num
          · intro hc; omega
          · intro hc; rw [h_n] at *; norm_num at *
        · -- p = 140
          norm_num at hp_prime
    · -- S >= 13
      have h_S_ge13 : S ≥ 13 := by omega
      have h_S_ge14 : S ≥ 14 := by
        by_contra hc
        have : S = 13 := by omega
        rw [this] at hS_prime
        norm_num at hS_prime
      have h_S_sq : S * S ≥ 196 := by nlinarith
      generalize hS_sq_eq : S * S = S_sq at *
      have hp_gt2 : p > 2 := by
        by_contra hc
        have : p = 2 := by omega
        have h_cond_p : n ≤ 61 := h_cond this
        omega
      have hk_ne_zero : (p - 1) / 2 ≠ 0 := by omega
      obtain ⟨p', hp'_prime, hp'1, hp'_le⟩ := exists_prime_lt_and_le_two_mul ((p - 1) / 2) hk_ne_zero
      use p'
      have hp'_lt_n1 : p' < n + 1 := by
        have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
        omega
      have h_eq : sqrt (n + 1 + p') = S - 1 := by
        refine (eq_sqrt.mpr ⟨?_, ?_⟩).symm
        · rw [sq_sub_one_sq S (by omega)]
          rw [hS_sq_eq]
          have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
          have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
          omega
        · have h_cancel : S - 1 + 1 = S := Nat.sub_add_cancel (by omega)
          rw [h_cancel]
          have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
          have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
          omega
      refine ⟨hp'_prime, hp'_lt_n1, ?_, ?_, ?_, ?_⟩
      · rwa [h_eq]
      · rw [h_eq]
        omega
      · intro hc
        have h_div_le : (p - 1) / 2 ≤ 1 := by omega
        have h_mod : (p - 1) % 2 < 2 := Nat.mod_lt (p - 1) (by decide)
        have h_decomp : p - 1 = 2 * ((p - 1) / 2) + (p - 1) % 2 := (Nat.div_add_mod (p - 1) 2).symm
        omega
      · intro hc
        rw [h_eq] at hc
        have hp_le_4S : p ≤ 4 * (S - 1) - 2 := by
          have h_sqrt : sqrt (n + p) = S - 1 := h_sqrt_eq
          have h_cond_premise : sqrt (n + p) ≥ 12 := by omega
          rw [h_sqrt] at h_cond2 h_cond_premise
          exact h_cond2 h_cond_premise
        have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
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
    refine ⟨hp_prime, by omega, ?_, ?_, ?_, ?_⟩
    · rwa [h_eq]
    · rwa [h_eq]
    · intro hp2
      have hn_le : n ≤ 61 := h_cond hp2
      have hp_ge2 : p ≥ 2 := hp_prime.two_le
      have hn_ne : n ≠ 61 := by
        intro hn61
        by_cases hp2_eq : p = 2
        · have h_not_rw : 61 + p + 1 ≠ (sqrt (61 + p + 1)) * (sqrt (61 + p + 1)) := by
            rwa [hn61] at h_not
          rw [hp2_eq] at h_not_rw
          norm_num at h_not_rw
        · have hp3_eq : p = 3 := by omega
          have hsqrt_prime_rw : (sqrt (61 + p)).Prime := by
            rwa [hn61] at hsqrt_prime
          rw [hp3_eq] at hsqrt_prime_rw
          norm_num at hsqrt_prime_rw
      omega
    · intro hc
      rw [h_eq] at hc
      have := h_cond2 hc
      rwa [h_eq]

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

theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  have hn3 : n ≥ 3 := by omega
  obtain ⟨p, hp_prime, hp_lt, hsqrt_prime, _, _, _⟩ := P_all n hn3
  exact ⟨p, hp_prime, hp_lt, hsqrt_prime⟩
