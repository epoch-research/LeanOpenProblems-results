import FormalConjectures.Util.ProblemImports
open Nat

def aa (T : ℕ) : ℕ :=
  if h : T ≤ 1 then 0 else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

lemma one_interval_of_aa_one {N : ℕ} (h : aa N = 1) :
    3 * 2^(N.log2 - 1) ≤ N ∧ N < 2^((N.log2 - 1)+2) := by
  unfold aa at h
  by_cases hle : N ≤ 1
  · rw [dif_pos hle] at h
    norm_num at h
  · rw [dif_neg hle] at h
    by_cases hbit : N.testBit (N.log2 - 1) = true
    · rw [if_pos hbit] at h
      have hkpos : 0 < 2^(N.log2 - 1) := by positivity
      have hlogpos : 0 < N.log2 := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_pos (by norm_num) (by omega)
      have htop : N < 2^((N.log2 - 1)+2) := by
        have : (N.log2 - 1)+2 = N.log2 + 1 := by omega
        rw [this]
        rw [Nat.log2_eq_log_two]
        exact Nat.lt_pow_succ_log_self (by norm_num) N
      have hq_lt : N / 2^(N.log2 - 1) < 4 := by
        rw [Nat.div_lt_iff_lt_mul hkpos]
        simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
      have hq_ge2 : 2 ≤ N / 2^(N.log2 - 1) := by
        rw [Nat.le_div_iff_mul_le hkpos]
        have hpow : 2 ^ N.log2 ≤ N := by
          rw [Nat.log2_eq_log_two]
          exact Nat.pow_log_le_self 2 (by omega)
        have hpowe : 2 * 2^(N.log2 - 1) = 2^N.log2 := by
          have : (N.log2 - 1)+1 = N.log2 := by omega
          rw [Nat.mul_comm, ← pow_succ, this]
        simpa [hpowe] using hpow
      have hodd : (N / 2^(N.log2 - 1)) % 2 = 1 := by
        have hb : N.testBit (N.log2 - 1) = true := hbit
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] at hb
        omega
      have hq : N / 2^(N.log2 - 1) = 3 := by omega
      constructor
      · rw [← Nat.le_div_iff_mul_le hkpos]
        exact hq.ge
      · exact htop
    · rw [if_neg hbit] at h
      norm_num at h

lemma zero_interval_of_aa_zero_large {N : ℕ} (hN : 2 ≤ N) (h : aa N = 0) :
    2^N.log2 ≤ N ∧ N < 3 * 2^(N.log2 - 1) := by
  unfold aa at h
  split_ifs at h with hle
  · omega
  · have hbit : N.testBit (N.log2 - 1) = false := by
      by_contra hb
      have hbtrue : N.testBit (N.log2 - 1) = true := by
        cases N.testBit (N.log2 - 1) <;> simp_all
      simp [hbtrue] at h
    have hkpos : 0 < 2^(N.log2 - 1) := by positivity
    have hlogpos : 0 < N.log2 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_pos (by norm_num) hN
    have hlow : 2^N.log2 ≤ N := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have htop : N < 2^((N.log2 - 1)+2) := by
      have : (N.log2 - 1)+2 = N.log2 + 1 := by omega
      rw [this]
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self (by norm_num) N
    have hq_lt : N / 2^(N.log2 - 1) < 4 := by
      rw [Nat.div_lt_iff_lt_mul hkpos]
      simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
    have hq_ge2 : 2 ≤ N / 2^(N.log2 - 1) := by
      rw [Nat.le_div_iff_mul_le hkpos]
      have hpowe : 2 * 2^(N.log2 - 1) = 2^N.log2 := by
        have : (N.log2 - 1)+1 = N.log2 := by omega
        rw [Nat.mul_comm, ← pow_succ, this]
      simpa [hpowe] using hlow
    have hodd : (N / 2^(N.log2 - 1)) % 2 = 0 := by
      have hb : N.testBit (N.log2 - 1) = false := hbit
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] at hb
      omega
    have hq : N / 2^(N.log2 - 1) = 2 := by omega
    constructor
    · exact hlow
    · have : N / 2^(N.log2 - 1) < 3 := by omega
      exact (Nat.div_lt_iff_lt_mul hkpos).mp this
