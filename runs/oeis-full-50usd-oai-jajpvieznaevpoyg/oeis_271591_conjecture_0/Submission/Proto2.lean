import FormalConjectures.Util.ProblemImports
open Nat

def aa (T : ℕ) : ℕ :=
  if h : T ≤ 1 then 0 else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

lemma testBit_false_of_interval {N k : ℕ} (hlo : 2^(k+1) ≤ N) (hhi : N < 3*2^k) :
    N.testBit k = false := by
  have hp : 0 < 2^k := pow_pos (by norm_num) _
  have hdiv : N / 2^k = 2 := by
    have hlo' : 2 ≤ N / 2^k := by
      rw [Nat.le_div_iff_mul_le hp]
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlo
    have hhi' : N / 2^k < 3 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
    omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

lemma testBit_true_of_interval {N k : ℕ} (hlo : 3*2^k ≤ N) (hhi : N < 2^(k+2)) :
    N.testBit k = true := by
  have hp : 0 < 2^k := pow_pos (by norm_num) _
  have hdiv : N / 2^k = 3 := by
    have hlo' : 3 ≤ N / 2^k := by
      rw [Nat.le_div_iff_mul_le hp]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlo
    have hhi' : N / 2^k < 4 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      have hpow : 2^(k+2) = 4 * 2^k := by
        rw [pow_add]
        norm_num
        ring
      simpa [hpow] using hhi
    omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

lemma aa_zero_of_interval {N k : ℕ} (hlo : 2^(k+1) ≤ N) (hhi : N < 3*2^k) : aa N = 0 := by
  unfold aa
  have hnot : ¬ N ≤ 1 := by
    have : (2:ℕ) ≤ N := by
      exact le_trans (by simpa using (show (2:ℕ) ≤ 2^(k+1) by
        exact Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) (Nat.succ_pos k))) hlo
    omega
  simp [hnot]
  have hlog : N.log2 = k+1 := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow hlo
    have : 3*2^k ≤ 2^(k+2) := by
      rw [pow_add]
      nlinarith [show (0:ℕ) < 2^k by positivity]
    exact lt_of_lt_of_le hhi this
  have hk : k+1 -1 = k := by omega
  simp [hlog, hk, testBit_false_of_interval hlo hhi]

lemma aa_one_of_interval {N k : ℕ} (hlo : 3*2^k ≤ N) (hhi : N < 2^(k+2)) : aa N = 1 := by
  unfold aa
  have hnot : ¬ N ≤ 1 := by
    have : (2:ℕ) ≤ N := by
      have h2 : 2^(k+1) ≤ 3*2^k := by
        rw [pow_succ]; nlinarith [show (0:ℕ) < 2^k by positivity]
      exact le_trans (le_trans (by simpa using (show (2:ℕ) ≤ 2^(k+1) by exact Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) (Nat.succ_pos k))) h2) hlo
    omega
  simp [hnot]
  have hlog : N.log2 = k+1 := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow ?_ hhi
    have hp : 0 < 2^k := pow_pos (by norm_num) _
    have : 2^(k+1) ≤ 3*2^k := by rw [pow_succ]; nlinarith
    exact le_trans this hlo
  have hk : k+1 -1 = k := by omega
  simp [hlog, hk, testBit_true_of_interval hlo hhi]
