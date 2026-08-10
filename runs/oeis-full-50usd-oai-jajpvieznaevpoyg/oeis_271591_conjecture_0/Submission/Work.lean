import FormalConjectures.Util.ProblemImports

open Nat

/--
The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.
-/
def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

/--
A271591: Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.
-/
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  -- The index of the MSB is T.log2. The index of the second MSB is T.log2 - 1.
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

-- Definition for a maximal run of a value $v \in \{0, 1\}$ starting at index $n$ with length $L$.
-- We restrict $n \ge 2$ to account for "after the first two 0's" $a(0)=0, a(1)=0$.
def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  -- The run consists of L consecutive $v$'s starting at n
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  -- The run is not followed by $v$
  (a (n + L) ≠ v) ∧
  -- The run is not preceded by $v$
  (a (n - 1) ≠ v)

/--
It is conjectured that after the first two 0's, the number of consecutive 0's is only 4 or 5,
and the number of consecutive 1's is only 3 or 4 (tested up to n=10^4).
-/
theorem oeis_271591_conjecture_0 :
  (∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧
  (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4)) :=
by sorry

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

lemma a_zero_of_interval {N k : ℕ} (hlo : 2^(k+1) ≤ N) (hhi : N < 3*2^k) : a N = 0 := by
  unfold a
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

lemma a_one_of_interval {N k : ℕ} (hlo : 3*2^k ≤ N) (hhi : N < 2^(k+2)) : a N = 1 := by
  unfold a
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
    have : 2^(k+1) ≤ 3*2^k := by rw [pow_succ]; nlinarith [show (0:ℕ) < 2^k by positivity]
    exact le_trans this hlo
  have hk : k+1 -1 = k := by omega
  simp [hlog, hk, testBit_true_of_interval hlo hhi]

def Plo (n : ℕ) : Prop := 1838*tribonacci n ≤ 1000*tribonacci (n+1)
def Phi (n : ℕ) : Prop := 1000*tribonacci (n+1) ≤ 1841*tribonacci n
lemma Plo_step {n} (h0:Plo n) (h1:Plo (n+1)) (h2:Plo (n+2)) : Plo (n+3) := by
  unfold Plo at *
  simp only [tribonacci] at *
  nlinarith
lemma Phi_step {n} (h0:Phi n) (h1:Phi (n+1)) (h2:Phi (n+2)) : Phi (n+3) := by
  unfold Phi at *
  simp only [tribonacci] at *
  nlinarith
lemma Plo_aux : ∀ k, Plo (k+9) ∧ Plo (k+10) ∧ Plo (k+11)
| 0 => by norm_num [Plo, tribonacci]
| k+1 => by
  rcases Plo_aux k with ⟨h9,h10,h11⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h10
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h11
  · have hs := Plo_step h9 h10 h11
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
lemma Phi_aux : ∀ k, Phi (k+9) ∧ Phi (k+10) ∧ Phi (k+11)
| 0 => by norm_num [Phi, tribonacci]
| k+1 => by
  rcases Phi_aux k with ⟨h9,h10,h11⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h10
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h11
  · have hs := Phi_step h9 h10 h11
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
lemma Plo_of_ge {n} (hn:9≤n): Plo n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']; exact (Plo_aux k).1
lemma Phi_of_ge {n} (hn:9≤n): Phi n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']; exact (Phi_aux k).1

lemma one_interval_of_a_one {N : ℕ} (h : a N = 1) :
    3 * 2^(N.log2 - 1) ≤ N ∧ N < 2^((N.log2 - 1)+2) := by
  -- placeholder copy later
  simpa [a] using (one_interval_of_aa_one (aa:=by sorry) h)
