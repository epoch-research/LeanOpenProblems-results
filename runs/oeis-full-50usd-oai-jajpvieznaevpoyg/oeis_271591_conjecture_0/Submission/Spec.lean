import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

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


def smsbit (T : ℕ) : ℕ :=
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

lemma smsbit_zero_of_interval {N k : ℕ} (hlo : 2^(k+1) ≤ N) (hhi : N < 3*2^k) : smsbit N = 0 := by
  unfold smsbit
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

lemma smsbit_one_of_interval {N k : ℕ} (hlo : 3*2^k ≤ N) (hhi : N < 2^(k+2)) : smsbit N = 1 := by
  unfold smsbit
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

lemma one_interval_of_smsbit_one {N : ℕ} (h : smsbit N = 1) :
    3 * 2^(N.log2 - 1) ≤ N ∧ N < 2^((N.log2 - 1)+2) := by
  unfold smsbit at h
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

lemma zero_interval_of_smsbit_zero_large {N : ℕ} (hN : 2 ≤ N) (h : smsbit N = 0) :
    2^N.log2 ≤ N ∧ N < 3 * 2^(N.log2 - 1) := by
  unfold smsbit at h
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

def Plo (n : ℕ) : Prop := 1838*tribonacci n ≤ 1000*tribonacci (n+1)
def Phi (n : ℕ) : Prop := 1000*tribonacci (n+1) ≤ 1841*tribonacci n

lemma tri_rec (n : ℕ) : tribonacci (n+3) = tribonacci (n+2) + tribonacci (n+1) + tribonacci n := by rfl

lemma Plo_step {n} (h0:Plo n) (h1:Plo (n+1)) (h2:Plo (n+2)) : Plo (n+3) := by
  unfold Plo at *
  simp only [Plo, tribonacci] at *
  nlinarith

lemma Phi_step {n} (h0:Phi n) (h1:Phi (n+1)) (h2:Phi (n+2)) : Phi (n+3) := by
  unfold Phi at *
  simp only [Phi, tribonacci] at *
  nlinarith

lemma Plo_aux : ∀ k, Plo (k+9) ∧ Plo (k+10) ∧ Plo (k+11)
| 0 => by norm_num [Plo, tribonacci]
| k+1 => by
  rcases Plo_aux k with ⟨h7,h8,h9⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h8
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h9
  · have hs := Plo_step h7 h8 h9
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

lemma Phi_aux : ∀ k, Phi (k+9) ∧ Phi (k+10) ∧ Phi (k+11)
| 0 => by norm_num [Phi, tribonacci]
| k+1 => by
  rcases Phi_aux k with ⟨h7,h8,h9⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h8
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h9
  · have hs := Phi_step h7 h8 h9
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

lemma Plo_of_ge {n} (hn:9≤n): Plo n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']
  exact (Plo_aux k).1

lemma Phi_of_ge {n} (hn:9≤n): Phi n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']
  exact (Phi_aux k).1


lemma a_zero_of_interval {n k : ℕ} (hlo : 2^(k+1) ≤ tribonacci n) (hhi : tribonacci n < 3*2^k) : a n = 0 := by
  change smsbit (tribonacci n) = 0
  exact smsbit_zero_of_interval hlo hhi

lemma a_one_of_interval {n k : ℕ} (hlo : 3*2^k ≤ tribonacci n) (hhi : tribonacci n < 2^(k+2)) : a n = 1 := by
  change smsbit (tribonacci n) = 1
  exact smsbit_one_of_interval hlo hhi

lemma one_interval_of_a_one {n : ℕ} (h : a n = 1) :
    3 * 2^((tribonacci n).log2 - 1) ≤ tribonacci n ∧ tribonacci n < 2^(((tribonacci n).log2 - 1)+2) := by
  change smsbit (tribonacci n) = 1 at h
  exact one_interval_of_smsbit_one h

lemma zero_interval_of_a_zero_large {n : ℕ} (hN : 2 ≤ tribonacci n) (h : a n = 0) :
    2^(tribonacci n).log2 ≤ tribonacci n ∧ tribonacci n < 3 * 2^((tribonacci n).log2 - 1) := by
  change smsbit (tribonacci n) = 0 at h
  exact zero_interval_of_smsbit_zero_large hN h

lemma a_eq_zero_or_one (n : ℕ) : a n = 0 ∨ a n = 1 := by
  change smsbit (tribonacci n) = 0 ∨ smsbit (tribonacci n) = 1
  unfold smsbit
  by_cases h : tribonacci n ≤ 1
  · simp [dif_pos h]
  · rw [dif_neg h]
    by_cases hb : (tribonacci n).testBit ((tribonacci n).log2 - 1) = true
    · simp [hb]
    · simp [hb]

lemma tribonacci_ge_two_of_ge_four {n : ℕ} (hn : 4 ≤ n) : 2 ≤ tribonacci n := by
  let k := n - 4
  have hn' : n = k + 4 := by omega
  rw [hn']
  clear hn hn'
  induction k with
  | zero => norm_num [tribonacci]
  | succ k ih =>
      rw [show k.succ + 4 = (k+2)+3 by omega, tribonacci]
      nlinarith [ih, Nat.zero_le (tribonacci (k+3)), Nat.zero_le (tribonacci (k+2))]

lemma pow_two_scale (k c : ℕ) : 2^(k+c) = 2^c * 2^k := by
  rw [pow_add, Nat.mul_comm]

lemma zero_transition_large {n k : ℕ} (hn : 10 ≤ n)
    (hprev : 3 * 2^k ≤ tribonacci (n-1) ∧ tribonacci (n-1) < 2^(k+2))
    (hz : a n = 0) :
    a n = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 ∧ a (n+5) = 1 := by
  let x := 2^k
  have hxpos : (0:ℕ) < x := by dsimp [x]; positivity
  have hAlo : 3*x ≤ tribonacci (n-1) := by simpa [x] using hprev.1
  have hAhi : tribonacci (n-1) < 4*x := by
    have hp : 2^(k+2) = 4*x := by dsimp [x]; rw [pow_add]; norm_num; ring
    simpa [hp] using hprev.2
  have r0lo : 1838 * tribonacci (n-1) ≤ 1000 * tribonacci n := by
    have := Plo_of_ge (n:=n-1) (by omega : 9 ≤ n-1)
    simpa [Plo, Nat.sub_add_cancel (by omega : 1 ≤ n)] using this
  have r0hi : 1000 * tribonacci n ≤ 1841 * tribonacci (n-1) := by
    have := Phi_of_ge (n:=n-1) (by omega : 9 ≤ n-1)
    simpa [Phi, Nat.sub_add_cancel (by omega : 1 ≤ n)] using this
  have hBge4 : 4*x ≤ tribonacci n := by linarith [hAlo, r0lo]
  have hBlt8 : tribonacci n < 8*x := by nlinarith [hAhi, r0hi]
  have hBlog : (tribonacci n).log2 = k+2 := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · have hp : 2^(k+2) = 4*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hBge4
    · have hp : 2^((k+2)+1) = 8*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [Nat.add_assoc, hp] using hBlt8
  have hB2 : 2 ≤ tribonacci n := by nlinarith [hBge4, hxpos]
  have hBint := zero_interval_of_a_zero_large hB2 hz
  have hBlt6 : tribonacci n < 6*x := by
    have := hBint.2
    rw [hBlog] at this
    have hp : 3 * 2^(k+1) = 6*x := by
      dsimp [x]; rw [pow_add]; norm_num; ring
    simpa [hp] using this
  have r1lo : 1838 * tribonacci n ≤ 1000 * tribonacci (n+1) := by exact Plo_of_ge (by omega : 9 ≤ n)
  have r1hi : 1000 * tribonacci (n+1) ≤ 1841 * tribonacci n := by exact Phi_of_ge (by omega : 9 ≤ n)
  have r2lo : 1838 * tribonacci (n+1) ≤ 1000 * tribonacci (n+2) := by
    have tmp := Plo_of_ge (n:=n+1) (by omega : 9 ≤ n+1)
    unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r2hi : 1000 * tribonacci (n+2) ≤ 1841 * tribonacci (n+1) := by
    have tmp := Phi_of_ge (n:=n+1) (by omega : 9 ≤ n+1)
    unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r3lo : 1838 * tribonacci (n+2) ≤ 1000 * tribonacci (n+3) := by
    have tmp := Plo_of_ge (n:=n+2) (by omega : 9 ≤ n+2)
    unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r3hi : 1000 * tribonacci (n+3) ≤ 1841 * tribonacci (n+2) := by
    have tmp := Phi_of_ge (n:=n+2) (by omega : 9 ≤ n+2)
    unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r4lo : 1838 * tribonacci (n+3) ≤ 1000 * tribonacci (n+4) := by
    have tmp := Plo_of_ge (n:=n+3) (by omega : 9 ≤ n+3)
    unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r4hi : 1000 * tribonacci (n+4) ≤ 1841 * tribonacci (n+3) := by
    have tmp := Phi_of_ge (n:=n+3) (by omega : 9 ≤ n+3)
    unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r5lo : 1838 * tribonacci (n+4) ≤ 1000 * tribonacci (n+5) := by
    have tmp := Plo_of_ge (n:=n+4) (by omega : 9 ≤ n+4)
    unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r5hi : 1000 * tribonacci (n+5) ≤ 1841 * tribonacci (n+4) := by
    have tmp := Phi_of_ge (n:=n+4) (by omega : 9 ≤ n+4)
    unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have hClo : 8*x ≤ tribonacci (n+1) := by linarith [hAlo, r0lo, r1lo]
  have hChi : tribonacci (n+1) < 12*x := by linarith [hBlt6, r1hi]
  have hDlo : 16*x ≤ tribonacci (n+2) := by linarith [hClo, r2lo]
  have hDhi : tribonacci (n+2) < 24*x := by linarith [hChi, r2hi]
  have hElo : 32*x ≤ tribonacci (n+3) := by linarith [hDlo, r3lo]
  have hEhi : tribonacci (n+3) < 48*x := by linarith [hDhi, r3hi]
  have lo0 : 1000 * tribonacci n ≥ 1838 * 3 * x := by linarith [hAlo, r0lo]
  have lo1 : 1000000 * tribonacci (n+1) ≥ 1838^2 * 3 * x := by linarith [lo0, r1lo]
  have lo2 : 1000000000 * tribonacci (n+2) ≥ 1838^3 * 3 * x := by linarith [lo1, r2lo]
  have lo3 : 1000000000000 * tribonacci (n+3) ≥ 1838^4 * 3 * x := by linarith [lo2, r3lo]
  have lo4 : 1000000000000000 * tribonacci (n+4) ≥ 1838^5 * 3 * x := by linarith [lo3, r4lo]
  have lo5 : 1000000000000000000 * tribonacci (n+5) ≥ 1838^6 * 3 * x := by linarith [lo4, r5lo]
  have hGlo : 96*x ≤ tribonacci (n+5) := by linarith [lo5, hxpos]
  have up1 : 1000 * tribonacci (n+1) < 1841 * 6 * x := by linarith [hBlt6, r1hi]
  have up2 : 1000000 * tribonacci (n+2) < 1841^2 * 6 * x := by linarith [up1, r2hi]
  have up3 : 1000000000 * tribonacci (n+3) < 1841^3 * 6 * x := by linarith [up2, r3hi]
  have up4 : 1000000000000 * tribonacci (n+4) < 1841^4 * 6 * x := by linarith [up3, r4hi]
  have up5 : 1000000000000000 * tribonacci (n+5) < 1841^5 * 6 * x := by linarith [up4, r5hi]
  have hGhi : tribonacci (n+5) < 128*x := by linarith [up5, hxpos]
  refine ⟨hz, ?_, ?_, ?_, ?_⟩
  · apply a_zero_of_interval (k:=k+2)
    · have hp : 2^((k+2)+1) = 8*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hClo
    · have hp : 3*2^(k+2) = 12*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hChi
  · apply a_zero_of_interval (k:=k+3)
    · have hp : 2^((k+3)+1) = 16*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hDlo
    · have hp : 3*2^(k+3) = 24*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hDhi
  · apply a_zero_of_interval (k:=k+4)
    · have hp : 2^((k+4)+1) = 32*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hElo
    · have hp : 3*2^(k+4) = 48*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hEhi
  · apply a_one_of_interval (k:=k+5)
    · have hp : 3*2^(k+5) = 96*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hGlo
    · have hp : 2^((k+5)+2) = 128*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hGhi

lemma one_transition_large {n k : ℕ} (hn : 10 ≤ n)
    (hprev : 2^(k+1) ≤ tribonacci (n-1) ∧ tribonacci (n-1) < 3*2^k)
    (ho : a n = 1) :
    a n = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 1 ∧ a (n+4) = 0 := by
  let x := 2^k
  have hxpos : (0:ℕ) < x := by dsimp [x]; positivity
  have hAlo : 2*x ≤ tribonacci (n-1) := by
    have hp : 2^(k+1) = 2*x := by dsimp [x]; rw [pow_add]; norm_num; ring
    simpa [hp] using hprev.1
  have hAhi : tribonacci (n-1) < 3*x := by simpa [x] using hprev.2
  have r0lo : 1838 * tribonacci (n-1) ≤ 1000 * tribonacci n := by
    have := Plo_of_ge (n:=n-1) (by omega : 9 ≤ n-1)
    simpa [Plo, Nat.sub_add_cancel (by omega : 1 ≤ n)] using this
  have r0hi : 1000 * tribonacci n ≤ 1841 * tribonacci (n-1) := by
    have := Phi_of_ge (n:=n-1) (by omega : 9 ≤ n-1)
    simpa [Phi, Nat.sub_add_cancel (by omega : 1 ≤ n)] using this
  have hBge3 : 3*x ≤ tribonacci n := by linarith [hAlo, r0lo]
  have hBlt6 : tribonacci n < 6*x := by linarith [hAhi, r0hi]
  have hBlt8 : tribonacci n < 8*x := by linarith [hBlt6, hxpos]
  have hBlt4 : tribonacci n < 4*x := by
    by_contra hnot
    have hBge4 : 4*x ≤ tribonacci n := by omega
    have hBlog : (tribonacci n).log2 = k+2 := by
      rw [Nat.log2_eq_log_two]
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · have hp : 2^(k+2) = 4*x := by dsimp [x]; rw [pow_add]; norm_num; ring
        simpa [hp] using hBge4
      · have hp : 2^((k+2)+1) = 8*x := by dsimp [x]; rw [pow_add]; norm_num; ring
        simpa [Nat.add_assoc, hp] using hBlt8
    have hint := one_interval_of_a_one ho
    have hb6 : 6*x ≤ tribonacci n := by
      have := hint.1
      rw [hBlog] at this
      have hp : 3 * 2^(k+1) = 6*x := by
        dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using this
    linarith
  have r1lo : 1838 * tribonacci n ≤ 1000 * tribonacci (n+1) := by exact Plo_of_ge (by omega : 9 ≤ n)
  have r1hi : 1000 * tribonacci (n+1) ≤ 1841 * tribonacci n := by exact Phi_of_ge (by omega : 9 ≤ n)
  have r2lo : 1838 * tribonacci (n+1) ≤ 1000 * tribonacci (n+2) := by
    have tmp := Plo_of_ge (n:=n+1) (by omega : 9 ≤ n+1); unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r2hi : 1000 * tribonacci (n+2) ≤ 1841 * tribonacci (n+1) := by
    have tmp := Phi_of_ge (n:=n+1) (by omega : 9 ≤ n+1); unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r3lo : 1838 * tribonacci (n+2) ≤ 1000 * tribonacci (n+3) := by
    have tmp := Plo_of_ge (n:=n+2) (by omega : 9 ≤ n+2); unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r3hi : 1000 * tribonacci (n+3) ≤ 1841 * tribonacci (n+2) := by
    have tmp := Phi_of_ge (n:=n+2) (by omega : 9 ≤ n+2); unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r4lo : 1838 * tribonacci (n+3) ≤ 1000 * tribonacci (n+4) := by
    have tmp := Plo_of_ge (n:=n+3) (by omega : 9 ≤ n+3); unfold Plo at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have r4hi : 1000 * tribonacci (n+4) ≤ 1841 * tribonacci (n+3) := by
    have tmp := Phi_of_ge (n:=n+3) (by omega : 9 ≤ n+3); unfold Phi at tmp
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tmp
  have hClo : 6*x ≤ tribonacci (n+1) := by linarith [hAlo, r0lo, r1lo]
  have hChi : tribonacci (n+1) < 8*x := by linarith [hBlt4, r1hi]
  have hDlo : 12*x ≤ tribonacci (n+2) := by linarith [hClo, r2lo]
  have hDhi : tribonacci (n+2) < 16*x := by linarith [hChi, r2hi]
  have lo0 : 1000 * tribonacci n ≥ 1838 * 2 * x := by linarith [hAlo, r0lo]
  have lo1 : 1000000 * tribonacci (n+1) ≥ 1838^2 * 2 * x := by linarith [lo0, r1lo]
  have lo2 : 1000000000 * tribonacci (n+2) ≥ 1838^3 * 2 * x := by linarith [lo1, r2lo]
  have lo3 : 1000000000000 * tribonacci (n+3) ≥ 1838^4 * 2 * x := by linarith [lo2, r3lo]
  have lo4 : 1000000000000000 * tribonacci (n+4) ≥ 1838^5 * 2 * x := by linarith [lo3, r4lo]
  have hFlo : 32*x ≤ tribonacci (n+4) := by linarith [lo4, hxpos]
  have up1 : 1000 * tribonacci (n+1) < 1841 * 4 * x := by linarith [hBlt4, r1hi]
  have up2 : 1000000 * tribonacci (n+2) < 1841^2 * 4 * x := by linarith [up1, r2hi]
  have up3 : 1000000000 * tribonacci (n+3) < 1841^3 * 4 * x := by linarith [up2, r3hi]
  have up4 : 1000000000000 * tribonacci (n+4) < 1841^4 * 4 * x := by linarith [up3, r4hi]
  have hFhi : tribonacci (n+4) < 48*x := by linarith [up4, hxpos]
  refine ⟨ho, ?_, ?_, ?_⟩
  · apply a_one_of_interval (k:=k+1)
    · have hp : 3*2^(k+1) = 6*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hClo
    · have hp : 2^((k+1)+2) = 8*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hChi
  · apply a_one_of_interval (k:=k+2)
    · have hp : 3*2^(k+2) = 12*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hDlo
    · have hp : 2^((k+2)+2) = 16*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hDhi
  · apply a_zero_of_interval (k:=k+4)
    · have hp : 2^((k+4)+1) = 32*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hFlo
    · have hp : 3*2^(k+4) = 48*x := by dsimp [x]; rw [pow_add]; norm_num; ring
      simpa [hp] using hFhi


lemma small_zero_run {n L : ℕ} (hn : n < 10) (h : is_maximal_run 0 n L) : L = 4 ∨ L = 5 := by
  by_cases h2 : n = 2
  · subst n
    unfold is_maximal_run at h
    have hrun := h.2.2.1
    have hfollow := h.2.2.2.1
    have hle : L ≤ 4 := by
      by_contra hc
      have hx := hrun 4 (by omega)
      exact (by decide : a (2+4) ≠ 0) hx
    have hge : 4 ≤ L := by
      by_contra hc
      interval_cases L <;> exact hfollow (by decide)
    omega
  by_cases h9 : n = 9
  · subst n
    unfold is_maximal_run at h
    have hrun := h.2.2.1
    have hfollow := h.2.2.2.1
    have hle : L ≤ 4 := by
      by_contra hc
      have hx := hrun 4 (by omega)
      exact (by decide : a (9+4) ≠ 0) hx
    have hge : 4 ≤ L := by
      by_contra hc
      interval_cases L <;> exact hfollow (by decide)
    omega
  unfold is_maximal_run at h
  interval_cases n
  all_goals
    exfalso
    first
    | omega
    | exact h2 rfl
    | exact h9 rfl
    | have hx := h.2.2.1 0 (by omega)
      revert hx
      decide
    | have hp := h.2.2.2.2
      revert hp
      decide

lemma small_one_run {n L : ℕ} (hn : n < 10) (h : is_maximal_run 1 n L) : L = 3 ∨ L = 4 := by
  by_cases h6 : n = 6
  · subst n
    unfold is_maximal_run at h
    have hrun := h.2.2.1
    have hfollow := h.2.2.2.1
    have hle : L ≤ 3 := by
      by_contra hc
      have hx := hrun 3 (by omega)
      exact (by decide : a (6+3) ≠ 1) hx
    have hge : 3 ≤ L := by
      by_contra hc
      interval_cases L <;> exact hfollow (by decide)
    omega
  by_cases h9 : n = 9
  · subst n
    unfold is_maximal_run at h
    exact False.elim (h.2.2.2.2 (by decide : a (9-1) = 1))
  unfold is_maximal_run at h
  interval_cases n
  all_goals
    exfalso
    first
    | omega
    | exact h6 rfl
    | exact h9 rfl
    | have hx := h.2.2.1 0 (by omega)
      revert hx
      decide
    | have hp := h.2.2.2.2
      revert hp
      decide


theorem oeis_271591_conjecture_0 :
  (∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧
  (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4)) :=
by
  constructor
  · intro n L hrunmax
    by_cases hnsmall : n < 10
    · exact small_zero_run hnsmall hrunmax
    have hnlarge : 10 ≤ n := by omega
    unfold is_maximal_run at hrunmax
    have hLpos : L ≥ 1 := hrunmax.2.1
    have hrun : ∀ i : ℕ, i < L → a (n+i) = 0 := hrunmax.2.2.1
    have hfollow : a (n+L) ≠ 0 := hrunmax.2.2.2.1
    have hprevne : a (n-1) ≠ 0 := hrunmax.2.2.2.2
    have hz : a n = 0 := by simpa using hrun 0 (by omega)
    have hprev1 : a (n-1) = 1 := by
      rcases a_eq_zero_or_one (n-1) with hp | hp
      · exact False.elim (hprevne hp)
      · exact hp
    let k := (tribonacci (n-1)).log2 - 1
    have hprevInt : 3 * 2^k ≤ tribonacci (n-1) ∧ tribonacci (n-1) < 2^(k+2) := by
      dsimp [k]
      exact one_interval_of_a_one hprev1
    rcases zero_transition_large (n:=n) (k:=k) hnlarge hprevInt hz with ⟨hz0,hz1,hz2,hz3,hz5one⟩
    have hle : L ≤ 5 := by
      by_contra hc
      have hx := hrun 5 (by omega)
      rw [hz5one] at hx
      norm_num at hx
    have hge : 4 ≤ L := by
      by_contra hc
      interval_cases L
      all_goals first
        | omega
        | exact hfollow (by simpa using hz1)
        | exact hfollow (by simpa using hz2)
        | exact hfollow (by simpa using hz3)
    omega
  · intro n L hrunmax
    by_cases hnsmall : n < 10
    · exact small_one_run hnsmall hrunmax
    have hnlarge : 10 ≤ n := by omega
    unfold is_maximal_run at hrunmax
    have hLpos : L ≥ 1 := hrunmax.2.1
    have hrun : ∀ i : ℕ, i < L → a (n+i) = 1 := hrunmax.2.2.1
    have hfollow : a (n+L) ≠ 1 := hrunmax.2.2.2.1
    have hprevne : a (n-1) ≠ 1 := hrunmax.2.2.2.2
    have ho : a n = 1 := by simpa using hrun 0 (by omega)
    have hprev0 : a (n-1) = 0 := by
      rcases a_eq_zero_or_one (n-1) with hp | hp
      · exact hp
      · exact False.elim (hprevne hp)
    let k := (tribonacci (n-1)).log2 - 1
    have hTprev : 2 ≤ tribonacci (n-1) := tribonacci_ge_two_of_ge_four (n:=n-1) (by omega)
    have hprevInt0 := zero_interval_of_a_zero_large (n:=n-1) hTprev hprev0
    have hprevInt : 2^(k+1) ≤ tribonacci (n-1) ∧ tribonacci (n-1) < 3*2^k := by
      dsimp [k]
      constructor
      · have hp : 2^((tribonacci (n-1)).log2 - 1 + 1) = 2^(tribonacci (n-1)).log2 := by
          have hlogpos : 0 < (tribonacci (n-1)).log2 := by
            rw [Nat.log2_eq_log_two]
            exact Nat.log_pos (by norm_num) hTprev
          congr 1
          omega
        simpa [hp] using hprevInt0.1
      · exact hprevInt0.2
    rcases one_transition_large (n:=n) (k:=k) hnlarge hprevInt ho with ⟨ho0,ho1,ho2,hz4⟩
    have hle : L ≤ 4 := by
      by_contra hc
      have hx := hrun 4 (by omega)
      rw [hz4] at hx
      norm_num at hx
    have hge : 3 ≤ L := by
      by_contra hc
      interval_cases L
      all_goals first
        | omega
        | exact hfollow (by simpa using ho1)
        | exact hfollow (by simpa using ho2)
    omega
