import Submission.JointBoundaryTriplePatternsExplore

/-! Polynomial bounds for the test encodings. These are what turn the
universal index budget into logarithmic or constant count bounds. -/
namespace Erdos66RarePatternCodeGrowth
open Erdos66JointBoundaryTriplePatterns
set_option maxHeartbeats 1600000

lemma pair_succ_le_sq (a b K : ℕ) (ha : a+1 ≤ K) (hb : b+1 ≤ K) :
    Nat.pair a b+1 ≤ K^2 := by
  have hh := Nat.succ_le_of_lt (Nat.pair_lt_max_add_one_sq a b)
  exact hh.trans (Nat.pow_le_pow_left (by omega) 2)

lemma pair_succ_le_pow (a b K r : ℕ) (hr : r≠0) (hK : 1 ≤ K)
    (ha : a+1 ≤ K) (hb : b+1 ≤ K^r) : Nat.pair a b+1 ≤ K^(2*r) := by
  have hh := pair_succ_le_sq a b (K^r) (ha.trans (Nat.le_self_pow hr K)) hb
  simpa only [←Nat.pow_mul,mul_comm r 2] using hh

lemma boundaryCode_bound (j n : ℕ) (hj : j ≤ n) : boundaryCode j n+1 ≤ (n+1)^4 := by
  have h1 := pair_succ_le_sq j n (n+1) (by omega) le_rfl
  have h2 := pair_succ_le_pow 0 (Nat.pair j n) (n+1) 2 (by omega) (by omega) (by omega) h1
  exact h2

lemma tripleCode_bound (C h N n z K : ℕ) (hK : 2 ≤ K)
    (hC : C+1 ≤ K) (hh : h+1 ≤ K) (hN : N+1 ≤ K) (hn : n+1 ≤ K) (hz : z+1 ≤ K) :
    tripleCode C h N n z+1 ≤ K^32 := by
  have h1 := pair_succ_le_sq n z K hn hz
  have h2 := pair_succ_le_pow N (Nat.pair n z) K 2 (by omega) (by omega) hN h1
  have h3 := pair_succ_le_pow h (Nat.pair N (Nat.pair n z)) K 4 (by omega) (by omega) hh h2
  have h4 := pair_succ_le_pow C (Nat.pair h (Nat.pair N (Nat.pair n z))) K 8 (by omega) (by omega) hC h3
  exact pair_succ_le_pow 1 (Nat.pair C (Nat.pair h (Nat.pair N (Nat.pair n z)))) K 16
    (by omega) (by omega) (by omega) h4

lemma code_shift_bound (m M N r : ℕ) (hN : 1 ≤ N) (hM : M ≤ N) (hr : r≠0)
    (hm : m+1 ≤ (N+1)^r) : m+M+2 ≤ (N+1)^(r+1) := by
  have hpow := Nat.le_self_pow hr (N+1)
  have hsum : m+M+2 ≤ 2*(N+1)^r := by omega
  have hmul := Nat.mul_le_mul_right ((N+1)^r) (show 2 ≤ N+1 by omega)
  rw [pow_succ,mul_comm ((N+1)^r)]
  exact hsum.trans hmul

lemma boundaryCode_shift_bound (j n M : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) (hM : M ≤ n) :
    boundaryCode j n+M+2 ≤ (n+1)^5 :=
  code_shift_bound _ M n 4 hn hM (by omega) (boundaryCode_bound j n hj)

lemma tripleCode_comparable (C h N n z : ℕ) (hN : 1 ≤ N) (hC : C ≤ N) (hh : h ≤ N)
    (hn : n ≤ C*N) (hz : z ≤ N^h) : tripleCode C h N n z+1 ≤ (N+1)^(32*(h+2)) := by
  let K := (N+1)^(h+2)
  have hp : N+1 ≤ K := Nat.le_self_pow (by omega) _
  have hK : 2 ≤ K := by omega
  have hnK : n+1 ≤ K := by
    have hn1 : n ≤ N^2 := by nlinarith only [hn,hC]
    have hp2 := Nat.pow_lt_pow_left (show N<N+1 by omega) (show 2≠0 by omega)
    have hp3 := Nat.pow_le_pow_right (show 0<N+1 by omega) (show 2 ≤ h+2 by omega)
    have hn2 : n < (N+1)^2 := hn1.trans_lt hp2
    exact (Nat.succ_le_of_lt hn2).trans hp3
  have hzK : z+1 ≤ K := by
    have h1 := Nat.pow_le_pow_left (show N ≤ N+1 by omega) h
    have h2 := Nat.pow_lt_pow_right (show 1<N+1 by omega) (show h<h+2 by omega)
    exact Nat.succ_le_of_lt ((hz.trans h1).trans_lt h2)
  have hb := tripleCode_bound C h N n z K hK (by omega) (by omega) hp hnK hzK
  simpa only [K,←Nat.pow_mul,mul_comm (h+2) 32] using hb

lemma tripleCode_shift_bound (C h N n z M : ℕ) (hN : 1 ≤ N) (hC : C ≤ N) (hh : h ≤ N)
    (hM : M ≤ N) (hn : n ≤ C*N) (hz : z ≤ N^h) :
    tripleCode C h N n z+M+2 ≤ (N+1)^(32*(h+2)+1) :=
  code_shift_bound _ M N (32*(h+2)) hN hM (by omega) (tripleCode_comparable C h N n z hN hC hh hn hz)

end Erdos66RarePatternCodeGrowth
