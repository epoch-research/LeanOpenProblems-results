import Submission.TwoLeastSieveEnvelope

/-! Summing the logarithmic layers geometrically bounds the product of the
two least distinct prime-factor logarithms without a log-log loss. -/
namespace Erdos972TwoLeastFactorMoment

open Finset ArithmeticFunction
open Erdos972TwoLeastPrimeFactors Erdos972TwoLeastSieveEnvelope
open Erdos972LeastFactorSieve Erdos972SelbergLowerTest Erdos972ExponentialSum
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma twoLeastCost_zero_of_secondFac_le_two {n : ℕ} (hn : secondFac n ≤ 2) :
    twoLeastCost n = 0 := by
  apply twoLeastCost_zero_of_empty
  intro he
  have hn1 : n ≠ 1 := by intro h; simp [h] at he
  have hq := mem_erase.mp (secondFac_mem he)
  have hp := Nat.minFac_prime hn1
  have hqprime := Nat.prime_of_mem_primeFactors hq.2
  have hple := Nat.minFac_le_of_dvd hqprime.two_le (Nat.dvd_of_mem_primeFactors hq.2)
  have hp2 := hp.two_le
  omega

lemma exists_log_layer {Q J : ℕ} (hQ : 2 < Q) (hJ : Q ≤ logLevel J) :
    ∃ j ∈ range J, logLevel j < Q ∧ Q ≤ logLevel (j+1) := by
  induction J with
  | zero => rw [logLevel_zero] at hJ; omega
  | succ J ih =>
    by_cases hQJ : Q ≤ logLevel J
    · obtain ⟨j, hj, hlo, hhi⟩ := ih hQJ
      exact ⟨j, mem_range.mpr ((mem_range.mp hj).trans (Nat.lt_succ_self J)), hlo, hhi⟩
    · exact ⟨J, mem_range.mpr (Nat.lt_succ_self J), lt_of_not_ge hQJ, hJ⟩

lemma sum_logLevel (J : ℕ) :
    (∑ j ∈ range J, Real.log (logLevel j)) = Real.log (logLevel J)-Real.log 2 := by
  induction J with
  | zero => simp [logLevel_zero]
  | succ J ih =>
    rw [sum_range_succ, ih, log_logLevel_succ]
    ring

lemma twoLeastCost_envelope_cover {n : ℕ} (J : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hlog : Real.log (secondFac n) ≤ K*Real.log (logLevel J)) :
    twoLeastCost n ≤
      (∑ j ∈ range J, cutoffEnvelope (2*Real.log (logLevel j)) (logLevel j) n)+
        cutoffEnvelope (K*Real.log (logLevel J)) (logLevel J) n := by
  have henv0 (j : ℕ) : 0 ≤ cutoffEnvelope (2*Real.log (logLevel j)) (logLevel j) n :=
    cutoffEnvelope_nonneg (by positivity [log_logLevel_pos j]) _ _
  have htail0 : 0 ≤ cutoffEnvelope (K*Real.log (logLevel J)) (logLevel J) n :=
    cutoffEnvelope_nonneg (mul_nonneg hK (log_logLevel_pos J).le) _ _
  have hsum0 := sum_nonneg (fun j (_ : j ∈ range J) => henv0 j)
  by_cases hn : secondFac n ≤ 2
  · rw [twoLeastCost_zero_of_secondFac_le_two hn]
    exact add_nonneg hsum0 htail0
  by_cases hJ : secondFac n ≤ logLevel J
  · obtain ⟨j, hj, hlo, hhi⟩ := exists_log_layer (lt_of_not_ge hn) hJ
    have hl : Real.log (secondFac n) ≤ 2*Real.log (logLevel j) := by
      have hh := monotone_log_natCast hhi
      dsimp only at hh
      rwa [log_logLevel_succ] at hh
    have hc := twoLeastCost_le_cutoffEnvelope (logLevel_two_le j)
      (show 0 ≤ 2*Real.log (logLevel j) by positivity [log_logLevel_pos j]) hlo hl
    exact hc.trans ((single_le_sum (fun i _ => henv0 i) hj).trans (le_add_of_nonneg_right htail0))
  · have hc := twoLeastCost_le_cutoffEnvelope (logLevel_two_le J)
      (mul_nonneg hK (log_logLevel_pos J).le) (lt_of_not_ge hJ) hlog
    exact hc.trans (le_add_of_nonneg_left hsum0)

/-- Finite weighted two-factor moment. There is no factor counting the
number of logarithmic layers in the resulting budget. -/
theorem weighted_twoLeastFactor_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) (J : ℕ)
    {X E K : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hlog : ∀ n ∈ S, Real.log (secondFac (g n)) ≤ K*Real.log (logLevel J))
    (hrows : ∀ d : ℕ, 0 < d → d ≤ (logLevel J)^3 → |row S a g d-X/d| ≤ E) :
    (∑ n ∈ S, a n*twoLeastCost (g n)) ≤
      (128+2*K^2+60*K)*X*Real.log (logLevel J)+
        (18+K^2+7*K)*E*(logLevel J:ℝ)^3*Real.log (logLevel J) := by
  let Z := logLevel J
  have hZlog : 0 ≤ Real.log Z := (log_logLevel_pos J).le
  have hmiddle (j : ℕ) (hj : j ∈ range J) :
      (∑ n ∈ S, a n*cutoffEnvelope (2*Real.log (logLevel j)) (logLevel j) (g n)) ≤
        (128*X+18*E*(Z:ℝ)^3)*Real.log (logLevel j) := by
    have hRZ := logLevel_mono (Nat.le_of_lt (mem_range.mp hj))
    have h := doublingEnvelope_upper S a g ha (logLevel_two_le j) hX hE
      (fun d hd hdb => hrows d hd (hdb.trans (Nat.pow_le_pow_left hRZ 3)))
    have hp : (logLevel j:ℝ)^3 ≤ (Z:ℝ)^3 := by
      exact_mod_cast Nat.pow_le_pow_left hRZ 3
    have he := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 18*E*Real.log (logLevel j) by positivity [log_logLevel_pos j])
    nlinarith only [h, he]
  have hsum := sum_le_sum hmiddle
  rw [← mul_sum, sum_logLevel] at hsum
  have hcoeff : 0 ≤ 128*X+18*E*(Z:ℝ)^3 := by positivity
  have hsbound :
      (∑ j ∈ range J, ∑ n ∈ S,
        a n*cutoffEnvelope (2*Real.log (logLevel j)) (logLevel j) (g n)) ≤
          (128*X+18*E*(Z:ℝ)^3)*Real.log Z := by
    exact hsum.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (Real.log_natCast_nonneg 2)) hcoeff)
  have htail := scaledEnvelope_upper S a g ha (logLevel_two_le J) hX hE hK hrows
  have hcover := sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
    (twoLeastCost_envelope_cover J hK (hlog n hn)) (ha n hn))
  simp only [mul_add, sum_add_distrib, mul_sum] at hcover
  rw [sum_comm] at hcover
  change (∑ n ∈ S, a n*twoLeastCost (g n)) ≤ _ at hcover
  nlinarith only [hcover, hsbound, htail]

/-- A convenient numerical specialization for the existing irrational
scales, whose output logarithm is at most 5000 times the sieve logarithm. -/
theorem weighted_twoLeastFactor_linear (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) (J : ℕ)
    {X E N : ℝ} (hN : 0 ≤ N) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hXup : X ≤ 7*N) (hEup : E*(logLevel J:ℝ)^4 ≤ N)
    (hlog : ∀ n ∈ S, Real.log (secondFac (g n)) ≤ 5000*Real.log (logLevel J))
    (hrows : ∀ d : ℕ, 0 < d → d ≤ (logLevel J)^3 → |row S a g d-X/d| ≤ E) :
    (∑ n ∈ S, a n*twoLeastCost (g n)) ≤ 1000000000*N*Real.log (logLevel J) := by
  have hb := weighted_twoLeastFactor_upper S a g ha J hX hE (by norm_num) hlog hrows
  have hZ1 : (1:ℝ) ≤ logLevel J := by exact_mod_cast (show 1 ≤ logLevel J by have := logLevel_two_le J; omega)
  have hE3 : E*(logLevel J:ℝ)^3 ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hZ1 (show 0 ≤ E*(logLevel J:ℝ)^3 by positivity)
    nlinarith only [hh, hEup]
  have hL := (log_logLevel_pos J).le
  have hx := mul_le_mul_of_nonneg_right hXup hL
  have he := mul_le_mul_of_nonneg_right hE3 hL
  have hn := mul_nonneg hN hL
  norm_num only at hb
  nlinarith only [hb, hx, he, hn]

#print axioms weighted_twoLeastFactor_upper
#print axioms weighted_twoLeastFactor_linear
end Erdos972TwoLeastFactorMoment
