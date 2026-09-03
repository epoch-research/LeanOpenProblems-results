import Submission.TwoLeastPrimeFactors
import Submission.SharpReciprocalPrimeCost

/-! A weighted envelope for integers whose second distinct prime factor
is beyond the sieve cutoff. The divisor level is exactly R^3. -/
namespace Erdos972TwoLeastSieveEnvelope

open Finset ArithmeticFunction
open Erdos972TwoLeastPrimeFactors Erdos972MaskedPrimeSieve
open Erdos972SelbergWeights Erdos972SelbergLowerTest Erdos972SelbergLowerMain
open Erdos972LeastFactorSieve Erdos972SharpReciprocalPrimeCost
open Erdos972ChebyshevRowMean Erdos972ExponentialSum
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def cutoffEnvelope (L : ℝ) (R n : ℕ) : ℝ := by
  classical
  exact L^2*(if n.Coprime R.factorial then 1 else 0) +
    L*∑ p ∈ smallPrimes R,
      if p ∣ n ∧ NoOtherSmallPrime R p n then Real.log p else 0

lemma cutoffEnvelope_nonneg {L : ℝ} (hL : 0 ≤ L) (R n : ℕ) :
    0 ≤ cutoffEnvelope L R n := by
  unfold cutoffEnvelope
  positivity [Real.log_natCast_nonneg]

lemma secondFac_log_nonneg (n : ℕ) : 0 ≤ Real.log (secondFac n) :=
  Real.log_natCast_nonneg _

lemma twoLeastCost_le_cutoffEnvelope {R n : ℕ} {L : ℝ} (hR : 2 ≤ R)
    (hL : 0 ≤ L) (hQ : R < secondFac n) (hlogQ : Real.log (secondFac n) ≤ L) :
    twoLeastCost n ≤ cutoffEnvelope L R n := by
  classical
  by_cases he : (n.primeFactors.erase n.minFac).Nonempty
  swap
  · rw [twoLeastCost_zero_of_empty he]
    exact cutoffEnvelope_nonneg hL R n
  have hn0 : n ≠ 0 := by intro h; simp [h] at he
  have hn1 : n ≠ 1 := by intro h; simp [h] at he
  have hp := Nat.minFac_prime hn1
  have hqmem := mem_of_mem_erase (secondFac_mem he)
  have hpq := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hqmem).two_le
    (Nat.dvd_of_mem_primeFactors hqmem)
  have hlogpq : Real.log n.minFac ≤ Real.log (secondFac n) :=
    monotone_log_natCast hpq
  have hsum0 : 0 ≤ ∑ p ∈ smallPrimes R,
      if p ∣ n ∧ NoOtherSmallPrime R p n then Real.log p else 0 := by
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  by_cases hpR : R < n.minFac
  · have hc := (Nat.coprime_factorial_iff hn1).mpr hpR
    unfold cutoffEnvelope twoLeastCost
    rw [if_pos hc, mul_one]
    have hb := mul_le_mul (hlogpq.trans hlogQ) hlogQ
      (secondFac_log_nonneg n) hL
    have hs := mul_nonneg hL hsum0
    nlinarith only [hb, hs]
  · have hpS : n.minFac ∈ smallPrimes R :=
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos, le_of_not_gt hpR⟩, hp⟩
    have hc := secondFac_noOtherSmallPrime hn0 he hQ
    have hs := single_le_sum (f := fun p =>
      if p ∣ n ∧ NoOtherSmallPrime R p n then Real.log p else 0)
      (s := smallPrimes R) (fun p _ => by
        dsimp only
        split_ifs
        · exact Real.log_natCast_nonneg _
        · exact le_rfl) hpS
    dsimp only at hs
    rw [if_pos ⟨Nat.minFac_dvd n, hc⟩] at hs
    have hprod := mul_le_mul_of_nonneg_left hlogQ (Real.log_natCast_nonneg n.minFac)
    have hsum := mul_le_mul_of_nonneg_left hs hL
    unfold cutoffEnvelope twoLeastCost
    split_ifs <;> nlinarith only [hprod, hsum, sq_nonneg L]

lemma weighted_cutoffEnvelope_eq (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (L : ℝ) (R : ℕ) :
    (∑ n ∈ S, a n*cutoffEnvelope L R (g n)) =
      L^2*roughWeight S a g R +
        L*∑ p ∈ smallPrimes R, Real.log p*singlePrimeWeight S a g R p := by
  classical
  simp only [cutoffEnvelope, mul_add, sum_add_distrib, roughWeight,
    singlePrimeWeight, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro n hn
    split_ifs <;> ring
  · rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro n hn
    split_ifs <;> ring

lemma smallPrime_log_sum_upper (R : ℕ) :
    (∑ p ∈ smallPrimes R, Real.log p) ≤ 7*(R:ℝ) := by
  calc
    _ = ∑ p ∈ smallPrimes R, Λ p := by
      exact sum_congr rfl (fun p hp => (vonMangoldt_apply_prime (mem_filter.mp hp).2).symm)
    _ ≤ ∑ p ∈ Ioc 0 R, Λ p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => vonMangoldt_nonneg)
    _ ≤ _ := by
      simpa only [Chebyshev.psi, Nat.floor_natCast] using
        psi_le_seven_mul (Nat.cast_nonneg (α := ℝ) R)

lemma smallPrime_reciprocal_log_sum_upper (R : ℕ) :
    (∑ p ∈ smallPrimes R, Real.log p/(p:ℝ)) ≤ Real.log R+7 := by
  calc
    _ = ∑ p ∈ smallPrimes R, Λ p/(p:ℝ) := by
      apply sum_congr rfl
      intro p hp
      rw [vonMangoldt_apply_prime (mem_filter.mp hp).2]
    _ ≤ ∑ p ∈ Ioc 0 R, Λ p/(p:ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    _ ≤ _ := reciprocal_mangoldt_log_upper R

/-- The logarithmic factor of the designated prime can be summed before
paying the row errors. This is the key distinction from an unweighted count
of numbers with at most one small prime factor. -/
theorem weighted_cutoffEnvelope_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R : ℕ} (hR : 2 ≤ R)
    {X E L : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^3 → |row S a g d-X/d| ≤ E) :
    Real.log R*(∑ n ∈ S, a n*cutoffEnvelope L R (g n)) ≤
      2*X*L^2+4*X*L*(Real.log R+7)+
        E*(R:ℝ)^2*Real.log R*(L^2+7*L*R) := by
  have hrough := log_mul_rough_weight_upper S a g ha hR hX hE
    (fun d hd hdb => hrows d hd (hdb.trans (Nat.pow_le_pow_right (by omega) (by omega))))
  have hsingle (p : ℕ) (hp : p ∈ smallPrimes R) :=
    log_mul_singlePrimeWeight_upper S a g ha hR (mem_filter.mp hp).2 hX hE
      (fun d hd hdb => hrows d hd (hdb.trans (by
        have hpR := (mem_Ioc.mp (mem_filter.mp hp).1).2
        nlinarith)))
  have hsum := sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hsingle p hp)
    (Real.log_natCast_nonneg p))
  have hsum' : Real.log R*(∑ p ∈ smallPrimes R, Real.log p*singlePrimeWeight S a g R p) ≤
      4*X*(∑ p ∈ smallPrimes R, Real.log p/(p:ℝ))+
      E*(R:ℝ)^2*Real.log R*(∑ p ∈ smallPrimes R, Real.log p) := by
    convert hsum using 1
    · simp only [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    · simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
  have hmain := mul_le_mul_of_nonneg_left (smallPrime_reciprocal_log_sum_upper R)
    (show 0 ≤ 4*X by positivity)
  have herr := mul_le_mul_of_nonneg_left (smallPrime_log_sum_upper R)
    (show 0 ≤ E*(R:ℝ)^2*Real.log R by positivity [Real.log_natCast_nonneg R])
  have hsum'' : Real.log R*(∑ p ∈ smallPrimes R, Real.log p*singlePrimeWeight S a g R p) ≤
      4*X*(Real.log R+7)+7*E*(R:ℝ)^3*Real.log R := by
    nlinarith only [hsum', hmain, herr]
  rw [weighted_cutoffEnvelope_eq]
  have hfirst := mul_le_mul_of_nonneg_left hrough (sq_nonneg L)
  have hsecond := mul_le_mul_of_nonneg_left hsum'' hL
  nlinarith only [hfirst, hsecond]

/-- On a doubling-logarithm layer the cost has size X log R, with no
log-logarithmic factor. -/
theorem doublingEnvelope_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R : ℕ} (hR : 2 ≤ R)
    {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^3 → |row S a g d-X/d| ≤ E) :
    (∑ n ∈ S, a n*cutoffEnvelope (2*Real.log R) R (g n)) ≤
      128*X*Real.log R+18*E*(R:ℝ)^3*Real.log R := by
  have hl0 : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlhalf : (1/2:ℝ) ≤ Real.log R := by
    have hh := monotone_log_natCast hR
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_gt_d9]
  have hlR : Real.log R ≤ R := by
    have hh := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (show 0 < R by omega) : (0:ℝ) < R)
    linarith only [hh]
  have h := weighted_cutoffEnvelope_upper S a g ha hR hX hE
    (show 0 ≤ 2*Real.log R by positivity) hrows
  have hmain := mul_le_mul_of_nonneg_left hlhalf (show 0 ≤ 112*X*Real.log R by positivity)
  have herr := mul_le_mul_of_nonneg_left hlR
    (show 0 ≤ 4*E*(R:ℝ)^2*(Real.log R)^2 by positivity)
  apply (mul_le_mul_iff_right₀ hl0).mp
  nlinarith only [h, hmain, herr]

/-- The terminal envelope allows an arbitrary fixed logarithmic scale loss. -/
theorem scaledEnvelope_upper (S : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℕ) (ha : ∀ n ∈ S, 0 ≤ a n) {R : ℕ} (hR : 2 ≤ R)
    {X E K : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^3 → |row S a g d-X/d| ≤ E) :
    (∑ n ∈ S, a n*cutoffEnvelope (K*Real.log R) R (g n)) ≤
      (2*K^2+60*K)*X*Real.log R+(K^2+7*K)*E*(R:ℝ)^3*Real.log R := by
  have hl0 : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlhalf : (1/2:ℝ) ≤ Real.log R := by
    have hh := monotone_log_natCast hR
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_gt_d9]
  have hlR : Real.log R ≤ R := by
    have hh := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (show 0 < R by omega) : (0:ℝ) < R)
    linarith only [hh]
  have h := weighted_cutoffEnvelope_upper S a g ha hR hX hE
    (show 0 ≤ K*Real.log R by positivity) hrows
  have hmain := mul_le_mul_of_nonneg_left hlhalf
    (show 0 ≤ 56*K*X*Real.log R by positivity)
  have herr := mul_le_mul_of_nonneg_left hlR
    (show 0 ≤ K^2*E*(R:ℝ)^2*(Real.log R)^2 by positivity)
  apply (mul_le_mul_iff_right₀ hl0).mp
  nlinarith only [h, hmain, herr]

#print axioms twoLeastCost_le_cutoffEnvelope
#print axioms weighted_cutoffEnvelope_upper
#print axioms doublingEnvelope_upper
#print axioms scaledEnvelope_upper
end Erdos972TwoLeastSieveEnvelope
