import Submission.WideSecondSieve
import Submission.ReciprocalDensity

/-!
# Reciprocal divergence at a fixed strict sub-square-root smoothness ratio

The wide modulus family removes all but one logarithm from the counting
loss. The resulting reciprocal divergence is unconditional, but the ratio
19400/40019 does not approach zero and does not settle Erdős 821.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 2000000

lemma smooth_prime_relative_of_power_bound (N Y A a b p : ℕ)
    (hp : p ∈ smoothPrimePool N Y) (hl : A < p) (hscale : Y^a ≤ A^b) :
    p ∈ rationalSmoothShiftedPrimes a b := by
  obtain ⟨hpN,hps⟩ := mem_filter.mp hp
  refine ⟨(Nat.mem_primesBelow.mp hpN).2,?_⟩
  intro q hq
  have hqY := Nat.mem_smoothNumbers'.mp hps q (Nat.prime_of_mem_primeFactors hq)
    (Nat.dvd_of_mem_primeFactors hq)
  exact (Nat.pow_le_pow_left hqY.le a).trans
    (hscale.trans (Nat.pow_le_pow_left (Nat.le_sub_one_of_lt hl) b))

lemma progressionScaleN_pow_swap (a b m : ℕ) :
    (progressionScaleN (b*m))^a = (progressionScaleN (a*m))^b := by
  simp only [progressionScaleN,← pow_mul]
  exact congrArg (fun e : ℕ => (2 : ℕ)^e) (by ring : 64*(b*m)*a = 64*(a*m)*b)

lemma wide_smooth_prime_relative (m p : ℕ)
    (hp : p ∈ smoothPrimePool (progressionScaleN (40020*m)) (progressionScaleN (19400*m)))
    (hl : progressionScaleN (40019*m) < p) :
    p ∈ rationalSmoothShiftedPrimes 40019 19400 := by
  exact smooth_prime_relative_of_power_bound _ _ _ _ _ _ hp hl
    (progressionScaleN_pow_swap 40019 19400 m).le

lemma wide_small_prime_card (m : ℕ) :
    ((smoothPrimePool (progressionScaleN (40020*m)) (progressionScaleN (19400*m))).filter
      (fun p => p ≤ progressionScaleN (40019*m))).card ≤ progressionScaleN (40019*m) := by
  have hsub : (smoothPrimePool (progressionScaleN (40020*m)) (progressionScaleN (19400*m))).filter
      (fun p => p ≤ progressionScaleN (40019*m)) ⊆ Icc 1 (progressionScaleN (40019*m)) := by
    intro p hp
    obtain ⟨hp,hbound⟩ := mem_filter.mp hp
    have hprime := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
    exact mem_Icc.mpr ⟨hprime.pos,hbound⟩
  exact (card_le_card hsub).trans_eq (by simp)

lemma eventually_wide_relative_prime_count :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ)^(2561280*m) ≤ (2*(wideCountConstant : ℝ))*m*
        (((range (2^(2561280*m)+1)).filter
          (fun p => p ∈ rationalSmoothShiftedPrimes 40019 19400)).card : ℝ) := by
  filter_upwards [eventually_wide_smooth_prime_count,
    eventually_nat_poly_le_two_pow 1 (2*wideCountConstant) 1] with m hcount hpoly
  let N := progressionScaleN (40020*m)
  let A := progressionScaleN (40019*m)
  let S := smoothPrimePool N (progressionScaleN (19400*m))
  let G := S.filter (fun p => A < p)
  let H := (range (2^(2561280*m)+1)).filter (fun p => p ∈ rationalSmoothShiftedPrimes 40019 19400)
  have hGsub : G ⊆ H := by
    intro p hp
    obtain ⟨hp,hl⟩ := mem_filter.mp hp
    have hpN := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).1
    refine mem_filter.mpr ⟨mem_range.mpr ?_,wide_smooth_prime_relative m p hp hl⟩
    simpa only [N,progressionScaleN,show 64*(40020*m) = 2561280*m by omega] using hpN
  have hcard : S.card ≤ G.card+A := by
    have hsplit := card_filter_add_card_filter_not (s := S) (p := fun p => A < p)
    have hsmall : (S.filter (fun p => ¬A < p)).card ≤ A := by
      simpa only [not_lt] using wide_small_prime_card m
    change (S.filter (fun p => A < p)).card+(S.filter (fun p => ¬A < p)).card = S.card at hsplit
    dsimp only [G]
    omega
  have hp : 2*wideCountConstant*m ≤ 2^(64*m) := by
    have h := hpoly
    simp only [one_mul,pow_one] at h
    exact (Nat.mul_le_mul_left (2*wideCountConstant) (by omega : m ≤ m+1)).trans
      (h.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsmallN : (2*(wideCountConstant : ℝ))*m*A ≤ (N : ℝ) := by
    have h := Nat.mul_le_mul_right A hp
    have he : 2^(64*m)*A = N := by
      dsimp [A,N,progressionScaleN]
      rw [← pow_add]
      congr 1
      omega
    rw [he] at h
    exact_mod_cast h
  have hcount' : (N : ℝ) ≤ (wideCountConstant : ℝ)*m*((G.card : ℝ)+A) := by
    apply hcount.trans
    gcongr
    exact_mod_cast hcard
  have hretained : (N : ℝ) ≤ (2*(wideCountConstant : ℝ))*m*(G.card : ℝ) := by
    nlinarith only [hcount',hsmallN]
  have hfinal := hretained.trans (mul_le_mul_of_nonneg_left
    (show (G.card : ℝ) ≤ H.card by exact_mod_cast card_le_card hGsub) (by positivity))
  simpa only [N,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,
    show 64*(40020*m) = 2561280*m by omega,H] using hfinal

/-- Fixed rational smoothness strictly below one half, with a divergent
reciprocal series rather than only divergence at subcritical powers. -/
theorem wide_prime_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 40019 19400).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  exact not_summable_reciprocal_of_eventual_dyadic_count _ (fun p hp => hp.1.pos)
    2561280 (by decide) (2*(wideCountConstant : ℝ)) eventually_wide_relative_prime_count

end Erdos821
