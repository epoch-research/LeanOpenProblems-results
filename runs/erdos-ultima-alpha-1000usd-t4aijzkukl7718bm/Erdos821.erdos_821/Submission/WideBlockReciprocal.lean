import Submission.ParametricWideDensity
import Submission.WideReciprocalDensity

/-!
# Reciprocal divergence from the blockwise fixed-mass prime count

The endpoint transfer removes small primes by a power saving. It does
not infer reciprocal divergence from a higher logarithmic counting loss.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma small_smooth_prime_card_le (N Y A : ℕ) :
    ((smoothPrimePool N Y).filter (fun p => p ≤ A)).card ≤ A := by
  have hs : (smoothPrimePool N Y).filter (fun p => p ≤ A) ⊆ Icc 1 A := by
    intro p hp
    obtain ⟨hp,hA⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2.pos,hA⟩
  exact (card_le_card hs).trans_eq (by simp)

lemma eventually_relative_prime_count_of_single_log (t b C : ℕ) (ht : 1 ≤ t)
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (2*(C : ℝ))*m*
        (((range (independentN t m+1)).filter
          (fun p => p ∈ rationalSmoothShiftedPrimes (t-1) b)).card : ℝ) := by
  filter_upwards [H,eventually_nat_poly_le_two_pow 1 (2*C) 1] with m hcount hpoly
  let N := independentN t m
  let A := independentN (t-1) m
  let S := smoothPrimePool N (independentN b m)
  let G := S.filter (fun p => A < p)
  let R := (range (N+1)).filter (fun p => p ∈ rationalSmoothShiftedPrimes (t-1) b)
  have hGsub : G ⊆ R := by
    intro p hp
    obtain ⟨hp,hl⟩ := mem_filter.mp hp
    have hpN := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).1
    refine mem_filter.mpr ⟨mem_range.mpr hpN,?_⟩
    apply smooth_prime_relative_of_power_bound N (independentN b m) A (t-1) b p hp hl
    apply le_of_eq
    simpa only [A,independentN,progressionScaleN,mul_assoc] using
      progressionScaleN_pow_swap (t-1) b m
  have hcard : S.card ≤ G.card+A := by
    have hsplit := card_filter_add_card_filter_not (s := S) (p := fun p => A < p)
    have hsmall : (S.filter (fun p => ¬A < p)).card ≤ A := by
      simpa only [not_lt] using small_smooth_prime_card_le N (independentN b m) A
    change (S.filter (fun p => A < p)).card+(S.filter (fun p => ¬A < p)).card = S.card at hsplit
    dsimp only [G]
    omega
  have hp : 2*C*m ≤ 2^(64*m) := by
    simp only [one_mul,pow_one] at hpoly
    exact (Nat.mul_le_mul_left (2*C) (Nat.le_succ m)).trans
      (hpoly.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsmallN : (2*(C : ℝ))*m*A ≤ (N : ℝ) := by
    have h := Nat.mul_le_mul_right A hp
    have he : 2^(64*m)*A=N := by
      dsimp [A,N,independentN]
      rw [← pow_add]
      congr 1
      have ht' := congrArg (fun z : ℕ => z*m) (Nat.sub_add_cancel ht)
      nlinarith only [ht']
    rw [he] at h
    exact_mod_cast h
  have hcount' : (N : ℝ) ≤ (C : ℝ)*m*((G.card : ℝ)+A) := by
    apply hcount.trans
    gcongr
    exact_mod_cast hcard
  have hretained : (N : ℝ) ≤ (2*(C : ℝ))*m*(G.card : ℝ) := by
    nlinarith only [hcount',hsmallN]
  exact hretained.trans (mul_le_mul_of_nonneg_left
    (show (G.card : ℝ) ≤ R.card by exact_mod_cast card_le_card hGsub) (by positivity))

theorem not_summable_relative_of_single_log_count (t b C : ℕ) (ht : 1 ≤ t)
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    ¬Summable ((rationalSmoothShiftedPrimes (t-1) b).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  apply not_summable_reciprocal_of_eventual_dyadic_count _ (fun p hp => hp.1.pos)
    (64*t) (by positivity) (2*(C : ℝ))
  simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat] using
    eventually_relative_prime_count_of_single_log t b C ht H

/-- Reciprocal divergence at the improved relative smoothness ratio
19268660/40000019, approximately 0.4817162712. -/
theorem wide_block_prime_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 40000019 19268660).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  obtain ⟨C,_hC,hcount⟩ := exists_wide_block_smooth_prime_count
  exact not_summable_relative_of_single_log_count 40000020 19268660 C (by decide) hcount

lemma rationalSmoothShiftedPrimes_mono_ratio (a b c d : ℕ) (ha : 0<a)
    (hcross : b*c ≤ d*a) :
    rationalSmoothShiftedPrimes a b ⊆ rationalSmoothShiftedPrimes c d := by
  intro p hp
  refine ⟨hp.1,?_⟩
  intro q hq
  have hp0 : 0<p-1 := by have := hp.1.two_le; omega
  apply (Nat.pow_le_pow_iff_left ha.ne').mp
  calc
    (q^c)^a = (q^a)^c := by rw [← pow_mul,← pow_mul,Nat.mul_comm c a]
    _ ≤ ((p-1)^b)^c := Nat.pow_le_pow_left (hp.2 q hq) c
    _ = (p-1)^(b*c) := (pow_mul _ _ _).symm
    _ ≤ (p-1)^(d*a) := Nat.pow_le_pow_right hp0 hcross
    _ = _ := pow_mul _ _ _

lemma not_summable_reciprocal_superset (S T : Set ℕ) (hST : S ⊆ T)
    (H : ¬Summable (S.indicator (fun p : ℕ => 1/(p : ℝ)))) :
    ¬Summable (T.indicator (fun p : ℕ => 1/(p : ℝ))) := by
  intro hT
  apply H
  apply hT.of_nonneg_of_le
  · intro p
    dsimp [Set.indicator]
    split_ifs <;> positivity
  · intro p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (hST hp)]
    · rw [Set.indicator_of_notMem hp]
      dsimp [Set.indicator]
      split_ifs <;> positivity

/-- A short decimal version: every prime factor q of p-1 satisfies
q^25000 <= (p-1)^12043. -/
theorem wide_block_decimal_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 25000 12043).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  exact not_summable_reciprocal_superset _ _
    (rationalSmoothShiftedPrimes_mono_ratio 40000019 19268660 25000 12043
      (by decide) (by norm_num)) wide_block_prime_reciprocal_divergence

lemma wide_block_reciprocal_strict_improvement :
    (19268660/40000019 : ℝ)<19400/40019 := by norm_num

lemma wide_block_multiplicity_strict_improvement :
    (2073135/4000001 : ℝ)<1036568/2000001 := by norm_num

end Erdos821
