import Submission.FinePoolBands

/-! Summing the thirty-six retained-pool rejection bands and the short tail. -/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma hyperbolic_card_le_fine_pool_bands (d H m k : ℕ) :
    (hyperbolicPrimePairPool d H (2^(128*finePoolEndpoint 0*m)) H).card ≤
      (∑ i ∈ range k, (hyperbolicPrimePairPool d H
        (2^(128*finePoolEndpoint i*m)) (2^(128*finePoolEndpoint (i+1)*m))).card)+
      (hyperbolicPrimePairPool d H (2^(128*finePoolEndpoint k*m)) H).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h := hyperbolic_prime_pair_card_split d H
      (2^(128*finePoolEndpoint k*m)) (2^(128*finePoolEndpoint (k+1)*m)) H
    omega

theorem eventually_fine_pool_rough_rejection_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((roughProgressionPrimes c (independentN 15600000 m) X).card : ℝ)) ≤
          (1999/2000 : ℝ)*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  filter_upwards [eventually_all_fine_pool_bands,eventually_scaled_band_short_tail,eventually_ge_atTop 1]
    with m hband hshort hm
  intro X hXlo hXhi
  let P := widePairPool 10000000 m
  let V := poolTotientMass P
  have hpos : 0 ≤ (X : ℝ)*V := mul_nonneg (Nat.cast_nonneg X) (poolTotientMass_nonneg _)
  have hpoint (c : ℕ) (hc : c ∈ P) :
      ((roughProgressionPrimes c (independentN 15600000 m) X).card : ℝ) ≤
        (∑ i : Fin 36, ((hyperbolicPrimePairPool c (X/c)
          (2^(128*finePoolEndpoint i*m)) (2^(128*finePoolEndpoint (i+1)*m))).card : ℝ))+
        ((hyperbolicPrimePairPool c (X/c) (2^(128*10000007*m)) (X/c)).card : ℝ) := by
    have hb := widePairPool_bounds 10000000 m c hc
    have hrough := rough_progression_card_le_hyperbolic c (independentN 15600000 m) X
      (by omega) (widePairPool_smooth_odd 10000000 15600000 m c (by decide) (by decide) hm hc).1
      (not_prime_two_pow _ (by omega))
    have h := hrough.trans (hyperbolic_card_le_fine_pool_bands c (X/c) m 36)
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((hyperbolicPrimePairPool c (X/c)
      (2^(128*finePoolEndpoint i*m)) (2^(128*finePoolEndpoint (i+1)*m))).card : ℝ))]
    exact_mod_cast h
  have hsum := mul_le_mul_of_nonneg_left (sum_le_sum hpoint) (Real.log_natCast_nonneg X)
  rw [sum_add_distrib,mul_add] at hsum
  have hlong : Real.log (X : ℝ)*(∑ c ∈ P, ∑ i : Fin 36,
      ((hyperbolicPrimePairPool c (X/c)
        (2^(128*finePoolEndpoint i*m)) (2^(128*finePoolEndpoint (i+1)*m))).card : ℝ)) ≤
          (99926455/100000000 : ℝ)*(X : ℝ)*V := by
    rw [sum_comm,mul_sum]
    apply (sum_le_sum (fun i _ => hband i X hXlo hXhi)).trans_eq
    rw [← sum_mul,← sum_mul,finePool_budget_sum]
  have htail : Real.log (X : ℝ)*(∑ c ∈ P,
      ((hyperbolicPrimePairPool c (X/c) (2^(128*10000007*m)) (X/c)).card : ℝ)) ≤
        (11/62500 : ℝ)*(X : ℝ)*V := by
    rw [mul_sum]
    apply (sum_le_sum (fun c hc => hshort X c hXlo hXhi
      (widePairPool_bounds 10000000 m c hc).2.1 (widePairPool_bounds 10000000 m c hc).2.2)).trans_eq
    dsimp [V,poolTotientMass]
    rw [mul_sum]
    exact sum_congr rfl (fun c _ => by ring)
  change _ ≤ (1999/2000 : ℝ)*(X : ℝ)*V
  nlinarith only [hsum,hlong,htail,hpos]

end Erdos821.AnalyticSieve
