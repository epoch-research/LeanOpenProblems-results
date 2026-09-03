import Submission.RestrictedRelativeMean
import Submission.ProductSmoothPrimeDensity

/-!
# An unconditional relative cofactor mean for the supplied smooth-prime family

The restricted mass hypothesis is discharged using the previously proved
fixed-ratio smooth-prime supply. The cofactor average remains essential;
this does not improve the smoothness ratio or prove a prime-only mean.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open HigherDivisors
set_option maxHeartbeats 4000000

noncomputable def smoothMangoldtWeight (N Y : ℕ) : ArithmeticFunction ℝ :=
  mangoldtRestriction (smoothPrimePool N Y : Set ℕ)

lemma smoothMangoldtMass_eq (N Y : ℕ) :
    restrictedMass (smoothMangoldtWeight N Y) N =
      ∑ p ∈ smoothPrimePool N Y, vonMangoldt p := by
  have hfilter : (Icc 1 N).filter (fun p => p ∈ smoothPrimePool N Y) = smoothPrimePool N Y := by
    ext p
    simp only [mem_filter]
    constructor
    · exact fun h => h.2
    · intro hp
      obtain ⟨hpP,_⟩ := mem_filter.mp hp
      obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hpP
      exact ⟨mem_Icc.mpr ⟨hpr.one_lt.le,by omega⟩,hp⟩
  simp only [restrictedMass,smoothMangoldtWeight,mangoldtRestriction,ArithmeticFunction.coe_mk,
    Finset.mem_coe,← sum_filter,hfilter]

lemma smoothMangoldtMass_card_lower (N Y : ℕ) :
    ((smoothPrimePool N Y).card : ℝ)/2 ≤ restrictedMass (smoothMangoldtWeight N Y) N := by
  rw [smoothMangoldtMass_eq]
  calc
    _ = ∑ _p ∈ smoothPrimePool N Y, (1/2 : ℝ) := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
      rw [vonMangoldt_apply_prime hpr]
      exact (show (1/2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
        (log_nat_mono hpr.two_le)

lemma supplied_cofactor_scale_eq (m : ℕ) : cofactorScale 100005 m = independentN 400020 m := by
  rw [cofactorScale_eq,independentN]

lemma supplied_smooth_scale_eq (m : ℕ) : cofactorScale 44425 m = independentN 177700 m := by
  rw [cofactorScale_eq,independentN]

/-- The actual fixed-ratio smooth-prime family has more than the mass
required by the relative-error theorem. -/
theorem eventually_supplied_smooth_mass :
    ∀ᶠ m : ℕ in atTop,
      (cofactorScale 100005 (2*m) : ℝ) ≤ (2 : ℝ)^m*
        restrictedMass (smoothMangoldtWeight (cofactorScale 100005 (2*m))
          (cofactorScale 44425 (2*m))) (cofactorScale 100005 (2*m)) := by
  obtain ⟨C,hC,HC⟩ := Erdos821.exists_product_smooth_prime_count
  obtain ⟨M,hM⟩ := eventually_atTop.mp HC
  filter_upwards [eventually_ge_atTop M,eventually_nat_poly_le_two_pow 1 (4*C) 1] with m hm hpoly
  have hcount := hM (2*m) (by omega)
  have hF := smoothMangoldtMass_card_lower (cofactorScale 100005 (2*m)) (cofactorScale 44425 (2*m))
  have hF0 := restrictedMass_nonneg
    (smoothMangoldtWeight (cofactorScale 100005 (2*m)) (cofactorScale 44425 (2*m)))
    (mangoldtRestriction_nonneg _) (cofactorScale 100005 (2*m))
  rw [← supplied_cofactor_scale_eq,← supplied_smooth_scale_eq] at hcount
  have hcm : (4 : ℝ)*C*m ≤ (2 : ℝ)^m := by
    have hh : 4*C*m ≤ 2^m := by
      have hh := (Nat.mul_le_mul_left (4*C) (Nat.le_succ m)).trans
        (by simpa only [pow_one,one_mul] using hpoly)
      exact hh
    exact_mod_cast hh
  have hweighted := mul_le_mul_of_nonneg_right hcm hF0
  push_cast at hcount
  have hcard := mul_le_mul_of_nonneg_left hF
    (show (0 : ℝ) ≤ 4*C*m by positivity)
  nlinarith only [hcount,hweighted,hcard]

/-- This result is unconditional, but concerns a cofactor times a prime
from the previously supplied family, not shifted primes alone. -/
theorem eventually_supplied_smooth_relative_mean (a b l v : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (hb : b+1 ≤ 100005)
    (hlevel : 2*b+1 ≤ l+100005) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ B : ℕ,
      cofactorScale l (2*m) ≤ B → B ≤ cofactorScale v (2*m) →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        let N := cofactorScale 100005 (2*m)
        let f := smoothMangoldtWeight N (cofactorScale 44425 (2*m))
        (∑ d ∈ Icc 1 (cofactorScale b (2*m)),
          |restrictedCofactorWeight f d (u d) 0 B N-(B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
            η*(B : ℝ)*restrictedMass f N := by
  filter_upwards [eventually_restricted_relative_mean a b l v 100005 ha hab hl hb hlevel η hη,
    eventually_supplied_smooth_mass] with m hmean hmass
  intro B hB hBup u
  exact hmean _ (mangoldtRestriction_nonneg _) (mangoldtRestriction_le _)
    B _ hB hBup le_rfl hmass u

end Erdos821.AnalyticSieve
