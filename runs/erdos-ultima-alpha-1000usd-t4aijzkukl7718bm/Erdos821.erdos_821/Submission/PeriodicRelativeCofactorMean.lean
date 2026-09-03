import Submission.PeriodicCofactorMean

/-!
# Uniform density-free cofactor-level relative error

This elementary complement to the product-half-level theorem works when
the cofactor length exceeds the modulus cutoff. The prime weight may be
arbitrarily sparse, and its upper cutoff is unrestricted.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma periodic_relative_coefficient_le (Q B P H Z : ℝ)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hZ : 0 < Z)
    (hQ : Z^2*Q ≤ B) (hP : Z^2 ≤ P) :
    Q+B*H/P ≤ (1+H)/Z^2*B := by
  have hZ2 : 0 < Z^2 := sq_pos_of_pos hZ
  have hq : Q ≤ B/Z^2 := (le_div_iff₀ hZ2).mpr (by simpa only [mul_comm] using hQ)
  have hp : H/P ≤ H/Z^2 := div_le_div_of_nonneg_left hH hZ2 hP
  have hh := _root_.add_le_add hq (mul_le_mul_of_nonneg_left hp hB)
  convert hh using 1 <;> ring

/-- The support lower cutoff controls nonunits; it is not a lower bound on
the total mass. No domination by Lambda is needed. -/
theorem eventually_periodic_relative_mean (b : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ cofactorScale 1 m ≤ n) →
      ∀ B N : ℕ, cofactorScale (b+1) m ≤ B →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B N-
          (B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤ η*(B : ℝ)*restrictedMass f N := by
  have ht := (tendsto_shifted_poly_div_two_pow 1).const_mul (256*(b : ℝ)+2)
  simp only [pow_one,mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hη] with m hm
  intro f hf hs B N hB u
  let Q := cofactorScale b m
  let P := cofactorScale 1 m
  let Z : ℝ := (2 : ℝ)^m
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hQ : Z^2*(Q : ℝ) ≤ B :=
    (cofactorScale_lift_saving b (b+1) m (by omega)).trans (by exact_mod_cast hB)
  have hP : Z^2 ≤ P := by
    have hh := cofactorScale_lift_saving 0 1 m (by decide)
    simpa [cofactorScale,progressionScaleN,Z,P] using hh
  have hH := cofactorScale_harmonic_le b m
  have hcoef : ((Q : ℝ)+(B : ℝ)*(harmonic Q : ℝ)/(P : ℝ)) ≤ η*B := by
    apply (periodic_relative_coefficient_le Q B P (harmonic Q) Z (Nat.cast_nonneg _)
      (harmonic_natCast_nonneg _) hZ hQ hP).trans
    have hH' : 1+(harmonic Q : ℝ) ≤ (256*(b : ℝ)+2)*((m : ℝ)+1) := by
      dsimp [Q]
      nlinarith only [hH,Nat.cast_nonneg (α := ℝ) m]
    have hZone : 1 ≤ Z := one_le_pow₀ (by norm_num)
    have hZZ : Z ≤ Z^2 := by nlinarith only [hZone]
    have hfirst : (1+(harmonic Q : ℝ))/Z^2 ≤
        (256*(b : ℝ)+2)*((m : ℝ)+1)/Z := by
      apply (div_le_div_of_nonneg_right hH' (sq_nonneg Z)).trans
      exact div_le_div_of_nonneg_left (by positivity) hZ hZZ
    have hlast : (256*(b : ℝ)+2)*((m : ℝ)+1)/Z ≤ η := by
      simpa only [← mul_div_assoc] using hm.le
    exact mul_le_mul_of_nonneg_right (hfirst.trans hlast) (Nat.cast_nonneg B)
  have hmain := periodic_prime_cofactor_relative_bound f hf Q B N P (cofactorScale_pos 1 m) hs u
  exact hmain.trans (mul_le_mul_of_nonneg_right hcoef (restrictedMass_nonneg f hf N))

/-- Any prime subset is permitted, even one with zero or very small mass.
Consequently this cannot be used as a lower bound for the size of that set. -/
theorem eventually_periodic_prime_subset_mean (b : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ S : Set ℕ, ∀ B N : ℕ,
      cofactorScale (b+1) m ≤ B → ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        let f := mangoldtRestriction {n : ℕ | n ∈ S ∧ n.Prime ∧ cofactorScale 1 m ≤ n}
        (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B N-
          (B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤ η*(B : ℝ)*restrictedMass f N := by
  filter_upwards [eventually_periodic_relative_mean b η hη] with m hm
  intro S B N hB u
  apply hm _ (mangoldtRestriction_nonneg _) _ B N hB u
  intro n hn
  by_cases hs : n ∈ S ∧ n.Prime ∧ cofactorScale 1 m ≤ n
  · exact hs.2
  · exfalso
    apply hn
    simp only [mangoldtRestriction,ArithmeticFunction.coe_mk,Set.mem_setOf_eq,hs,if_false]

end Erdos821.AnalyticSieve
