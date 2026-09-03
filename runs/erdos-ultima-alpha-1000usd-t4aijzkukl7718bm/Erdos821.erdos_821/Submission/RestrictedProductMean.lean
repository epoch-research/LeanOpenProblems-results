import Submission.RestrictedCofactorCompletion
import Submission.RestrictedPrincipalMean
import Submission.CofactorProductMean

/-!
# Uniform restricted-weight all-modulus mean at the product half level

The constant is independent of the arithmetic weight f. The main term
retains its actual mass F(X), but the error is measured at the ambient
prime-variable scale. A relative saving therefore needs a lower bound on
F(X); none is asserted for an arbitrary prime restriction.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

/-- The level condition is `2*b+1 <= l+t`, in place of the earlier
prime-variable-only half level `2*b+5 <= t`. -/
theorem exists_restricted_product_principal_power_saving (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ m B X : ℕ,
      cofactorScale l m ≤ B → B ≤ cofactorScale v m → X ≤ cofactorScale t m →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B X-
          restrictedCofactorPrincipal f d 0 B X|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  obtain ⟨C,hC,HC⟩ := exists_restricted_all_modulus_mean_bound ε (by dsimp [ε]; positivity)
  refine ⟨C*cofactorProductErrorConstant a b v t,
    mul_pos hC (cofactorProductErrorConstant_pos a b v t),?_⟩
  intro f hf hΛ m B X hB hBup hX u
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B X-
    restrictedCofactorPrincipal f d 0 B X|
  let Z : ℝ := (2 : ℝ)^m
  let N : ℝ := cofactorScale t m
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hlogX : (Nat.log 2 X : ℝ) ≤ Nat.log 2 (cofactorScale t m) := by
    exact_mod_cast Nat.log_mono_right hX
  have hmain0 := HC f hf hΛ (cofactorScale b m) (cofactorScale a m) B X u
  have hmain : E ≤ C*(cofactorScale b m : ℝ)^ε*
      (restrictedMass f X*(harmonic (cofactorScale b m) : ℝ)*(cofactorScale a m : ℝ)*
        (Real.sqrt (cofactorScale a m)*(1+Real.log (cofactorScale a m)))+
        (harmonic (cofactorScale b m) : ℝ)*restrictedPrimitiveMean f
          (Ioc (cofactorScale a m) (cofactorScale b m)) B X+
        (B : ℝ)*(cofactorScale b m : ℝ)*(Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m)) := by
    apply hmain0.trans
    gcongr
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  have hsmall := (cofactorScale_small_saving a l m hl).trans (show (cofactorScale l m : ℝ) ≤ B by exact_mod_cast hB)
  have hlarge := restricted_cofactorScale_primitive_saving f hf hΛ a b l v t m B X ha hab (by omega) (by omega)
    hlevel hB hBup hX
  have hnorm := cofactor_product_error_normalize E C Z B N (restrictedMass f X)
    (harmonic (cofactorScale b m)) ((cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m))
    (1+Real.log (cofactorScale a m))
    (restrictedPrimitiveMean f (Ioc (cofactorScale a m) (cofactorScale b m)) B X)
    (cofactorScale b m) (Nat.log 2 (cofactorScale t m)) (Real.log (cofactorScale b m))
    (cofactorProductMeanConstant b v t*((m : ℝ)+1)^3)
    hC.le hZ.le (Nat.cast_nonneg B) (Nat.cast_nonneg _) (harmonic_natCast_nonneg _) (by positivity)
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    (by convert hmain using 1; dsimp [E,Z]; ring)
    (((restrictedMass_le_mangoldt f hΛ X).trans (Erdos821.mangoldtSum_le_six_mul X)).trans (by dsimp [N]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hX) (by norm_num)))
    (by convert hsmall using 1; dsimp [Z]; ring)
    hlarge (cofactorScale_lift_saving b t m ht)
  have hpoly := mul_le_mul_of_nonneg_left (cofactor_product_polynomial_bound a b v t m)
    (show 0 ≤ C*(B : ℝ)*N by dsimp [N]; positivity)
  have hscaled : Z*E ≤ C*(B : ℝ)*N*cofactorProductErrorConstant a b v t*((m : ℝ)+1)^6 := by
    have hh := hnorm.trans hpoly
    convert hh using 1; ring
  change E ≤ C*cofactorProductErrorConstant a b v t*((m : ℝ)+1)^6/Z*(B : ℝ)*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  field_simp

/-- The natural main term is `B*F(X)/d` with the actual restricted mass. -/
theorem exists_restricted_product_natural_power_saving (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ m B X : ℕ,
      cofactorScale l m ≤ B → B ≤ cofactorScale v m → X ≤ cofactorScale t m →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B X-
          (B : ℝ)*restrictedMass f X/(d : ℝ)|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*(cofactorScale t m : ℝ) := by
  obtain ⟨K₁,hK₁,HK₁⟩ := exists_restricted_product_principal_power_saving a b l v t ha hab hl ht hlevel
  obtain ⟨K₂,hK₂,HK₂⟩ := exists_restricted_principal_power_saving_cutoff b t l (by omega) (by omega) (by omega)
  refine ⟨K₁+K₂,add_pos hK₁ hK₂,?_⟩
  intro f hf hΛ m B X hB hBup hX u
  have htri : (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B X-
      (B : ℝ)*restrictedMass f X/(d : ℝ)|) ≤
      (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorWeight f d (u d) 0 B X-restrictedCofactorPrincipal f d 0 B X|)+
      (∑ d ∈ Icc 1 (cofactorScale b m), |restrictedCofactorPrincipal f d 0 B X-(B : ℝ)*restrictedMass f X/(d : ℝ)|) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun d _ => abs_sub_le _ _ _)
  have hprincipal := HK₂ f hf hΛ m 0 B X hX (by simpa only [Nat.sub_zero] using hB)
  simp only [Nat.sub_zero] at hprincipal
  apply (htri.trans (_root_.add_le_add (HK₁ f hf hΛ m B X hB hBup hX u) hprincipal)).trans_eq
  ring


end Erdos821.AnalyticSieve
