import Submission.CofactorProductPrimitiveMean
import Submission.CofactorBilinearCompletion
import Submission.UniformCofactorNaturalMean

/-!
# An all-modulus cofactor mean at the product half level

The cofactor prefix lies between two fixed power scales, and the prime
variable may stop at any cutoff below its ambient scale. The main term
uses the actual Mangoldt mass. The result is an upper bound for the
averaged discrepancy, not a prime-successor lower bound.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma cofactor_product_error_normalize (E C Z B N S H R T P Q J K W : ℝ)
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hE : E ≤ C*Z*(S*H*R*T+H*P+B*Q*J*K))
    (hSN : S ≤ 6*N) (hsmall : Z^2*R ≤ B) (hlarge : Z^2*P ≤ W*B*N) (hlift : Z^2*Q ≤ N) :
    Z*E ≤ C*B*N*(6*H*T+H*W+J*K) := by
  have hEZ := mul_le_mul_of_nonneg_left hE hZ
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul hSN hsmall (mul_nonneg (sq_nonneg Z) hR) (by positivity))
    (mul_nonneg hH hT)
  have hl := mul_le_mul_of_nonneg_left hlarge hH
  have hi := mul_le_mul_of_nonneg_right hlift (mul_nonneg (mul_nonneg hB hJ) hK)
  have hsum := mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hs hl) hi) hC
  nlinarith only [hEZ,hsum]

noncomputable def cofactorProductErrorConstant (a b v t : ℕ) : ℝ :=
  6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1)+
    (256*(b : ℝ)+1)*cofactorProductMeanConstant b v t+(256*(t : ℝ))*(256*(b : ℝ))

lemma cofactorProductErrorConstant_pos (a b v t : ℕ) : 0 < cofactorProductErrorConstant a b v t := by
  have := cofactorProductMeanConstant_nonneg b v t
  unfold cofactorProductErrorConstant
  positivity

lemma cofactor_product_polynomial_bound (a b v t m : ℕ) :
    6*(harmonic (cofactorScale b m) : ℝ)*(1+Real.log (cofactorScale a m))+
      (harmonic (cofactorScale b m) : ℝ)*(cofactorProductMeanConstant b v t*((m : ℝ)+1)^3)+
        (Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m) ≤
      cofactorProductErrorConstant a b v t*((m : ℝ)+1)^6 := by
  have hm : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hT : 1+Real.log (cofactorScale a m) ≤ (256*(a : ℝ)+1)*((m : ℝ)+1) := by
    nlinarith only [cofactorScale_log_le a m,Nat.cast_nonneg (α := ℝ) m]
  have hH := cofactorScale_harmonic_le b m
  have hJK := mul_le_mul (cofactorScale_natLog_le t m) (cofactorScale_log_le b m)
    (Real.log_natCast_nonneg _) (by positivity)
  have hs := mul_le_mul_of_nonneg_left (mul_le_mul hH hT
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (by positivity)) (show (0 : ℝ) ≤ 6 by norm_num)
  have hl := mul_le_mul_of_nonneg_right hH
    (mul_nonneg (cofactorProductMeanConstant_nonneg b v t) (by positivity : 0 ≤ ((m : ℝ)+1)^3))
  have hp2 := pow_le_pow_right₀ hm (by decide : 2 ≤ 6)
  have hp4 := pow_le_pow_right₀ hm (by decide : 4 ≤ 6)
  have hs' := mul_le_mul_of_nonneg_left hp2
    (show 0 ≤ 6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1) by positivity)
  have hl' := mul_le_mul_of_nonneg_left hp4
    (mul_nonneg (show 0 ≤ 256*(b : ℝ)+1 by positivity) (cofactorProductMeanConstant_nonneg b v t))
  have hi' := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ (256*(t : ℝ))*(256*(b : ℝ)) by positivity)
  unfold cofactorProductErrorConstant
  nlinarith only [hs,hl,hJK,hs',hl',hi']

/-- The level condition is `2*b+1 <= l+t`, in place of the earlier
prime-variable-only half level `2*b+5 <= t`. -/
theorem exists_cofactor_product_principal_power_saving (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ m B X : ℕ,
      cofactorScale l m ≤ B → B ≤ cofactorScale v m → X ≤ cofactorScale t m →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) 0 B X-
          cofactorPrincipalMain d 0 B X|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  obtain ⟨C,hC,HC⟩ := exists_cofactor_bilinear_all_modulus_mean_bound ε (by dsimp [ε]; positivity)
  refine ⟨C*cofactorProductErrorConstant a b v t,
    mul_pos hC (cofactorProductErrorConstant_pos a b v t),?_⟩
  intro m B X hB hBup hX u
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) 0 B X-
    cofactorPrincipalMain d 0 B X|
  let Z : ℝ := (2 : ℝ)^m
  let N : ℝ := cofactorScale t m
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hlogX : (Nat.log 2 X : ℝ) ≤ Nat.log 2 (cofactorScale t m) := by
    exact_mod_cast Nat.log_mono_right hX
  have hmain0 := HC (cofactorScale b m) (cofactorScale a m) B X u
  have hmain : E ≤ C*(cofactorScale b m : ℝ)^ε*
      (mangoldtSum X*(harmonic (cofactorScale b m) : ℝ)*(cofactorScale a m : ℝ)*
        (Real.sqrt (cofactorScale a m)*(1+Real.log (cofactorScale a m)))+
        (harmonic (cofactorScale b m) : ℝ)*primitiveCofactorBilinearMean
          (Ioc (cofactorScale a m) (cofactorScale b m)) B X+
        (B : ℝ)*(cofactorScale b m : ℝ)*(Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m)) := by
    apply hmain0.trans
    gcongr
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  have hsmall := (cofactorScale_small_saving a l m hl).trans (show (cofactorScale l m : ℝ) ≤ B by exact_mod_cast hB)
  have hlarge := cofactorScale_bilinear_primitive_saving a b l v t m B X ha hab (by omega) (by omega)
    hlevel hB hBup hX
  have hnorm := cofactor_product_error_normalize E C Z B N (mangoldtSum X)
    (harmonic (cofactorScale b m)) ((cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m))
    (1+Real.log (cofactorScale a m))
    (primitiveCofactorBilinearMean (Ioc (cofactorScale a m) (cofactorScale b m)) B X)
    (cofactorScale b m) (Nat.log 2 (cofactorScale t m)) (Real.log (cofactorScale b m))
    (cofactorProductMeanConstant b v t*((m : ℝ)+1)^3)
    hC.le hZ.le (Nat.cast_nonneg B) (Nat.cast_nonneg _) (harmonic_natCast_nonneg _) (by positivity)
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    (by convert hmain using 1; dsimp [E,Z]; ring)
    ((Erdos821.mangoldtSum_le_six_mul X).trans (by dsimp [N]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hX) (by norm_num)))
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

/-- The natural main term is `B*psi(X)/d` with the actual cutoff X. -/
theorem exists_cofactor_product_natural_power_saving (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ m B X : ℕ,
      cofactorScale l m ≤ B → B ≤ cofactorScale v m → X ≤ cofactorScale t m →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) 0 B X-
          (B : ℝ)*mangoldtSum X/(d : ℝ)|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*(cofactorScale t m : ℝ) := by
  obtain ⟨K₁,hK₁,HK₁⟩ := exists_cofactor_product_principal_power_saving a b l v t ha hab hl ht hlevel
  obtain ⟨K₂,hK₂,HK₂⟩ := exists_cofactor_principal_power_saving_cutoff b t l (by omega) (by omega) (by omega)
  refine ⟨K₁+K₂,add_pos hK₁ hK₂,?_⟩
  intro m B X hB hBup hX u
  have htri : (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) 0 B X-
      (B : ℝ)*mangoldtSum X/(d : ℝ)|) ≤
      (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) 0 B X-cofactorPrincipalMain d 0 B X|)+
      (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorPrincipalMain d 0 B X-(B : ℝ)*mangoldtSum X/(d : ℝ)|) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun d _ => abs_sub_le _ _ _)
  have hprincipal := HK₂ m 0 B X hX (by simpa only [Nat.sub_zero] using hB)
  simp only [Nat.sub_zero] at hprincipal
  apply (htri.trans (_root_.add_le_add (HK₁ m B X hB hBup hX u) hprincipal)).trans_eq
  ring

end Erdos821.AnalyticSieve
