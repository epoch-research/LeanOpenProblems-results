import Submission.CofactorPrincipalMean

/-!
# A power-saving all-modulus mean with multiplicative principal density

The main term is now `(B-A)*psi(N)/d`, which is suitable for a sieve kernel.
The result concerns a cofactor times a prime-power weighted variable. It is
not a distribution assertion for primes alone at these moduli.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma cofactor_principal_log_polynomial (b t m : ℕ) :
    (harmonic (cofactorScale b m) : ℝ)*
      (6+(Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m)) ≤
        ((256*(b : ℝ)+1)*(6+(256*(t : ℝ))*(256*(b : ℝ))))*((m : ℝ)+1)^6 := by
  have hm : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hH := cofactorScale_harmonic_le b m
  have hJ := cofactorScale_natLog_le t m
  have hK := cofactorScale_log_le b m
  have hJK := mul_le_mul hJ hK (Real.log_natCast_nonneg _) (by positivity)
  have hpow2 : (1 : ℝ) ≤ ((m : ℝ)+1)^2 := one_le_pow₀ hm
  have hbracket : 6+(Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m) ≤
      (6+(256*(t : ℝ))*(256*(b : ℝ)))*((m : ℝ)+1)^2 := by
    nlinarith only [hJK,hpow2]
  have hprod := mul_le_mul hH hbracket
    (by have := Real.log_natCast_nonneg (cofactorScale b m); positivity) (by positivity)
  have hpoly := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm (by decide : 3 ≤ 6))
    (show 0 ≤ (256*(b : ℝ)+1)*(6+(256*(t : ℝ))*(256*(b : ℝ))) by positivity)
  nlinarith only [hprod,hpoly]

lemma exists_cofactor_principal_power_saving (b t l : ℕ) (hb : 1 ≤ b) (ht : 1 ≤ t) (hl : 1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B : ℕ, cofactorScale l m ≤ B-A →
      (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorPrincipalMain d A B (cofactorScale t m)-
        ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t m)/(d : ℝ)|) ≤
          K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  obtain ⟨C,hC,HC⟩ := exists_cofactor_principal_mean_bound ε (by dsimp [ε]; positivity)
  let D : ℝ := (256*(b : ℝ)+1)*(6+(256*(t : ℝ))*(256*(b : ℝ)))
  refine ⟨C*D,mul_pos hC (by dsimp [D]; positivity),?_⟩
  intro m A B hAB
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |cofactorPrincipalMain d A B (cofactorScale t m)-
    ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t m)/(d : ℝ)|
  let L : ℝ := (B-A : ℕ)
  let N : ℝ := cofactorScale t m
  let Z : ℝ := (2 : ℝ)^m
  let H : ℝ := harmonic (cofactorScale b m)
  let J : ℝ := Nat.log 2 (cofactorScale t m)
  let Q : ℝ := Real.log (cofactorScale b m)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hH : 0 ≤ H := harmonic_natCast_nonneg _
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Real.log_natCast_nonneg _
  have hmain := HC (cofactorScale b m) A B (cofactorScale t m)
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  change E ≤ C*Z*H*(mangoldtSum (cofactorScale t m)+L*J*Q) at hmain
  have hZL : Z^2 ≤ L := by
    have hh := cofactorScale_lift_saving 0 l m hl
    have he : (cofactorScale 0 m : ℝ)=1 := by simp [cofactorScale,progressionScaleN]
    rw [he,mul_one] at hh
    exact hh.trans (by dsimp [L]; exact_mod_cast hAB)
  have hZN : Z^2 ≤ N := by
    have hh := cofactorScale_lift_saving 0 t m ht
    simpa [cofactorScale,progressionScaleN,Z,N] using hh
  have hS : Z^2*mangoldtSum (cofactorScale t m) ≤ 6*L*N := by
    have hh := mul_le_mul hZL (Erdos821.mangoldtSum_le_six_mul (cofactorScale t m))
      (mangoldtSum_nonneg _) hL
    convert hh using 1; dsimp [N]; ring
  have hI := mul_le_mul_of_nonneg_right hZN (mul_nonneg (mul_nonneg hL hJ) hQ)
  have hsum := mul_le_mul_of_nonneg_left (_root_.add_le_add hS hI) (mul_nonneg hC.le hH)
  have hEZ := mul_le_mul_of_nonneg_left hmain hZ.le
  have hnormalized : Z*E ≤ C*L*N*(H*(6+J*Q)) := by
    nlinarith only [hEZ,hsum]
  have hpoly := mul_le_mul_of_nonneg_left (cofactor_principal_log_polynomial b t m)
    (show 0 ≤ C*L*N by positivity)
  have hscaled : Z*E ≤ C*L*N*D*((m : ℝ)+1)^6 := by
    have hh := hnormalized.trans hpoly
    convert hh using 1; dsimp [D]; ring
  change E ≤ C*D*((m : ℝ)+1)^6/Z*L*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  field_simp

/-- The all-modulus cofactor mean with the simple multiplicative main term.
All residues and both cofactor endpoints may vary with the scale. -/
theorem exists_cofactor_natural_main_power_saving (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B : ℕ, cofactorScale l m ≤ B-A →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
          ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t m)/(d : ℝ)|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  obtain ⟨K₁,hK₁,HK₁⟩ := exists_cofactor_all_modulus_power_saving a b t l ha hab ht hlevel hl
  obtain ⟨K₂,hK₂,HK₂⟩ := exists_cofactor_principal_power_saving b t l (by omega) (by omega) (by omega)
  refine ⟨K₁+K₂,add_pos hK₁ hK₂,?_⟩
  intro m A B hAB u
  have htriangle : (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
      ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t m)/(d : ℝ)|) ≤
      (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B (cofactorScale t m)-
        cofactorPrincipalMain d A B (cofactorScale t m)|)+
      (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorPrincipalMain d A B (cofactorScale t m)-
        ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t m)/(d : ℝ)|) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun d _ => abs_sub_le _ _ _)
  apply (htriangle.trans (_root_.add_le_add (HK₁ m A B hAB u) (HK₂ m A B hAB))).trans_eq
  ring

end Erdos821.AnalyticSieve
