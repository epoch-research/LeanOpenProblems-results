import Submission.CofactorLargeConductorMean

/-!
# A finite all-modulus error estimate for cofactor-averaged progressions

This retains the exact principal cofactor term and separates three errors:
small conductors, large primitive means, and prime powers lost on lifting.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def cofactorPrincipalMain (d A B N : ℕ) : ℝ :=
  (coprimeCofactorCount d A B : ℝ)*(mangoldtSum N-nonunitMangoldt d N)/(d.totient : ℝ)

lemma harmonic_natCast_nonneg (Q : ℕ) : 0 ≤ (harmonic Q : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))

lemma inverse_totient_le_of_local_weight (d : ℕ) (K : ℝ)
    (H : (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    1/(d.totient : ℝ) ≤ K/(d : ℝ) := by
  exact (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤2))
    (Nat.cast_nonneg _)).trans H

lemma small_conductor_mean_of_local_weight (Q R : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*smallConductorCofactorWeight d R) ≤
      K*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R)) := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, K/(d : ℝ)*smallConductorCofactorWeight d R :=
      sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right (H d hd) (smallConductorCofactorWeight_nonneg d R))
    _ = K*∑ d ∈ Icc 1 Q, smallConductorCofactorWeight d R/(d : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun d _ => by ring)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (smallConductorCofactorWeight_harmonic_mean Q R) hK
      convert hh using 1; ring

lemma large_conductor_mean_of_local_weight (Q R N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, largePrimitiveConductorMangoldt d R N/(d.totient : ℝ)) ≤
      K*(harmonic Q : ℝ)*primitivePoolMean (Ioc R Q) N := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, K/(d : ℝ)*largePrimitiveConductorMangoldt d R N := by
      apply sum_le_sum
      intro d hd
      have hh := mul_le_mul_of_nonneg_right (inverse_totient_le_of_local_weight d K (H d hd))
        (largePrimitiveConductorMangoldt_nonneg d R N)
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
    _ = K*∑ d ∈ Icc 1 Q, largePrimitiveConductorMangoldt d R N/(d : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun d _ => by ring)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (largePrimitiveConductorMangoldt_harmonic_mean Q R N) hK
      convert hh using 1; ring

lemma lift_error_mean_of_local_weight (Q N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, (d : ℝ)*characterLiftError d N/(d.totient : ℝ)) ≤
      K*(Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 Q) :
      (d : ℝ)*characterLiftError d N/(d.totient : ℝ) ≤ K*((Nat.log 2 N : ℝ)*Real.log Q) := by
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (mem_Icc.mp hd).1
    have hlog : characterLiftError d N ≤ (Nat.log 2 N : ℝ)*Real.log Q :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hd0 (by exact_mod_cast (mem_Icc.mp hd).2)) (Nat.cast_nonneg _)
    have hratio : (d : ℝ)/(d.totient : ℝ) ≤ K := by
      have hh := mul_le_mul_of_nonneg_left (inverse_totient_le_of_local_weight d K (H d hd)) hd0.le
      have he : (d : ℝ)*(K/(d : ℝ))=K := by field_simp
      rw [he] at hh
      simpa only [one_div,← div_eq_mul_inv] using hh
    have hh := mul_le_mul hratio hlog (characterLiftError_nonneg d N) hK
    convert hh using 1; ring
  calc
    _ ≤ ∑ _d ∈ Icc 1 Q, K*((Nat.log 2 N : ℝ)*Real.log Q) := sum_le_sum hpoint
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; ring

/-- A common local weight bound controls the complete averaged discrepancy. -/
theorem cofactor_all_modulus_mean_of_local_weight (Q R A B N : ℕ)
    (u : ∀ d : ℕ, (ZMod d)ˣ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, |cofactorCongruenceWeight d (u d) A B N-cofactorPrincipalMain d A B N|) ≤
      K*((mangoldtSum N)*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R))+
        ((B-A : ℕ) : ℝ)*(harmonic Q : ℝ)*primitivePoolMean (Ioc R Q) N+
          ((B-A : ℕ) : ℝ)*(Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 Q) :
      |cofactorCongruenceWeight d (u d) A B N-cofactorPrincipalMain d A B N| ≤
        mangoldtSum N*((2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*smallConductorCofactorWeight d R)+
          ((B-A : ℕ) : ℝ)*(largePrimitiveConductorMangoldt d R N/(d.totient : ℝ))+
            ((B-A : ℕ) : ℝ)*((d : ℝ)*characterLiftError d N/(d.totient : ℝ)) := by
    letI : NeZero d := ⟨by have := (mem_Icc.mp hd).1; omega⟩
    have hh := cofactor_averaged_progression_split d (u d) R A B N
    convert hh using 1; dsimp [cofactorPrincipalMain]; ring
  have hh := sum_le_sum hpoint
  simp only [sum_add_distrib,← mul_sum] at hh
  have hsmall := mul_le_mul_of_nonneg_left (small_conductor_mean_of_local_weight Q R K hK H)
    (mangoldtSum_nonneg N)
  have hlarge := mul_le_mul_of_nonneg_left (large_conductor_mean_of_local_weight Q R N K hK H)
    (Nat.cast_nonneg (B-A))
  have hlift := mul_le_mul_of_nonneg_left (lift_error_mean_of_local_weight Q N K hK H)
    (Nat.cast_nonneg (B-A))
  apply (hh.trans (_root_.add_le_add (_root_.add_le_add hsmall hlarge) hlift)).trans_eq
  ring

/-- The all-modulus bound is unconditional. The constant depends only on
 epsilon, not on any interval endpoint or residue. -/
theorem exists_cofactor_all_modulus_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R A B N : ℕ, ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
      (∑ d ∈ Icc 1 Q, |cofactorCongruenceWeight d (u d) A B N-cofactorPrincipalMain d A B N|) ≤
        C*(Q : ℝ)^ε*((mangoldtSum N)*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R))+
          ((B-A : ℕ) : ℝ)*(harmonic Q : ℝ)*primitivePoolMean (Ioc R Q) N+
            ((B-A : ℕ) : ℝ)*(Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_two_pow_primeFactors_div_totient ε hε
  refine ⟨C,hC,?_⟩
  intro Q R A B N u
  exact cofactor_all_modulus_mean_of_local_weight Q R A B N u (C*(Q : ℝ)^ε) (by positivity)
    (fun d hd => HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)

end Erdos821.AnalyticSieve
