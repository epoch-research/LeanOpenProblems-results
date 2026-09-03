import Submission.CofactorBilinearSplit
import Submission.CofactorBilinearLargeSieve

/-!
# All-modulus completion of the retained bilinear conductor mean
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma largeCofactorBilinearConductor_le_divisor_sum (d R Q B N : ℕ) (hdQ : d ≤ Q) :
    largeCofactorBilinearConductor d R B N ≤
      ∑ c ∈ Icc (R+1) Q, if c ∣ d then
        ∑ ψ ∈ Erdos821.primitiveCharacters c, cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ vonMangoldt N‖ else 0 := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨hcD,hcR⟩ := mem_filter.mp hc
    have hcdiv := (mem_erase.mp hcD).2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hcR,(Nat.divisor_le hcdiv).trans hdQ⟩,
      Nat.dvd_of_mem_divisors hcdiv⟩
  · intro c hc hnot
    exact sum_nonneg (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg _))

lemma largeCofactorBilinearConductor_harmonic_mean (Q R B N : ℕ) :
    (∑ d ∈ Icc 1 Q, largeCofactorBilinearConductor d R B N/(d : ℝ)) ≤
      (harmonic Q : ℝ)*primitiveCofactorBilinearMean (Ioc R Q) B N := by
  let S : ℕ → ℝ := fun c => ∑ ψ ∈ Erdos821.primitiveCharacters c, cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ vonMangoldt N‖
  have hS : ∀ c, 0 ≤ S c := fun c => sum_nonneg (fun ψ _ => mul_nonneg (cofactorMaxPrefix_nonneg ψ B) (norm_nonneg _))
  have hH : 0 ≤ (harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (∑ c ∈ Icc (R+1) Q, if c ∣ d then S c else 0)/(d : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right
        (largeCofactorBilinearConductor_le_divisor_sum d R Q B N (mem_Icc.mp hd).2)
        (Nat.cast_nonneg d)
    _ = ∑ c ∈ Icc (R+1) Q, S c*(∑ d ∈ Icc 1 Q with c ∣ d, (d : ℝ)⁻¹) := by
      simp only [sum_div]
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro d hd
      split_ifs <;> simp [div_eq_mul_inv]
    _ ≤ ∑ c ∈ Icc (R+1) Q, S c*((c : ℝ)⁻¹*(harmonic Q : ℝ)) := by
      apply sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (Sieve.sum_inv_multiples_le_harmonic Q c (by have := (mem_Icc.mp hc).1; omega)) (hS c)
    _ = (harmonic Q : ℝ)*∑ c ∈ Icc (R+1) Q, S c/(c : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      ring
    _ ≤ (harmonic Q : ℝ)*∑ c ∈ Icc (R+1) Q, S c/(c.totient : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply sum_le_sum
      intro c hc
      have hc0 : 0 < c := by have := (mem_Icc.mp hc).1; omega
      exact div_le_div_of_nonneg_left (hS c) (by exact_mod_cast Nat.totient_pos.mpr hc0)
        (by exact_mod_cast Nat.totient_le c)
    _ = _ := by rw [show Icc (R+1) Q = Ioc R Q by ext n; simp]; rfl

lemma bilinear_conductor_mean_of_local_weight (Q R B N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*largeCofactorBilinearConductor d R B N) ≤
      K*(harmonic Q : ℝ)*primitiveCofactorBilinearMean (Ioc R Q) B N := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, K/(d : ℝ)*largeCofactorBilinearConductor d R B N := by
      apply sum_le_sum
      intro d hd
      have hh := mul_le_mul_of_nonneg_right (H d hd)
        (largeCofactorBilinearConductor_nonneg d R B N)
      exact hh
    _ = K*∑ d ∈ Icc 1 Q, largeCofactorBilinearConductor d R B N/(d : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun d _ => by ring)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (largeCofactorBilinearConductor_harmonic_mean Q R B N) hK
      convert hh using 1; ring

/-- A common local weight bound controls the complete averaged discrepancy. -/
theorem cofactor_bilinear_all_modulus_mean_of_local_weight (Q R B N : ℕ)
    (u : ∀ d : ℕ, (ZMod d)ˣ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, |cofactorCongruenceWeight d (u d) 0 B N-cofactorPrincipalMain d 0 B N|) ≤
      K*((mangoldtSum N)*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R))+
        (harmonic Q : ℝ)*primitiveCofactorBilinearMean (Ioc R Q) B N+
          (B : ℝ)*(Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 Q) :
      |cofactorCongruenceWeight d (u d) 0 B N-cofactorPrincipalMain d 0 B N| ≤
        mangoldtSum N*((2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*smallConductorCofactorWeight d R)+
          ((2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*largeCofactorBilinearConductor d R B N)+
            (B : ℝ)*((d : ℝ)*characterLiftError d N/(d.totient : ℝ)) := by
    letI : NeZero d := ⟨by have := (mem_Icc.mp hd).1; omega⟩
    have hh := cofactor_bilinear_progression_split d (u d) R B N
    convert hh using 1; dsimp [cofactorPrincipalMain]; ring
  have hh := sum_le_sum hpoint
  simp only [sum_add_distrib,← mul_sum] at hh
  have hsmall := mul_le_mul_of_nonneg_left (small_conductor_mean_of_local_weight Q R K hK H)
    (mangoldtSum_nonneg N)
  have hlarge := bilinear_conductor_mean_of_local_weight Q R B N K hK H
  have hlift := mul_le_mul_of_nonneg_left (lift_error_mean_of_local_weight Q N K hK H)
    (Nat.cast_nonneg B)
  apply (hh.trans (_root_.add_le_add (_root_.add_le_add hsmall hlarge) hlift)).trans_eq
  ring

/-- The all-modulus bound is unconditional. The constant depends only on
 epsilon, not on any interval endpoint or residue. -/
theorem exists_cofactor_bilinear_all_modulus_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R B N : ℕ, ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
      (∑ d ∈ Icc 1 Q, |cofactorCongruenceWeight d (u d) 0 B N-cofactorPrincipalMain d 0 B N|) ≤
        C*(Q : ℝ)^ε*((mangoldtSum N)*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R))+
          (harmonic Q : ℝ)*primitiveCofactorBilinearMean (Ioc R Q) B N+
            (B : ℝ)*(Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_two_pow_primeFactors_div_totient ε hε
  refine ⟨C,hC,?_⟩
  intro Q R B N u
  exact cofactor_bilinear_all_modulus_mean_of_local_weight Q R B N u (C*(Q : ℝ)^ε) (by positivity)
    (fun d hd => HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)


end Erdos821.AnalyticSieve
