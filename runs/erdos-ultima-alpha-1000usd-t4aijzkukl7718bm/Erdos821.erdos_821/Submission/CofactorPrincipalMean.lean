import Submission.CofactorPrincipalCount

/-!
# Replacing the exact cofactor principal term by the multiplicative density

The replacement is uniform over all moduli. Its error is harmonic, rather
than linear, in the modulus cutoff; the local-factor counts are subpower.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma coprimeCofactorCount_le_length (d A B : ℕ) : coprimeCofactorCount d A B ≤ B-A := by
  unfold coprimeCofactorCount
  simpa using (card_filter_le (Icc (A+1) B) (fun a => a.Coprime d))

lemma cofactorPrincipalMain_error (d A B N : ℕ) (hd : 0 < d) :
    |cofactorPrincipalMain d A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ)| ≤
      (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*mangoldtSum N+
        ((B-A : ℕ) : ℝ)*characterLiftError d N/(d.totient : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hφ : (0 : ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hS : 0 ≤ mangoldtSum N := mangoldtSum_nonneg N
  have hU : 0 ≤ nonunitMangoldt d N := nonunitMangoldt_nonneg d N
  have hcount : (coprimeCofactorCount d A B : ℝ) ≤ ((B-A : ℕ) : ℝ) := by
    exact_mod_cast coprimeCofactorCount_le_length d A B
  have he : cofactorPrincipalMain d A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ) =
      ((coprimeCofactorCount d A B : ℝ)-((B-A : ℕ) : ℝ)*(d.totient : ℝ)/(d : ℝ))*
        (mangoldtSum N/(d.totient : ℝ))-
          (coprimeCofactorCount d A B : ℝ)*nonunitMangoldt d N/(d.totient : ℝ) := by
    unfold cofactorPrincipalMain
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (div_nonneg hS hφ.le),
    abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hU) hφ.le)]
  have h1 := mul_le_mul_of_nonneg_right (coprimeCofactorCount_density_error d A B hd) (div_nonneg hS hφ.le)
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul hcount (nonunitMangoldt_le_liftError d N hd.ne') hU (Nat.cast_nonneg _)) hφ.le
  apply (_root_.add_le_add h1 h2).trans_eq
  ring

lemma local_factor_div_totient_le (B : ℝ) (hB : 0 ≤ B) (d : ℕ) (hd : 0 < d) :
    B^d.primeFactors.card/(d.totient : ℝ) ≤ (2*B)^d.primeFactors.card/(d : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).mpr
  have hh := mul_le_mul_of_nonneg_left (totient_ratio_le_two_pow_primeFactors d hd) (pow_nonneg hB d.primeFactors.card)
  convert hh using 1
  · ring
  · rw [mul_pow]; ring

lemma exists_uniform_local_factor_div_totient (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q d : ℕ, 0 < d → d ≤ Q →
      B^d.primeFactors.card/(d.totient : ℝ) ≤ C*(Q : ℝ)^ε/(d : ℝ) := by
  obtain ⟨C,hC,HC⟩ := Sieve.exists_card_pow_le_const_product_rpow (2*B) ε (by linarith) hε
  refine ⟨C,hC,?_⟩
  intro Q d hd hdQ
  apply (local_factor_div_totient_le B (by linarith) d hd).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  apply (HC d.primeFactors (fun p hp => Nat.pos_of_mem_primeFactors hp)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast
    ((Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)).trans hdQ)) hε.le

lemma cofactor_principal_mean_of_local_weight (Q A B N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, |cofactorPrincipalMain d A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ)|) ≤
      K*(harmonic Q : ℝ)*(mangoldtSum N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 Q) :
      |cofactorPrincipalMain d A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ)| ≤
        (K/(d : ℝ))*(mangoldtSum N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
    have hdR : (0 : ℝ)<d := by exact_mod_cast (mem_Icc.mp hd).1
    have h1 : 1/(d.totient : ℝ) ≤ K/(d : ℝ) :=
      (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤3)) (Nat.cast_nonneg _)).trans (H d hd)
    have hlog : characterLiftError d N ≤ (Nat.log 2 N : ℝ)*Real.log Q :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hdR (by exact_mod_cast (mem_Icc.mp hd).2)) (Nat.cast_nonneg _)
    have hsmall := mul_le_mul_of_nonneg_right (H d hd) (mangoldtSum_nonneg N)
    have hlarge := mul_le_mul_of_nonneg_left
      (mul_le_mul h1 hlog (characterLiftError_nonneg d N) (div_nonneg hK hdR.le)) (Nat.cast_nonneg (B-A))
    apply (cofactorPrincipalMain_error d A B N (mem_Icc.mp hd).1).trans
    convert _root_.add_le_add hsmall hlarge using 1 <;> ring
  apply (sum_le_sum hpoint).trans_eq
  rw [← sum_mul]
  have he : (∑ d ∈ Icc 1 Q, K/(d : ℝ)) = K*(harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl (fun d _ => by ring)
  rw [he]

/-- Uniform over all positive moduli, including those with small conductors. -/
theorem exists_cofactor_principal_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q A B N : ℕ,
      (∑ d ∈ Icc 1 Q, |cofactorPrincipalMain d A B N-((B-A : ℕ) : ℝ)*mangoldtSum N/(d : ℝ)|) ≤
        C*(Q : ℝ)^ε*(harmonic Q : ℝ)*(mangoldtSum N+((B-A : ℕ) : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_local_factor_div_totient 3 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro Q A B N
  exact cofactor_principal_mean_of_local_weight Q A B N (C*(Q : ℝ)^ε) (by positivity)
    (fun d hd => HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)

end Erdos821.AnalyticSieve
