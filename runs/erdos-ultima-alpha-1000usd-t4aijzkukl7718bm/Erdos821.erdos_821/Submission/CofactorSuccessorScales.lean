import Submission.CofactorSuccessorSieve

/-!
# Uniform prime-successor bounds after absorbing the sieve weights

Doubling the progression scale leaves a full exponential saving even
after the fixed subpower loss from the Selberg support weights.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma cofactorScale_square (b m : ℕ) :
    (cofactorScale b m)^2 = cofactorScale b (2*m) := by
  simp only [cofactorScale,progressionScaleN,← pow_mul]
  congr 1
  ring

lemma cofactorScale_double (b m : ℕ) :
    cofactorScale b (2*m) = cofactorScale (2*b) m := by
  unfold cofactorScale progressionScaleN
  congr 1
  ring

lemma cofactorScale_log (b m : ℕ) :
    Real.log (cofactorScale b m : ℝ) = 256*(b : ℝ)*m*Real.log 2 := by
  rw [cofactorScale_cast,Real.log_pow]
  push_cast
  ring

lemma doubled_poly_sieve_saving (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (m : ℕ) :
    C*(2 : ℝ)^m*(K*(((2*m : ℕ) : ℝ)+1)^6/(2 : ℝ)^(2*m)) ≤
      (64*C*K)*((m : ℝ)+1)^6/(2 : ℝ)^m := by
  have hpow : (((2*m : ℕ) : ℝ)+1)^6 ≤ 64*((m : ℝ)+1)^6 := by
    have hh : ((2*m : ℕ) : ℝ)+1 ≤ 2*((m : ℝ)+1) := by push_cast; linarith
    have hp := pow_le_pow_left₀ (by positivity) hh 6
    simpa only [mul_pow,show (2 : ℝ)^6=64 by norm_num] using hp
  have htwo : (0 : ℝ)<2^m := by positivity
  rw [show (2 : ℝ)^(2*m)=((2 : ℝ)^m)^2 by rw [mul_comm 2 m,pow_mul]]
  have he : C*(2 : ℝ)^m*(K*(((2*m : ℕ) : ℝ)+1)^6/((2 : ℝ)^m)^2) =
      C*K*(((2*m : ℕ) : ℝ)+1)^6/(2 : ℝ)^m := by field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ htwo.le
  have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)
  nlinarith only [hh]

/-- The coefficient c and the cofactor interval endpoints may vary with m.
The Mangoldt main mass is retained exactly; no prime number theorem is
inserted in its place. -/
theorem exists_cofactor_prime_successor_power_saving (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B c : ℕ, 0 < c → cofactorScale l (2*m) ≤ B-A →
      cofactorPrimeSuccessorWeight c A B (cofactorScale t (2*m)) (cofactorScale b m) ≤
        ((B-A : ℕ) : ℝ)*mangoldtSum (cofactorScale t (2*m))*
            ((c : ℝ)/(c.totient : ℝ))/Real.log ((cofactorScale b m : ℝ)+1)+
          K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
  let ε : ℝ := 1/(256*((2*b : ℕ) : ℝ))
  have hb : 1 ≤ b := by omega
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,HC⟩ := exists_cofactor_successor_log_bound ε hε
  obtain ⟨K,hK,HK⟩ := exists_cofactor_natural_main_power_saving a b t l ha hab ht hlevel hl
  refine ⟨64*C*K,by positivity,?_⟩
  intro m A B c hc hAB
  have hsieve := HC c A B (cofactorScale t (2*m)) (cofactorScale b m) hc
    (cofactorScale_pos b m)
  rw [cofactorScale_square] at hsieve
  have hweight : (cofactorScale b (2*m) : ℝ)^ε = (2 : ℝ)^m := by
    rw [cofactorScale_double]
    exact cofactorScale_rpow (2*b) m (by omega)
  rw [hweight] at hsieve
  have hmean := HK (2*m) A B hAB (successorUnit c)
  change (∑ d ∈ Icc 1 (cofactorScale b (2*m)),
      cofactorSuccessorDiscrepancy c A B (cofactorScale t (2*m)) d) ≤ _ at hmean
  apply hsieve.trans
  apply _root_.add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_left hmean (show 0 ≤ C*(2 : ℝ)^m by positivity)).trans
  have hpoly := doubled_poly_sieve_saving C K hC.le hK.le m
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly (Nat.cast_nonneg (B-A)))
      (Nat.cast_nonneg (cofactorScale t (2*m)))
  simpa only [mul_assoc] using hh

end Erdos821.AnalyticSieve
