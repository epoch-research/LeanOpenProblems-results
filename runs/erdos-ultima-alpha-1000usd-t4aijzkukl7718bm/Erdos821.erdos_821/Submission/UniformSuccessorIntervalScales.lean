import Submission.CofactorSuccessorIntervals

/-!
# A coefficient-uniform power-saving bound on prime-successor rectangles

Both prime-variable endpoints and both cofactor endpoints are arbitrary
within the stated bounds. The main term retains the actual interval mass.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

/-- No roughness or size bound is required for the linear coefficient c. -/
theorem exists_cofactor_interval_successor_power_saving (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B c M N : ℕ, 0 < c → M ≤ N →
      N ≤ cofactorScale t (2*m) → cofactorScale l (2*m) ≤ B-A →
        cofactorIntervalPrimeSuccessorWeight c A B M N (cofactorScale b m) ≤
          ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*
            ((c : ℝ)/(c.totient : ℝ))/Real.log ((cofactorScale b m : ℝ)+1)+
              K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
  let ε : ℝ := 1/(256*((2*b : ℕ) : ℝ))
  have hb : 1 ≤ b := by omega
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,HC⟩ := exists_cofactor_interval_successor_log_bound ε hε
  obtain ⟨K,hK,HK⟩ := exists_cofactor_natural_main_power_saving_cutoff a b t l ha hab ht hlevel hl
  refine ⟨64*C*(2*K),by positivity,?_⟩
  intro m A B c M N hc hMN hN hAB
  have hsieve := HC c A B M N (cofactorScale b m) hMN hc (cofactorScale_pos b m)
  rw [cofactorScale_square] at hsieve
  have hweight : (cofactorScale b (2*m) : ℝ)^ε = (2 : ℝ)^m := by
    rw [cofactorScale_double]
    exact cofactorScale_rpow (2*b) m (by omega)
  rw [hweight] at hsieve
  have hmeanN := HK (2*m) A B N hN hAB (successorUnit c)
  have hmeanM := HK (2*m) A B M (hMN.trans hN) hAB (successorUnit c)
  have hmean : (∑ d ∈ Icc 1 (cofactorScale b (2*m)),
      (cofactorSuccessorDiscrepancy c A B N d+cofactorSuccessorDiscrepancy c A B M d)) ≤
        (2*K)*(((2*m : ℕ) : ℝ)+1)^6/(2 : ℝ)^(2*m)*
          ((B-A : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
    rw [sum_add_distrib]
    apply (_root_.add_le_add hmeanN hmeanM).trans_eq
    ring
  apply hsieve.trans
  apply _root_.add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_left hmean (show 0 ≤ C*(2 : ℝ)^m by positivity)).trans
  have hpoly := doubled_poly_sieve_saving C (2*K) hC.le (by positivity) m
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly (Nat.cast_nonneg (B-A)))
      (Nat.cast_nonneg (cofactorScale t (2*m)))
  simpa only [mul_assoc] using hh

lemma eventually_poly_sieve_error_le (K δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, K*((m : ℝ)+1)^6/(2 : ℝ)^m ≤ δ/((m : ℝ)+1) := by
  have hlim := (Erdos821.tendsto_succ_pow_div_two_pow 7).const_mul K
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hδ)] with m hm
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(m : ℝ)+1)).mpr
  convert hm using 1
  rw [show 7=6+1 by decide,pow_succ]
  ring

/-- The error can be made arbitrarily small even relative to L*N/log N.
The ambient N here is the fixed scale, not an interval's upper endpoint. -/
theorem eventually_cofactor_interval_successor_log_error (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ A B c M N : ℕ, 0 < c → M ≤ N →
      N ≤ cofactorScale t (2*m) → cofactorScale l (2*m) ≤ B-A →
        cofactorIntervalPrimeSuccessorWeight c A B M N (cofactorScale b m) ≤
          ((B-A : ℕ) : ℝ)*(mangoldtSum N-mangoldtSum M)*
            ((c : ℝ)/(c.totient : ℝ))/Real.log ((cofactorScale b m : ℝ)+1)+
              δ/((m : ℝ)+1)*((B-A : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
  obtain ⟨K,_hK,HK⟩ := exists_cofactor_interval_successor_power_saving a b t l ha hab ht hlevel hl
  filter_upwards [eventually_poly_sieve_error_le K δ hδ] with m hm
  intro A B c M N hc hMN hN hAB
  apply (HK m A B c M N hc hMN hN hAB).trans
  exact _root_.add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

end Erdos821.AnalyticSieve
