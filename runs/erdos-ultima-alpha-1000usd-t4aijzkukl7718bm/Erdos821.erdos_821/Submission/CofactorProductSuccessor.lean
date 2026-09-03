import Submission.CofactorProductMean
import Submission.UniformSuccessorIntervalScales

/-!
# Prime-successor rectangles from the product-half-level mean
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

/-- No roughness or size bound is required for the linear coefficient c. -/
theorem exists_cofactor_product_successor_power_saving (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : b+1 ≤ t) (hlevel : 2*b+1 ≤ l+t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m B c M N : ℕ, 0 < c → M ≤ N →
      N ≤ cofactorScale t (2*m) → cofactorScale l (2*m) ≤ B → B ≤ cofactorScale t (2*m) →
        cofactorIntervalPrimeSuccessorWeight c 0 B M N (cofactorScale b m) ≤
          (B : ℝ)*(mangoldtSum N-mangoldtSum M)*
            ((c : ℝ)/(c.totient : ℝ))/Real.log ((cofactorScale b m : ℝ)+1)+
              K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*(cofactorScale t (2*m) : ℝ) := by
  let ε : ℝ := 1/(256*((2*b : ℕ) : ℝ))
  have hb : 1 ≤ b := by omega
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,HC⟩ := exists_cofactor_interval_successor_log_bound ε hε
  obtain ⟨K,hK,HK⟩ := exists_cofactor_product_natural_power_saving a b l t t ha hab hl ht hlevel
  refine ⟨64*C*(2*K),by positivity,?_⟩
  intro m B c M N hc hMN hN hAB hBup
  have hsieve := HC c 0 B M N (cofactorScale b m) hMN hc (cofactorScale_pos b m)
  simp only [Nat.sub_zero] at hsieve
  rw [cofactorScale_square] at hsieve
  have hweight : (cofactorScale b (2*m) : ℝ)^ε = (2 : ℝ)^m := by
    rw [cofactorScale_double]
    exact cofactorScale_rpow (2*b) m (by omega)
  rw [hweight] at hsieve
  have hmeanN := HK (2*m) B N hAB hBup hN (successorUnit c)
  have hmeanM := HK (2*m) B M hAB hBup (hMN.trans hN) (successorUnit c)
  have hmean : (∑ d ∈ Icc 1 (cofactorScale b (2*m)),
      (cofactorSuccessorDiscrepancy c 0 B N d+cofactorSuccessorDiscrepancy c 0 B M d)) ≤
        (2*K)*(((2*m : ℕ) : ℝ)+1)^6/(2 : ℝ)^(2*m)*
          (B : ℝ)*(cofactorScale t (2*m) : ℝ) := by
    unfold cofactorSuccessorDiscrepancy
    simp only [Nat.sub_zero]
    rw [sum_add_distrib]
    apply (_root_.add_le_add hmeanN hmeanM).trans_eq
    ring
  apply hsieve.trans
  apply _root_.add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_left hmean (show 0 ≤ C*(2 : ℝ)^m by positivity)).trans
  have hpoly := doubled_poly_sieve_saving C (2*K) hC.le (by positivity) m
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly (Nat.cast_nonneg B))
      (Nat.cast_nonneg (cofactorScale t (2*m)))
  simpa only [mul_assoc] using hh


end Erdos821.AnalyticSieve
