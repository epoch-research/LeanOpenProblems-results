import Submission.DyadicProductHyperbola
import Submission.LongCofactorHyperbolicBound

/-!
# A long hyperbolic range using the product-half-level sieve
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

/-- The constant C is independent of both dyadic endpoints and of c,H.
There is no roughness hypothesis on c. -/
theorem exists_product_cofactor_hyperbolic_bound (a b t l r : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : b+1 ≤ t) (hlevel : 2*b+1 ≤ l+t) (hl : 2*a+1 ≤ l)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, ∀ K R c H : ℕ, K₀ ≤ K → 2 ≤ K → 0 < c → H ≤ 2^(2*K) →
      cofactorScale l (2*cofactorDyadicIndex t (K+R)) ≤ H/2^(K+R) →
        ((hyperbolicPrimePairPool c H (2^K) (2^(K+R))).card : ℝ) ≤
          ((2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^r)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))/(Real.log 2)^2)*
            (Real.log 2*(1/((K : ℝ)-1)-1/((K : ℝ)+R-1))+2*C/(K : ℝ)^2)+
              (η*(H : ℝ)/(Real.log 2)^2)*(1/((K : ℝ)-1)-1/((K : ℝ)+R-1)) := by
  obtain ⟨C,hC,HC⟩ := exists_dyadicMangoldtTail_bound
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp
    (eventually_dyadic_product_hyperbolic_prime_pairs a b t l r ha hab ht hlevel hl η hη)
  refine ⟨C,hC,K₀,?_⟩
  intro K R c H hKK hK hc hH hlong
  let A : ℝ := (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^r)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))/(Real.log 2)^2
  let E : ℝ := η*(H : ℝ)/(Real.log 2)^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hblock (j : ℕ) (hj : j ∈ range R) :
      ((hyperbolicPrimePairPool c H (2^(K+j)) (2^(K+j+1))).card : ℝ) ≤
        A*(dyadicMangoldtMass (K+j)/((K : ℝ)+j)^2)+E*(1/((K : ℝ)+j)^2) := by
    have hbound : K+j+1 ≤ K+R := by have := mem_range.mp hj; omega
    have hlong' : cofactorScale l (2*cofactorDyadicIndex t (K+j+1)) ≤ H/2^(K+j+1) := by
      apply (cofactorScale_mono_right l (Nat.mul_le_mul_left 2 (cofactorDyadicIndex_mono t hbound))).trans
      exact hlong.trans (Nat.div_le_div_left
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbound) (by positivity))
    have hh := hK₀ (K+j) (by omega) c H hc
      (hH.trans (Nat.pow_le_pow_right (by decide) (by omega))) hlong'
    apply hh.trans_eq
    dsimp [A,E]
    push_cast
    simp only [mul_pow,div_mul_eq_div_div]
    ring
  rw [hyperbolic_prime_pair_dyadic_blocks]
  apply (sum_le_sum hblock).trans
  rw [sum_add_distrib,← mul_sum,← mul_sum]
  exact _root_.add_le_add (mul_le_mul_of_nonneg_left (HC K R hK) hA)
    (mul_le_mul_of_nonneg_left (sum_shifted_inv_sq_le K R hK) hE)


end Erdos821.AnalyticSieve
