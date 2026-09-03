import Submission.PoolDyadicHyperbola

/-!
# A retained-pool bound over a long hyperbolic prime range

The leading main term retains the reciprocal-logarithm difference. The
ambient error has an arbitrary extra inverse logarithmic power.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

/-- Both endpoints and the multiplier pool may vary after the threshold. -/
theorem exists_pool_hyperbolic_bound (a b s l v t r w : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hbt : b < 2*t) (hlevel : 2*b+1 ≤ l+t)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, ∀ K R D H : ℕ, K₀ ≤ K → 2 ≤ K →
      cofactorScale s (2*cofactorDyadicIndex t (K+R)) ≤ H/2^(K+R) →
      cofactorScale l (2*cofactorDyadicIndex t (K+R)) ≤ D*(H/2^(K+R)) →
      D*(H/2^K) ≤ cofactorScale v (2*cofactorDyadicIndex t (K+1)) →
      ∀ P : Finset ℕ, P ⊆ Icc 1 D →
      (∀ c ∈ P, ∀ p : ℕ, p.Prime → p ≤ cofactorScale b (cofactorDyadicIndex t (K+R)) → ¬p ∣ c) →
      ((poolHyperbolicPrimePairs P H (2^K) (2^(K+R))).card : ℝ) ≤
        ((2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^r)*(H : ℝ)*(P.card : ℝ)/(Real.log 2)^2)*
          (Real.log 2*(1/((K : ℝ)-1)-1/((K : ℝ)+R-1))+2*C/(K : ℝ)^2)+
        (η*(D : ℝ)*(H : ℝ)/((Real.log 2)^2*((K : ℝ)+1)^w))*
          (1/((K : ℝ)-1)-1/((K : ℝ)+R-1)) := by
  obtain ⟨C,hC,HC⟩ := exists_dyadicMangoldtTail_bound
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp
    (eventually_dyadic_pool_hyperbolic_pairs a b s l v t r w ha hab hs hl ht hbt hlevel η hη)
  refine ⟨C,hC,K₀,?_⟩
  intro K R D H hKK hK hshort hlong hup P hP hrough
  let A : ℝ := (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^r)*(H : ℝ)*(P.card : ℝ)/(Real.log 2)^2
  let E : ℝ := η*(D : ℝ)*(H : ℝ)/((Real.log 2)^2*((K : ℝ)+1)^w)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hblock (j : ℕ) (hj : j ∈ range R) :
      ((poolHyperbolicPrimePairs P H (2^(K+j)) (2^(K+j+1))).card : ℝ) ≤
        A*(dyadicMangoldtMass (K+j)/((K : ℝ)+j)^2)+E*(1/((K : ℝ)+j)^2) := by
    have hbound : K+j+1 ≤ K+R := by have := mem_range.mp hj; omega
    have hquot : H/2^(K+R) ≤ H/2^(K+j+1) :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hbound) (by positivity)
    have hshort' : cofactorScale s (2*cofactorDyadicIndex t (K+j+1)) ≤ H/2^(K+j+1) :=
      ((cofactorScale_mono_right s (Nat.mul_le_mul_left 2 (cofactorDyadicIndex_mono t hbound))).trans hshort).trans hquot
    have hlong' : cofactorScale l (2*cofactorDyadicIndex t (K+j+1)) ≤ D*(H/2^(K+j+1)) :=
      ((cofactorScale_mono_right l (Nat.mul_le_mul_left 2 (cofactorDyadicIndex_mono t hbound))).trans hlong).trans
        (Nat.mul_le_mul_left D hquot)
    have hup' : D*(H/2^(K+j)) ≤ cofactorScale v (2*cofactorDyadicIndex t (K+j+1)) := by
      apply (Nat.mul_le_mul_left D (Nat.div_le_div_left
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : K ≤ K+j)) (by positivity))).trans
      exact hup.trans (cofactorScale_mono_right v (Nat.mul_le_mul_left 2
        (cofactorDyadicIndex_mono t (by omega : K+1 ≤ K+j+1))))
    have hrough' : ∀ c ∈ P, ∀ p : ℕ, p.Prime →
        p ≤ cofactorScale b (cofactorDyadicIndex t (K+j+1)) → ¬p ∣ c := by
      intro c hc p hp hpz
      exact hrough c hc p hp (hpz.trans (cofactorScale_mono_right b (cofactorDyadicIndex_mono t hbound)))
    have hh := hK₀ (K+j) (by omega) D H hshort' hlong' hup' P hP hrough'
    apply hh.trans
    have hpow : ((K : ℝ)+1)^w ≤ (((K+j : ℕ) : ℝ)+1)^w := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have herr : η*(D : ℝ)*(H : ℝ)/((((K+j : ℕ) : ℝ)*Real.log 2)^2*(((K+j : ℕ) : ℝ)+1)^w) ≤
        E*(1/((K : ℝ)+j)^2) := by
      have hKR : (0 : ℝ)<K+j := by exact_mod_cast (show 0<K+j by omega)
      have hlog : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
      have hb := div_le_div_of_nonneg_left (show 0 ≤ η*(D : ℝ)*(H : ℝ) by positivity)
        (show 0 < ((((K+j : ℕ) : ℝ)*Real.log 2)^2*((K : ℝ)+1)^w) by positivity)
        (mul_le_mul_of_nonneg_left hpow (sq_nonneg (((K+j : ℕ) : ℝ)*Real.log 2)))
      apply hb.trans_eq
      dsimp [E]
      push_cast
      simp only [mul_pow,div_mul_eq_div_div]
      ring
    convert _root_.add_le_add le_rfl herr using 1
    dsimp [A]
    push_cast
    simp only [mul_pow,div_mul_eq_div_div]
    ring
  rw [pool_hyperbolic_dyadic_blocks]
  apply (sum_le_sum hblock).trans
  rw [sum_add_distrib,← mul_sum,← mul_sum]
  exact _root_.add_le_add (mul_le_mul_of_nonneg_left (HC K R hK) hA)
    (mul_le_mul_of_nonneg_left (sum_shifted_inv_sq_le K R hK) hE)

end Erdos821.AnalyticSieve
