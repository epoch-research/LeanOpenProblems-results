import Submission.RefinedMultiplierPools

/-!
# Summing the retained-pool hyperbolic bounds over narrow multiplier blocks

The original wide reciprocal mass is preserved up to 1+2^(-r). Ambient
errors cost the number of blocks, not the number of multipliers.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma sum_hyperbolic_card_le_uniform (P : Finset ℕ) (C X Y Z : ℕ)
    (hC : 0 < C) (hP : ∀ c ∈ P, C ≤ c) :
    (∑ c ∈ P, ((hyperbolicPrimePairPool c (X/c) Y Z).card : ℝ)) ≤
      ((poolHyperbolicPrimePairs P (X/C) Y Z).card : ℝ) := by
  rw [poolHyperbolicPrimePairs_card,Nat.cast_sum]
  apply sum_le_sum
  intro c hc
  apply Nat.cast_le.mpr
  apply card_le_card
  intro x hx
  obtain ⟨hxI,hprod,hq,hs⟩ := mem_filter.mp hx
  obtain ⟨ha,hn⟩ := mem_product.mp hxI
  have hquot : X/c ≤ X/C := Nat.div_le_div_left (hP c hc) hC
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans hquot⟩,hn⟩,
      hprod.trans hquot,hq,hs⟩

lemma narrow_pool_hyperbolic_sum_bound (P : Finset ℕ) (X Y Z K L r : ℕ)
    (hrK : r ≤ K) (hP : ∀ c ∈ P, 2^K<c ∧ c ≤ 2^(K+L))
    (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hb : ∀ i ∈ range L, ∀ j ∈ range (2^r),
      ((poolHyperbolicPrimePairs (refinedMultiplierPool P (K+i) r j)
        (X/multiplierLower (K+i) r j) Y Z).card : ℝ) ≤
        A*((refinedMultiplierPool P (K+i) r j).card : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ)+
          E*(multiplierUpper (K+i) r j : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ)) :
    (∑ c ∈ P, ((hyperbolicPrimePairPool c (X/c) Y Z).card : ℝ)) ≤
      A*(1+1/(2 : ℝ)^r)*(X : ℝ)*(∑ c ∈ P, (c : ℝ)⁻¹)+
        E*(1+1/(2 : ℝ)^r)*(X : ℝ)*(L : ℝ)*(2 : ℝ)^r := by
  have hh : (∑ c ∈ P, ((hyperbolicPrimePairPool c (X/c) Y Z).card : ℝ)) ≤
      ∑ i ∈ range L, ∑ j ∈ range (2^r),
        (A*(((refinedMultiplierPool P (K+i) r j).card : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ))+
          E*((multiplierUpper (K+i) r j : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ))) := by
    rw [← sum_refinedMultiplierPools P K L r hrK hP]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hdom := sum_hyperbolic_card_le_uniform (refinedMultiplierPool P (K+i) r j)
      (multiplierLower (K+i) r j) X Y Z (multiplierLower_pos (K+i) r j)
      (fun c hc => (mem_filter.mp hc).2.1.le)
    apply (hdom.trans (hb i hi j hj)).trans_eq
    ring
  have hmain : (∑ i ∈ range L, ∑ j ∈ range (2^r),
      ((refinedMultiplierPool P (K+i) r j).card : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ)) ≤
        (1+1/(2 : ℝ)^r)*(X : ℝ)*(∑ c ∈ P, (c : ℝ)⁻¹) := by
    calc
      _ ≤ ∑ i ∈ range L, ∑ j ∈ range (2^r),
          (X : ℝ)*(((refinedMultiplierPool P (K+i) r j).card : ℝ)/(multiplierLower (K+i) r j : ℝ)) := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        have h := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := X) (n := multiplierLower (K+i) r j))
          (Nat.cast_nonneg (refinedMultiplierPool P (K+i) r j).card)
        convert h using 1; ring
      _ = (X : ℝ)*(∑ i ∈ range L, ∑ j ∈ range (2^r),
          ((refinedMultiplierPool P (K+i) r j).card : ℝ)/(multiplierLower (K+i) r j : ℝ)) := by
        simp_rw [← mul_sum]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (sum_refinedMultiplierPool_mass P K L r hrK hP) (Nat.cast_nonneg X)
        convert h using 1; ring
  have herr : (∑ i ∈ range L, ∑ j ∈ range (2^r),
      (multiplierUpper (K+i) r j : ℝ)*((X/multiplierLower (K+i) r j : ℕ) : ℝ)) ≤
        (1+1/(2 : ℝ)^r)*(X : ℝ)*(L : ℝ)*(2 : ℝ)^r := by
    calc
      _ ≤ ∑ _i ∈ range L, ∑ _j ∈ range (2^r), (1+1/(2 : ℝ)^r)*(X : ℝ) :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => refinedMultiplierPool_ambient X (K+i) r j))
      _ = _ := by simp only [sum_const,nsmul_eq_mul,card_range,Nat.cast_pow,Nat.cast_ofNat]; ring
  simp only [sum_add_distrib,← mul_sum] at hh
  apply (hh.trans (_root_.add_le_add (mul_le_mul_of_nonneg_left hmain hA)
    (mul_le_mul_of_nonneg_left herr hE))).trans_eq
  ring

/-- The analytic estimate on the full wide pool. Scale hypotheses are
required separately for each narrow block, rather than for its minimum. -/
theorem exists_wide_pool_hyperbolic_bound (a b s l v t rq rc w : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hbt : b < 2*t) (hlevel : 2*b+1 ≤ l+t)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, ∀ K R X KC LC : ℕ,
      K₀ ≤ K → 2 ≤ K → rc ≤ KC → ∀ P : Finset ℕ,
      (∀ c ∈ P, 2^KC<c ∧ c ≤ 2^(KC+LC)) →
      (∀ c ∈ P, ∀ p : ℕ, p.Prime → p ≤ cofactorScale b (cofactorDyadicIndex t (K+R)) → ¬p ∣ c) →
      (∀ i ∈ range LC, ∀ j ∈ range (2^rc),
        let D := multiplierUpper (KC+i) rc j
        let H := X/multiplierLower (KC+i) rc j
        cofactorScale s (2*cofactorDyadicIndex t (K+R)) ≤ H/2^(K+R) ∧
        cofactorScale l (2*cofactorDyadicIndex t (K+R)) ≤ D*(H/2^(K+R)) ∧
        D*(H/2^K) ≤ cofactorScale v (2*cofactorDyadicIndex t (K+1))) →
      (∑ c ∈ P, ((hyperbolicPrimePairPool c (X/c) (2^K) (2^(K+R))).card : ℝ)) ≤
        ((2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^rq)*(1+1/(2 : ℝ)^rc)*(X : ℝ)*
            (∑ c ∈ P, (c : ℝ)⁻¹)/(Real.log 2)^2)*
          (Real.log 2*(1/((K : ℝ)-1)-1/((K : ℝ)+R-1))+2*C/(K : ℝ)^2)+
        (η*(1+1/(2 : ℝ)^rc)*(X : ℝ)*(LC : ℝ)*(2 : ℝ)^rc/
          ((Real.log 2)^2*((K : ℝ)+1)^w))*
            (1/((K : ℝ)-1)-1/((K : ℝ)+R-1)) := by
  obtain ⟨C,hC,K₀,HK⟩ := exists_pool_hyperbolic_bound a b s l v t rq w ha hab hs hl ht hbt hlevel η hη
  refine ⟨C,hC,K₀,?_⟩
  intro K R X KC LC hK₀ hK hrc P hP hrough hscale
  let Δ : ℝ := 1/((K : ℝ)-1)-1/((K : ℝ)+R-1)
  let V : ℝ := Real.log 2*Δ+2*C/(K : ℝ)^2
  let A : ℝ := (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^rq)/(Real.log 2)^2*V
  let E : ℝ := η/((Real.log 2)^2*((K : ℝ)+1)^w)*Δ
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith)
    (by linarith [Nat.cast_nonneg (α := ℝ) R]))
  have hA : 0 ≤ A := by dsimp [A,V]; positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hb (i : ℕ) (hi : i ∈ range LC) (j : ℕ) (hj : j ∈ range (2^rc)) :
      ((poolHyperbolicPrimePairs (refinedMultiplierPool P (KC+i) rc j)
        (X/multiplierLower (KC+i) rc j) (2^K) (2^(K+R))).card : ℝ) ≤
        A*((refinedMultiplierPool P (KC+i) rc j).card : ℝ)*((X/multiplierLower (KC+i) rc j : ℕ) : ℝ)+
          E*(multiplierUpper (KC+i) rc j : ℝ)*((X/multiplierLower (KC+i) rc j : ℕ) : ℝ) := by
    obtain ⟨hs0,hl0,hv0⟩ := hscale i hi j hj
    have h := HK K R (multiplierUpper (KC+i) rc j) (X/multiplierLower (KC+i) rc j) hK₀ hK
      hs0 hl0 hv0 (refinedMultiplierPool P (KC+i) rc j) (refinedMultiplierPool_subset P (KC+i) rc j)
      (fun c hc p hp hpz => hrough c (mem_filter.mp hc).1 p hp hpz)
    convert h using 1; dsimp [A,E,V,Δ]; ring
  have h := narrow_pool_hyperbolic_sum_bound P X (2^K) (2^(K+R)) KC LC rc hrc hP A E hA hE hb
  apply h.trans_eq
  dsimp [A,E,V,Δ]
  ring

end Erdos821.AnalyticSieve
