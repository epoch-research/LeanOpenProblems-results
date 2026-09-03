import Submission.PoolDyadicRectangles
import Submission.RoughHyperbolicSuccessors

/-!
# Finite hyperbolic covers for retained multiplier pools

A lower endpoint for a multiplier block is kept explicit. No replacement
of a wide pool by its minimum is used without accounting for that loss.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def poolHyperbolicPrimePairs (P : Finset ℕ) (H Y Z : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (P ×ˢ (Icc 1 H ×ˢ Icc (Y+1) Z)).filter
    (fun x => x.2.1*x.2.2 ≤ H ∧ x.2.2.Prime ∧ (x.1*x.2.1*x.2.2+1).Prime)

lemma poolHyperbolicPrimePairs_card (P : Finset ℕ) (H Y Z : ℕ) :
    (poolHyperbolicPrimePairs P H Y Z).card =
      ∑ c ∈ P, (hyperbolicPrimePairPool c H Y Z).card := by
  simp only [poolHyperbolicPrimePairs,hyperbolicPrimePairPool,card_eq_sum_ones,sum_filter,sum_product]

lemma pool_hyperbolic_card_le_sum {ι : Type*} (I : Finset ι)
    (P : Finset ℕ) (H Y Z : ℕ) (M N B : ι → ℕ)
    (hM : ∀ i ∈ I, 0 < M i) (hB : ∀ i ∈ I, H/(M i) ≤ B i)
    (hcover : ∀ q ∈ Icc (Y+1) Z, ∃ i ∈ I, M i<q ∧ q ≤ N i) :
    (poolHyperbolicPrimePairs P H Y Z).card ≤
      ∑ i ∈ I, (poolPrimePairPool P 0 (B i) (M i) (N i)).card := by
  rw [poolHyperbolicPrimePairs_card]
  calc
    _ ≤ ∑ c ∈ P, ∑ i ∈ I, (cofactorPrimePairPool c 0 (B i) (M i) (N i)).card :=
      sum_le_sum (fun c _ => hyperbolic_prime_pair_card_le_sum I c H Y Z M N B hM hB hcover)
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl (fun i _ => (poolPrimePairPool_card P 0 (B i) (M i) (N i)).symm)

lemma pool_hyperbolic_dyadic_blocks (P : Finset ℕ) (H K R : ℕ) :
    ((poolHyperbolicPrimePairs P H (2^K) (2^(K+R))).card : ℝ) =
      ∑ j ∈ range R, ((poolHyperbolicPrimePairs P H (2^(K+j)) (2^(K+j+1))).card : ℝ) := by
  simp only [poolHyperbolicPrimePairs_card,Nat.cast_sum]
  calc
    _ = ∑ c ∈ P, ∑ j ∈ range R, ((hyperbolicPrimePairPool c H (2^(K+j)) (2^(K+j+1))).card : ℝ) :=
      sum_congr rfl (fun c _ => hyperbolic_prime_pair_dyadic_blocks c H K R)
    _ = _ := sum_comm

/-- This bound applies to one multiplier block whose elements are >=C.
Its main-term loss X/C has not yet been identified with reciprocal mass. -/
lemma rough_pool_card_le_hyperbolic (P : Finset ℕ) (C Y X : ℕ)
    (hC : 0 < C) (hP : ∀ c ∈ P, C ≤ c ∧ c ∈ Nat.smoothNumbers Y)
    (hY : ¬Y.Prime) :
    (∑ c ∈ P, (roughProgressionPrimes c Y X).card) ≤
      (poolHyperbolicPrimePairs P (X/C) Y (X/C)).card := by
  rw [poolHyperbolicPrimePairs_card]
  apply sum_le_sum
  intro c hc
  have hc0 := hC.trans_le (hP c hc).1
  apply (rough_progression_card_le_hyperbolic c Y X hc0 (hP c hc).2 hY).trans
  apply card_le_card
  intro x hx
  obtain ⟨hxI,hprod,hq,hs⟩ := mem_filter.mp hx
  obtain ⟨ha,hn⟩ := mem_product.mp hxI
  have hquot : X/c ≤ X/C := Nat.div_le_div_left (hP c hc).1 hC
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans hquot⟩,
      mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hquot⟩⟩,
        hprod.trans hquot,hq,hs⟩

lemma rectangle_pool_error_upper (δ D L H X M S T U V : ℝ) (w : ℕ)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hS : 0 < S) (hV : 0 < V) (hXM : X ≤ M) (hLM : L*M ≤ H)
    (hST : S ≤ T) (hSU : S ≤ U) (hVT : V ≤ T) :
    δ*D*L*(2*X)/(T^(w+1)*U) ≤ 2*δ*D*H/(S^2*V^w) := by
  have hden1 : S^2 ≤ T*U := by
    simpa only [pow_two] using mul_le_mul hST hSU hS.le (hS.le.trans hST)
  have hden2 := mul_le_mul hden1 (pow_le_pow_left₀ hV.le hVT w)
    (pow_nonneg hV.le w) (mul_nonneg (hS.le.trans hST) (hS.le.trans hSU))
  have hden : S^2*V^w ≤ T^(w+1)*U := by
    apply hden2.trans_eq
    rw [pow_succ]
    ring
  have hprod : L*X ≤ H := (mul_le_mul_of_nonneg_left hXM hL).trans hLM
  have hnum : δ*D*L*(2*X) ≤ 2*δ*D*H := by
    nlinarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg hδ hD)]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

end Erdos821.AnalyticSieve
