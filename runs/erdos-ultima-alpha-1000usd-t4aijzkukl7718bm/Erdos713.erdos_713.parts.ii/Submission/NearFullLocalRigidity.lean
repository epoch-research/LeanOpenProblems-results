import FormalConjecturesUtil
import Submission.LocallyInjectiveLayers
import Submission.NearFullCoverRigidity

/-! An asymptotic size obstruction for locally injective maps onto H-free
targets. Fibers may be unequal and the target need not be connected.
This is not an existence theorem for such maps and does not prove rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713NearFullLocalRigidity
open Erdos713ProductCover Erdos713LocallyInjectiveLayers Erdos713NearFullCoverRigidity
set_option maxHeartbeats 2000000

lemma rpow_factor {x α : ℝ} (hx : 0 ≤ x) (ha : 1 < α) : x^α=x^(α-1)*x := by
  calc
    _ = x^(α-1+1) := by congr 1; ring
    _ = _ := Real.rpow_add_one' hx (by linarith)

/-- A finite upper bound from an all-order extremal envelope. The constant
error sums to B times the SOURCE order, not B times the target order. -/
theorem power_bound {V W T : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph T) {G : SimpleGraph V} {F : SimpleGraph W} (f : G →g F)
    (hLocal : ∀ x, Function.Injective (neighborMap f x)) (hFree : H.Free F)
    {α C B : ℝ} (ha : 1 < α) (hC : 0 ≤ C)
    (hU : ∀ k : ℕ, (extremalNumber k H : ℝ) ≤ C*(k : ℝ)^α+B) :
    (Nat.card G.edgeSet : ℝ) ≤
      C*(Fintype.card W : ℝ)^(α-1)*Fintype.card V+B*Fintype.card V := by
  have hE : (Nat.card G.edgeSet : ℝ) ≤
      ∑ j ∈ range (Fintype.card V), (extremalNumber (layer f j).card H : ℝ) := by
    exact_mod_cast extremal_layers H f hLocal hFree
  have hBound (j : ℕ) : (extremalNumber (layer f j).card H : ℝ) ≤
      C*(Fintype.card W : ℝ)^(α-1)*(layer f j).card+B := by
    have hs : ((layer f j).card : ℝ) ≤ Fintype.card W := by
      exact_mod_cast (card_le_univ (layer f j))
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg (layer f j).card) hs (by linarith : 0 ≤ α-1)
    have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (layer f j).card)
    have hmc := mul_le_mul_of_nonneg_left hm hC
    have hu := hU (layer f j).card
    rw [rpow_factor (Nat.cast_nonneg _) ha] at hu
    nlinarith only [hu,hmc]
  have hSum := sum_le_sum (s := range (Fintype.card V)) (fun j _ => hBound j)
  have hVertices : (∑ j ∈ range (Fintype.card V), ((layer f j).card : ℝ)) = Fintype.card V := by
    exact_mod_cast layer_vertices (f : V → W)
  have hFormula : (∑ j ∈ range (Fintype.card V),
      (C*(Fintype.card W : ℝ)^(α-1)*(layer f j).card+B)) =
      C*(Fintype.card W : ℝ)^(α-1)*Fintype.card V+B*Fintype.card V := by
    rw [sum_add_distrib,← mul_sum,hVertices,sum_const,card_range,nsmul_eq_mul]
    ring
  exact hE.trans (hSum.trans_eq hFormula)

/-- Fix any target-order ratio theta<1. At one sufficiently small fixed
near-full density tolerance, all large locally injective maps to H-free
targets have target order greater than theta times source order.
Neither surjectivity nor source H-freeness is required. -/
theorem target_order_lower {T : Type*} (H : SimpleGraph T) {α c θ : ℝ}
    (ha : 1 < α) (hc : 0 < c) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ (V W : Type) [Fintype V] [Fintype W],
      ∀ (G : SimpleGraph V) (F : SimpleGraph W) (f : G →g F),
      N ≤ Fintype.card V → (∀ x, Function.Injective (neighborMap f x)) → H.Free F →
      (c-ε)*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) →
      θ*Fintype.card V < (Fintype.card W : ℝ) := by
  let s : ℝ := θ^(α-1)
  have hs0 : 0 ≤ s := Real.rpow_nonneg hθ _
  have hs1 : s < 1 := Real.rpow_lt_one hθ hθ1 (by linarith)
  let ε : ℝ := c*(1-s)/4
  have hε : 0 < ε := div_pos (mul_pos hc (sub_pos.mpr hs1)) (by norm_num)
  have hεs : ε*s ≤ ε := by nlinarith only [mul_le_mul_of_nonneg_left hs1.le hε.le]
  have heq : c*s+4*ε=c := by dsimp [ε]; ring
  have hco : (c+ε)*s+ε < c-ε := by nlinarith only [hεs,heq,hε]
  obtain ⟨B,hB,hEnvelope⟩ := upper_envelope (fun n => extremalNumber n H) hc hε h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (linear_negligible ha hε (B := B))
  refine ⟨ε,hε,max N 1,?_⟩
  intro V W instV instW G F f hn hLocal hFree hDense
  by_contra hSmall
  have hm : (Fintype.card W : ℝ) ≤ θ*Fintype.card V := le_of_not_gt hSmall
  have hnN : N ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hErr := hN (Fintype.card V) hnN
  have hG := power_bound H f hLocal hFree ha (show 0 ≤ c+ε by positivity) hEnvelope
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card W)) hm (by linarith : 0 ≤ α-1)
  rw [Real.mul_rpow hθ hnR.le] at hp
  have hm' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show 0 ≤ c+ε by positivity)) hnR.le
  have hf := rpow_factor hnR.le ha
  have hc' := mul_lt_mul_of_pos_right hco (Real.rpow_pos_of_pos hnR α)
  change (c+ε)*(Fintype.card W : ℝ)^(α-1)*Fintype.card V ≤
    (c+ε)*(s*(Fintype.card V : ℝ)^(α-1))*Fintype.card V at hm'
  rw [hf] at hDense hErr hc'
  nlinarith only [hG,hm',hDense,hErr,hc']

/-- The bound concerns the actual image, not unused target vertices. -/
theorem image_order_lower {T : Type*} (H : SimpleGraph T) {α c θ : ℝ}
    (ha : 1 < α) (hc : 0 < c) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ (V W : Type) [Fintype V] [Fintype W],
      ∀ (G : SimpleGraph V) (F : SimpleGraph W) (f : G →g F),
      N ≤ Fintype.card V → (∀ x, Function.Injective (neighborMap f x)) → H.Free F →
      (c-ε)*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) →
      θ*Fintype.card V < (Nat.card (Set.range f) : ℝ) := by
  obtain ⟨ε,hε,N,hN⟩ := target_order_lower H ha hc hθ hθ1 h
  refine ⟨ε,hε,N,?_⟩
  intro V W instV instW G F f hn hLocal hFree hDense
  let S : Set W := Set.range f
  let g : G →g F.induce S := ⟨Set.rangeFactorization f,fun {_ _} hxy => f.map_adj hxy⟩
  have hL : ∀ x, Function.Injective (neighborMap g x) := by
    intro x a b hab
    apply hLocal x
    apply Subtype.ext
    exact congrArg (fun z : (F.induce S).neighborSet (g x) => z.val.val) hab
  have hf : H.Free (F.induce S) := fun hh => hFree (hh.trans ⟨Copy.induce F S⟩)
  have hh := hN V S G (F.induce S) g hn hL hf hDense
  simpa only [Fintype.card_eq_nat_card] using hh


#print axioms power_bound
#print axioms target_order_lower
#print axioms image_order_lower
end Erdos713NearFullLocalRigidity
