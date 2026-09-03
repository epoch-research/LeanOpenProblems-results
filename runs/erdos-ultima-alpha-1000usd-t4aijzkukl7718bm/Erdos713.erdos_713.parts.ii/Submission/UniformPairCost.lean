import FormalConjecturesUtil
import Submission.CommonBlockerPairCount
import Submission.UniformOverlap

/-! Uniform control of the full merger cost on ordered vertex pairs.
No maximum-degree assumption is needed for this estimate. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713UniformPairCost
open Erdos713DegreePenalty Erdos713MergeDegreePenalty Erdos713UniformOverlap
open Erdos713CommonBlockerPairCount
variable {V W : Type*}
set_option maxHeartbeats 2000000

noncomputable def highCost [Fintype V] (G : SimpleGraph V) (lam t : ℝ) : Finset (V × V) :=
  univ.filter (fun p => t < pairCost G lam p)

lemma highCost_budget [Fintype V] (G : SimpleGraph V) {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    t*(highCost G lam t).card ≤ energy G+2*Fintype.card V*(lam*energy G) := by
  have hp (p : V × V) : 0 ≤ pairCost G lam p := by
    dsimp [pairCost]
    have h₁ := degreeR_nonneg G p.1
    have h₂ := degreeR_nonneg G p.2
    positivity
  have hs := sum_le_sum (s := highCost G lam t) (fun p hp => (mem_filter.mp hp).2.le)
  have hu := sum_le_univ_sum_of_nonneg (s := highCost G lam t) hp
  simp only [sum_const,nsmul_eq_mul] at hs
  have he : (∑ p : V × V, 2*lam*degreeR G p.1*degreeR G p.2)=8*lam*(edgesR G)^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum,degreeR_sum]
    rw [← sum_mul,← mul_sum,degreeR_sum]
    ring
  have hsum : (∑ p : V × V, pairCost G lam p)=energy G+8*lam*(edgesR G)^2 := by
    simp only [pairCost,sum_add_distrib,sum_common,he]
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := degreeR G)
  rw [card_univ,degreeR_sum] at hc
  change (2*edgesR G)^2 ≤ (Fintype.card V : ℝ)*energy G at hc
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*lam by positivity)
  rw [hsum] at hu
  nlinarith only [hs,hu,hm]

/-- The accuracy η is fixed before the order, graph, or penalty parameter.
The codegree part uses the uniform second-moment theorem; the penalty part
uses Cauchy--Schwarz and the given energy bound. -/
theorem eventually_few_highCost (H : SimpleGraph W) {α c s ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (hs : 0 < s) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)), H.Free G → ∀ lam : ℝ, 0 ≤ lam →
        lam*energy G ≤ η*(n : ℝ)^α →
        ((highCost G lam (s*(n : ℝ)^(α-1))).card : ℝ) ≤ ε*(n : ℝ)^2 := by
  let η := ε*s/4
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η,hη,?_⟩
  filter_upwards [small_second_moment H ha ha2 hc h (show 0 < ε*s/2 by positivity),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro G hFree lam hlam hEnergy
  have hE : energy G ≤ (ε*s/2)*(n : ℝ)^(α+1) :=
    hn (Fin n) G (Fintype.card_fin n) hFree
  have hb := highCost_budget G hlam (s*(n : ℝ)^(α-1))
  simp only [Fintype.card_fin] at hb
  have hm := mul_le_mul_of_nonneg_left hEnergy (show 0 ≤ 2*(n : ℝ) by positivity)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hpow₁ : (n : ℝ)^(α+1)=(n : ℝ)^α*n := by rw [Real.rpow_add hnR,Real.rpow_one]
  have hpow₂ : (n : ℝ)^(α-1)*(n : ℝ)^2=(n : ℝ)^(α+1) := by
    rw [← Real.rpow_two,← Real.rpow_add hnR]
    congr 1
    ring
  have hbound : (s*(n : ℝ)^(α-1))*((highCost G lam (s*(n : ℝ)^(α-1))).card : ℝ) ≤
      (s*(n : ℝ)^(α-1))*(ε*(n : ℝ)^2) := by
    have hright : (s*(n : ℝ)^(α-1))*(ε*(n : ℝ)^2)=ε*s*(n : ℝ)^(α+1) := by
      rw [← hpow₂]
      ring
    rw [hright,hpow₁]
    rw [hpow₁] at hE
    dsimp only [η] at hm
    nlinarith only [hb,hm,hE]
  exact (mul_le_mul_iff_right₀ (mul_pos hs (Real.rpow_pos_of_pos hnR _))).mp hbound

#print axioms highCost_budget
#print axioms eventually_few_highCost
end Erdos713UniformPairCost
