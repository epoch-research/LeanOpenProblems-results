import FormalConjecturesUtil
import Submission.UniformPairCost

/-! Propagation of costs and degrees through disjoint vertex mergers. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713MergeCostPropagation
open Erdos713DegreePenalty Erdos713MergeDegreePenalty Erdos713CommonBlockerPairCount
open Erdos713VertexMerging Erdos713DoubleMergeCost Erdos713RobustMergeWitnesses
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 2000000

lemma pairCost_mono {F G : SimpleGraph V} (hle : F ≤ G) {lam : ℝ} (hlam : 0 ≤ lam)
    (p : V × V) : pairCost F lam p ≤ pairCost G lam p := by
  have hC : (Nat.card (F.commonNeighbors p.1 p.2) : ℝ) ≤ Nat.card (G.commonNeighbors p.1 p.2) :=
    Nat.cast_le.mpr (common_card_mono hle p.1 p.2)
  have hP := mul_le_mul (degreeR_mono hle p.1) (degreeR_mono hle p.2)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  have hM := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*lam by positivity)
  dsimp only [pairCost]
  nlinarith only [hC,hM]

/-- For a disjoint candidate, only its common-neighbor cost can increase,
and that increase is at most one. -/
lemma pairCost_merge (G : SimpleGraph V) {a b : V} (hn : ¬G.Adj a b)
    (p : {x : V // x ≠ b} × {x : V // x ≠ b})
    (h₁ : p.1.val ≠ a) (h₂ : p.2.val ≠ a) {lam : ℝ} (hlam : 0 ≤ lam) :
    pairCost (merge G a b hn) lam p ≤ pairCost G lam (p.1.val,p.2.val)+1 := by
  have hC : (Nat.card ((merge G a b hn).commonNeighbors p.1 p.2) : ℝ) ≤
      Nat.card (G.commonNeighbors p.1.val p.2.val)+1 := by
    exact_mod_cast common_after_merge_le G a b hn p.1 p.2 h₁ h₂
  have hP := mul_le_mul (degree_merge_other G hn p.1 h₁) (degree_merge_other G hn p.2 h₂)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  have hM := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*lam by positivity)
  dsimp only [pairCost]
  nlinarith only [hC,hM]

lemma merge_score_loss (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b)
    {lam s : ℝ} (hlam : 0 ≤ lam) (hs : pairCost G lam (a,b) ≤ s) :
    score lam G-s ≤ score lam (merge G a b hn) := by
  have he : edgesR (merge G a b hn)+(Nat.card (G.commonNeighbors a b) : ℝ)=edgesR G := by
    unfold edgesR
    exact_mod_cast merge_edge_count G hab hn
  have hm := mul_le_mul_of_nonneg_left (merge_energy G hab hn) hlam
  dsimp only [score,pairCost] at *
  nlinarith only [he,hm,hs]

lemma degree_merge_other_nat (G : SimpleGraph V) {a b : V} (hn : ¬G.Adj a b)
    (v : {x : V // x ≠ b}) (hv : v.val ≠ a) :
    (merge G a b hn).degree v ≤ G.degree v.val := by
  have hh := degree_merge_other G hn v hv
  simpa only [degreeR,Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Nat.cast_le] using hh

/-- A root pair of degrees at most D cannot increase a global 2D cap. -/
lemma degree_cap_preserved (G : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b)
    (D : ℕ) (hCap : ∀ v, G.degree v ≤ 2*D) (ha : G.degree a ≤ D) (hb : G.degree b ≤ D) :
    ∀ v, (merge G a b hn).degree v ≤ 2*D := by
  intro v
  by_cases hv : v.val=a
  · have he : v=⟨a,hab⟩ := Subtype.ext hv
    rw [he]
    have hh := degree_merge_root G hab hn
    have hh' : (merge G a b hn).degree ⟨a,hab⟩ ≤ G.degree a+G.degree b := by
      simp only [degreeR,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hh
      exact_mod_cast hh
    omega
  · exact (degree_merge_other_nat G hn v hv).trans (hCap v.val)

#print axioms pairCost_merge
#print axioms merge_score_loss
#print axioms degree_cap_preserved
end Erdos713MergeCostPropagation
