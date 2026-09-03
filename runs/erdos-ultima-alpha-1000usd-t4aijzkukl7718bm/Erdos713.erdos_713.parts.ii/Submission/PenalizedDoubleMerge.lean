import FormalConjecturesUtil
import Submission.PenalizedContraction
import Submission.DoubleMergeCost
import Submission.C8TwoMergers

/-! Common blockers on globally penalized hosts. This does not construct a
cheap common blocker and does not settle the rationality conjecture. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713PenalizedDoubleMerge
open Erdos713DegreePenalty Erdos713DegreePenaltySupports
open Erdos713MergeDegreePenalty Erdos713VertexMerging Erdos713DoubleMergeCost
open Erdos713PenalizedContraction Erdos713C8TwoMergers Erdos713TwoPathRootCounting
open Erdos713RobustMergeWitnesses
variable {V W : Type*}
set_option maxHeartbeats 2000000

/-- The energy increase for disjoint mergers is bounded by the two original
root-degree products, because the second pair's degrees do not increase. -/
lemma double_merge_energy [Fintype V] (G : SimpleGraph V) {a b : V}
    (hab : a ≠ b) (hn : ¬G.Adj a b) (c d : {x : V // x ≠ b})
    (hca : c.val ≠ a) (hda : d.val ≠ a) (hcd : c ≠ d)
    (hncd : ¬ (merge G a b hn).Adj c d) :
    energy (merge (merge G a b hn) c d hncd) ≤ energy G+
      2*degreeR G a*degreeR G b+2*degreeR G c.val*degreeR G d.val := by
  have h1 := merge_energy G hab hn
  have h2 : energy (merge (merge G a b hn) c d hncd) ≤
      energy (merge G a b hn)+2*degreeR (merge G a b hn) c*degreeR (merge G a b hn) d := by
    convert merge_energy (merge G a b hn) hcd hncd using 1
    congr 1
    exact Subsingleton.elim _ _
  have hp := mul_le_mul (degree_merge_other G hn c hca) (degree_merge_other G hn d hda)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  calc
    _ ≤ energy (merge G a b hn)+2*degreeR (merge G a b hn) c*degreeR (merge G a b hn) d := h2
    _ ≤ (energy G+2*degreeR G a*degreeR G b)+2*degreeR G c.val*degreeR G d.val := by
      apply add_le_add h1
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)

/-- The loss t is paid once, not once per merger. No exact extremal
increment or optimality of the intermediate graph is used. -/
lemma safe_double_after_loss [Fintype V] {H : SimpleGraph W} {G F : SimpleGraph V}
    {lam mu t : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t)
    {a b : V} (hab : a ≠ b) (hn : ¬F.Adj a b) (c d : {x : V // x ≠ b})
    (hca : c.val ≠ a) (hda : d.val ≠ a) (hcd : c ≠ d)
    (hncd : ¬ (merge F a b hn).Adj c d)
    (hf : H.Free (merge (merge F a b hn) c d hncd)) :
    mu*(4*Fintype.card V-4) ≤ t+(Nat.card (G.commonNeighbors a b) : ℝ)+
      (Nat.card (G.commonNeighbors c.val d.val) : ℝ)+1+
      2*lam*(degreeR G a*degreeR G b+degreeR G c.val*degreeR G d.val) := by
  have hh := hg.compare_graph (merge (merge F a b hn) c d hncd) hf
  have hcard₁ : Fintype.card {x : V // x ≠ b}=Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hcard₂ : Fintype.card {x : {x : V // x ≠ b} // x ≠ d}=Fintype.card V-2 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,hcard₁,Nat.sub_sub]
  have hpos : 2 ≤ Fintype.card V := by
    have hc := card_le_univ ({a,b} : Finset V)
    simpa [hab] using hc
  unfold potential score at hh
  rw [hcard₂,Nat.cast_sub hpos,Nat.cast_ofNat] at hh
  have he : edgesR F ≤ edgesR (merge (merge F a b hn) c d hncd)+
      (Nat.card (F.commonNeighbors a b) : ℝ)+
      (Nat.card (F.commonNeighbors c.val d.val) : ℝ)+1 := by
    unfold edgesR
    exact_mod_cast double_merge_edge_bound F hab hn c d hca hda hcd hncd
  have habC : (Nat.card (F.commonNeighbors a b) : ℝ) ≤ Nat.card (G.commonNeighbors a b) :=
    Nat.cast_le.mpr (common_card_mono hle a b)
  have hcdC : (Nat.card (F.commonNeighbors c.val d.val) : ℝ) ≤
      Nat.card (G.commonNeighbors c.val d.val) :=
    Nat.cast_le.mpr (common_card_mono hle c.val d.val)
  have hp₁ := mul_le_mul (degreeR_mono hle a) (degreeR_mono hle b)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  have hp₂ := mul_le_mul (degreeR_mono hle c.val) (degreeR_mono hle d.val)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  have henergy : energy (merge (merge F a b hn) c d hncd) ≤ energy G+
      2*degreeR G a*degreeR G b+2*degreeR G c.val*degreeR G d.val := by
    have hF := energy_mono hle
    have hM := double_merge_energy F hab hn c d hca hda hcd hncd
    nlinarith only [hF,hM,hp₁,hp₂]
  have henergy' := mul_le_mul_of_nonneg_left henergy hlam
  nlinarith only [hh,he,habC,hcdC,hloss,henergy']

/-- If a common edge loss makes both mergers individually safe but is
cheaper than their joint potential decrement, their interaction is counted
by the two-walk endpoint bound in the retained graph. -/
theorem common_blocker_mem_total [Fintype V] {G F : SimpleGraph V}
    {lam mu t : ℝ} (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t)
    (a b c d : V) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    (hn : ¬ F.Adj a b) (hncd : ¬ F.Adj c d)
    (hfirst : (cycleGraph 8).Free (merge F a b hn))
    (hsecond : (cycleGraph 8).Free (merge F c d hncd))
    (hcost : t+(Nat.card (G.commonNeighbors a b) : ℝ)+
      (Nat.card (G.commonNeighbors c d) : ℝ)+1+
      2*lam*(degreeR G a*degreeR G b+degreeR G c*degreeR G d) <
      mu*(4*Fintype.card V-4)) :
    ((a,b),(c,d)) ∈ totalLengthRoots F 8 := by
  have hncd' : ¬ (merge F a b hn).Adj ⟨c,hcb⟩ ⟨d,hdb⟩ := by
    rw [merge_adj]
    simpa only [hca,hda,false_and,or_false] using hncd
  have hc : cycleGraph 8 ⊑ merge (merge F a b hn) ⟨c,hcb⟩ ⟨d,hdb⟩ hncd' := by
    by_contra hf
    have hb := safe_double_after_loss hg hlam hle hloss hab hn ⟨c,hcb⟩ ⟨d,hdb⟩ hca hda
      (fun he => hcd (congrArg Subtype.val he)) hncd' hf
    exact (not_lt_of_ge hb) hcost
  exact genuine_mem_total ⟨(fun hh => hg.free (hh.trans ⟨Copy.ofLE _ _ hle⟩)),
    hab,hca,hcb,hda,hdb,hcd,hn,hncd,hncd',hfirst,hsecond,hc⟩

#print axioms double_merge_energy
#print axioms safe_double_after_loss
#print axioms common_blocker_mem_total
end Erdos713PenalizedDoubleMerge
