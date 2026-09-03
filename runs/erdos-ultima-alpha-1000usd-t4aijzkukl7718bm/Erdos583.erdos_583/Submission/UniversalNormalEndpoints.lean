import Submission.NormalRemainderCritical
import Submission.MatchingCutGlue
import Submission.CubicRemainder

/-! Universal root-endpoint and root-avoidance restrictions in optimal normal
partitions. No endpoint-flexibility premise is assumed. -/
namespace Erdos583UniversalNormalEndpointsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.StarPathPieces
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583MatchingCutGlueDevelopment Erdos583CubicRemainderDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma optimal_normal_family_nonnil
    (U : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (U.walk j).IsPath) :
    ∀ j, ¬(U.walk j).Nil := by
  obtain ⟨E,hE,hEc,hparts⟩ := CutVertexReduction.path_family_partition_tracked U hp
  have hmin : ∀ J, GoodDecomposition (remainder F D) J → E.card ≤ J.card :=
    fun J hJ ↦ hEc.trans (normal_partition_lower_bound F D J hJ)
  intro j hn
  obtain ⟨e,he⟩ := min_decomposition_edgeSet_nonempty hE hmin (hparts j)
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hn,List.not_mem_nil] at he

lemma short_tail_normal_family_endpoints
    (hl : D.rep.tail.length ≤ 1)
    (U : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (U.walk j).IsPath) :
    ∀ j, U.start j ≠ D.root ∧ U.finish j ≠ D.root := by
  obtain ⟨E,hE,hEc,hparts⟩ := CutVertexReduction.path_family_partition_tracked U hp
  have hEq : E.card=normalBudget F D := (normal_partition_lower_bound F D E hE).antisymm' hEc
  have hn := optimal_normal_family_nonnil F D U hp
  intro j
  have hs : MarkedPartition (remainder F D) (normalBudget F D) (U.start j) :=
    ⟨E,U.finish j,U.walk j,hE,hEq,hp j,hn j,hparts j⟩
  have ht : MarkedPartition (remainder F D) (normalBudget F D) (U.finish j) :=
    ⟨E,U.start j,(U.walk j).reverse,hE,hEq,(hp j).reverse,
      (by simpa only [Walk.nil_reverse] using hn j),
      (by simpa only [Walk.toSubgraph_reverse] using hparts j)⟩
  exact ⟨fun h ↦ short_tail_root_not_marked F D hl (h ▸ hs),
    fun h ↦ short_tail_root_not_marked F D hl (h ▸ ht)⟩

lemma short_tail_normal_family_quota_zero
    (hl : D.rep.tail.length ≤ 1)
    (U : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (U.walk j).IsPath) :
    U.quota D.root=0 := by
  have h := short_tail_normal_family_endpoints F D hl U hp
  rw [quota_eq_sum_endpoints]
  simp only [if_neg (h _).1,if_neg (h _).2,add_zero,Finset.sum_const_zero]

lemma normal_root_degree :
    Nat.card ((remainder F D).neighborSet D.root)+3=Nat.card (F.graph.neighborSet D.root) := by
  have hsplit := ncard_neighbor_delete_subgraph_add (D.family.walk D.rep.index).toSubgraph D.root
  rw [←selected_erase_eq_delete D.family D.rep.index,
    FreeTailGroups.open_rooted_member_degree D.family D.root D.rep (tail_not_nil F D)] at hsplit
  simpa only [Nat.card_coe_set_eq] using hsplit

lemma short_tail_root_avoiders
    (hl : D.rep.tail.length ≤ 1)
    (U : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (U.walk j).IsPath) :
    1 ≤ Fintype.card (AvoidIndex U D.root) := by
  have hcount := degree_quota_twice_avoid U hp D.root
  rw [short_tail_normal_family_quota_zero F D hl U hp] at hcount
  simp only [←Nat.card_eq_fintype_card] at hcount ⊢
  have hdegree := normal_root_degree F D
  have hbound : Nat.card (F.graph.neighborSet D.root) < F.order := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Fintype.card_fin] using
      F.graph.degree_lt_card_verts D.root
  have hbudget : F.order ≤ 2*normalBudget F D+2 := by
    rw [normalBudget_eq]
    have hpos := D.rep.index.isLt
    simp only [budget,BridgeGlue.ceil_half,Fintype.card_fin] at *
    omega
  omega

lemma odd_short_tail_two_root_avoiders
    (ho : Odd F.order) (hl : D.rep.tail.length ≤ 1)
    (U : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (U.walk j).IsPath) :
    2 ≤ Fintype.card (AvoidIndex U D.root) := by
  have hcount := degree_quota_twice_avoid U hp D.root
  rw [short_tail_normal_family_quota_zero F D hl U hp] at hcount
  simp only [←Nat.card_eq_fintype_card] at hcount ⊢
  have hdegree := normal_root_degree F D
  have hbound : Nat.card (F.graph.neighborSet D.root) < F.order := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Fintype.card_fin] using
      F.graph.degree_lt_card_verts D.root
  have hb := odd_normalBudget F D ho
  omega

end Erdos583UniversalNormalEndpointsDevelopment
