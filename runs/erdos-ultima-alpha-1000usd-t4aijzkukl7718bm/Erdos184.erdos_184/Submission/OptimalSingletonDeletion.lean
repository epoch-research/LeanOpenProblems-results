import Submission.OptimalSingletonForest
import Submission.MinimalBridgeRestoration

/-! Valid inheritance and lifting rules for secondary-optimal singleton forests.
These do not assert that global minimality is inherited by a cycle cofactor,
and do not establish a uniform decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical EvenCore
set_option maxHeartbeats 1000000
variable {V : Type*}

lemma sdiff_commute (G F C : SimpleGraph V) : (G \ F) \ C = (G \ C) \ F := by
  ext x y
  simp only [SimpleGraph.sdiff_adj]
  tauto

variable [Fintype V]

/-- An optimal split lifts across an even deletion whose numbers add exactly. -/
lemma Optimal.extend_even {G C T : SimpleGraph V} (hCG : C ≤ G)
    (hC : ∀ v, Even (Nat.card (C.neighborSet v)))
    (hadd : number (G \ C) + number C = number G)
    (hT : Optimal (G \ C) T) : Optimal G T := by
  have hTG : T ≤ G := hT.1.trans sdiff_le
  have hCT : C ≤ G \ T := by
    intro x y hxy
    exact ⟨hCG hxy, fun ht => (hT.1 ht).2 hxy⟩
  have heven : ∀ v, Even (Nat.card ((G \ T).neighborSet v)) := by
    intro v
    have hd := degree_sdiff_add (G \ T) C hCT v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hd
    rw [sdiff_commute G T C] at hd
    have he := Nat.even_iff.mp (hT.2.1 v)
    have hc := Nat.even_iff.mp (hC v)
    rw [Nat.even_iff]
    omega
  have hu := number_sdiff_add_le (G \ T) C hCT
  rw [sdiff_commute G T C] at hu
  have hlo := split_lower_bound hTG
  have hopt := hT.2.2
  exact ⟨hTG, heven, by omega⟩

/-- Any optimal singleton split of an additive even cofactor has at least
as many singleton edges as a Best split of the original graph. -/
lemma Best.singleton_count_le_cofactor {G F C T : SimpleGraph V}
    (hb : Best G F) (hCG : C ≤ G)
    (hC : ∀ v, Even (Nat.card (C.neighborSet v)))
    (hadd : number (G \ C) + number C = number G)
    (hT : Optimal (G \ C) T) : Nat.card F.edgeSet ≤ Nat.card T.edgeSet :=
  hb.2 T (hT.extend_even hCG hC hadd)

/-- An even part that is additive within the optimal even remainder can be
removed without changing the Best singleton forest. -/
lemma Best.delete_even {G F C : SimpleGraph V} (hb : Best G F)
    (hCE : C ≤ G \ F) (hC : ∀ v, Even (Nat.card (C.neighborSet v)))
    (hadd : number ((G \ F) \ C) + number C = number (G \ F)) :
    Best (G \ C) F := by
  have hCG : C ≤ G := hCE.trans sdiff_le
  have hFC : F ≤ G \ C := by
    intro x y hxy
    exact ⟨hb.1.1 hxy, fun hc => (hCE hc).2 hxy⟩
  have heven : ∀ v, Even (Nat.card (((G \ C) \ F).neighborSet v)) := by
    intro v
    rw [← sdiff_commute G F C]
    have hd := degree_sdiff_add (G \ F) C hCE v
    have he := Nat.even_iff.mp (hb.1.2.1 v)
    have hc := Nat.even_iff.mp (hC v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hd
    rw [Nat.even_iff]
    omega
  have hrestore := number_sdiff_add_le G C hCG
  have hlo := split_lower_bound hFC
  have hopt := hb.1.2.2
  rw [sdiff_commute G F C] at hadd
  have heq : number ((G \ C) \ F) + Nat.card F.edgeSet = number (G \ C) := by
    omega
  have htotal : number (G \ C) + number C = number G := by omega
  refine ⟨⟨hFC, heven, heq⟩, ?_⟩
  intro T hT
  exact hb.singleton_count_le_cofactor hCG hC htotal hT

/-- Cycle-criticality alone suffices for the singleton-count comparison.
It does NOT say the original singleton forest is optimal after this deletion. -/
lemma Best.singleton_count_le_delete_cycle {G F T : SimpleGraph V}
    (hb : Best G F) (hcrit : CycleCritical G)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hT : Optimal (G \ p.toSubgraph.spanningCoe) T) :
    Nat.card F.edgeSet ≤ Nat.card T.edgeSet := by
  have hc : number p.toSubgraph.spanningCoe = 1 :=
    GraphCircuitCode.cycle_number_one p.toSubgraph (by
      simpa only [SimpleGraph.IsRegularOfDegree,
        ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using cycle_coe_regular G hp)
  have he : ∀ v, Even (Nat.card (p.toSubgraph.spanningCoe.neighborSet v)) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_spanning_even G hp v
  apply hb.singleton_count_le_cofactor p.toSubgraph.spanningCoe_le he ?_ hT
  rw [hc]
  exact (hcrit u p hp).symm

lemma Best.singleton_count_le_minimal_delete_cycle {G F T : SimpleGraph V}
    (hb : Best G F) (hm : EdgeHull.Minimal G)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hT : Optimal (G \ p.toSubgraph.spanningCoe) T) :
    Nat.card F.edgeSet ≤ Nat.card T.edgeSet :=
  hb.singleton_count_le_delete_cycle hm.cycleCritical p hp hT

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.Optimal.extend_even
#print axioms Erdos184Work.SingletonExchange.Best.delete_even
#print axioms Erdos184Work.SingletonExchange.Best.singleton_count_le_minimal_delete_cycle
