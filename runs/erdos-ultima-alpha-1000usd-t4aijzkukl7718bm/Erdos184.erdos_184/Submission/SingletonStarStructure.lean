import Submission.OptimalSingletonForest
import Submission.EdgeHullPotential

/-! Structural consequences of nested neighborhoods along a best singleton forest.
No compression monotonicity or uniform bound is asserted here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical Compression
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V]

lemma acyclic_no_triangle {F : SimpleGraph V} (ha : F.IsAcyclic)
    {u v w : V} (huv : F.Adj u v) (hvw : F.Adj v w) (huw : F.Adj u w) : False := by
  let p : F.Walk u w := .cons huv (.cons hvw .nil)
  have hp : p.IsPath := by
    simp [p,Walk.cons_isPath_iff,huv.ne,hvw.ne,huw.ne]
  have he := ha.path_unique ⟨p,hp⟩ (SimpleGraph.Path.singleton huw)
  have hl := congrArg (fun q : F.Path u w => q.val.length) he
  change 2 = 1 at hl
  omega

/-- Domination at a singleton edge forces the dominated endpoint to be a leaf
of the best singleton forest. -/
lemma Best.dominated_leaf {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v)
    (hd : ∀ w, w ≠ u → G.Adj v w → G.Adj u w) :
    ∀ w, F.Adj v w → w = u := by
  intro w hvw
  by_contra hwu
  have huwG := hd w hwu (hb.1.1 hvw)
  have huwF := hb.reachable_induced (huv.reachable.trans hvw.reachable) huwG
  exact acyclic_no_triangle hb.1.acyclic huv hvw huwF

lemma Best.dominated_leaf_degree {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v)
    (hd : ∀ w, w ≠ u → G.Adj v w → G.Adj u w) :
    Nat.card (F.neighborSet v) = 1 := by
  have hs : F.neighborSet v = {u} := by
    ext w
    constructor
    · exact hb.dominated_leaf huv hd w
    · rintro rfl
      exact huv.symm
  rw [hs]
  simp

lemma Optimal.odd_of_forest_leaf {G F : SimpleGraph V} (h : Optimal G F) {v : V}
    (hv : Nat.card (F.neighborSet v) = 1) : Odd (Nat.card (G.neighborSet v)) := by
  have he := Nat.even_iff.mp (h.2.1 v)
  have hd := degree_sdiff_add G F h.1 v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
  rw [Nat.odd_iff]
  omega

/-- The weaker terminal property relevant to compression restricted to best
singleton edges. It is not the full NestedAlongEdges predicate. -/
def NestedSingletons (G F : SimpleGraph V) : Prop :=
  ∀ u v, F.Adj u v → Nat.card (G.neighborSet v) ≤ Nat.card (G.neighborSet u) →
    ∀ w, w ≠ u → G.Adj v w → G.Adj u w

lemma Best.lower_endpoint_leaf {G F : SimpleGraph V} (hb : Best G F)
    (hn : NestedSingletons G F) {u v : V} (huv : F.Adj u v)
    (hdeg : Nat.card (G.neighborSet v) ≤ Nat.card (G.neighborSet u)) :
    Nat.card (F.neighborSet v) = 1 ∧ Odd (Nat.card (G.neighborSet v)) := by
  have hf := hb.dominated_leaf_degree huv (hn u v huv hdeg)
  exact ⟨hf,hb.1.odd_of_forest_leaf hf⟩

/-- In particular, the singleton forest has no path of length three. -/
lemma Best.no_three_edge_path {G F : SimpleGraph V} (hb : Best G F)
    (hn : NestedSingletons G F) {a b c d : V}
    (hab : F.Adj a b) (hbc : F.Adj b c) (hcd : F.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  rcases le_total (Nat.card (G.neighborSet b)) (Nat.card (G.neighborSet c)) with h | h
  · have hh := hb.dominated_leaf hbc.symm (hn c b hbc.symm h) a hab.symm
    exact hac hh
  · have hh := hb.dominated_leaf hbc (hn b c hbc h) d hcd
    exact hbd hh.symm

/-- Conditional reduction: the unproved full-transfer rule restricted to best
singleton edges forces this weaker terminal property at a global extremizer.
A bound on this weaker terminal class is NOT supplied. -/
lemma global_extremizer_nested_singletons
    (hc : ∀ G : SimpleGraph V, EdgeHull.Minimal G → ∀ F, Best G F →
      ∀ u v, F.Adj u v → number G ≤ EdgeHull.value (transfer G u v)) :
    ∃ G F : SimpleGraph V, EdgeHull.Minimal G ∧
      number G = EdgeHull.value (⊤ : SimpleGraph V) ∧ Best G F ∧ NestedSingletons G F := by
  obtain ⟨G,hm,hG,hmin,hmax⟩ := EdgeHull.exists_global_extremizer (V := V) degreePotential
  obtain ⟨F,hF⟩ := exists_best G
  refine ⟨G,F,hm,hG,hF,?_⟩
  intro u v huv hdeg w hwu hvw
  by_contra huw
  have huvG := hF.1.1 huv
  have hp := transfer_potential_lt G huvG.ne hdeg
    ⟨w,mem_privateNeighbors.mpr ⟨hwu,hvw,huw⟩⟩
  have hcard := transfer_edge_card G u v
  have heq := EdgeHull.number_eq_of_hull_at_global_minimizer (T := transfer G u v) hG hmin
    (by simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hcard)
    (hc G hm F hF u v huv)
  exact (not_le_of_gt hp) (hmax _ heq (by
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hcard))

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.Best.no_three_edge_path
#print axioms Erdos184Work.SingletonExchange.global_extremizer_nested_singletons
