import Submission.HullForestReduction
import Submission.VertexSeparatorReduction
import Submission.GraphCircuitCode

/-! Kernel-checkable certificates bounding a decomposition by a contained forest.
These certificates are for specified finite graphs, not a general bound. -/
open SimpleGraph
namespace Erdos184Work.CycleForestCertificate
open Critical
set_option maxHeartbeats 800000
attribute [local instance 2000] Finset.decidableDforallFinset
variable {V : Type*} [Fintype V] [DecidableEq V]

def graph (s : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
instance (s : Finset (Sym2 V)) : DecidableRel (graph s).Adj := by
  unfold graph
  infer_instance

def vertices (s : Finset (Sym2 V)) : Finset V := s.biUnion Sym2.toFinset

def PieceValid (s : Finset (Sym2 V)) : Prop :=
  s.card = 1 ∨ ((graph s).induce (vertices s : Set V)).Connected ∧
    ∀ v : (vertices s : Set V), ((graph s).induce (vertices s : Set V)).degree v = 2
instance (s : Finset (Sym2 V)) : Decidable (PieceValid s) := by
  unfold PieceValid
  infer_instance

def ForestValid (s : Finset (Sym2 V)) (r : V → ℕ) (p : V → Option V) : Prop :=
  ∀ u v, (graph s).Adj u v →
    (r u < r v ∧ p v = some u) ∨ (r v < r u ∧ p u = some v)
instance (s : Finset (Sym2 V)) (r : V → ℕ) (p : V → Option V) :
    Decidable (ForestValid s r p) := by
  unfold ForestValid
  infer_instance

structure Data (V : Type*) [DecidableEq V] where
  pieces : Finset (Finset (Sym2 V))
  forest : Finset (Sym2 V)
  rank : V → ℕ
  parent : V → Option V

def Data.Valid (d : Data V) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ s ∈ d.pieces, PieceValid s) ∧
  (∀ s ∈ d.pieces, ∀ t ∈ d.pieces, s ≠ t → Disjoint s t) ∧
  d.pieces.biUnion id = G.edgeFinset ∧
  d.forest ⊆ G.edgeFinset ∧ d.pieces.card ≤ d.forest.card ∧ ForestValid d.forest d.rank d.parent
instance (d : Data V) (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable (d.Valid G) := by
  haveI : Decidable (∀ s ∈ d.pieces, PieceValid s) := inferInstance
  haveI : Decidable (∀ s ∈ d.pieces, ∀ t ∈ d.pieces, s ≠ t → Disjoint s t) := inferInstance
  haveI : Decidable (ForestValid d.forest d.rank d.parent) := inferInstance
  unfold Data.Valid
  infer_instance

lemma support_subset_vertices (s : Finset (Sym2 V)) : (graph s).support ⊆ vertices s := by
  rintro v ⟨w,hvw⟩
  change (graph s).Adj v w at hvw
  have hm := ((SimpleGraph.fromEdgeSet_adj _).mp hvw).1
  apply Finset.mem_biUnion.mpr
  exact ⟨s(v,w),hm,by simp⟩

lemma edgeFinset_subset (s : Finset (Sym2 V)) : (graph s).edgeFinset ⊆ s := by
  intro e he
  have hh := SimpleGraph.mem_edgeFinset.mp he
  change e ∈ (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet at hh
  rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
  exact hh.1

lemma piece_number_le_one {s : Finset (Sym2 V)} (h : PieceValid s) : number (graph s) ≤ 1 := by
  classical
  rcases h with h | ⟨hc,hr⟩
  · have h₁ := number_le_edges (graph s)
    have h₂ := Finset.card_le_card (edgeFinset_subset s)
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at h₁ h₂
    omega
  · letI : Fintype (vertices s : Set V) :=
      @Subtype.fintype V (fun v => v ∈ (vertices s : Set V))
        (fun v => Classical.propDecidable _) inferInstance
    let K := (graph s).induce (vertices s : Set V)
    have hKr : K.IsRegularOfDegree 2 := by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hr
    have hh : (⊤ : K.Subgraph).coe.Connected ∧ (⊤ : K.Subgraph).coe.IsRegularOfDegree 2 := by
      refine ⟨(SimpleGraph.Subgraph.topIso (G := K)).connected_iff.mpr hc,?_⟩
      intro v
      have he := (SimpleGraph.Subgraph.topIso (G := K)).degree_eq v
      have hv := hKr v.val
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he hv ⊢
      exact he.symm.trans hv
    have hp : ∀ H ∈ ({⊤} : Finset K.Subgraph), IsCycleOrEdge H.coe := by
      intro H hH
      have he : H = ⊤ := Finset.mem_singleton.mp hH
      subst H
      apply Or.inl
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hh
    have hdec : IsDecomposition K ({⊤} : Finset K.Subgraph) := by
      constructor
      · intro H hH J hJ hne
        exact (hne ((Finset.mem_singleton.mp hH).trans (Finset.mem_singleton.mp hJ).symm)).elim
      · simp only [Finset.set_biUnion_singleton]
        rfl
    have hn : number K ≤ 1 := by
      have h := number_le ({⊤} : Finset K.Subgraph) hp hdec
      simpa only [Finset.card_singleton] using h
    exact (VertexSeparators.number_induce_support (graph s) (vertices s)
      (support_subset_vertices s)).trans hn

lemma rank_acyclic {s : Finset (Sym2 V)} {r : V → ℕ}
    (h : (∀ u v, (graph s).Adj u v → r u ≠ r v) ∧
      ∀ v u w, (graph s).Adj v u → (graph s).Adj v w →
        r u < r v → r w < r v → u = w) :
    (graph s).IsAcyclic := by
  classical
  intro u p hp
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image p.support.toFinset r
    ⟨u,by simp⟩
  have hvp : v ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr (List.mem_toFinset.mp hv)
  let C := p.toSubgraph.spanningCoe
  have hd : C.degree v = 2 := by
    have hh := regular_two_spanning_degree p.toSubgraph (cycle_coe_regular (graph s) hp).2 v
    rw [if_pos hvp] at hh
    exact hh
  have hn : 1 < (C.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hn
  have hva : C.Adj v a := C.mem_neighborFinset v a |>.mp ha
  have hvb : C.Adj v b := C.mem_neighborFinset v b |>.mp hb
  have hga := p.toSubgraph.spanningCoe_le hva
  have hgb := p.toSubgraph.spanningCoe_le hvb
  have hma : r a ≤ r v := hmax a (List.mem_toFinset.mpr
    (p.mem_verts_toSubgraph.mp (SimpleGraph.Subgraph.Adj.snd_mem hva)))
  have hmb : r b ≤ r v := hmax b (List.mem_toFinset.mpr
    (p.mem_verts_toSubgraph.mp (SimpleGraph.Subgraph.Adj.snd_mem hvb)))
  exact hab (h.2 v a b hga hgb (lt_of_le_of_ne hma (h.1 a v hga.symm))
    (lt_of_le_of_ne hmb (h.1 b v hgb.symm)))

lemma forest_acyclic {s : Finset (Sym2 V)} {r : V → ℕ} {p : V → Option V}
    (h : ForestValid s r p) : (graph s).IsAcyclic := by
  apply rank_acyclic (r := r)
  constructor
  · intro u v huv
    rcases h u v huv with h | h <;> omega
  · intro v u w hvu hvw huv hwv
    have hpu : p v = some u := by
      rcases h v u hvu with hh | hh
      · omega
      · exact hh.2
    have hpw : p v = some w := by
      rcases h v w hvw with hh | hh
      · omega
      · exact hh.2
    exact Option.some.inj (hpu.symm.trans hpw)

lemma number_sup_le {G H : SimpleGraph V} (hd : Disjoint G.edgeSet H.edgeSet) :
    number (G ⊔ H) ≤ number G + number H := by
  classical
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  obtain ⟨E,hE,hdecE,hcardE⟩ := exists_minimum H
  obtain ⟨B,hB,hdecB,hbound⟩ := combine_decompositions le_sup_left le_sup_right hd
    (SimpleGraph.edgeSet_sup G H).symm D E hD hdec hE hdecE
  have hn := number_le B hB hdecB
  omega

lemma pieces_number_le (D : Finset (Finset (Sym2 V)))
    (hp : ∀ s ∈ D, PieceValid s)
    (hd : ∀ s ∈ D, ∀ t ∈ D, s ≠ t → Disjoint s t) :
    number (graph (D.biUnion id)) ≤ D.card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [graph,number_bot]
  | @insert s D hs ih =>
    have hps := hp s (Finset.mem_insert_self _ _)
    have hpD : ∀ t ∈ D, PieceValid t := fun t ht => hp t (Finset.mem_insert_of_mem ht)
    have hdD : ∀ t ∈ D, ∀ u ∈ D, t ≠ u → Disjoint t u :=
      fun t ht u hu htu => hd t (Finset.mem_insert_of_mem ht) u (Finset.mem_insert_of_mem hu) htu
    have hsd : Disjoint (graph s).edgeSet (graph (D.biUnion id)).edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hf
      have hes := edgeFinset_subset s (SimpleGraph.mem_edgeFinset.mpr he)
      have hef := edgeFinset_subset (D.biUnion id) (SimpleGraph.mem_edgeFinset.mpr hf)
      obtain ⟨t,ht,het⟩ := Finset.mem_biUnion.mp hef
      exact Finset.disjoint_left.mp (hd s (Finset.mem_insert_self _ _) t
        (Finset.mem_insert_of_mem ht) (fun h => hs (h ▸ ht))) hes het
    have heq : graph ((insert s D).biUnion id) = graph s ⊔ graph (D.biUnion id) := by
      simp only [Finset.biUnion_insert,id_eq,graph,Finset.coe_union,SimpleGraph.fromEdgeSet_union]
    rw [heq,Finset.card_insert_of_notMem hs]
    have hnum := number_sup_le hsd
    have hnumS := piece_number_le_one hps
    have hnumD := ih hpD hdD
    omega

lemma Data.forestBound {d : Data V} {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : d.Valid G) : ForestBound G := by
  classical
  have hfG : graph d.forest ≤ G := by
    intro x y hxy
    exact SimpleGraph.mem_edgeFinset.mp (h.2.2.2.1 hxy.1)
  have hfc : (graph d.forest).edgeFinset = d.forest := by
    apply Finset.Subset.antisymm (edgeFinset_subset _)
    intro e he
    apply SimpleGraph.mem_edgeFinset.mpr
    rw [graph,SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he,G.edgeSet_subset_setOf_not_isDiag (SimpleGraph.mem_edgeFinset.mp (h.2.2.2.1 he))⟩
  have hnum := pieces_number_le d.pieces h.1 h.2.1
  rw [h.2.2.1] at hnum
  have heq : graph G.edgeFinset = G := by simp [graph]
  rw [heq] at hnum
  refine ⟨graph d.forest,hfG,forest_acyclic h.2.2.2.2.2,?_⟩
  have hcard := congrArg Finset.card hfc
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcard ⊢
  rw [hcard]
  exact hnum.trans h.2.2.2.2.1

end Erdos184Work.CycleForestCertificate
#print axioms Erdos184Work.CycleForestCertificate.Data.forestBound
