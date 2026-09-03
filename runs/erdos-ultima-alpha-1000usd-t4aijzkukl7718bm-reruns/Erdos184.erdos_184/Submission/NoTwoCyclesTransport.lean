import Submission.CycleOutsideBudget

/-! Transport of the no-two-edge-disjoint-cycles property through embeddings. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.NoTwoCyclesTransport
open EvenCycleCore
variable {V W : Type*} [Fintype V] [Fintype W]
set_option maxHeartbeats 1000000

lemma of_injective_hom {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : NoTwoCycles G) (f : H →g G) (hf : Function.Injective f) : NoTwoCycles H := by
  intro P Q hp hq hd
  have hp' := subgraph_image_cycle_of_injective f hf P hp.1 (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v)
  have hq' := subgraph_image_cycle_of_injective f hf Q hq.1 (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hq.2 v)
  apply hG (P.map f) (Q.map f) hp' hq'
  rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map]
  apply Set.disjoint_left.mpr
  rintro e ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
  have hab := Sym2.map.injective hf (hea.trans heb.symm)
  exact Set.disjoint_left.mp hd ha (hab ▸ hb)

lemma induce_cycle {G : SimpleGraph V} (S : Set V) (hGS : G.support ⊆ S)
    (P : G.Subgraph) (hp : P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) :
    ∃ Q : (G.induce S).Subgraph,
      (Q.coe.Connected ∧ Q.coe.IsRegularOfDegree 2) ∧
      Sym2.map (Subtype.val : S → V) '' Q.edgeSet = P.edgeSet := by
  obtain ⟨a⟩ := hp.1.nonempty
  obtain ⟨p,hpC,hpP⟩ := CycleRing.cycle_piece_walk_at P hp.1 hp.2 a.val a.property
  have hs : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    have hxP : x ∈ P.verts := hpP ▸ p.mem_verts_toSubgraph.mpr hx
    exact hGS (CriticalOutsideCycles.cycle_verts_in_support P hp.2 hxP)
  let q := p.induce S hs
  have hq : q.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective (f := (Embedding.induce S).toHom)
      Subtype.val_injective).mp
    change (q.map (Embedding.induce S).toHom).IsCycle
    rw [Walk.map_induce]
    exact hpC
  refine ⟨q.toSubgraph,cycle_subgraph_regular (G.induce S) hq,?_⟩
  have heq : q.toSubgraph.map (Embedding.induce S).toHom = P := by
    rw [← Walk.toSubgraph_map,Walk.map_induce,hpP]
  have hh := congrArg Subgraph.edgeSet heq
  simpa only [Subgraph.edgeSet_map] using hh

lemma of_induce {G : SimpleGraph V} (S : Set V) (hGS : G.support ⊆ S)
    (hG : NoTwoCycles (G.induce S)) : NoTwoCycles G := by
  intro P Q hp hq hd
  obtain ⟨P',hp',heP⟩ := induce_cycle S hGS P hp
  obtain ⟨Q',hq',heQ⟩ := induce_cycle S hGS Q hq
  apply hG P' Q' hp' hq'
  apply Set.disjoint_left.mpr
  intro e heP' heQ'
  apply Set.disjoint_left.mp hd
  · rw [← heP]
    exact ⟨e,heP',rfl⟩
  · rw [← heQ]
    exact ⟨e,heQ',rfl⟩

lemma map {G : SimpleGraph V} (hG : NoTwoCycles G) (f : V ↪ W) :
    NoTwoCycles (G.map f) := by
  have hs : (G.map f).support ⊆ Set.range f := by
    rintro v ⟨w,hw⟩
    obtain ⟨x,y,hxy,hx,hy⟩ := (map_adj f G v w).mp hw
    exact ⟨x,hx⟩
  apply of_induce (Set.range f) hs
  let e := f.toEquivRange
  let φ : ((G.map f).induce (Set.range f)) →g G :=
    { toFun := e.symm
      map_rel' := by
        intro u v huv
        obtain ⟨x,y,hxy,hx,hy⟩ := (map_adj f G u.val v.val).mp huv
        have hu : u = e x := Subtype.ext hx.symm
        have hv : v = e y := Subtype.ext hy.symm
        rw [hu,hv,e.symm_apply_apply,e.symm_apply_apply]
        exact hxy }
  have hh := of_injective_hom hG φ e.symm.injective
  intro P Q hp hq hd
  apply hh P Q ⟨hp.1,?_⟩ ⟨hq.1,?_⟩ hd
  · intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v
  · intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hq.2 v

end Erdos184.NoTwoCyclesTransport
