import Submission.EmbeddingPathFamily
import Submission.TwoColorInitialPacking

/-! Closing paths whose endpoints, but not necessarily all vertices, are adjacent to a root. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.RootedClosure
open OddPaths Critical UniversalCycles
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable (v : V)

noncomputable def close (p : Piece G) (hs : G.Adj v p.src) (ht : G.Adj v p.dst) : G.Walk v v :=
  Walk.cons hs (p.walk.concat ht.symm)

lemma close_cycle (p : Piece G) (hs : G.Adj v p.src) (ht : G.Adj v p.dst)
    (hp : v ∉ p.walk.support) : (close v p hs ht).IsCycle := by
  rw [close,Walk.cons_isCycle_iff]
  refine ⟨p.isPath.concat hp _,?_⟩
  rw [Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
  rintro (he | he)
  · exact hp (p.walk.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with h | h
    · exact hp (h.1.symm ▸ p.walk.end_mem_support)
    · exact p.ne h.2

lemma close_edges (p : Piece G) (hs : G.Adj v p.src) (ht : G.Adj v p.dst) :
    (close v p hs ht).edges.Perm (p.walk.edges ++ [s(v,p.src),s(v,p.dst)]) := by
  apply List.perm_iff_count.mpr
  intro e
  simp only [close,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,
    List.count_cons,List.count_append,List.count_nil,Sym2.eq_swap]
  omega

lemma close_disjoint {L : List (Piece G)} (hn : (edgeList L).Nodup)
    (hends : (endpoints L).Nodup) {p q : Piece G} (hp : p ∈ L) (hq : q ∈ L)
    (hne : p ≠ q) (hvp : v ∉ p.walk.support) (hvq : v ∉ q.walk.support)
    (hps : G.Adj v p.src) (hpt : G.Adj v p.dst)
    (hqs : G.Adj v q.src) (hqt : G.Adj v q.dst) :
    (close v p hps hpt).edges.Disjoint (close v q hqs hqt).edges := by
  intro e hep heq
  have heP := (close_edges v p hps hpt).mem_iff.mp hep
  have heQ := (close_edges v q hqs hqt).mem_iff.mp heq
  have hnotp (he : e ∈ p.walk.edges) : v ∉ e := fun h => hvp (Walk.mem_support_of_mem_edges he h)
  have hnotq (he : e ∈ q.walk.edges) : v ∉ e := fun h => hvq (Walk.mem_support_of_mem_edges he h)
  rcases List.mem_append.mp heP with heP | heP
  · rcases List.mem_append.mp heQ with heQ | heQ
    · exact hne (edge_owner_unique hn hp hq heP heQ)
    · exact hnotp heP (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at heQ
        rcases heQ with rfl | rfl <;> simp)
  · rcases List.mem_append.mp heQ with heQ | heQ
    · exact hnotq heQ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at heP
        rcases heP with rfl | rfl <;> simp)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at heP heQ
      rcases heP with rfl | rfl <;> rcases heQ with heQ | heQ
      · exact hne (endpoint_owner_unique hends hp hq (Or.inl rfl) (Or.inl (star_injective v heQ)))
      · exact hne (endpoint_owner_unique hends hp hq (Or.inl rfl) (Or.inr (star_injective v heQ)))
      · exact hne (endpoint_owner_unique hends hp hq (Or.inr rfl) (Or.inl (star_injective v heQ)))
      · exact hne (endpoint_owner_unique hends hp hq (Or.inr rfl) (Or.inr (star_injective v heQ)))

lemma packing_bound (L : List (Piece G)) (hn : (edgeList L).Nodup)
    (hends : (endpoints L).Nodup) (havoid : ∀ p ∈ L, v ∉ p.walk.support)
    (hroot : ∀ a ∈ endpoints L, G.Adj v a)
    (F : Finset (Sym2 V))
    (hcover : ∀ e ∈ G.edgeSet, e ∈ edgeList L ∨
      (∃ a ∈ endpoints L, e = s(v,a)) ∨ e ∈ F) :
    number G ≤ L.length + F.card := by
  have hs (p : Piece G) (hp : p ∈ L) : G.Adj v p.src :=
    hroot _ (TwoColor.endpoint_mem_of_piece hp).1
  have ht (p : Piece G) (hp : p ∈ L) : G.Adj v p.dst :=
    hroot _ (TwoColor.endpoint_mem_of_piece hp).2
  let I := ↥L.toFinset
  have hb : number G ≤ Fintype.card I + F.card := by
    apply cycle_pack_budget (fun _ : I => v)
      (fun p : I => close v p.val (hs _ (List.mem_toFinset.mp p.property)) (ht _ (List.mem_toFinset.mp p.property)))
      (fun p => close_cycle v p.val _ _ (havoid _ (List.mem_toFinset.mp p.property))) (fun p q hne =>
        close_disjoint v hn hends (List.mem_toFinset.mp p.property)
          (List.mem_toFinset.mp q.property) (fun he => hne (Subtype.ext he)) (havoid _ (List.mem_toFinset.mp p.property))
          (havoid _ (List.mem_toFinset.mp q.property)) _ _ _ _) F
    intro e he
    rcases hcover e he with he | ⟨a,ha,he⟩ | he
    · obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp he
      refine Or.inl ⟨⟨p,List.mem_toFinset.mpr hp⟩,?_⟩
      exact (close_edges v p _ _).mem_iff.mpr (List.mem_append_left _ hep)
    · obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp ha
      refine Or.inl ⟨⟨p,List.mem_toFinset.mpr hp⟩,?_⟩
      apply (close_edges v p _ _).mem_iff.mpr
      apply List.mem_append_right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hep ⊢
      exact hep.imp (fun h => he.trans (congrArg (fun x => s(v,x)) h))
        (fun h => he.trans (congrArg (fun x => s(v,x)) h))
    · exact Or.inr he
  have hc : Fintype.card I ≤ L.length :=
    (Fintype.card_coe L.toFinset).trans_le L.toFinset_card_le
  omega

end Erdos184Work.RootedClosure
#print axioms Erdos184Work.RootedClosure.packing_bound
