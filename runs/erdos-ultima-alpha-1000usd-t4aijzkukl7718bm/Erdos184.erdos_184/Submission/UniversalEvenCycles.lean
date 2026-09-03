import Submission.AllOddPaths

/-! Closing the all-odd path partition at a universal vertex of an even graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open OddPaths Critical
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma degree_induce_except {v : V} (x : {x : V // x ≠ v}) (hx : G.Adj x.val v) :
    (G.induce {x | x ≠ v}).degree x + 1 = G.degree x.val := by
  have he := G.map_neighborFinset_induce (s := {x | x ≠ v}) x
  have hs : G.neighborFinset x.val ∩ ({x : V | x ≠ v} : Set V).toFinset =
      (G.neighborFinset x.val).erase v := by ext y; simp [and_comm]
  rw [hs] at he
  have hc := congrArg Finset.card he
  rw [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree] at hc
  rw [hc]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr hx)

variable (v : V) (hv : ∀ x : V, x ≠ v → G.Adj v x)
abbrev Rest := {x : V // x ≠ v}
abbrev Base : SimpleGraph (Rest v) := G.induce {x | x ≠ v}
abbrev emb : Base (G := G) v ↪g G := SimpleGraph.Embedding.induce _

include hv in
lemma base_odd (he : ∀ x : V, Even (G.degree x)) (x : Rest v) :
    Odd (Nat.card ((Base (G := G) v).neighborSet x)) := by
  have hd := degree_induce_except x (hv x x.property).symm
  have h := Nat.even_iff.mp (he x.val)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd h
  rw [Nat.odd_iff]
  change Nat.card ((Base (G := G) v).neighborSet x) + 1 = _ at hd
  omega

noncomputable def close (p : Piece (Base (G := G) v)) : G.Walk v v :=
  Walk.cons (hv p.src p.src.property)
    ((p.walk.map (emb v).toHom).concat (hv p.dst p.dst.property).symm)

lemma mapped_avoids (p : Piece (Base (G := G) v)) :
    v ∉ (p.walk.map (emb v).toHom).support := by
  simp only [Walk.support_map,List.mem_map]
  rintro ⟨x,_,hx⟩
  exact x.property hx

lemma close_cycle (p : Piece (Base (G := G) v)) : (close v hv p).IsCycle := by
  rw [close,Walk.cons_isCycle_iff]
  have hp := p.walk.map_isPath_of_injective (f := (emb v).toHom) (emb (G := G) v).injective p.isPath
  refine ⟨hp.concat (mapped_avoids v p) _,?_⟩
  rw [Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
  rintro (he | he)
  · exact mapped_avoids v p ((p.walk.map (emb v).toHom).fst_mem_support_of_mem_edges he)
  · change s(v,p.src.val) = s(p.dst.val,v) at he
    rcases Sym2.eq_iff.mp he with h | h
    · exact p.dst.property h.1.symm
    · exact p.ne (Subtype.ext h.2)

lemma close_edges (p : Piece (Base (G := G) v)) :
    (close v hv p).edges.Perm
      ((p.walk.edges.map (Sym2.map Subtype.val)) ++ [s(v,p.src.val),s(v,p.dst.val)]) := by
  apply List.perm_iff_count.mpr
  intro e
  simp only [close,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,Walk.edges_map,
    List.count_cons,List.count_append,List.count_nil]
  have hf : ⇑(emb (G := G) v).toHom = (Subtype.val : Rest v → V) := rfl
  simp only [hf,Sym2.eq_swap]
  omega

lemma old_edge_avoids (p : Piece (Base (G := G) v)) {e : Sym2 V}
    (he : e ∈ p.walk.edges.map (Sym2.map Subtype.val)) : v ∉ e := by
  intro hm
  apply mapped_avoids v p
  apply Walk.mem_support_of_mem_edges (p := p.walk.map (emb v).toHom) _ hm
  simpa only [Walk.edges_map] using he

lemma star_injective {a b : V} (he : s(v,a) = s(v,b)) : a = b := by
  rcases Sym2.eq_iff.mp he with h | h
  · exact h.2
  · exact h.2.trans h.1

lemma close_disjoint {L : List (Piece (Base (G := G) v))} (hL : Admissible L)
    {p q : Piece (Base (G := G) v)} (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) :
    (close v hv p).edges.Disjoint (close v hv q).edges := by
  intro e hep heq
  have heP := (close_edges v hv p).mem_iff.mp hep
  have heQ := (close_edges v hv q).mem_iff.mp heq
  rcases List.mem_append.mp heP with heP | heP
  · rcases List.mem_append.mp heQ with heQ | heQ
    · obtain ⟨a,ha,hea⟩ := List.mem_map.mp heP
      obtain ⟨b,hb,heb⟩ := List.mem_map.mp heQ
      have hab := Sym2.map.injective Subtype.val_injective (hea.trans heb.symm)
      subst b
      exact hne (edge_owner_unique hL.1 hp hq ha hb)
    · exact old_edge_avoids v p heP (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at heQ
        rcases heQ with rfl | rfl <;> simp)
  · rcases List.mem_append.mp heQ with heQ | heQ
    · exact old_edge_avoids v q heQ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at heP
        rcases heP with rfl | rfl <;> simp)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at heP heQ
      rcases heP with rfl | rfl <;> rcases heQ with heQ | heQ
      · exact hne (endpoint_owner_unique hL.2.1 hp hq (Or.inl rfl)
          (Or.inl (Subtype.ext (star_injective v heQ))))
      · exact hne (endpoint_owner_unique hL.2.1 hp hq (Or.inl rfl)
          (Or.inr (Subtype.ext (star_injective v heQ))))
      · exact hne (endpoint_owner_unique hL.2.1 hp hq (Or.inr rfl)
          (Or.inl (Subtype.ext (star_injective v heQ))))
      · exact hne (endpoint_owner_unique hL.2.1 hp hq (Or.inr rfl)
          (Or.inr (Subtype.ext (star_injective v heQ))))

lemma close_covers {L : List (Piece (Base (G := G) v))} (hL : Admissible L)
    (hcover : ∀ e, e ∈ (Base (G := G) v).edgeSet ↔ e ∈ edgeList L) (a b : V) :
    G.Adj a b ↔ ∃ p ∈ L, s(a,b) ∈ (close v hv p).edges := by
  constructor
  · intro hab
    by_cases ha : a = v
    · subst a
      let b' : Rest v := ⟨b,hab.ne.symm⟩
      obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp (hL.2.2 b')
      refine ⟨p,hp,(close_edges v hv p).mem_iff.mpr (List.mem_append_right _ ?_)⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hep ⊢
      exact hep.imp (fun he => congrArg (fun z : Rest v => s(v,z.val)) he)
        (fun he => congrArg (fun z : Rest v => s(v,z.val)) he)
    · by_cases hb : b = v
      · subst b
        let a' : Rest v := ⟨a,ha⟩
        obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp (hL.2.2 a')
        refine ⟨p,hp,(close_edges v hv p).mem_iff.mpr (List.mem_append_right _ ?_)⟩
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hep ⊢
        rw [Sym2.eq_swap]
        exact hep.imp (fun he => congrArg (fun z : Rest v => s(v,z.val)) he)
          (fun he => congrArg (fun z : Rest v => s(v,z.val)) he)
      · let a' : Rest v := ⟨a,ha⟩
        let b' : Rest v := ⟨b,hb⟩
        have he : s(a',b') ∈ edgeList L := (hcover _).mp hab
        obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp he
        refine ⟨p,hp,(close_edges v hv p).mem_iff.mpr (List.mem_append_left _ ?_)⟩
        exact List.mem_map.mpr ⟨s(a',b'),hep,rfl⟩
  · rintro ⟨p,_,he⟩
    exact (close v hv p).edges_subset_edgeSet he

include v hv in
lemma universal_even_bound (he : ∀ x : V, Even (G.degree x)) :
    2 * number G ≤ Fintype.card V - 1 := by
  obtain ⟨L,hL,hcover,hcard⟩ := all_odd_path_partition (Base (G := G) v) (base_odd v hv he)
  let I := ↥L.toFinset
  have hbound : number G ≤ Fintype.card I := by
    apply DiminishingReturns.number_le_cycle_family (fun _ : I => v)
      (fun p : I => close v hv p.val) (fun p => close_cycle v hv p.val)
    · intro p q hne
      apply Finset.disjoint_left.mpr
      intro e hp hq
      exact close_disjoint v hv hL (List.mem_toFinset.mp p.property)
        (List.mem_toFinset.mp q.property) (fun he => hne (Subtype.ext he))
        (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq)
    · intro a b
      rw [close_covers v hv hL hcover]
      constructor
      · rintro ⟨p,hp,he⟩
        exact ⟨⟨p,List.mem_toFinset.mpr hp⟩,List.mem_toFinset.mpr he⟩
      · rintro ⟨p,he⟩
        exact ⟨p.val,List.mem_toFinset.mp p.property,List.mem_toFinset.mp he⟩
  have hc : Fintype.card I ≤ L.length := by
    exact (Fintype.card_coe L.toFinset).trans_le L.toFinset_card_le
  have hr : Fintype.card (Rest v) = Fintype.card V - 1 := by
    simp only [Rest,Fintype.card_subtype_compl, Fintype.card_unique]
  rw [hr] at hcard
  omega

end Erdos184Work.UniversalCycles

#print axioms Erdos184Work.UniversalCycles.universal_even_bound
