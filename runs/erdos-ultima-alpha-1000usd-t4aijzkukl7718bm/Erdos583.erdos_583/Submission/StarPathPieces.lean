import Submission.Work

/-! Splitting a path family at a center gives edge-disjoint rooted arms with distinct first neighbors. -/
namespace Erdos583StarPathPiecesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.RootedTailSystem
open scoped Classical
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V}

structure Arm (G : SimpleGraph V) (x : V) where
  finish : V
  walk : G.Walk x finish
  isPath : walk.IsPath

noncomputable def half {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) (d : Bool) : Arm G x :=
  if hx : x ∈ P.support then
    if d then ⟨a,(P.takeUntil x hx).reverse,(hp.takeUntil hx).reverse⟩
    else ⟨b,P.dropUntil x hx,hp.dropUntil hx⟩
  else ⟨x,.nil,by simp⟩

lemma half_nil_of_not_mem {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V)
    (hx : x ∉ P.support) (d : Bool) : (half P hp x d).walk.Nil := by
  unfold half
  rw [dif_neg hx]
  simp

lemma half_cover {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) (hx : x ∈ P.support) :
    (half P hp x true).walk.toSubgraph.edgeSet ∪ (half P hp x false).walk.toSubgraph.edgeSet=
      P.toSubgraph.edgeSet := by
  unfold half
  rw [dif_pos hx,dif_pos hx,if_pos rfl,if_neg (by decide : false ≠ true)]
  simp only [Walk.toSubgraph_reverse]
  rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,P.take_spec hx]

lemma half_edges_subset {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) (d : Bool) :
    (half P hp x d).walk.toSubgraph.edgeSet ⊆ P.toSubgraph.edgeSet := by
  by_cases hx : x ∈ P.support
  · rw [←half_cover P hp x hx]
    cases d
    · exact Set.subset_union_right
    · exact Set.subset_union_left
  · unfold half
    rw [dif_neg hx]
    simp

lemma half_disjoint {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) :
    Disjoint (half P hp x true).walk.toSubgraph.edgeSet (half P hp x false).walk.toSubgraph.edgeSet := by
  by_cases hx : x ∈ P.support
  · unfold half
    rw [dif_pos hx,dif_pos hx,if_pos rfl,if_neg (by decide : false ≠ true)]
    simp only [Walk.toSubgraph_reverse]
    apply append_trail_disjoint
    rw [P.take_spec hx]
    exact hp.isTrail
  · unfold half
    rw [dif_neg hx,dif_neg hx]
    simp

lemma tail_avoids_start {x y : V} (P : G.Walk x y) (hp : P.IsPath) (hn : ¬P.Nil) :
    x ∉ P.tail.support := by
  have hh := hp.support_nodup
  rw [←P.cons_support_tail hn,List.nodup_cons] at hh
  exact hh.1

lemma head_tail_cover {x y : V} (P : G.Walk x y) (hn : ¬P.Nil) :
    P.toSubgraph.edgeSet={s(x,P.snd)} ∪ P.tail.toSubgraph.edgeSet := by
  nth_rw 1 [←P.cons_tail_eq hn]
  ext e
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Set.mem_union,Set.mem_singleton_iff]

lemma head_edge_mem {x y : V} (P : G.Walk x y) (hn : ¬P.Nil) : s(x,P.snd) ∈ P.toSubgraph.edgeSet := by
  rw [head_tail_cover P hn]
  exact Or.inl rfl

lemma tail_edges_subset {x y : V} (P : G.Walk x y) (hn : ¬P.Nil) :
    P.tail.toSubgraph.edgeSet ⊆ P.toSubgraph.edgeSet := by
  rw [head_tail_cover P hn]
  exact Set.subset_union_right

variable {k : ℕ} (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (x : V)

noncomputable def familyHalf (e : Fin k × Bool) : Arm G x := half (T.walk e.1) (hp e.1) x e.2

lemma familyHalf_disjoint : Pairwise (fun e f : Fin k × Bool ↦
    Disjoint (familyHalf T hp x e).walk.toSubgraph.edgeSet (familyHalf T hp x f).walk.toSubgraph.edgeSet) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ hne
  by_cases hij : i=j
  · subst j
    have hbc : b ≠ c := fun h ↦ hne (congrArg (Prod.mk i) h)
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (half_disjoint (T.walk i) (hp i) x).symm
    · exact half_disjoint (T.walk i) (hp i) x
    · exact (hbc rfl).elim
  · exact (T.disjoint hij).mono (half_edges_subset (T.walk i) (hp i) x b)
      (half_edges_subset (T.walk j) (hp j) x c)

abbrev ArmIndex := {e : Fin k × Bool // ¬(familyHalf T hp x e).walk.Nil}

noncomputable def tip (e : ArmIndex T hp x) : V := (familyHalf T hp x e.val).walk.snd

lemma tip_adj (e : ArmIndex T hp x) : G.Adj x (tip T hp x e) :=
  (familyHalf T hp x e.val).walk.adj_snd e.property

lemma tip_injective : Function.Injective (tip T hp x) := by
  intro e f he
  by_contra hne
  have hval : e.val ≠ f.val := fun h ↦ hne (Subtype.ext h)
  apply Set.disjoint_left.mp (familyHalf_disjoint T hp x hval)
    (head_edge_mem (familyHalf T hp x e.val).walk e.property)
  have hh := head_edge_mem (familyHalf T hp x f.val).walk f.property
  change s(x,tip T hp x e) ∈ (familyHalf T hp x f.val).walk.toSubgraph.edgeSet
  rwa [he]

lemma arm_owner_touches (e : ArmIndex T hp x) : x ∈ (T.walk e.val.1).support := by
  by_contra hx
  exact e.property (half_nil_of_not_mem (T.walk e.val.1) (hp e.val.1) x hx e.val.2)

lemma tip_surjective_neighbor (v : V) (hv : G.Adj x v) : ∃ e : ArmIndex T hp x, tip T hp x e=v := by
  obtain ⟨i,hi⟩ := (T.cover s(x,v)).mp hv
  have hx := Walk.mem_support_of_adj_toSubgraph hi
  rw [←half_cover (T.walk i) (hp i) x hx] at hi
  have aux (d : Bool) (hd : s(x,v) ∈ (half (T.walk i) (hp i) x d).walk.toSubgraph.edgeSet) :
      ∃ e : ArmIndex T hp x, tip T hp x e=v := by
    let A := half (T.walk i) (hp i) x d
    have hn : ¬A.walk.Nil := by
      intro hh
      have he := Walk.edges_eq_nil.mpr hh
      have hd' := (half (T.walk i) (hp i) x d).walk.mem_edges_toSubgraph.mp hd
      rw [he] at hd'
      exact List.not_mem_nil hd' 
    have hhead : s(x,v)=s(x,A.walk.snd) := by
      rw [head_tail_cover A.walk hn] at hd
      rcases hd with hd|hd
      · exact hd
      · exact (tail_avoids_start A.walk A.isPath hn (Walk.mem_support_of_adj_toSubgraph hd)).elim
    have he : v=A.walk.snd := (Sym2.eq_iff.mp hhead).elim (fun h ↦ h.2)
      (fun h ↦ h.2.trans h.1)
    exact ⟨⟨(i,d),hn⟩,he.symm⟩
  exact hi.elim (aux true) (aux false)

lemma tip_bijective_neighbor : Function.Bijective
    (fun e : ArmIndex T hp x ↦ (⟨tip T hp x e,tip_adj T hp x e⟩ : G.neighborSet x)) := by
  constructor
  · intro e f he
    exact tip_injective T hp x (congrArg Subtype.val he)
  · rintro ⟨v,hv⟩
    obtain ⟨e,he⟩ := tip_surjective_neighbor T hp x v hv
    exact ⟨e,Subtype.ext he⟩

abbrev AvoidIndex := {i : Fin k // x ∉ (T.walk i).support}

lemma avoid_index_card_lt (hx : ∃ i, x ∈ (T.walk i).support) :
    Fintype.card (AvoidIndex T x) < k := by
  obtain ⟨i,hi⟩ := hx
  have h := Fintype.card_subtype_lt (p := fun q : Fin k ↦ x ∉ (T.walk q).support) (x := i)
    (show ¬x ∉ (T.walk i).support from fun hh ↦ hh hi)
  simpa only [Fintype.card_fin] using h

lemma tail_disjoint : Pairwise (fun e f : ArmIndex T hp x ↦
    Disjoint (familyHalf T hp x e.val).walk.tail.toSubgraph.edgeSet
      (familyHalf T hp x f.val).walk.tail.toSubgraph.edgeSet) := by
  intro e f hne
  exact (familyHalf_disjoint T hp x (fun he ↦ hne (Subtype.ext he))).mono
    (tail_edges_subset _ e.property) (tail_edges_subset _ f.property)

lemma tail_avoids_center (e : ArmIndex T hp x) :
    x ∉ (familyHalf T hp x e.val).walk.tail.support :=
  tail_avoids_start _ (familyHalf T hp x e.val).isPath e.property

lemma outside_cover : (BridgeGlue.within G ({x}ᶜ : Set V)).edgeSet=
    (⋃ i : AvoidIndex T x, (T.walk i.val).toSubgraph.edgeSet) ∪
      ⋃ e : ArmIndex T hp x, (familyHalf T hp x e.val).walk.tail.toSubgraph.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    induction e using Sym2.ind with
    | h y z =>
      obtain ⟨hyz,hy,hz⟩ := he
      obtain ⟨i,hi⟩ := (T.cover s(y,z)).mp hyz
      by_cases hxi : x ∈ (T.walk i).support
      · rw [←half_cover (T.walk i) (hp i) x hxi] at hi
        have aux (d : Bool) (hd : s(y,z) ∈ (half (T.walk i) (hp i) x d).walk.toSubgraph.edgeSet) :
            ∃ e : ArmIndex T hp x, s(y,z) ∈ (familyHalf T hp x e.val).walk.tail.toSubgraph.edgeSet := by
          let A := half (T.walk i) (hp i) x d
          have hn : ¬A.walk.Nil := by
            intro hh
            have he := Walk.edges_eq_nil.mpr hh
            have hd' := A.walk.mem_edges_toSubgraph.mp hd
            rw [he] at hd'
            exact List.not_mem_nil hd'
          refine ⟨⟨(i,d),hn⟩,?_⟩
          rw [head_tail_cover A.walk hn] at hd
          rcases hd with hd|hd
          · rcases Sym2.eq_iff.mp hd with h|h
            · exact (hy h.1).elim
            · exact (hz h.2).elim
          · exact hd
        exact Or.inr (Set.mem_iUnion.mpr (hi.elim (aux true) (aux false)))
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i,hxi⟩,hi⟩)
  · apply Set.union_subset
    · apply Set.iUnion_subset
      intro i
      apply PentagonCarriers.subgraph_edges_within
      intro y hy
      exact fun he ↦ i.property (he ▸ (T.walk i.val).mem_verts_toSubgraph.mp hy)
    · apply Set.iUnion_subset
      intro e
      apply PentagonCarriers.subgraph_edges_within
      intro y hy
      exact fun he ↦ tail_avoids_center T hp x e
        (he ▸ (familyHalf T hp x e.val).walk.tail.mem_verts_toSubgraph.mp hy)


end Erdos583StarPathPiecesDevelopment
