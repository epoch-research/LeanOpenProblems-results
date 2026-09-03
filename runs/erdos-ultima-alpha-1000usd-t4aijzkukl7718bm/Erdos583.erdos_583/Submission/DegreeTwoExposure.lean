import Submission.NonneighborShortening

/-! Prescribed exposure at a unique even vertex of degree two. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.SingletonRotation
open Erdos583Work.PendantCompletion
open Erdos583NonneighborShorteningDevelopment
namespace Erdos583DegreeTwoExposureDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma avoids_leaf_of_disjoint {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (P : G.Walk a b) (hn : ¬P.Nil) (hcd : G.Adj c d)
    (hleaf : ∀ x, G.Adj d x → x=c)
    (hdis : Disjoint P.toSubgraph.edgeSet (G.subgraphOfAdj hcd).edgeSet) :
    d ∉ P.support := by
  intro hd
  obtain ⟨x,hx⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor P hn (P.mem_verts_toSubgraph.mpr hd)
  have hxc : x=c := hleaf x (P.toSubgraph.adj_sub hx)
  subst x
  exact Set.disjoint_left.mp hdis (show s(d,c) ∈ P.toSubgraph.edgeSet from hx) (by simp [Sym2.eq_swap])

lemma force_split_preserving_leaf {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (l : Fin k) {a u c w d b : V} (h : G.Adj u c) (hcd : G.Adj c d)
    (hud : u ≠ d) (hleaf : ∀ x, G.Adj d x → x=c)
    (hnbr : ∀ x, G.Adj c x → x=u ∨ x=w ∨ x=d)
    (hl : (T.walk l).toSubgraph = G.subgraphOfAdj hcd)
    (A : G.Walk a u) (B : G.Walk c b)
    (hp : (A.append (Walk.cons h B)).IsTrail)
    (hm : IsMember T (A.append (Walk.cons h B))) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      (S.walk l).toSubgraph = G.subgraphOfAdj hcd ∧
      ∃ t, ∃ q : G.Walk c t, (Walk.cons h q).IsPath ∧ IsMember S (Walk.cons h q) := by
  classical
  let P := A.append (Walk.cons h B)
  have hpP : P.IsPath := max_score_member_isPath T hmax P hp hm
  have hnP : ¬P.Nil := by simp [P,Walk.nil_append_iff]
  obtain ⟨i,hends,he⟩ := hm
  have hedge : s(u,c) ∈ P.toSubgraph.edgeSet := by simp [P]
  have hil : i ≠ l := by
    intro hi
    subst i
    rw [←he,hl] at hedge
    have hh : u=c ∧ c=d ∨ u=d ∧ c=c := by simpa only [edgeSet_subgraphOfAdj,Set.mem_singleton_iff,Sym2.eq_iff] using hedge
    exact hh.elim (fun hh ↦ h.ne hh.1) (fun hh ↦ hud hh.1)
  have hdis : Disjoint P.toSubgraph.edgeSet (G.subgraphOfAdj hcd).edgeSet := by
    rw [←he,←hl]
    exact T.disjoint hil
  have hdP : d ∉ P.support := avoids_leaf_of_disjoint P hnP hcd hleaf hdis
  have hcnends := (endpoints_of_path_subgraph T l (Walk.cons hcd Walk.nil)
    (by simp [hcd.ne]) (by simp) (by simpa using hl)).1
  have hbnc : b ≠ c := by
    intro hbc
    have hci : c=T.start i ∨ c=T.finish i := by
      rcases hends with hh | hh
      · exact Or.inr (hbc ▸ hh.2.symm)
      · exact Or.inl (hbc ▸ hh.1.symm)
    exact hil (endpoint_index_eq T hci hcnends)
  have hBn : ¬B.Nil := Walk.not_nil_of_ne hbnc.symm
  have hsnd : B.snd=w := by
    rcases hnbr B.snd (B.adj_snd hBn) with hu | hw | hd
    · have huB : u ∈ B.support := hu ▸ B.getVert_mem_support 1
      exact ((Walk.cons_isPath_iff h B).mp hpP.of_append_right).2 huB |>.elim
    · exact hw
    · apply False.elim
      apply hdP
      have hdB : d ∈ B.support := hd ▸ B.getVert_mem_support 1
      exact (Walk.mem_support_append_iff _ _).mpr (Or.inr (List.mem_cons_of_mem _ hdB))
  have hprefix_disj : A.support.dropLast.Disjoint (Walk.cons h B).support := by
    have hh := hpP.support_nodup
    rw [show P = A.append (Walk.cons h B) from rfl,Walk.support_append_eq_support_dropLast_append] at hh
    exact List.disjoint_of_nodup_append hh
  have hguard : ∀ x ∈ A.support.dropLast, x ∉ (T.walk l).support ∧
      ∀ z ∈ (T.walk l).support, ¬G.Adj x z := by
    intro x hx
    have hxu : x ≠ u := by
      intro hh; subst x
      exact hprefix_disj hx (Walk.cons h B).start_mem_support
    have hxc : x ≠ c := by
      intro hh; subst x
      exact hprefix_disj hx (List.mem_cons_of_mem _ B.start_mem_support)
    have hxw : x ≠ w := by
      intro hh; subst x
      exact hprefix_disj hx (List.mem_cons_of_mem _ (hsnd ▸ B.getVert_mem_support 1))
    have hxd : x ≠ d := by
      intro hh; subst x
      exact hdP ((Walk.mem_support_append_iff _ _).mpr
        (Or.inl (List.mem_of_mem_dropLast hx)))
    have hsupport (z) : z ∈ (T.walk l).support ↔ z=c ∨ z=d := by
      rw [← Walk.mem_verts_toSubgraph,hl]
      simp [eq_comm]
    refine ⟨?_,?_⟩
    · simpa only [hsupport,not_or] using And.intro hxc hxd
    · intro z hz hxz
      rcases (hsupport z).mp hz with rfl | rfl
      · exact (hnbr x hxz.symm).elim hxu (fun hh ↦ hh.elim hxw hxd)
      · exact hxc (hleaf x hxz.symm)
  obtain ⟨S,hS,hSl,t,r,hr,hmr⟩ := extend_suffix_preserving A T hmax l
    (Walk.cons h B) (by simp) hp ⟨i,hends,he⟩ hguard
  have hSmax : ∀ U : NormalTrailSystem G k, U.score ≤ S.score := by
    intro U; rw [hS]; exact hmax U
  exact ⟨S,hS,hSl.trans hl,t,B.append r,
    max_score_member_isPath S hSmax _ hr hmr,hmr⟩

lemma force_first_preserving_leaf {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (l : Fin k) {u c w d : V} (h : G.Adj u c) (hcd : G.Adj c d)
    (hud : u ≠ d) (hleaf : ∀ x, G.Adj d x → x=c)
    (hnbr : ∀ x, G.Adj c x → x=u ∨ x=w ∨ x=d)
    (hl : (T.walk l).toSubgraph = G.subgraphOfAdj hcd) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      (S.walk l).toSubgraph = G.subgraphOfAdj hcd ∧
      ∃ t, ∃ q : G.Walk c t, (Walk.cons h q).IsPath ∧ IsMember S (Walk.cons h q) := by
  obtain ⟨i,hi⟩ := (T.cover s(u,c)).mp h
  obtain ⟨a,b,hab,A,B,hee,he⟩ := walk_split_at_edge (T.walk i) s(u,c)
    ((T.walk i).mem_edges_toSubgraph.mp hi)
  have hp : (A.append (Walk.cons hab B)).IsTrail := he ▸ T.isTrail i
  have hm : IsMember T (A.append (Walk.cons hab B)) := he ▸ isMember_walk T i
  rcases Sym2.eq_iff.mp hee with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact force_split_preserving_leaf T hmax l h hcd hud hleaf hnbr hl A B hp hm
  · have hpr := hp.reverse
    have hmr := isMember_reverse hm
    rw [Walk.reverse_append,Walk.reverse_cons,← Walk.append_assoc,Walk.cons_nil_append] at hpr hmr
    exact force_split_preserving_leaf T hmax l h hcd hud hleaf hnbr hl B.reverse A.reverse hpr hmr


lemma projected_member_mem {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (T : NormalTrailSystem (leafCompletion G S) k) {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    (htrack : ∀ H ∈ D, ∃ i, H = (projectWalk (T.walk i)).toSubgraph)
    {a b : V ⊕ S} (p : (leafCompletion G S).Walk a b) (hm : IsMember T p)
    (hn : ¬(projectWalk p).Nil) : (projectWalk p).toSubgraph ∈ D := by
  obtain ⟨i,_,he⟩ := hm
  have he' : (projectWalk (T.walk i)).toSubgraph.edgeSet = (projectWalk p).toSubgraph.edgeSet := by
    ext e
    rw [project_edgeSet,project_edgeSet,he]
  have hin : ¬(projectWalk (T.walk i)).Nil := by
    intro hi
    have hmem := (projectWalk p).toSubgraph_adj_snd hn
    change s(root a,(projectWalk p).snd) ∈ (projectWalk p).toSubgraph.edgeSet at hmem
    rw [←he'] at hmem
    have hh := (projectWalk (T.walk i)).mem_edges_toSubgraph.mp hmem
    rw [Walk.edges_eq_nil.mpr hi] at hh
    exact List.not_mem_nil hh
  have heq := CanonicalRotation.walk_subgraph_eq_of_edges _ _ hin hn he'
  rw [←heq]
  exact (CanonicalRotation.projection_mem_iff T hD hne htrack i).mpr hin

/-- In a graph whose unique even vertex has degree two, either incident
edge can be prescribed starting at its odd end in a sharp path partition. -/
lemma one_even_degree_two_exposure {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V) (hc : Nat.card (G.neighborSet c)=2)
    (ho : ∀ x, x ≠ c → Odd (Nat.card (G.neighborSet x)))
    {u : V} (h : G.Adj u c) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1=Fintype.card V ∧
      ∃ t, ∃ p : G.Walk c t, (Walk.cons h p).IsPath ∧ (Walk.cons h p).toSubgraph ∈ D := by
  classical
  let A : Set V := {c}
  let H := leafCompletion G A
  let c' : A := ⟨c,Set.mem_singleton c⟩
  have hodd (x : V ⊕ A) : Odd (H.degree x) := by
    suffices hh : Odd (Nat.card (H.neighborSet x)) by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh
    cases x with
    | inl v =>
      rw [original_neighbor_ncard]
      by_cases hv : v=c
      · subst v; rw [hc]; simpa only [A,Set.mem_singleton_iff,if_pos rfl] using (show Odd (2+1 : ℕ) by decide)
      · simpa [A,hv] using ho v hv
    | inr v => rw [leaf_neighbor_ncard]; decide
  obtain ⟨k,hk,⟨T⟩⟩ := all_odd_normal_trail_system H hodd
  obtain ⟨R,hR⟩ := T.exists_max_score
  have hleafedge : H.Adj (.inl c) (.inr c') := rfl
  obtain ⟨U,hU,t,q,hq,hmem⟩ := TrailNormalization.force_first_edge R hR hleafedge
  have hUmax : ∀ X : NormalTrailSystem H k, X.score ≤ U.score := by
    intro X; rw [hU]; exact hR X
  have hpq := TrailNormalization.max_score_member_isPath U hUmax _ hq hmem
  have hqn : q.Nil := by
    by_contra hn
    have hs : q.snd = .inl c := (leaf_adj c' _).mp (q.adj_snd hn)
    have hh : Sum.inl c ∈ q.support := hs ▸ q.getVert_mem_support 1
    exact (Walk.cons_isPath_iff hleafedge q).mp hpq |>.2 hh
  cases hqn
  obtain ⟨l,_,hle⟩ := hmem
  have hl : (U.walk l).toSubgraph = H.subgraphOfAdj hleafedge := by simpa using hle
  obtain ⟨v,w,hvw,hcw⟩ := Set.ncard_eq_two.mp (show (G.neighborSet c).ncard=2 from hc)
  have hunbr : u=v ∨ u=w := by simpa only [hcw,Set.mem_insert_iff,Set.mem_singleton_iff] using (show u ∈ G.neighborSet c from h.symm)
  have htwonbr : ∃ w, ∀ x, G.Adj c x → x=u ∨ x=w := by
    rcases hunbr with rfl | rfl
    · exact ⟨w,fun x hx ↦ by simpa only [hcw,Set.mem_insert_iff,Set.mem_singleton_iff] using (show x ∈ G.neighborSet c from hx)⟩
    · refine ⟨v,fun x hx ↦ ?_⟩
      simpa only [hcw,Set.mem_insert_iff,Set.mem_singleton_iff,or_comm] using (show x ∈ G.neighborSet c from hx)
  obtain ⟨w,hnbr⟩ := htwonbr
  have hH : H.Adj (.inl u) (.inl c) := h
  have hHnbr (x : V ⊕ A) (hx : H.Adj (.inl c) x) :
      x=Sum.inl u ∨ x=Sum.inl w ∨ x=Sum.inr c' := by
    cases x with
    | inl x =>
      exact (hnbr x hx).elim (fun hh ↦ Or.inl (congrArg Sum.inl hh))
        (fun hh ↦ Or.inr (Or.inl (congrArg Sum.inl hh)))
    | inr x => exact Or.inr (Or.inr (congrArg Sum.inr (Subtype.ext hx.symm)))
  obtain ⟨S,hS,hSl,t,p,hp,hm⟩ := force_first_preserving_leaf U hUmax l hH hleafedge
    (by simp) (fun x hx ↦ (leaf_adj c' x).mp hx) hHnbr hl
  have hSmax : ∀ X : NormalTrailSystem H k, X.score ≤ S.score := by
    intro X; rw [hS]; exact hUmax X
  have hpS := max_score_isPath S hSmax
  obtain ⟨D,hD,hne,hcard,_,htrack⟩ := project_system_tracked S hpS
  have hlvanish : l ∈ vanished S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(project_nil_iff (S.walk l) (hpS l)).mpr ?_⟩
    obtain ⟨ha,hb⟩ | ⟨ha,hb⟩ := CanonicalRotation.single_edge_endpoints hleafedge
      (S.walk l) (hpS l) hSl
    · rw [ha,hb]; rfl
    · rw [ha,hb]; rfl
  have hvl : 1 ≤ (vanished S).card := Finset.card_pos.mpr ⟨l,hlvanish⟩
  have hk' : 2*k=Fintype.card V+1 := by simpa [A] using hk
  have hbound : 2*D.card+1 ≤ Fintype.card V := by omega
  have hpar (x : V) : Odd (G.degree x) ↔ x ≠ c := by
    constructor
    · intro hx hxc
      subst x
      have hh : G.degree c=2 := by simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hc
      rw [hh] at hx
      exact (by decide : ¬Odd (2:ℕ)) hx
    · intro hx
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho x hx
  have hcount : Fintype.card {x : V // Odd (G.degree x)}=Fintype.card V-1 := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hpar),Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have hlow := odd_vertices_le_twice_path_count G hD
  rw [hcount] at hlow
  have hproj : projectWalk (Walk.cons hH p) = Walk.cons h (projectWalk p) := rfl
  refine ⟨D,hD,by omega,root t,projectWalk p,?_,?_⟩
  · rw [←hproj]
    exact (project_path_support _ hp).1
  · rw [←hproj]
    exact projected_member_mem S hD hne htrack _ hm (by rw [hproj]; simp)

end Erdos583DegreeTwoExposureDevelopment
