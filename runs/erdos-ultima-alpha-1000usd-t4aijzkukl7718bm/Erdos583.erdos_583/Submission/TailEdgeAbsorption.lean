import Submission.ComponentIntegrated

/-! Absorb the terminal edge of a defective lollipop into a normal group. -/
namespace Erdos583TailEdgeAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.LollipopEar Erdos583Work.EdgeAbsorption
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma padded_path_family (v : V) (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (hcard : D.card ≤ k) : ∃ P : TrailFamily G k, ∀ j, (P.walk j).IsPath := by
  classical
  obtain ⟨R,hR,_⟩ := EdgeDefect.decomposition_path_family D hD
  let s (j : Fin k) := if hj : j.val < D.card then R.start ⟨j.val,hj⟩ else v
  let t (j : Fin k) := if hj : j.val < D.card then R.finish ⟨j.val,hj⟩ else v
  have hex (j : Fin k) : ∃ Q : G.Walk (s j) (t j), Q.IsPath ∧
      (∀ hj : j.val < D.card, Q.toSubgraph=(R.walk ⟨j.val,hj⟩).toSubgraph) ∧
      (¬j.val < D.card → Q.toSubgraph.edgeSet=∅) := by
    by_cases hj : j.val < D.card
    · rw [show s j=R.start ⟨j.val,hj⟩ by simp [s,hj],show t j=R.finish ⟨j.val,hj⟩ by simp [t,hj]]
      exact ⟨R.walk ⟨j.val,hj⟩,hR _,fun _ ↦ rfl,fun hh ↦ (hh hj).elim⟩
    · rw [show s j=v by simp [s,hj],show t j=v by simp [t,hj]]
      exact ⟨Walk.nil,Walk.IsPath.nil,fun hh ↦ (hj hh).elim,fun _ ↦ by simp⟩
  choose q hp hin hout using hex
  let P : TrailFamily G k :=
    { start := s, finish := t, walk := q, isTrail := fun j ↦ (hp j).isTrail
      disjoint := by
        intro j l hjl
        by_cases hj : j.val < D.card
        · rw [hin j hj]
          by_cases hl : l.val < D.card
          · rw [hin l hl]
            exact R.disjoint (fun he ↦ hjl (Fin.ext (congrArg (fun z : Fin D.card ↦ z.val) he)))
          · rw [hout l hl]; simp
        · rw [hout j hj]; simp
      cover := by
        intro d
        constructor
        · intro hd
          obtain ⟨j,hj⟩ := (R.cover d).mp hd
          let l : Fin k := ⟨j.val,j.isLt.trans_le hcard⟩
          exact ⟨l,by rw [hin l j.isLt]; exact hj⟩
        · rintro ⟨j,hj⟩
          exact (q j).toSubgraph.edgeSet_subset hj }
  exact ⟨P,hp⟩

/-- A path group and a separate trail can be replaced together. Padding by nil
members avoids an unproved exact-cardinality assertion for the enlarged group. -/
lemma replace_group_and_trail (T : TrailFamily G k) (i : Fin k)
    (F : Finset (Fin k)) (hiF : i ∉ F)
    (J : SimpleGraph V) (hJG : J ≤ G)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsTrail)
    (hd : Disjoint J.edgeSet Q.toSubgraph.edgeSet)
    (he : J.edgeSet ∪ Q.toSubgraph.edgeSet=
      (selectedGraph T F).edgeSet ∪ (T.walk i).toSubgraph.edgeSet)
    (D : Finset J.Subgraph) (hD : GoodDecomposition J D) (hDc : D.card ≤ F.card) :
    ∃ U : TrailFamily G k, U.start i=a ∧ U.finish i=b ∧ (U.walk i).toSubgraph=Q.toSubgraph ∧
      (∀ l, l ∉ F → l ≠ i → (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      ∀ l ∈ F, (U.walk l).IsPath := by
  classical
  obtain ⟨P,hP⟩ := padded_path_family a D hD hDc
  let e : F ≃ Fin F.card := Fintype.equivFinOfCardEq (by simp)
  let s (l : Fin k) := if l=i then a else if hl : l ∈ F then P.start (e ⟨l,hl⟩) else T.start l
  let t (l : Fin k) := if l=i then b else if hl : l ∈ F then P.finish (e ⟨l,hl⟩) else T.finish l
  have hex (l : Fin k) : ∃ q : G.Walk (s l) (t l), q.IsTrail ∧
      (l=i → q.toSubgraph=Q.toSubgraph) ∧
      (∀ hl : l ∈ F, q.toSubgraph=((P.walk (e ⟨l,hl⟩)).mapLe hJG).toSubgraph ∧ q.IsPath) ∧
      (l ∉ F → l ≠ i → q.toSubgraph=(T.walk l).toSubgraph) := by
    by_cases hli : l=i
    · subst l
      rw [show s i=a by simp [s],show t i=b by simp [t]]
      exact ⟨Q,hQ,fun _ ↦ rfl,fun hh ↦ (hiF hh).elim,fun _ hh ↦ (hh rfl).elim⟩
    · by_cases hl : l ∈ F
      · rw [show s l=P.start (e ⟨l,hl⟩) by simp [s,hli,hl],show t l=P.finish (e ⟨l,hl⟩) by simp [t,hli,hl]]
        exact ⟨(P.walk (e ⟨l,hl⟩)).mapLe hJG,((hP _).mapLe _).isTrail,
          fun hh ↦ (hli hh).elim,fun _ ↦ ⟨rfl,(hP _).mapLe _⟩,fun hh _ ↦ (hh hl).elim⟩
      · rw [show s l=T.start l by simp [s,hli,hl],show t l=T.finish l by simp [t,hli,hl]]
        exact ⟨T.walk l,T.isTrail l,fun hh ↦ (hli hh).elim,fun hh ↦ (hl hh).elim,fun _ _ ↦ rfl⟩
  choose q hq hqi hqF hqout using hex
  have hqin (l : Fin k) (hl : l ∈ F) : (q l).toSubgraph.edgeSet=(P.walk (e ⟨l,hl⟩)).toSubgraph.edgeSet := by
    rw [(hqF l hl).1]
    simp only [Walk.mapLe,Walk.toSubgraph_map,edgeSet_lift]
  have hcross (l : Fin k) (hl : l ∉ F) (hli : l ≠ i) :
      Disjoint (J.edgeSet ∪ Q.toSubgraph.edgeSet) (T.walk l).toSubgraph.edgeSet := by
    rw [he]
    exact disjoint_sup_left.mpr ⟨selected_disjoint T F l hl,T.disjoint hli.symm⟩
  have hdis : Pairwise fun l m ↦ Disjoint (q l).toSubgraph.edgeSet (q m).toSubgraph.edgeSet := by
    intro l m hlm
    by_cases hli : l=i
    · subst l
      rw [hqi i rfl]
      by_cases hm : m ∈ F
      · rw [hqin m hm]
        exact (hd.mono_left (P.walk (e ⟨m,hm⟩)).toSubgraph.edgeSet_subset).symm
      · rw [hqout m hm hlm.symm]
        exact (disjoint_sup_left.mp (hcross m hm hlm.symm)).2
    · by_cases hmi : m=i
      · subst m
        rw [hqi i rfl]
        by_cases hl : l ∈ F
        · rw [hqin l hl]
          exact hd.mono_left (P.walk (e ⟨l,hl⟩)).toSubgraph.edgeSet_subset
        · rw [hqout l hl hli]
          exact (disjoint_sup_left.mp (hcross l hl hli)).2.symm
      · by_cases hl : l ∈ F
        · rw [hqin l hl]
          by_cases hm : m ∈ F
          · rw [hqin m hm]
            exact P.disjoint (fun hh ↦ hlm (congrArg Subtype.val (e.injective hh)))
          · rw [hqout m hm hmi]
            exact ((disjoint_sup_left.mp (hcross m hm hmi)).1).mono_left
              (P.walk (e ⟨l,hl⟩)).toSubgraph.edgeSet_subset
        · rw [hqout l hl hli]
          by_cases hm : m ∈ F
          · rw [hqin m hm]
            exact (((disjoint_sup_left.mp (hcross l hl hli)).1).mono_left
              (P.walk (e ⟨m,hm⟩)).toSubgraph.edgeSet_subset).symm
          · rw [hqout m hm hmi]
            exact T.disjoint hlm
  have hinJ (d : Sym2 V) (hdJ : d ∈ J.edgeSet) : ∃ l, d ∈ (q l).toSubgraph.edgeSet := by
    obtain ⟨j,hj⟩ := (P.cover d).mp hdJ
    let l := e.symm j
    refine ⟨l.val,?_⟩
    rw [hqin l.val l.property]
    change d ∈ (P.walk (e (e.symm j))).toSubgraph.edgeSet
    rw [e.apply_symm_apply]
    exact hj
  have hcover (d : Sym2 V) : d ∈ G.edgeSet ↔ ∃ l, d ∈ (q l).toSubgraph.edgeSet := by
    constructor
    · intro hdG
      obtain ⟨l,hl⟩ := (T.cover d).mp hdG
      by_cases hli : l=i
      · subst l
        have hh : d ∈ J.edgeSet ∪ Q.toSubgraph.edgeSet := he.symm ▸ Or.inr hl
        exact hh.elim (hinJ d) (fun hh ↦ ⟨i,by rwa [hqi i rfl]⟩)
      · by_cases hlF : l ∈ F
        · have hh : d ∈ J.edgeSet ∪ Q.toSubgraph.edgeSet :=
            he.symm ▸ Or.inl ((selected_edge_iff T F d).mpr ⟨l,hlF,hl⟩)
          exact hh.elim (hinJ d) (fun hh ↦ ⟨i,by rwa [hqi i rfl]⟩)
        · exact ⟨l,by rwa [hqout l hlF hli]⟩
    · rintro ⟨l,hl⟩
      exact (q l).toSubgraph.edgeSet_subset hl
  let U : TrailFamily G k := ⟨s,t,q,hq,hdis,hcover⟩
  exact ⟨U,by simp [U,s],by simp [U,t],hqi i rfl,hqout,fun l hl ↦ (hqF l hl).2⟩

lemma replacement_score [Fintype V] (T U : TrailFamily G k) (i : Fin k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsTrail)
    (he : (U.walk i).toSubgraph=Q.toSubgraph) (hQc : Q.toSubgraph.verts.ncard=Q.length)
    (hp : ∀ j, j ≠ i → (U.walk j).IsPath) : U.score=T.score := by
  classical
  have hlen : (U.walk i).length=Q.length := by
    rw [←trail_edgeSet_ncard _ (U.isTrail i),he,trail_edgeSet_ncard _ hQ]
  have hd : U.defect i=1 := by
    have hh := U.defect_add_vertices i
    rw [he,hQc,hlen] at hh
    omega
  have hsum : ∑ j, U.defect j=1 := by
    rw [Finset.sum_eq_single i,hd]
    · intro j _ hji
      exact (U.defect_eq_zero_iff j).mpr (hp j hji)
    · simp
  have hh := U.sum_defect_add_score
  rw [hsum] at hh
  omega

lemma absorb_tail_edge [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (r : V) (L : RootedCycleRep T r)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    {w : V} (R : G.Walk r w) (h : G.Adj w L.finish)
    (hform : L.tail=R.append (Walk.cons h Walk.nil))
    (D : Finset (selectedGraph T F ⊔ edge L.finish w).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge L.finish w) D) (hDc : D.card ≤ F.card) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length+1=L.tail.length := by
  have hR : R.IsPath := (hform ▸ L.isPath).of_append_left
  have hinter (x : V) (hx : x ∈ L.cycle.support) (hxR : x ∈ R.support) : x=r := by
    apply L.inter x hx
    rw [hform,Walk.mem_support_append_iff]
    exact Or.inl hxR
  let Q := L.cycle.append R
  have hQ : Q.IsTrail := trail_append_of_disjoint L.isCycle.isTrail hR.isTrail
    (edge_disjoint_of_one_common_vertex _ _ hinter)
  have hold : (Q.append (Walk.cons h Walk.nil)).IsTrail := by
    simpa only [Q,←Walk.append_assoc,←hform] using
      trail_append_of_disjoint L.isCycle.isTrail L.isPath.isTrail
        (edge_disjoint_of_one_common_vertex _ _ L.inter)
  have hsingle : (Walk.cons h Walk.nil).toSubgraph.edgeSet={s(L.finish,w)} := by
    simp only [Walk.toSubgraph_cons_nil_eq_subgraphOfAdj,edgeSet_subgraphOfAdj,Sym2.eq_swap]
  have hOld : (T.walk L.index).toSubgraph.edgeSet=Q.toSubgraph.edgeSet ∪ {s(L.finish,w)} := by
    rw [L.subgraph,hform,Walk.append_assoc]
    simp only [Q,Walk.toSubgraph_append,Subgraph.edgeSet_sup,hsingle]
  have hQsub : Q.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [hOld]; exact Set.subset_union_left
  let J := selectedGraph T F ⊔ edge L.finish w
  have hJG : J ≤ G := sup_le (selectedGraph_le T F) ((edge_le_iff G).mpr (Or.inr h.symm))
  have hd : Disjoint J.edgeSet Q.toSubgraph.edgeSet := by
    rw [show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(L.finish,w)} by
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne.symm]]
    refine disjoint_sup_left.mpr ⟨(selected_disjoint T F L.index hiF).mono_right hQsub,?_⟩
    have hh := append_trail_disjoint hold
    rw [hsingle] at hh
    exact hh.symm
  have he : J.edgeSet ∪ Q.toSubgraph.edgeSet=
      (selectedGraph T F).edgeSet ∪ (T.walk L.index).toSubgraph.edgeSet := by
    rw [hOld,show J.edgeSet=(selectedGraph T F).edgeSet ∪ {s(L.finish,w)} by
      rw [edgeSet_sup,edge_edgeSet_of_ne h.ne.symm]]
    ext d
    simp only [Set.mem_union]
    tauto
  obtain ⟨U,hUa,hUb,hUi,hrest,hpaths⟩ := replace_group_and_trail T L.index F hiF J hJG Q hQ hd he D hD hDc
  have hUs : U.score=T.score := by
    apply replacement_score T U L.index hs Q hQ hUi
      (lollipop_vertex_card L.cycle L.isCycle R hR hinter)
    intro j hji
    by_cases hjF : j ∈ F
    · exact hpaths j hjF
    · exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail j)
        ((T.one_defect_other_paths hs L.index L.member_not_path).2 j hji) (hrest j hjF hji)
  let M : RootedCycleRep U r := ⟨L.index,w,hUa,hUb,L.cycle,R,L.isCycle,hR,hinter,hUi⟩
  refine ⟨U,M,hUs,rfl,?_⟩
  change R.length+1=L.tail.length
  rw [hform,Walk.length_append,Walk.length_cons,Walk.length_nil]

lemma absorb_last_tail_edge [Fintype V] (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (r : V) (L : RootedCycleRep T r)
    (hn : ¬L.tail.Nil) (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (D : Finset (selectedGraph T F ⊔ edge L.finish L.tail.penultimate).Subgraph)
    (hD : GoodDecomposition (selectedGraph T F ⊔ edge L.finish L.tail.penultimate) D)
    (hDc : D.card ≤ F.card) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length+1=L.tail.length := by
  apply absorb_tail_edge T hs r L F hiF L.tail.dropLast (L.tail.adj_penultimate hn) ?_ D hD hDc
  rw [←Walk.concat_eq_append,Walk.concat_dropLast]

lemma shorten_at_small_marked_group {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hb : L.finish ∈ (selectedGraph T F).support)
    (hm : MarkedCycleGroups.MarkedPartition (selectedGraph T F) F.card L.finish) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length+1=L.tail.length := by
  obtain ⟨D,hD,hDc⟩ := MarkedAbsorption.marked_edge_partition hsmall (selectedGraph T F) hc
    (L.tail.adj_penultimate hn).ne.symm hb horder hsize hm
  exact absorb_last_tail_edge T hs r L hn F hiF D hD hDc

end Erdos583TailEdgeAbsorptionDevelopment
