import Submission.ComponentIntegrated

/-! Integrated free-tail absorption and joint carrier optimum. -/
namespace Erdos583Work
/- Absorb the terminal edge of a defective lollipop into a normal group. -/
namespace TailEdgeAbsorption
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.RootedTailSystem _root_.Erdos583Work.TrailNormalization
open _root_.Erdos583Work.LollipopEar _root_.Erdos583Work.EdgeAbsorption
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

end TailEdgeAbsorption

/- Free shortest tails allow nil tails; a tight normal component can then
no longer remain attached only at the final endpoint. -/
namespace FreeTailAbsorption
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.MemberExpansion _root_.Erdos583Work.MemberNormalExpansion
open _root_.Erdos583Work.MarkedCycleGroups _root_.Erdos583Work.LollipopEar
open _root_.Erdos583Work.CyclePrefixRepair _root_.Erdos583Work.VertexCritical _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.TailEdgeAbsorption
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_shortest_tail (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      ∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length := by
  let P (m : ℕ) := ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
    U.score=T.score ∧ M.cycle=L.cycle ∧ M.tail.length=m
  have hex : ∃ m, P m := ⟨L.tail.length,T,L,rfl,rfl,rfl⟩
  obtain ⟨U,M,hUs,hC,hLen⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,hC,?_⟩
  intro W N hWs hNC
  rw [hLen]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,hNC.trans hC,rfl⟩

lemma fully_marked_tail_hit_is_finish [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x)
    (hhit : ∃ x ∈ L.tail.support, x ∈ (selectedGraph T F).support) :
    L.finish ∈ (selectedGraph T F).support := by
  classical
  obtain ⟨y,hy,R,B,hform,hB⟩ := CycleDefect.last_hit_split L.tail (selectedGraph T F).support hhit
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark y hy
  obtain ⟨A,hAs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun j hj ↦ (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      (fun he ↦ hiF (he ▸ hj))) D hD hcard
  let N : RootedCycleRep A r :=
    ⟨L.index,L.finish,(hrest L.index hiF).1.trans L.start_eq,
      (hrest L.index hiF).2.1.trans L.finish_eq,L.cycle,L.tail,L.isCycle,L.isPath,L.inter,
      (hrest L.index hiF).2.2.trans L.subgraph⟩
  obtain ⟨j,hj,hAj⟩ := hparts P.toSubgraph hPD
  have hij : N.index ≠ j := fun he ↦ hiF (he.symm ▸ hj)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hBQ : ∀ x ∈ B.support, x ∈ Q.support → x=y := by
    intro x hx hxQ
    apply hB x hx
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hxQ
  obtain ⟨U,M,hUs,hMC,hMf,hML⟩ := FreeTailGroups.shorten_tail_at_marked_path A r N (by omega)
    j hij R B hform Q hQ (hAj.trans hQe.symm) hBQ
  have hh := hmin U M (hUs.trans hAs) hMC
  have hlen : L.tail.length=R.length+B.length := by rw [hform,Walk.length_append]
  have hnil : B.Nil := Walk.nil_iff_length_eq.mpr (by omega)
  exact hnil.eq ▸ hy

lemma small_marked_group_misses_tail {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x) :
    Disjoint L.tail.toSubgraph.verts (selectedGraph T F).support := by
  apply Set.disjoint_left.mpr
  intro x hx hxF
  have hb := fully_marked_tail_hit_is_finish T hs r L hmin F hiF hmark
    ⟨x,L.tail.mem_verts_toSubgraph.mp hx,hxF⟩
  obtain ⟨U,M,hUs,hMC,hML⟩ := shorten_at_small_marked_group hsmall T hs r L hn F hiF hc horder hsize hb (hmark _ hb)
  have hh := hmin U M hUs hMC
  omega

lemma small_marked_group_misses_lollipop {n : ℕ} (hsmall : SmallerOrders n) [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (hn : ¬L.tail.Nil)
    (hmin : ∀ U : TrailFamily G k, ∀ M : RootedCycleRep U r,
      U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (F : Finset (Fin k)) (hiF : L.index ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (horder : (selectedGraph T F).support.ncard < n)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x) :
    Disjoint (T.walk L.index).toSubgraph.verts (selectedGraph T F).support := by
  have htail := small_marked_group_misses_tail hsmall T hs r L hn hmin F hiF hc horder hsize hmark
  have hrF : r ∉ (selectedGraph T F).support :=
    fun hh ↦ Set.disjoint_left.mp htail L.tail.start_mem_verts_toSubgraph hh
  have hnone := NilSlot.max_score_nonpath_no_nil T (maximum_of_one_defect_failure hfail T hs)
    ⟨L.index,L.member_not_path⟩
  have hav (j : Fin k) (hj : j ∈ F) : r ∉ (T.walk j).support := by
    intro hrj
    apply hrF
    rw [selected_support_eq T F (fun j _ ↦ hnone j)]
    exact ⟨j,hj,hrj⟩
  have hcycle := fully_marked_outside_group_misses_cycle hfail T hs r L F hav hmark
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.verts_sup]
  exact hcycle.union_left htail

lemma small_normal_group_proper {n : ℕ}
    {G : SimpleGraph (Fin n)} (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F)
    (hsize : (selectedGraph T F).support.ncard ≤ 2*F.card) :
    (selectedGraph T F).support.ncard < n := by
  have hFcard : F.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ F,fun hh ↦ hiF (hh.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  simp only [Fintype.card_fin,ceil_half] at hFcard
  omega

section Minimal
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (r : Fin n) (L : RootedCycleRep T r)
  (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
    U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
include hsmall hG hfail hs hmin

lemma component_unmarked (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard ≤
      2*(MemberComponents.componentMembers T L.index C).card) :
    ∃ x ∈ (selectedGraph T (MemberComponents.componentMembers T L.index C)).support,
      ¬MarkedPartition (selectedGraph T (MemberComponents.componentMembers T L.index C))
        (MemberComponents.componentMembers T L.index C).card x := by
  classical
  by_contra! hmark
  let F := MemberComponents.componentMembers T L.index C
  change (selectedGraph T F).support.ncard ≤ 2*F.card at hsize
  have hiF : L.index ∉ F := MemberComponents.removed_not_mem T L.index C
  have hc := MemberComponents.component_support_connected T L.index C
  have horder := small_normal_group_proper T L.index F hiF hsize
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  obtain ⟨x,hxL,hxF⟩ := MemberComponents.component_meets_removed T hG L.index hn C
  by_cases hnil : L.tail.Nil
  · have he : (T.walk L.index).toSubgraph=L.cycle.toSubgraph := by
      have hz : ∀ {a b c : Fin n} (P : G.Walk a b) (Q : G.Walk b c), Q.Nil →
          (P.append Q).toSubgraph=P.toSubgraph := by
        intro a b c P Q hQ
        cases hQ
        simp
      rw [L.subgraph]
      exact hz L.cycle L.tail hnil
    have hd := marked_normal_group_disjoint_cycle hsmall hfail T hs hm L.index L.cycle L.isCycle
      he F hiF hc hmark horder (by omega)
    exact Set.disjoint_left.mp hd (he ▸ hxL) hxF
  · exact Set.disjoint_left.mp
      (small_marked_group_misses_lollipop hsmall hfail T hs r L hnil hmin F hiF hc horder hsize hmark)
      hxL hxF

lemma component_expands (C : (MemberComponents.normalGraph T L.index).ConnectedComponent) :
    2*(MemberComponents.componentMembers T L.index C).card ≤
      (selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard := by
  let F := MemberComponents.componentMembers T L.index C
  have hiF : L.index ∉ F := MemberComponents.removed_not_mem T L.index C
  have hc := MemberComponents.component_support_connected T L.index C
  have hb := normal_group_expands hsmall hfail T hs L.index L.member_not_path F hiF hc
  by_contra hn
  change ¬2*F.card ≤ (selectedGraph T F).support.ncard at hn
  have he : 2*F.card=(selectedGraph T F).support.ncard+1 := by omega
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C (by
    change (selectedGraph T F).support.ncard ≤ 2*F.card
    omega)
  exact hxno (tight_normal_group_marked hsmall hfail T hs L.index L.member_not_path F hiF hc he x hx)

lemma normal_support_bound : 2*(⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1) ≤
    (selectedGraph T (Finset.univ.erase L.index)).support.ncard := by
  classical
  rw [←MemberComponents.sum_component_support,←MemberComponents.sum_component_members T L.index,Finset.mul_sum]
  exact Finset.sum_le_sum (fun C _ ↦ component_expands hsmall hG hfail T hs r L hmin C)

lemma component_surplus_le_two : ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 2 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hb : (selectedGraph T (Finset.univ.erase L.index)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase L.index)).support
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  omega

lemma odd_component_surplus_le_one (ho : Odd n) :
    ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 1 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hb : (selectedGraph T (Finset.univ.erase L.index)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase L.index)).support
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  obtain ⟨m,hmo⟩ := ho
  omega

lemma zero_component_large (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus T L.index C=0) :
    n ≤ 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard := by
  have hb := Nat.sub_eq_zero_iff_le.mp hzero
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C hb
  exact MarkedAbsorption.unmarked_normal_group_large hsmall hfail T hs L.index L.member_not_path _
    (MemberComponents.removed_not_mem T L.index C) (MemberComponents.component_support_connected T L.index C)
    hb x hx hxno

lemma zero_half_component_edge_bound
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (C : (MemberComponents.normalGraph T L.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus T L.index C=0)
    (hhalf : 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).support.ncard=n) :
    G.edgeSet.ncard ≤ 2*(selectedGraph T (MemberComponents.componentMembers T L.index C)).edgeSet.ncard+1 := by
  have hb := Nat.sub_eq_zero_iff_le.mp hzero
  obtain ⟨x,hx,hxno⟩ := component_unmarked hsmall hG hfail T hs r L hmin C hb
  by_contra hn
  exact hxno (half_normal_group_marked hcritical hfail T hs L.index L.member_not_path _
    (MemberComponents.removed_not_mem T L.index C) (MemberComponents.component_support_connected T L.index C)
    hhalf (by omega) hb x hx)

lemma cubic_open_surplus_le_one (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil) :
    ∑ C, CycleComponentBudget.componentSurplus T L.index C ≤ 1 := by
  have hh := CycleComponentBudget.component_surplus_identity T L.index
    (component_expands hsmall hG hfail T hs r L hmin)
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rintro ⟨y,j,hj,hrj⟩
    exact FreeTailGroups.cubic_open_root_others_avoid T r L hs
      (maximum_of_one_defect_failure hfail T hs) hd hn j (Finset.mem_erase.mp hj).1
      (Walk.mem_support_of_adj_toSubgraph hrj)
  have hb := Set.ncard_le_card (insert r (selectedGraph T (Finset.univ.erase L.index)).support)
  rw [Set.ncard_insert_of_notMem hr,show Nat.card (Fin n)=n by simp] at hb
  have hk : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  omega

end Minimal

lemma two_components_cycle_edge_bound [Fintype V] (T : TrailFamily G k) (r : V)
    (L : RootedCycleRep T r)
    {C D : (MemberComponents.normalGraph T L.index).ConnectedComponent} (hCD : C ≠ D) :
    (selectedGraph T (MemberComponents.componentMembers T L.index C)).edgeSet.ncard+
      (selectedGraph T (MemberComponents.componentMembers T L.index D)).edgeSet.ncard+L.cycle.length ≤
        G.edgeSet.ncard := by
  let J := selectedGraph T (MemberComponents.componentMembers T L.index C)
  let K := selectedGraph T (MemberComponents.componentMembers T L.index D)
  have hJK : Disjoint J.edgeSet K.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heJ heK
    induction e using Sym2.ind with
    | h x y =>
      exact Set.disjoint_left.mp (MemberComponents.component_support_disjoint T L.index hCD) ⟨y,heJ⟩ ⟨y,heK⟩
  have hsubC : L.cycle.toSubgraph.edgeSet ⊆ (T.walk L.index).toSubgraph.edgeSet := by
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hJC : Disjoint J.edgeSet L.cycle.toSubgraph.edgeSet :=
    (selected_disjoint T _ L.index (MemberComponents.removed_not_mem T L.index C)).mono_right hsubC
  have hKC : Disjoint K.edgeSet L.cycle.toSubgraph.edgeSet :=
    (selected_disjoint T _ L.index (MemberComponents.removed_not_mem T L.index D)).mono_right hsubC
  have hsub : J.edgeSet ∪ K.edgeSet ∪ L.cycle.toSubgraph.edgeSet ⊆ G.edgeSet := by
    rintro e ((he|he)|he)
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact edgeSet_mono (selectedGraph_le T _) he
    · exact L.cycle.toSubgraph.edgeSet_subset he
  have hb := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq (hJC.union_left hKC),Set.ncard_union_eq hJK,
    trail_edgeSet_ncard L.cycle L.isCycle.isTrail] at hb
  exact hb

section Critical
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (r : Fin n) (L : RootedCycleRep T r)
  (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep U r,
    U.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
include hsmall hG hfail hcritical hs hmin

lemma zero_components_equal {C D : (MemberComponents.normalGraph T L.index).ConnectedComponent}
    (hC : CycleComponentBudget.componentSurplus T L.index C=0)
    (hD : CycleComponentBudget.componentSurplus T L.index D=0) : C=D := by
  by_contra hCD
  have hsize := Set.ncard_le_card ((selectedGraph T (MemberComponents.componentMembers T L.index C)).support ∪
    (selectedGraph T (MemberComponents.componentMembers T L.index D)).support)
  rw [Set.ncard_union_eq (MemberComponents.component_support_disjoint T L.index hCD),
    show Nat.card (Fin n)=n by simp] at hsize
  have hCl := zero_component_large hsmall hG hfail T hs r L hmin C hC
  have hDl := zero_component_large hsmall hG hfail T hs r L hmin D hD
  have hCe := zero_half_component_edge_bound hsmall hG hfail T hs r L hmin hcritical C hC (by omega)
  have hDe := zero_half_component_edge_bound hsmall hG hfail T hs r L hmin hcritical D hD (by omega)
  have hE := two_components_cycle_edge_bound T r L hCD
  have hlen := L.isCycle.three_le_length
  omega

lemma zero_component_count :
    (Finset.univ.filter fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      CycleComponentBudget.componentSurplus T L.index C=0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  exact zero_components_equal hsmall hG hfail hcritical T hs r L hmin
    (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

lemma component_count_le_surplus_add_one :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤
      (∑ C, CycleComponentBudget.componentSurplus T L.index C)+1 := by
  classical
  have hz := zero_component_count hsmall hG hfail hcritical T hs r L hmin
  have hpos : (Finset.univ.filter fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      ¬CycleComponentBudget.componentSurplus T L.index C=0).card ≤
        ∑ C, CycleComponentBudget.componentSurplus T L.index C := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun C _ ↦ by split_ifs <;> omega)
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun C : (MemberComponents.normalGraph T L.index).ConnectedComponent ↦
      CycleComponentBudget.componentSurplus T L.index C=0)
  rw [Finset.card_univ] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

lemma normal_component_count_le_three : Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 3 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := component_surplus_le_two hsmall hG hfail T hs r L hmin
  omega

lemma odd_normal_component_count_le_two (ho : Odd n) :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 2 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := odd_component_surplus_le_one hsmall hG hfail T hs r L hmin ho
  omega

lemma cubic_open_component_count_le_two (hd : Nat.card (G.neighborSet r)=3) (hn : ¬L.tail.Nil) :
    Nat.card (MemberComponents.normalGraph T L.index).ConnectedComponent ≤ 2 := by
  have hb := component_count_le_surplus_add_one hsmall hG hfail hcritical T hs r L hmin
  have hs := cubic_open_surplus_le_one hsmall hG hfail T hs r L hmin hd hn
  omega

end Critical

lemma exists_short_tail_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      (∀ C : (MemberComponents.normalGraph U M.index).ConnectedComponent,
        2*(MemberComponents.componentMembers U M.index C).card ≤
          (selectedGraph U (MemberComponents.componentMembers U M.index C)).support.ncard) ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length := by
  obtain ⟨U,M,hUs,hMC,hmin⟩ := exists_shortest_tail T r L
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  exact ⟨U,M,hUs,hMC,component_expands hsmall hG hfail U hsU r M hmin,
    normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hmin,
    odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hmin,
    cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hmin,hmin⟩

end FreeTailAbsorption

/- Compatible free-tail and fixed-anchor carrier optimization.
No quota-energy constraint is added or claimed to survive. -/
namespace JointTailCarrier
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.QuotaSurgery
open _root_.Erdos583Work.RootedTailSystem _root_.Erdos583Work.TrailNormalization _root_.Erdos583Work.LollipopEar
open _root_.Erdos583Work.CarrierCount _root_.Erdos583Work.CarrierLength _root_.Erdos583Work.CarrierGroups
open _root_.Erdos583Work.OutsideCarrierBudget _root_.Erdos583Work.AnchorCarrier _root_.Erdos583Work.AnchorComponentBudget
open _root_.Erdos583Work.FreeTailAbsorption
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_joint_optimum (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts ≤ carrierCount U (U.walk M.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts=carrierCount U (U.walk M.index).toSubgraph.verts →
        carrierLength U (U.walk M.index).toSubgraph.verts ≤ carrierLength W (U.walk M.index).toSubgraph.verts) := by
  obtain ⟨R,N,hRs,hNC,hTail⟩ := exists_shortest_tail T r L
  let K := (R.walk N.index).toSubgraph
  obtain ⟨A,hAs,hAi,hMax,hMin⟩ := AnchorCarrier.exists_shortest_maximum_carriers R N.index K rfl
  have hP : (N.cycle.append N.tail).IsTrail := trail_append_of_disjoint N.isCycle.isTrail N.isPath.isTrail
    (edge_disjoint_of_one_common_vertex _ _ N.inter)
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general A N.index (N.cycle.append N.tail) hP
    (N.subgraph.symm.trans hAi.symm)
  let M : RootedCycleRep U r :=
    ⟨N.index,N.finish,hUa,hUb,N.cycle,N.tail,N.isCycle,N.isPath,N.inter,
      (hparts N.index).trans (hAi.trans N.subgraph)⟩
  have hUi : (U.walk N.index).toSubgraph=K := (hparts N.index).trans hAi
  have hCount : carrierCount U K.verts=carrierCount A K.verts := by
    apply carrierCount_congr
    intro j
    rw [hparts]
  have hLength : carrierLength U K.verts=carrierLength A K.verts := by
    unfold carrierLength
    apply Finset.sum_congr rfl
    intro j _
    exact carrier_weight_of_same_subgraph A U K.verts j (hparts j)
  refine ⟨U,M,hUs.trans (hAs.trans hRs),hNC,?_,?_,?_⟩
  · intro W P hWs hPC
    exact hTail W P (hWs.trans (hUs.trans hAs)) hPC
  · intro W hWs hWi
    change (W.walk N.index).toSubgraph=(U.walk N.index).toSubgraph at hWi
    rw [hUi] at hWi
    change carrierCount W (U.walk N.index).toSubgraph.verts ≤ carrierCount U (U.walk N.index).toSubgraph.verts
    rw [hUi,hCount]
    exact hMax W (hWs.trans hUs) hWi
  · intro W hWs hWi hWc
    change (W.walk N.index).toSubgraph=(U.walk N.index).toSubgraph at hWi
    rw [hUi] at hWi
    change carrierCount W (U.walk N.index).toSubgraph.verts=carrierCount U (U.walk N.index).toSubgraph.verts at hWc
    rw [hUi,hCount] at hWc
    change carrierLength U (U.walk N.index).toSubgraph.verts ≤ carrierLength W (U.walk N.index).toSubgraph.verts
    rw [hUi,hLength]
    exact hMin W (hWs.trans hUs) hWi hWc

lemma exists_joint_component_certificate {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      M.cycle.length+M.tail.length ≤ 2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2 ∧
      M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+3 ∧
      (Odd n → M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2) := by
  obtain ⟨U,M,hUs,hMC,hTail,hMax,hMin⟩ := exists_joint_optimum T r L
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hnK : ¬IsPathSubgraph (U.walk M.index).toSubgraph := by
    rintro ⟨a,b,P,hP,hPe⟩
    exact M.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail M.index) hP hPe)
  have hAB := AnchorCarrier.optimized_anchor_size_bound hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hCB := AnchorComponentBudget.anchor_component_budget hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hv : (U.walk M.index).toSubgraph.verts.ncard=M.cycle.length+M.tail.length := by
    rw [M.subgraph,LollipopEar.lollipop_vertex_card M.cycle M.isCycle M.tail M.isPath M.inter,Walk.length_append]
  refine ⟨U,M,hUs,hMC,
    normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hTail,
    odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hTail,
    cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hTail,?_,?_,?_⟩
  · have hh := hAB.1
    rwa [hv] at hh
  · have hh := hCB.1
    rwa [hv] at hh
  · intro ho
    have hh := hCB.2 ho
    rwa [hv] at hh

end JointTailCarrier

end Erdos583Work
