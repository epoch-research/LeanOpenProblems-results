import Submission.VertexTracking

/-! Local normalization with a protected triangle-free edge. No general
protected normalization or Gallai bound is asserted in this file. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.SingletonRotation
open Erdos583VertexTrackingDevelopment
namespace Erdos583ProtectedEdgeDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma trail_isPath_of_subgraph_eq {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (hp : p.IsTrail) (hq : q.IsPath)
    (he : p.toSubgraph = q.toSubgraph) : p.IsPath := by
  classical
  have he' : p.edges.toFinset = q.edges.toFinset := by
    ext e
    simp only [List.mem_toFinset,← Walk.mem_edges_toSubgraph,he]
  have hlen : p.length = q.length := by
    have hh := congrArg Finset.card he'
    simpa only [List.toFinset_card_of_nodup hp.edges_nodup,
      List.toFinset_card_of_nodup hq.isTrail.edges_nodup,Walk.length_edges] using hh
  have hs : p.support.toFinset = q.support.toFinset := by
    ext x
    simp only [List.mem_toFinset,← Walk.mem_verts_toSubgraph,he]
  rw [Walk.isPath_def]
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (p.support : Multiset V))).mp
  change p.support.toFinset.card = p.support.length
  rw [hs,List.toFinset_card_of_nodup hq.support_nodup,Walk.length_support,
    Walk.length_support,hlen]

/-- Two exits suffice to avoid a whole outside singleton edge when the root
cannot be adjacent to both its endpoints. -/
lemma repair_avoiding_single_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {x : V} {B : Finset V} (R : RootedTailSystem G k x B)
    (l : Fin k) (hl : l ∉ R.active) {u v : V} (huv : G.Adj u v)
    (he : (R.system.walk l).toSubgraph = G.subgraphOfAdj huv)
    (hsep : ¬(G.Adj x u ∧ G.Adj x v)) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      (T.walk l).toSubgraph = G.subgraphOfAdj huv := by
  classical
  let w := if G.Adj x u then u else v
  obtain ⟨S,hs,hesc,havoid,htrack⟩ := DoubleEscape.expose_escape_avoiding R w
  obtain ⟨T,hT,j,hj,hown,hTe⟩ := MultipleEscape.finish_exposed_tracked S hesc
  have hlS : l ∉ S.active := htrack.1.symm ▸ hl
  have hlj : l ≠ j := by
    intro hh
    subst j
    let z := (S.tail ⟨x,S.root_mem⟩).snd
    have hzmem : z ∈ (S.system.walk l).toSubgraph.verts := by
      apply (S.system.walk l).mem_verts_toSubgraph.mpr
      rcases hown with hh | hh
      · change (S.tail ⟨x,S.root_mem⟩).snd ∈ _
        rw [hh]
        exact (S.system.walk l).start_mem_support
      · change (S.tail ⟨x,S.root_mem⟩).snd ∈ _
        rw [hh]
        exact (S.system.walk l).end_mem_support
    rw [(htrack.2 l hl).2.2,he] at hzmem
    have hzu : z=u ∨ z=v := by simpa only [subgraphOfAdj_verts,Set.mem_insert_iff,Set.mem_singleton_iff] using hzmem
    have hzx : G.Adj x z := (S.tail ⟨x,S.root_mem⟩).adj_snd S.root_nonempty
    have hzw : z=w := by
      rcases hzu with rfl | rfl
      · simp [w,hzx]
      · have hnx : ¬G.Adj x u := fun hh ↦ hsep ⟨hh,hzx⟩
        simp [w,hnx]
    exact havoid hzw
  exact ⟨T,by omega,(hTe l hlS hlj).trans ((htrack.2 l hl).2.2.trans he)⟩

/-- A repeated starting vertex can be repaired while a marked triangle-free
edge remains a whole member at its original index. -/
lemma improve_repeated_start_protect_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k) {u v : V} (huv : G.Adj u v)
    (heL : (T.walk l).toSubgraph = G.subgraphOfAdj huv)
    (hsep : ∀ x, ¬(G.Adj x u ∧ G.Adj x v)) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail) (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support) :
    ∃ U : NormalTrailSystem G k, U.score = T.score + 1 ∧
      (U.walk l).toSubgraph = G.subgraphOfAdj huv := by
  classical
  have hpEdge : (Walk.cons huv Walk.nil).IsPath := by simp [huv.ne]
  have hil : i ≠ l := by
    intro hh
    have he' : (Walk.cons h p).toSubgraph = (Walk.cons huv Walk.nil).toSubgraph := by
      rw [←he,hh,heL,Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
    have hpath := trail_isPath_of_subgraph_eq _ _ hp hpEdge he'
    exact (Walk.cons_isPath_iff h p).mp hpath |>.2 hv
  have hend := endpoints_of_path_subgraph T l (Walk.cons huv Walk.nil) hpEdge (by simp)
    (by simpa using heL)
  have hrootout : T.start i ∉ (T.walk l).support := by
    intro hx
    rw [← Walk.mem_verts_toSubgraph,heL] at hx
    have hxuv : T.start i=u ∨ T.start i=v := by simpa using hx
    apply hil
    rcases hxuv with hh | hh
    · exact endpoint_index_eq T (Or.inl rfl) (hh.symm ▸ hend.1)
    · exact endpoint_index_eq T (Or.inl rfl) (hh.symm ▸ hend.2)
  let C := Walk.cons h (p.takeUntil (T.start i) hv)
  let q := p.dropUntil (T.start i) hv
  have hform : C.append q = Walk.cons h p := by simp [C,q]
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix T i C q (by rw [hform]; exact he)
    (by rw [hform]; exact hp) (by simp [C])
  have hl : l ∉ R.active := by
    intro hl
    have hh := root_mem_of_active R l hl
    rw [hR] at hh
    exact hrootout hh
  obtain ⟨U,hU,hUL⟩ := repair_avoiding_single_edge R l hl huv (by rw [hR]; exact heL) (hsep _)
  exact ⟨U,by simpa only [hR] using hU,hUL⟩

lemma protected_no_repeated_start {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k) {u v : V} (huv : G.Adj u v)
    (heL : (T.walk l).toSubgraph = G.subgraphOfAdj huv)
    (hsep : ∀ x, ¬(G.Adj x u ∧ G.Adj x v))
    (hmax : ∀ U : NormalTrailSystem G k,
      (U.walk l).toSubgraph = G.subgraphOfAdj huv → U.score ≤ T.score)
    (i : Fin k) {y : V} (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail) (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph) :
    T.start i ∉ p.support := by
  intro hv
  obtain ⟨U,hU,hUL⟩ := improve_repeated_start_protect_edge T l huv heL hsep i h p hp he hv
  have hh := hmax U hUL
  omega

lemma shorten_oriented_no_return {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬G.Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      (U.walk i).toSubgraph = p.toSubgraph ∧
      ∃ l₀ : Fin k,
        (∃ x ∈ (T.walk l₀).support, ∃ h : G.Adj (T.start i) x,
          (U.walk l₀).toSubgraph = G.subgraphOfAdj h ⊔ (T.walk l₀).toSubgraph) ∧
        ∀ l, l ≠ i → T.start i ∉ (T.walk l).support → l ≠ l₀ →
          (U.walk l).toSubgraph = (T.walk l).toSubgraph := by
  classical
  obtain ⟨S,hSi,hSj,hSl,hSa,hSb,hs⟩ := slide_oriented T i j hij h p hp he
  have hai : S.start i = T.start j := by simp [hSa]
  have haj : S.start j = T.start i := by simp [hSa]
  have hbi : S.finish i = T.finish i := congrFun hSb i
  have hbj : S.finish j = T.finish j := congrFun hSb j
  have hpcard := cons_ncard_of_notMem h p hnot
  by_cases hv : T.start i ∈ (T.walk j).support
  · have hqcard := cons_ncard_of_mem h (T.walk j) hv
    have hscore : S.score + 1 = T.score := by omega
    let C₀ := Walk.cons h ((T.walk j).takeUntil (T.start i) hv)
    let q₀ := (T.walk j).dropUntil (T.start i) hv
    have hform : C₀.append q₀ = Walk.cons h (T.walk j) := by simp [C₀,q₀]
    have hslide : (Walk.cons h (T.walk j)).IsTrail :=
      (trail_slide_data h p (T.walk j) hp (T.isTrail j) (he ▸ T.disjoint hij)).2.1
    have hCq : (C₀.append q₀).IsTrail := hform.symm ▸ hslide
    have hC : C₀.IsTrail := hCq.of_append_left
    have hCn : ¬C₀.Nil := by simp [C₀]
    have hCdis : Disjoint C₀.reverse.toSubgraph.edgeSet q₀.toSubgraph.edgeSet := by
      rw [Walk.toSubgraph_reverse]
      exact append_trail_disjoint hCq
    have hrev : (C₀.reverse.append q₀).IsTrail :=
      trail_append_of_disjoint hC.reverse hCq.of_append_right hCdis
    let C := C₀.reverse.copy haj.symm haj.symm
    let q := q₀.copy haj.symm hbj.symm
    have hCeq : C.toSubgraph = C₀.toSubgraph := by
      rw [NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_reverse]
    have hqeq : q.toSubgraph = q₀.toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
    have hrep : (S.walk j).toSubgraph = (C.append q).toSubgraph := by
      rw [hSj,←hform,Walk.toSubgraph_append,Walk.toSubgraph_append,hCeq,hqeq]
    have hrepTrail : (C.append q).IsTrail := by
      simpa only [C,q,Walk.append_copy_copy,Walk.isTrail_copy] using hrev
    obtain ⟨B,R,hR,hroot⟩ := of_closed_prefix S j C q hrep hrepTrail
      (by simpa only [C,Walk.nil_copy,Walk.nil_reverse] using hCn)
    have hlout : i ∉ R.active := by
      intro hi
      have hh := root_mem_of_active R i hi
      rw [hR,← Walk.mem_verts_toSubgraph,hSi,Walk.mem_verts_toSubgraph,haj] at hh
      exact hnot hh
    obtain ⟨R',hscore',hesc,havoid,htrack⟩ := DoubleEscape.expose_escape_avoiding R (T.start j)
    obtain ⟨U,hU,l₀,hl₀,hown,hUrec,hUl⟩ := Erdos583Work.SingletonRotation.finish_exposed_receiver R' hesc
    have hiout : i ∉ R'.active := htrack.1.symm ▸ hlout
    have hi₀ : i ≠ l₀ := by
      intro hh
      subst l₀
      obtain ⟨hisa,hisb,_⟩ := htrack.2 i hlout
      rcases hown with hh | hh
      · apply havoid
        simpa only [hisa,hR,hai] using hh
      · have hadj := (R'.tail ⟨S.start j,R'.root_mem⟩).adj_snd R'.root_nonempty
        apply hnadj
        rw [hh,hisb,hR,hbi] at hadj
        simpa only [haj] using hadj
    have hui : (U.walk i).toSubgraph = p.toSubgraph := by
      rw [hUl i hiout hi₀,(htrack.2 i hlout).2.2,hR,hSi]
    refine ⟨U,?_,hui,l₀,?_,?_⟩
    · rw [hR] at hscore'
      omega
    · have hl₀R : l₀ ∉ R.active := htrack.1 ▸ hl₀
      have hjR : j ∈ R.active := by
        apply (R.start_mem j).mp
        rw [hR]
        exact R.root_mem
      have hl₀j : l₀ ≠ j := fun hh ↦ hl₀R (hh ▸ hjR)
      let x := (R'.tail ⟨S.start j,R'.root_mem⟩).snd
      have hx : x ∈ (R'.system.walk l₀).support := by
        rcases hown with hh | hh
        · change (R'.tail ⟨S.start j,R'.root_mem⟩).snd ∈ _
          rw [hh]
          exact (R'.system.walk l₀).start_mem_support
        · change (R'.tail ⟨S.start j,R'.root_mem⟩).snd ∈ _
          rw [hh]
          exact (R'.system.walk l₀).end_mem_support
      have hxT : x ∈ (T.walk l₀).support := by
        rw [← Walk.mem_verts_toSubgraph,(htrack.2 l₀ hl₀R).2.2,hR,
          hSl l₀ hi₀.symm hl₀j,Walk.mem_verts_toSubgraph] at hx
        exact hx
      have hh := (R'.tail ⟨S.start j,R'.root_mem⟩).adj_snd R'.root_nonempty
      have hxadj : G.Adj (T.start i) x := by simpa only [haj] using hh
      refine ⟨x,hxT,hxadj,?_⟩
      have heE : G.subgraphOfAdj hh = G.subgraphOfAdj hxadj := by
        ext <;> simp [haj,x]
      rw [hUrec,heE,(htrack.2 l₀ hl₀R).2.2,hR,hSl l₀ hi₀.symm hl₀j]
    · intro l hli hav hl₀'
      have hlj : l ≠ j := by rintro rfl; exact hav hv
      have hlR : l ∉ R.active := by
        intro hl
        have hroot := root_mem_of_active R l hl
        rw [hR,← Walk.mem_verts_toSubgraph,hSl l hli hlj,Walk.mem_verts_toSubgraph,haj] at hroot
        exact hav hroot
      have hlR' : l ∉ R'.active := htrack.1.symm ▸ hlR
      rw [hUl l hlR' hl₀',(htrack.2 l hlR).2.2,hR,hSl l hli hlj]
  · have hqcard := cons_ncard_of_notMem h (T.walk j) hv
    refine ⟨S,by omega,hSi,j,⟨T.start j,(T.walk j).start_mem_support,h,?_⟩,
      fun l hli _ hlj ↦ hSl l hli hlj⟩
    rw [hSj,Walk.toSubgraph]



/-- A chordless two-edge member can be shortened to its far edge at exactly the
same incidence score. Unlike the earlier shortening theorem, no global score
maximality is required. -/
lemma strip_chordless_two_edge {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (l : Fin k) {a u v : V}
    (hau : G.Adj a u) (huv : G.Adj u v) (hav : a ≠ v) (hnadj : ¬G.Adj a v)
    (he : (T.walk l).toSubgraph = G.subgraphOfAdj hau ⊔ G.subgraphOfAdj huv) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      (S.walk l).toSubgraph = G.subgraphOfAdj huv := by
  classical
  let p := Walk.cons hau (Walk.cons huv Walk.nil)
  have hp : p.IsPath := by simp [p,hau.ne,huv.ne,hav]
  have he' : (T.walk l).toSubgraph = p.toSubgraph := by simpa [p,Walk.toSubgraph] using he
  have hends := endpoints_of_path_subgraph T l p hp (by simp [p]) he'
  obtain ⟨U,hs,ha,_,hUe⟩ := orient_receiver T l a hends.1
  have hendsU := endpoints_of_path_subgraph U l p hp (by simp [p]) ((hUe l).trans he')
  have hv : U.finish l = v := by
    rcases hendsU.2 with hh | hh
    · rw [ha] at hh
      exact (hav hh.symm).elim
    · exact hh.symm
  let j := NormalTrailSystem.owner U u
  have hjown := NormalTrailSystem.owner_spec U u
  have hlj : l ≠ j := by
    intro hh
    change u=U.start j ∨ u=U.finish j at hjown
    rw [←hh,ha,hv] at hjown
    exact hjown.elim hau.ne.symm huv.ne
  obtain ⟨R,hR,hRu,hRl,hRe⟩ := orient_receiver U j u hjown
  obtain ⟨hRa,hRv⟩ := hRl l hlj
  have haR : R.start l=a := hRa.trans ha
  have hvR : R.finish l=v := hRv.trans hv
  let q := (Walk.cons huv Walk.nil).copy hRu.symm hvR.symm
  have h : G.Adj (R.start l) (R.start j) := by rw [haR,hRu]; exact hau
  have hform : Walk.cons h q = p.copy haR.symm hvR.symm :=
    cons_copy_vertices hau (Walk.cons huv Walk.nil) haR.symm hRu.symm hvR.symm h
  have heR : (R.walk l).toSubgraph = (Walk.cons h q).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hRe,hUe,he']
  have hqtrail : (Walk.cons h q).IsTrail := by rw [hform]; simpa only [Walk.isTrail_copy] using hp.isTrail
  have hnot : R.start l ∉ q.support := by simp [q,haR,hau.ne,hav]
  obtain ⟨S,hS,hSl,_⟩ := shorten_oriented_no_return R l j hlj h q hqtrail heR hnot
    (by rw [haR,hvR]; exact hnadj)
  refine ⟨S,hS.trans (hR.trans hs),?_⟩
  rw [hSl,NormalTrailSystem.walk_copy_subgraph]
  simp


/-- A closed segment based at the marked endpoint cannot occur immediately
after the first edge of another member at a protected score maximum. The proof
uses a temporary chordless two-edge buffer, an internal protected repair, and
then strips the buffer without losing score. -/
lemma protected_no_closed_after_first_marked {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k)
    (huv : G.Adj (T.start l) (T.finish l))
    (heL : (T.walk l).toSubgraph = G.subgraphOfAdj huv)
    (hsep : ∀ x, ¬(G.Adj x (T.start l) ∧ G.Adj x (T.finish l)))
    (hmax : ∀ U : NormalTrailSystem G k,
      (U.walk l).toSubgraph = G.subgraphOfAdj huv → U.score ≤ T.score)
    (i : Fin k) (h : G.Adj (T.start i) (T.start l))
    (C : G.Walk (T.start l) (T.start l)) (q : G.Walk (T.start l) (T.finish i))
    (hp : (Walk.cons h (C.append q)).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h (C.append q)).toSubgraph) : C.Nil := by
  classical
  by_contra hCn
  have hil : i ≠ l := fun hh ↦ h.ne (congrArg T.start hh)
  have hav : T.start i ≠ T.finish l := by
    intro hh
    exact hil (endpoint_index_eq T (Or.inl rfl) (Or.inr hh))
  have hnadj : ¬G.Adj (T.start i) (T.finish l) := fun hh ↦ hsep _ ⟨h,hh⟩
  have hnot := protected_no_repeated_start T l huv heL hsep hmax i h (C.append q) hp he
  have hnotL : T.start i ∉ (T.walk l).support := by
    rw [← Walk.mem_verts_toSubgraph,heL]
    simpa only [subgraphOfAdj_verts,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using ⟨h.ne,hav⟩
  obtain ⟨S,hSi,hSl,_,hSa,hSb,hs⟩ := slide_oriented T i l hil h (C.append q) hp he
  have hscore : S.score = T.score := by
    rw [cons_ncard_of_notMem h (C.append q) hnot,
      cons_ncard_of_notMem h (T.walk l) hnotL] at hs
    omega
  have hai : S.start i = T.start l := by simp [hSa]
  have hbi : S.finish i = T.finish i := congrFun hSb i
  let C' := C.copy hai.symm hai.symm
  let q' := q.copy hai.symm hbi.symm
  have hform : C'.append q' = (C.append q).copy hai.symm hbi.symm := by
    simp only [C',q',Walk.append_copy_copy]
  have hrep : (S.walk i).toSubgraph = (C'.append q').toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hSi]
  have hrepTrail : (C'.append q').IsTrail := by
    rw [hform]
    simpa only [Walk.isTrail_copy] using (Walk.isTrail_cons h (C.append q)).mp hp |>.1
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix S i C' q' hrep hrepTrail
    (by simpa only [C',Walk.nil_copy] using hCn)
  have hcenter : (S.walk l).toSubgraph = G.subgraphOfAdj h ⊔ G.subgraphOfAdj huv := by
    rw [hSl,Walk.toSubgraph,heL]
  have hlR : l ∈ R.active := by
    by_contra hl
    have hout := R.outside l hl
    rw [hR,← Walk.mem_verts_toSubgraph,hcenter,hai] at hout
    apply hout
    simp
  have h' : G.Adj (T.start i) (S.start i) := by rw [hai]; exact h
  have huv' : G.Adj (S.start i) (T.finish l) := by rw [hai]; exact huv
  have hEdge : G.subgraphOfAdj h' = G.subgraphOfAdj h := by ext <;> simp [hai]
  have hEdge' : G.subgraphOfAdj huv' = G.subgraphOfAdj huv := by ext <;> simp [hai]
  obtain ⟨U,hU,hUl⟩ := repair_chordless_three_path R l hlR h' huv' hnadj
    (by rw [hR,hcenter,hEdge,hEdge'])
  obtain ⟨W,hW,hWl⟩ := strip_chordless_two_edge U l h' huv' hav hnadj
    (by rw [hUl,hR,hcenter,hEdge,hEdge'])
  have hcap := hmax W (hWl.trans hEdge')
  rw [hR] at hU
  omega

end Erdos583ProtectedEdgeDevelopment
