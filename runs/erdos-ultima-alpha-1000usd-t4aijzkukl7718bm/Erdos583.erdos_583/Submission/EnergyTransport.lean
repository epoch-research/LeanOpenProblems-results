import Submission.Work

/-! Exact vertex-set transport in a shortening exchange. -/
open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.VertexTracking Erdos583Work.SingletonRotation
namespace Erdos583EnergyTransportDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma escape_slide_receiver_vertices {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧
      (S.walk (NormalTrailSystem.owner T y)).toSubgraph =
        G.subgraphOfAdj h ⊔ (T.walk (NormalTrailSystem.owner T y)).toSubgraph ∧
      (∀ l, l ≠ i → l ≠ NormalTrailSystem.owner T y →
        (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      ∀ l, l ≠ NormalTrailSystem.owner T y →
        (S.walk l).toSubgraph.verts = (T.walk l).toSubgraph.verts := by
  classical
  let j := NormalTrailSystem.owner T y
  have hjown := NormalTrailSystem.owner_spec T y
  have hij : i ≠ j := by
    intro hh
    apply havoid
    change T.start i ∈ (T.walk j).support
    rw [← hh]
    exact (T.walk i).start_mem_support
  obtain ⟨U,hUs,hUj,hUl,hUe⟩ := orient_receiver T j y hjown
  obtain ⟨hi,hi'⟩ := hUl i hij
  have h' : G.Adj (U.start i) (U.start j) := by rw [hi,hUj]; exact h
  let pU := p.copy hUj.symm hi'.symm
  have hform : Walk.cons h' pU = (Walk.cons h p).copy hi.symm hi'.symm :=
    cons_copy_vertices h p hi.symm hUj.symm hi'.symm h'
  have hpU : (Walk.cons h' pU).IsTrail := by rw [hform]; simpa using hp
  have heU : (U.walk i).toSubgraph = (Walk.cons h' pU).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hUe,he]
  have hvU : U.start i ∈ pU.support := by simpa [pU,hi] using hv
  have havoidU : U.start i ∉ (U.walk j).support := by
    rw [hi,← Walk.mem_verts_toSubgraph,hUe,Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨S,hSi,hSj,hSl,_,_,hs⟩ := slide_oriented U i j hij h' pU hpU heU
  rw [cons_ncard_of_mem h' pU hvU,cons_ncard_of_notMem h' (U.walk j) havoidU] at hs
  have heE : G.subgraphOfAdj h' = G.subgraphOfAdj h := by
    ext <;> simp [hi,hUj]
  refine ⟨S,by omega,?_,(fun l hli hlj ↦ (hSl l hli hlj).trans (hUe l)),?_⟩
  · change (S.walk j).toSubgraph = _
    rw [hSj,Walk.toSubgraph,heE,hUe]
  · intro l hlj
    by_cases hli : l=i
    · subst l
      rw [hSi,←hUe i,heU,cons_verts]
      exact (Set.insert_eq_of_mem (pU.mem_verts_toSubgraph.mpr hvU)).symm
    · rw [hSl l hli hlj,hUe]


/-- Finishing a rooted exchange changes only one outside member: the owner of
the escape vertex. All other outside subgraphs are retained at their indices. -/
lemma finish_exposed_receiver_vertices {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ j : Fin k, j ∉ R.active ∧
        ((R.tail ⟨v,R.root_mem⟩).snd = R.system.start j ∨
          (R.tail ⟨v,R.root_mem⟩).snd = R.system.finish j) ∧
        (T.walk j).toSubgraph =
          G.subgraphOfAdj ((R.tail ⟨v,R.root_mem⟩).adj_snd R.root_nonempty) ⊔
            (R.system.walk j).toSubgraph ∧
        (∀ l, l ∉ R.active → l ≠ j → (T.walk l).toSubgraph = (R.system.walk l).toSubgraph) ∧
        ∀ l, l ≠ j → (T.walk l).toSubgraph.verts = (R.system.walk l).toSubgraph.verts := by
  classical
  obtain ⟨S,hs,ht,htrack,⟨i,hi⟩,hVs⟩ := orient_root_start_vertices R
  have hia : i ∈ S.active := (S.start_mem i).mp (hi.symm ▸ S.root_mem)
  let a : B := ⟨S.system.start i,(S.start_mem i).mpr hia⟩
  let b : B := ⟨S.system.finish i,(S.finish_mem i).mpr hia⟩
  have ha : a = ⟨v,S.root_mem⟩ := Subtype.ext hi
  have hab : a ≠ b := fun h ↦ S.system.endpoints_ne i (congrArg Subtype.val h)
  have hd : Disjoint (S.tail a).toSubgraph.edgeSet (S.tail b).reverse.toSubgraph.edgeSet := by
    simpa only [Walk.toSubgraph_reverse] using S.disjoint hab
  have hp := trail_append_of_disjoint (S.trail a) (S.trail b).reverse hd
  have he : (S.system.walk i).toSubgraph = ((S.tail a).append (S.tail b).reverse).toSubgraph := by
    rw [Walk.toSubgraph_append,Walk.toSubgraph_reverse]
    exact S.decomp i hia
  have hnil : ¬(S.tail a).Nil := ha.symm ▸ S.root_nonempty
  let C := S.tail a
  let h := C.adj_snd hnil
  let p := C.tail.append (S.tail b).reverse
  have hform : Walk.cons h p = C.append (S.tail b).reverse :=
    congrArg (fun z : G.Walk a.val v ↦ z.append (S.tail b).reverse) (C.cons_tail_eq hnil)
  have hv : S.system.start i ∈ p.support := by
    rw [hi]
    exact (Walk.mem_support_append_iff _ _).mpr (Or.inl C.tail.end_mem_support)
  have hfirst : C.snd = (R.tail ⟨v,R.root_mem⟩).snd := by
    change (S.tail a).snd = _
    rw [ha,ht]
  have hesc' : C.snd ∉ B := hfirst.symm ▸ hesc
  let j := NormalTrailSystem.owner S.system C.snd
  have hj : j ∉ S.active := fun hh ↦ hesc' ((S.mem_ends_iff_owner_active C.snd).mpr hh)
  have hout : S.system.start i ∉ (S.system.walk j).support := by
    rw [hi]
    exact S.outside j hj
  obtain ⟨T,hT,hTj,hTl,hTv⟩ := escape_slide_receiver_vertices S.system i h p
    (by rw [hform]; exact hp) (by rw [hform]; exact he) hv hout
  have hjR : j ∉ R.active := htrack.1 ▸ hj
  refine ⟨T,by omega,j,hjR,?_,?_,?_,?_⟩
  · obtain ⟨hja,hjb,_⟩ := htrack.2 j hjR
    have hown : C.snd = S.system.start j ∨ C.snd = S.system.finish j :=
      NormalTrailSystem.owner_spec S.system C.snd
    simpa only [hfirst,hja,hjb] using hown
  · have heE : G.subgraphOfAdj h =
        G.subgraphOfAdj ((R.tail ⟨v,R.root_mem⟩).adj_snd R.root_nonempty) := by
      ext <;> simp [ha,hfirst]
    change (T.walk j).toSubgraph = _
    rw [hTj,heE,(htrack.2 j hjR).2.2]
  · intro l hl hlj
    have hli : l ≠ i := fun hh ↦ hl (hh ▸ (htrack.1 ▸ hia))
    exact (hTl l hli hlj).trans ((htrack.2 l hl).2.2)
  · intro l hlj
    exact (hTv l hlj).trans (hVs l)


lemma shorten_oriented_vertex_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬G.Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      (U.walk i).toSubgraph = p.toSubgraph ∧
      ∃ l₀ : Fin k, i ≠ l₀ ∧ T.start i ∉ (T.walk l₀).support ∧
        (∃ x ∈ (T.walk l₀).support, ∃ h : G.Adj (T.start i) x,
          (U.walk l₀).toSubgraph = G.subgraphOfAdj h ⊔ (T.walk l₀).toSubgraph) ∧
        ∀ l, l ≠ i → l ≠ l₀ →
          (U.walk l).toSubgraph.verts = (T.walk l).toSubgraph.verts := by
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
    have hZfirst : (R.tail ⟨S.start j,R.root_mem⟩).snd ∉ ({T.start j} : Set V) := by
      rw [hroot]
      simp only [C,walk_snd_copy,Walk.snd_reverse,Set.mem_singleton_iff]
      have hh := closed_trail_snd_ne_penultimate C₀ hC hCn
      simpa only [C₀,Walk.snd_cons] using hh.symm
    have hZedge : ∀ z ∈ ({T.start j} : Set V),
        s(S.start j,z) ∈ (R.tail ⟨S.start j,R.root_mem⟩).toSubgraph.edgeSet := by
      rintro z rfl
      rw [hroot,hCeq,haj]
      simpa only [C₀,Walk.snd_cons] using C₀.toSubgraph_adj_snd hCn
    obtain ⟨R',hscore',hesc,havoid,htrack,hRvs⟩ := expose_escape_vertices R {T.start j} hZfirst hZedge
    obtain ⟨U,hU,l₀,hl₀,hown,hUrec,hUl,hUvs⟩ := finish_exposed_receiver_vertices R' hesc
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
    have hl₀R : l₀ ∉ R.active := htrack.1 ▸ hl₀
    have hjR : j ∈ R.active := by
      apply (R.start_mem j).mp
      rw [hR]
      exact R.root_mem
    have hl₀j : l₀ ≠ j := fun hh ↦ hl₀R (hh ▸ hjR)
    have hnot₀ : T.start i ∉ (T.walk l₀).support := by
      have hout := R.outside l₀ hl₀R
      rw [hR,← Walk.mem_verts_toSubgraph,hSl l₀ hi₀.symm hl₀j,Walk.mem_verts_toSubgraph,haj] at hout
      exact hout
    refine ⟨U,?_,hui,l₀,hi₀,hnot₀,?_,?_⟩
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
    · intro l hli hl₀'
      rw [hUvs l hl₀',hRvs l,hR]
      by_cases hlj : l=j
      · subst l
        rw [hSj,cons_verts]
        exact Set.insert_eq_of_mem ((T.walk j).mem_verts_toSubgraph.mpr hv)
      · rw [hSl l hli hlj]
  · have hqcard := cons_ncard_of_notMem h (T.walk j) hv
    refine ⟨S,by omega,hSi,j,hij,hv,⟨T.start j,(T.walk j).start_mem_support,h,?_⟩,
      fun l hli hlj ↦ congrArg Subgraph.verts (hSl l hli hlj)⟩
    rw [hSj,Walk.toSubgraph]




/-- A secondary optimization measuring concentration of member sizes. -/
noncomputable def vertexEnergy {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : ℕ := ∑ i, (T.walk i).toSubgraph.verts.ncard ^ 2

lemma vertexEnergy_transfer {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T U : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (hi : (U.walk i).toSubgraph.verts.ncard+1=(T.walk i).toSubgraph.verts.ncard)
    (hj : (U.walk j).toSubgraph.verts.ncard=(T.walk j).toSubgraph.verts.ncard+1)
    (hrest : ∀ l, l ≠ i → l ≠ j → (U.walk l).toSubgraph.verts=(T.walk l).toSubgraph.verts) :
    vertexEnergy U + 2*(T.walk i).toSubgraph.verts.ncard =
      vertexEnergy T + 2*(T.walk j).toSubgraph.verts.ncard + 2 := by
  classical
  have hr : ∑ l ∈ (Finset.univ.erase i).erase j, (U.walk l).toSubgraph.verts.ncard^2 =
      ∑ l ∈ (Finset.univ.erase i).erase j, (T.walk l).toSubgraph.verts.ncard^2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hrest l (Finset.mem_erase.mp (Finset.mem_of_mem_erase hl)).1 (Finset.mem_erase.mp hl).1]
  unfold vertexEnergy
  rw [NormalTrailSystem.sum_extract_two _ i j hij,NormalTrailSystem.sum_extract_two _ i j hij,hr]
  nlinarith

lemma shorten_oriented_energy {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬G.Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem G k, U.score=T.score ∧
      (U.walk i).toSubgraph=p.toSubgraph ∧
      ∃ r : Fin k, i ≠ r ∧ T.start i ∉ (T.walk r).support ∧
        (∃ x ∈ (T.walk r).support, ∃ h : G.Adj (T.start i) x,
          (U.walk r).toSubgraph=G.subgraphOfAdj h ⊔ (T.walk r).toSubgraph) ∧
        (∀ l, l ≠ i → l ≠ r → (U.walk l).toSubgraph.verts=(T.walk l).toSubgraph.verts) ∧
        vertexEnergy U + 2*(T.walk i).toSubgraph.verts.ncard =
          vertexEnergy T + 2*(T.walk r).toSubgraph.verts.ncard + 2 := by
  obtain ⟨U,hU,hUi,r,hir,hr,hrec,hrest⟩ := shorten_oriented_vertex_transfer T i j hij h p hp he hnot hnadj
  refine ⟨U,hU,hUi,r,hir,hr,hrec,hrest,vertexEnergy_transfer T U i r hir ?_ ?_ hrest⟩
  · rw [hUi,he,cons_ncard_of_notMem h p hnot]
  · obtain ⟨x,hx,ha,hUr⟩ := hrec
    have hv : (U.walk r).toSubgraph.verts = insert (T.start i) (T.walk r).toSubgraph.verts := by
      rw [hUr,Subgraph.verts_sup,subgraphOfAdj_verts]
      ext y
      simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
      have hx' := (T.walk r).mem_verts_toSubgraph.mpr hx
      aesop
    rw [hv,Set.ncard_insert_of_notMem (by simpa using hr)]

/-- At an energy maximum within a score level, the recipient of a shortening
must be strictly smaller than the donor. This is only a local optimality
condition; it supplies no global count of singleton members. -/
lemma energy_maximum_recipient_smaller {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k)
    (hmax : ∀ U : NormalTrailSystem G k, U.score=T.score → vertexEnergy U ≤ vertexEnergy T)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬G.Adj (T.start i) (T.finish i)) :
    ∃ r : Fin k, i ≠ r ∧ T.start i ∉ (T.walk r).support ∧
      (T.walk r).toSubgraph.verts.ncard < (T.walk i).toSubgraph.verts.ncard ∧
      ∃ x ∈ (T.walk r).support, G.Adj (T.start i) x := by
  obtain ⟨U,hU,_,r,hir,hr,hrec,_,henergy⟩ := shorten_oriented_energy T i j hij h p hp he hnot hnadj
  have hh := hmax U hU
  obtain ⟨x,hx,ha,_⟩ := hrec
  exact ⟨r,hir,hr,by omega,x,hx,ha⟩

lemma vertexEnergy_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : vertexEnergy T ≤ k * (Fintype.card V)^2 := by
  unfold vertexEnergy
  calc
    _ ≤ ∑ _i : Fin k, (Fintype.card V)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Nat.pow_le_pow_left
      simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (T.walk i).toSubgraph.verts
    _ = _ := by simp

lemma exists_score_energy_maximum {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) :
    ∃ U : NormalTrailSystem G k,
      (∀ R : NormalTrailSystem G k, R.score ≤ U.score) ∧
      (∀ R : NormalTrailSystem G k, R.score=U.score → vertexEnergy R ≤ vertexEnergy U) := by
  classical
  obtain ⟨S,hS⟩ := T.exists_max_score
  let P (m : ℕ) := ∃ U : NormalTrailSystem G k, U.score=S.score ∧ vertexEnergy U=m
  obtain ⟨U,hU,hEU⟩ := Nat.findGreatest_spec (P := P) (vertexEnergy_le S) ⟨S,rfl,rfl⟩
  refine ⟨U,(fun R ↦ by rw [hU]; exact hS R),?_⟩
  intro R hR
  rw [hEU]
  exact Nat.le_findGreatest (vertexEnergy_le R) ⟨R,hR.trans hU,rfl⟩

end Erdos583EnergyTransportDevelopment
