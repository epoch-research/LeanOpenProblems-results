import Submission.Work

/-! Controlled singleton-edge exchanges. This does not assert global augmentation. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.PendantCompletion
open Erdos583Work.LeafPermutation
namespace Erdos583SingletonRotationDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma escape_slide_receiver {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧
      (S.walk (NormalTrailSystem.owner T y)).toSubgraph =
        G.subgraphOfAdj h ⊔ (T.walk (NormalTrailSystem.owner T y)).toSubgraph ∧
      ∀ l, l ≠ i → l ≠ NormalTrailSystem.owner T y →
        (S.walk l).toSubgraph = (T.walk l).toSubgraph := by
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
  obtain ⟨S,_,hSj,hSl,_,_,hs⟩ := slide_oriented U i j hij h' pU hpU heU
  rw [cons_ncard_of_mem h' pU hvU,cons_ncard_of_notMem h' (U.walk j) havoidU] at hs
  have heE : G.subgraphOfAdj h' = G.subgraphOfAdj h := by
    ext <;> simp [hi,hUj]
  refine ⟨S,by omega,?_,fun l hli hlj ↦ (hSl l hli hlj).trans (hUe l)⟩
  change (S.walk j).toSubgraph = _
  rw [hSj,Walk.toSubgraph,heE,hUe]


/-- Finishing a rooted exchange changes only one outside member: the owner of
the escape vertex. All other outside subgraphs are retained at their indices. -/
lemma finish_exposed_receiver {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ j : Fin k, j ∉ R.active ∧
        ((R.tail ⟨v,R.root_mem⟩).snd = R.system.start j ∨
          (R.tail ⟨v,R.root_mem⟩).snd = R.system.finish j) ∧
        (T.walk j).toSubgraph =
          G.subgraphOfAdj ((R.tail ⟨v,R.root_mem⟩).adj_snd R.root_nonempty) ⊔
            (R.system.walk j).toSubgraph ∧
        ∀ l, l ∉ R.active → l ≠ j → (T.walk l).toSubgraph = (R.system.walk l).toSubgraph := by
  classical
  obtain ⟨S,hs,ht,htrack,i,hi⟩ := orient_root_start_tracked R
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
  obtain ⟨T,hT,hTj,hTl⟩ := escape_slide_receiver S.system i h p
    (by rw [hform]; exact hp) (by rw [hform]; exact he) hv hout
  have hjR : j ∉ R.active := htrack.1 ▸ hj
  refine ⟨T,by omega,j,hjR,?_,?_,?_⟩
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

/-- If the discarded starting vertex is nonadjacent to the far endpoint,
shortening retains the entire suffix at its index. Among old members avoiding
the discarded vertex, at most one other indexed subgraph changes. -/
lemma shorten_oriented_one_exception {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hnadj : ¬G.Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      (U.walk i).toSubgraph = p.toSubgraph ∧
      ∃ l₀ : Fin k,
        (∃ x ∈ (T.walk l₀).support, ∃ h : G.Adj (T.start i) x,
          (U.walk l₀).toSubgraph = G.subgraphOfAdj h ⊔ (T.walk l₀).toSubgraph) ∧
        ∀ l, l ≠ i → T.start i ∉ (T.walk l).support → l ≠ l₀ →
          (U.walk l).toSubgraph = (T.walk l).toSubgraph := by
  classical
  have hm : IsMember T (Walk.cons h p) := ⟨i,Or.inl ⟨rfl,rfl⟩,he⟩
  have hnot := member_no_repeated_start hmax h p hp hm
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
    obtain ⟨U,hU,l₀,hl₀,hown,hUrec,hUl⟩ := finish_exposed_receiver R' hesc
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

/-- The singleton pendant member representing an inactive core vertex. -/
def leafPart {V : Type*} (G : SimpleGraph V) (z : V) : (allLeafCompletion G).Subgraph :=
  (leafWalk (Walk.nil : G.Walk z z)).toSubgraph

lemma leafPart_edges {V : Type*} (G : SimpleGraph V) (z : V) :
    (leafPart G z).edgeSet = {s(Sum.inl z,Sum.inr ⟨z,Set.mem_univ _⟩)} := by
  unfold leafPart
  ext e
  rw [leafWalk_edges]
  simp

lemma leafPart_verts {V : Type*} (G : SimpleGraph V) (z : V) :
    (leafPart G z).verts = {Sum.inl z,Sum.inr ⟨z,Set.mem_univ _⟩} := by
  ext x
  simp [leafPart,Walk.verts_toSubgraph,leafWalk,inclusion]

lemma leafPart_injective {V : Type*} (G : SimpleGraph V) : Function.Injective (leafPart G) := by
  intro z w he
  have hh : Sum.inl z ∈ (leafPart G w).verts := by
    rw [←he,leafPart_verts]
    simp
  simpa only [leafPart_verts,Set.mem_insert_iff,Set.mem_singleton_iff,
    Sum.inl.injEq,Sum.inl_ne_inr,or_false] using hh

lemma leafPart_owners {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (l : Fin k) (z : V)
    (he : (T.walk l).toSubgraph = leafPart G z) :
    NormalTrailSystem.owner T (Sum.inl z) = l ∧
      NormalTrailSystem.owner T (Sum.inr ⟨z,Set.mem_univ _⟩) = l := by
  let p := leafWalk (Walk.nil : G.Walk z z)
  have hp : p.IsPath := leafWalk_isPath _ Walk.IsPath.nil
  have hn : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have hown (x) (hx : x = Sum.inl z ∨ x = Sum.inr ⟨z,Set.mem_univ _⟩) :
      NormalTrailSystem.owner T x = l := by
    apply (NormalTrailSystem.endpoint_iff_owner T x l).mp
    apply ((trail_neighbor_ncard_odd_iff (T.isTrail l) x).mp ?_).2
    have hh := (EndpointSelection.path_neighbor_one_iff hp hn x).mpr hx
    rw [he]
    change Odd (p.toSubgraph.neighborSet x).ncard
    rw [hh]
    decide
  exact ⟨hown _ (Or.inl rfl),hown _ (Or.inr rfl)⟩

/-- A member containing a core edge cannot be a singleton pendant member. -/
lemma core_edge_not_leafPart {V : Type*} {G : SimpleGraph V}
    {K : (allLeafCompletion G).Subgraph} {a b : V}
    (he : s(Sum.inl a,Sum.inl b) ∈ K.edgeSet) (z : V) : K ≠ leafPart G z := by
  intro hh
  rw [hh,leafPart_edges] at he
  have hx := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he)
  rcases hx with hx | hx
  · exact Sum.inl_ne_inr hx.2
  · exact Sum.inl_ne_inr hx.1

/-- Shortening a lifted singleton core edge purifies its destination. Every old
singleton pendant member except possibly one is retained at its original index.
All resulting members are paths; no internal-defect normalization is assumed. -/
lemma purify_short_core_member {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath) (i : Fin k) {b a : V} (hba : G.Adj b a)
    (hai : T.start i = Sum.inl b)
    (hbi : T.finish i = Sum.inr ⟨a,Set.mem_univ _⟩)
    (hei : (T.walk i).toSubgraph = (leafWalk (Walk.cons hba Walk.nil)).toSubgraph) :
    ∃ S : NormalTrailSystem (allLeafCompletion G) k,
      S.score = T.score ∧ (∀ l, (S.walk l).IsPath) ∧
      (S.walk i).toSubgraph = leafPart G a ∧
      ∃ l₀ : Fin k,
        (∀ z, (T.walk l₀).toSubgraph = leafPart G z →
          ∃ h : G.Adj b z,
            (S.walk l₀).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph) ∧
        ∀ z l, (T.walk l).toSubgraph = leafPart G z → l ≠ l₀ →
          (S.walk l).toSubgraph = leafPart G z := by
  classical
  have hmax : ∀ X : NormalTrailSystem (allLeafCompletion G) k, X.score ≤ T.score := by
    intro X
    rw [T.score_eq_edges_add_iff.mpr hpT]
    exact X.score_le_edges_add
  let j := NormalTrailSystem.owner T (Sum.inl a)
  have hown : Sum.inl a = T.start j ∨ Sum.inl a = T.finish j :=
    NormalTrailSystem.owner_spec T (Sum.inl a)
  have hij : i ≠ j := by
    intro hh
    rw [←hh,hai,hbi] at hown
    rcases hown with hh | hh
    · exact hba.ne (Sum.inl.inj hh).symm
    · exact Sum.inl_ne_inr hh
  obtain ⟨U,hUs,hUj,hUl,hUe⟩ := orient_receiver T j (Sum.inl a) hown
  obtain ⟨hUia,hUib⟩ := hUl i hij
  have ha : U.start i = Sum.inl b := hUia.trans hai
  have hb : U.finish i = Sum.inr ⟨a,Set.mem_univ _⟩ := hUib.trans hbi
  let p₀ := leafWalk (Walk.nil : G.Walk a a)
  let p := p₀.copy hUj.symm hb.symm
  have h₀ : (allLeafCompletion G).Adj (Sum.inl b) (Sum.inl a) := hba
  have h : (allLeafCompletion G).Adj (U.start i) (U.start j) := by rw [ha,hUj]; exact h₀
  have hform : Walk.cons h p = (Walk.cons h₀ p₀).copy ha.symm hb.symm :=
    cons_copy_vertices h₀ p₀ ha.symm hUj.symm hb.symm h
  have hshort : Walk.cons h₀ p₀ = leafWalk (Walk.cons hba Walk.nil) := rfl
  have hpath : (Walk.cons h p).IsPath := by
    rw [hform,hshort]
    simpa only [Walk.isPath_copy] using leafWalk_isPath (Walk.cons hba Walk.nil) (by simp [hba.ne])
  have hrep : (U.walk i).toSubgraph = (Walk.cons h p).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hshort,hUe,hei]
  have hnadj : ¬(allLeafCompletion G).Adj (U.start i) (U.finish i) := by
    rw [ha,hb]
    exact hba.ne
  have hUmax : ∀ X : NormalTrailSystem (allLeafCompletion G) k, X.score ≤ U.score := by
    intro X; rw [hUs]; exact hmax X
  obtain ⟨S,hS,hSi,l₀,hneighbor,hSl⟩ := shorten_oriented_one_exception U hUmax i j hij h p
    hpath.isTrail hrep hnadj
  have hSp : ∀ l, (S.walk l).IsPath := by
    apply S.score_eq_edges_add_iff.mp
    rw [hS,hUs,T.score_eq_edges_add_iff.mpr hpT]
  refine ⟨S,hS.trans hUs,hSp,?_,l₀,?_,?_⟩
  · rw [hSi,NormalTrailSystem.walk_copy_subgraph]
    rfl
  · intro z hz
    obtain ⟨x,hx,hadj,_hrec⟩ := hneighbor
    rw [ha] at hadj
    rw [← Walk.mem_verts_toSubgraph,hUe,hz,leafPart_verts] at hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨hadj,?_⟩
      have hEdge : (allLeafCompletion G).subgraphOfAdj (ha ▸ hadj) =
          (allLeafCompletion G).subgraphOfAdj (show (allLeafCompletion G).Adj (Sum.inl b) (Sum.inl z) from hadj) := by
        ext <;> simp [ha]
      rw [_hrec,hEdge,hUe,hz]
      rfl
    · rw [Set.mem_singleton_iff.mp hx] at hadj
      have hbz : b = z := hadj
      subst z
      have howner := (leafPart_owners T l₀ b hz).1
      have howner' : NormalTrailSystem.owner T (Sum.inl b) = i :=
        (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inl hai.symm)
      have hli : l₀ = i := howner.symm.trans howner'
      rw [hli] at hz
      have hcore : s(Sum.inl b,Sum.inl a) ∈ (T.walk i).toSubgraph.edgeSet := by
        rw [hei,leafWalk_edges]
        exact Or.inl ⟨s(b,a),by simp,rfl⟩
      exact (core_edge_not_leafPart hcore b hz).elim
  · intro z l hl hl₀
    have hcore : s(Sum.inl b,Sum.inl a) ∈ (T.walk i).toSubgraph.edgeSet := by
      rw [hei,leafWalk_edges]
      exact Or.inl ⟨s(b,a),by simp,rfl⟩
    have hli : l ≠ i := by
      rintro rfl
      exact core_edge_not_leafPart hcore z hl
    have hzb : z ≠ b := by
      intro hz
      subst z
      have howner := (leafPart_owners T l b hl).1
      have howner' : NormalTrailSystem.owner T (Sum.inl b) = i :=
        (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inl hai.symm)
      exact hli (howner.symm.trans howner')
    have hav : U.start i ∉ (U.walk l).support := by
      rw [ha,← Walk.mem_verts_toSubgraph,hUe,hl,leafPart_verts]
      simpa using hzb.symm
    rw [hSl l hli hav hl₀,hUe,hl]

/-- Core vertices whose pendant edge is a singleton member. -/
noncomputable def purified {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) : Finset V := by
  classical
  exact Finset.univ.filter (fun z ↦ ∃ l, (T.walk l).toSubgraph = leafPart G z)

@[simp] lemma mem_purified {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (z : V) :
    z ∈ purified T ↔ ∃ l, (T.walk l).toSubgraph = leafPart G z := by
  classical
  simp [purified]

lemma destination_not_purified {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (i : Fin k) {b a : V}
    (hba : G.Adj b a) (hbi : T.finish i = Sum.inr ⟨a,Set.mem_univ _⟩)
    (hei : (T.walk i).toSubgraph = (leafWalk (Walk.cons hba Walk.nil)).toSubgraph) :
    a ∉ purified T := by
  intro ha
  obtain ⟨l,hl⟩ := (mem_purified T a).mp ha
  have howner := (leafPart_owners T l a hl).2
  have howner' : NormalTrailSystem.owner T (Sum.inr ⟨a,Set.mem_univ _⟩) = i :=
    (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inr hbi.symm)
  have hli : l = i := howner.symm.trans howner'
  rw [hli] at hl
  have hcore : s(Sum.inl b,Sum.inl a) ∈ (T.walk i).toSubgraph.edgeSet := by
    rw [hei,leafWalk_edges]
    exact Or.inl ⟨s(b,a),by simp,rfl⟩
  exact core_edge_not_leafPart hcore a hl

/-- At a maximum of the number of purified vertices, shortening a singleton
core edge gives an exact exchange with one previously purified neighbor of its
source. This does not force an increase of the maximum. -/
lemma singleton_neighbor_exchange {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath)
    (hmax : ∀ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) → (purified U).card ≤ (purified T).card)
    (i : Fin k) {b a : V} (hba : G.Adj b a)
    (hai : T.start i = Sum.inl b)
    (hbi : T.finish i = Sum.inr ⟨a,Set.mem_univ _⟩)
    (hei : (T.walk i).toSubgraph = (leafWalk (Walk.cons hba Walk.nil)).toSubgraph) :
    ∃ S : NormalTrailSystem (allLeafCompletion G) k,
      S.score = T.score ∧ (∀ l, (S.walk l).IsPath) ∧
      (S.walk i).toSubgraph = leafPart G a ∧
      ∃ z ∈ purified T, ∃ h : G.Adj b z,
        purified S = insert a ((purified T).erase z) ∧
        ∃ l, (S.walk l).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph := by
  classical
  obtain ⟨S,hS,hSp,hSi,l₀,hneighbor,hpres⟩ := purify_short_core_member T hpT i hba hai hbi hei
  have ha : a ∈ purified S := (mem_purified S a).mpr ⟨i,hSi⟩
  have han : a ∉ purified T := destination_not_purified T i hba hbi hei
  have hcap := hmax S hSp
  have hnsub : ¬purified T ⊆ purified S := by
    intro hsub
    have hh := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨ha,hsub⟩)
    rw [Finset.card_insert_of_notMem han] at hh
    omega
  obtain ⟨z,hz,hzn⟩ := Finset.not_subset.mp hnsub
  obtain ⟨l,hl⟩ := (mem_purified T z).mp hz
  have hll : l = l₀ := by
    by_contra hh
    exact hzn ((mem_purified S z).mpr ⟨l,hpres z l hl hh⟩)
  have hzl : (T.walk l₀).toSubgraph = leafPart G z := hll ▸ hl
  have hsub : insert a ((purified T).erase z) ⊆ purified S := by
    apply Finset.insert_subset_iff.mpr
    refine ⟨ha,?_⟩
    intro w hw
    obtain ⟨hwz,hwT⟩ := Finset.mem_erase.mp hw
    obtain ⟨m,hm⟩ := (mem_purified T w).mp hwT
    have hm₀ : m ≠ l₀ := by
      intro hh
      rw [hh,hzl] at hm
      exact hwz ((leafPart_injective G hm).symm)
    exact (mem_purified S w).mpr ⟨m,hpres w m hm hm₀⟩
  have hc : (insert a ((purified T).erase z)).card = (purified T).card := by
    rw [Finset.card_insert_of_notMem (fun hh ↦ han (Finset.mem_of_mem_erase hh)),
      Finset.card_erase_of_mem hz]
    have hh := Finset.card_pos.mpr ⟨z,hz⟩
    omega
  have heq : purified S = insert a ((purified T).erase z) := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact hcap)
  obtain ⟨h,hrec⟩ := hneighbor z hzl
  exact ⟨S,hS,hSp,hSi,z,hz,h,heq,l₀,hrec⟩

/-- A singleton core edge whose source has no previously purified neighbor
admits a strict purification increase. -/
lemma singleton_augmentation_of_no_purified_neighbor {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath) (i : Fin k) {b a : V} (hba : G.Adj b a)
    (hai : T.start i = Sum.inl b)
    (hbi : T.finish i = Sum.inr ⟨a,Set.mem_univ _⟩)
    (hei : (T.walk i).toSubgraph = (leafWalk (Walk.cons hba Walk.nil)).toSubgraph)
    (havoid : ∀ z ∈ purified T, ¬G.Adj b z) :
    ∃ S : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (S.walk l).IsPath) ∧ purified T ⊂ purified S := by
  classical
  obtain ⟨S,_,hSp,hSi,l₀,hneighbor,hpres⟩ := purify_short_core_member T hpT i hba hai hbi hei
  have hsub : purified T ⊆ purified S := by
    intro z hz
    obtain ⟨l,hl⟩ := (mem_purified T z).mp hz
    have hll : l ≠ l₀ := by
      intro hh
      exact havoid z hz (hneighbor z (hh ▸ hl)).choose
    exact (mem_purified S z).mpr ⟨l,hpres z l hl hll⟩
  refine ⟨S,hSp,Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩⟩
  intro heq
  have ha : a ∈ purified S := (mem_purified S a).mpr ⟨i,hSi⟩
  rw [←heq] at ha
  exact destination_not_purified T i hba hbi hei ha

lemma endpoints_of_path_subgraph {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hn : ¬p.Nil) (he : (T.walk i).toSubgraph = p.toSubgraph) :
    (a = T.start i ∨ a = T.finish i) ∧ (b = T.start i ∨ b = T.finish i) := by
  have hends (x) (hx : x = a ∨ x = b) : x = T.start i ∨ x = T.finish i := by
    apply ((trail_neighbor_ncard_odd_iff (T.isTrail i) x).mp ?_).2
    rw [he,(EndpointSelection.path_neighbor_one_iff hp hn x).mpr hx]
    decide
  exact ⟨hends a (Or.inl rfl),hends b (Or.inr rfl)⟩

lemma orient_short_core_member {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (i : Fin k) {b a : V}
    (h : G.Adj b a)
    (he : (T.walk i).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph) :
    ∃ U : NormalTrailSystem (allLeafCompletion G) k,
      U.score = T.score ∧ (∀ l, (U.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      U.start i = Sum.inl b ∧ U.finish i = Sum.inr ⟨a,Set.mem_univ _⟩ := by
  have hp := leafWalk_isPath (Walk.cons h Walk.nil) (by simp [h.ne])
  have hn : ¬(leafWalk (Walk.cons h Walk.nil)).Nil := Walk.not_nil_of_ne (by simp)
  have hends := endpoints_of_path_subgraph T i _ hp hn he
  obtain ⟨U,hs,ha,_,hUe⟩ := orient_receiver T i (Sum.inl b) hends.1
  have hendsU := endpoints_of_path_subgraph U i _ hp hn ((hUe i).trans he)
  have hb : U.finish i = Sum.inr ⟨a,Set.mem_univ _⟩ := by
    rcases hendsU.2 with hh | hh
    · rw [ha] at hh
      exact (Sum.inr_ne_inl hh).elim
    · exact hh.symm
  exact ⟨U,hs,hUe,ha,hb⟩

lemma purified_eq_of_subgraphs {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T U : NormalTrailSystem (allLeafCompletion G) k)
    (he : ∀ l, (U.walk l).toSubgraph = (T.walk l).toSubgraph) :
    purified U = purified T := by
  ext z
  simp only [mem_purified,he]

/-- A genuine repeatable singleton rotation. At a global purification maximum,
`b -> a` can be replaced by `b -> z`, where z was purified, a becomes purified,
and every other purification status is unchanged. The new short member is
oriented in the same direction from the fixed root b. -/
lemma rooted_singleton_rotation {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath)
    (hmax : ∀ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) → (purified U).card ≤ (purified T).card)
    (i : Fin k) {b a : V} (hba : G.Adj b a)
    (hai : T.start i = Sum.inl b)
    (hbi : T.finish i = Sum.inr ⟨a,Set.mem_univ _⟩)
    (hei : (T.walk i).toSubgraph = (leafWalk (Walk.cons hba Walk.nil)).toSubgraph) :
    ∃ S : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (S.walk l).IsPath) ∧
      (∀ U : NormalTrailSystem (allLeafCompletion G) k,
        (∀ l, (U.walk l).IsPath) → (purified U).card ≤ (purified S).card) ∧
      ∃ z ∈ purified T, ∃ h : G.Adj b z,
        purified S = insert a ((purified T).erase z) ∧
        ∃ l, S.start l = Sum.inl b ∧ S.finish l = Sum.inr ⟨z,Set.mem_univ _⟩ ∧
          (S.walk l).toSubgraph = (leafWalk (Walk.cons h Walk.nil)).toSubgraph := by
  classical
  obtain ⟨R,hs,hRp,_,z,hz,h,heq,l,hl⟩ := singleton_neighbor_exchange T hpT hmax i hba hai hbi hei
  obtain ⟨S,hS,hSe,ha,hb⟩ := orient_short_core_member R l h hl
  have hSp : ∀ m, (S.walk m).IsPath := by
    apply S.score_eq_edges_add_iff.mp
    rw [hS,R.score_eq_edges_add_iff.mpr hRp]
  have hpur : purified S = insert a ((purified T).erase z) :=
    (purified_eq_of_subgraphs R S hSe).trans heq
  have han : a ∉ purified T := destination_not_purified T i hba hbi hei
  have hcard : (purified S).card = (purified T).card := by
    rw [hpur,Finset.card_insert_of_notMem (fun hh ↦ han (Finset.mem_of_mem_erase hh)),
      Finset.card_erase_of_mem hz]
    have hh := Finset.card_pos.mpr ⟨z,hz⟩
    omega
  refine ⟨S,hSp,?_,z,hz,h,hpur,l,ha,hb,(hSe l).trans hl⟩
  intro U hU
  rw [hcard]
  exact hmax U hU

end Erdos583SingletonRotationDevelopment
