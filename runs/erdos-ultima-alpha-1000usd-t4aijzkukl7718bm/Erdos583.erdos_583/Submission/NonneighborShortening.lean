import Submission.Work

/-! Prefix shortening with a whole nonneighbor member protected. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.SingletonRotation
namespace Erdos583NonneighborShorteningDevelopment
open scoped Classical
set_option maxHeartbeats 1200000
set_option Elab.async false

lemma member_of_path_subgraph {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hn : ¬p.Nil) (he : (T.walk i).toSubgraph = p.toSubgraph) :
    IsMember T p := by
  have hab : a ≠ b := fun hh ↦ by subst b; apply hn; rw [(Walk.isPath_iff_eq_nil p).mp hp]; exact Walk.Nil.nil
  obtain ⟨ha,hb⟩ := endpoints_of_path_subgraph T i p hp hn he
  refine ⟨i,?_,he⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha.symm,hb.symm⟩
  · exact Or.inr ⟨hb.symm,ha.symm⟩
  · exact (hab (ha.trans hb.symm)).elim

lemma member_orient_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : NormalTrailSystem G k} {a b : V} {p : G.Walk a b} (hm : IsMember T p) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      (∀ l, (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      ∃ i, S.start i = a ∧ S.finish i = b ∧ (S.walk i).toSubgraph = p.toSubgraph := by
  classical
  obtain ⟨i, hi, he⟩ := hm
  rcases hi with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨T,rfl,fun _ ↦ rfl,i,ha,hb,he⟩
  · obtain ⟨S, hs, hS⟩ := T.orient (fun j ↦ decide (j=i))
    refine ⟨S,hs,fun l ↦ (hS l).2.2,i,?_,?_,(hS i).2.2.trans he⟩
    · simpa using (hS i).1.trans (by simp [hb])
    · simpa using (hS i).2.1.trans (by simp [ha])

/-- Shortening can retain any whole member all of whose vertices avoid the
closed neighborhood of the discarded start. The shortened suffix may extend
at its other end. -/
lemma shorten_oriented_preserving {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail) (hpn : ¬p.Nil)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hlroot : T.start i ∉ (T.walk l).support)
    (hlnbr : ∀ x ∈ (T.walk l).support, ¬G.Adj (T.start i) x) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      (U.walk l).toSubgraph = (T.walk l).toSubgraph ∧
      ∃ t, ∃ q : G.Walk (T.finish i) t, (p.append q).IsTrail ∧ IsMember U (p.append q) := by
  classical
  have hm : IsMember T (Walk.cons h p) := ⟨i,Or.inl ⟨rfl,rfl⟩,he⟩
  have hnot := member_no_repeated_start hmax h p hp hm
  have hpp : p.IsPath := ((Walk.cons_isPath_iff h p).mp
    (max_score_member_isPath T hmax _ hp hm)).1
  have hli : l ≠ i := by rintro rfl; exact hlroot (T.walk l).start_mem_support
  have hlj : l ≠ j := by
    rintro rfl
    exact hlnbr _ (T.walk l).start_mem_support h
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
    obtain ⟨B,R,hR,_⟩ := of_closed_prefix S j C q hrep hrepTrail
      (by simpa only [C,Walk.nil_copy,Walk.nil_reverse] using hCn)
    have hiR : i ∉ R.active := by
      intro hi
      have hh := root_mem_of_active R i hi
      rw [hR,← Walk.mem_verts_toSubgraph,hSi,Walk.mem_verts_toSubgraph,haj] at hh
      exact hnot hh
    have hlR : l ∉ R.active := by
      intro hl
      have hh := root_mem_of_active R l hl
      rw [hR,← Walk.mem_verts_toSubgraph,hSl l hli hlj,Walk.mem_verts_toSubgraph,haj] at hh
      exact hlroot hh
    obtain ⟨R',hscore',hesc,havoid,htrack⟩ := DoubleEscape.expose_escape_avoiding R (T.start j)
    obtain ⟨U,hU,l₀,hl₀,hown,hUrec,hUl⟩ := finish_exposed_receiver R' hesc
    have hiR' : i ∉ R'.active := htrack.1.symm ▸ hiR
    have hlR' : l ∉ R'.active := htrack.1.symm ▸ hlR
    have hl₀R : l₀ ∉ R.active := htrack.1 ▸ hl₀
    have hlne : l ≠ l₀ := by
      intro hh
      subst l₀
      let x := (R'.tail ⟨S.start j,R'.root_mem⟩).snd
      have hx : x ∈ (R'.system.walk l).support := by
        rcases hown with hh | hh
        · change (R'.tail ⟨S.start j,R'.root_mem⟩).snd ∈ _
          rw [hh]; exact (R'.system.walk l).start_mem_support
        · change (R'.tail ⟨S.start j,R'.root_mem⟩).snd ∈ _
          rw [hh]; exact (R'.system.walk l).end_mem_support
      have hxT : x ∈ (T.walk l).support := by
        rw [← Walk.mem_verts_toSubgraph,(htrack.2 l hlR).2.2,hR,
          hSl l hli hlj,Walk.mem_verts_toSubgraph] at hx
        exact hx
      exact hlnbr x hxT (haj ▸ (R'.tail ⟨S.start j,R'.root_mem⟩).adj_snd R'.root_nonempty)
    refine ⟨U,?_,?_,?_⟩
    · rw [hR] at hscore'
      omega
    · rw [hUl l hlR' hlne,(htrack.2 l hlR).2.2,hR,hSl l hli hlj]
    · by_cases hi₀ : i = l₀
      · subst l₀
        obtain ⟨hisa,hisb,hise⟩ := htrack.2 i hiR
        have hx : (R'.tail ⟨S.start j,R'.root_mem⟩).snd = T.finish i := by
          rcases hown with hh | hh
          · exact (havoid (hh.trans (hisa.trans (by rw [hR]; exact hai)))).elim
          · exact hh.trans (hisb.trans (by rw [hR]; exact hbi))
        have hbroot : G.Adj (T.finish i) (T.start i) := by
          have hh := (R'.tail ⟨S.start j,R'.root_mem⟩).adj_snd R'.root_nonempty
          rw [hx] at hh
          change G.Adj (S.start j) (T.finish i) at hh
          rw [haj] at hh
          exact hh.symm
        let e : G.Walk (T.finish i) (T.start i) := Walk.cons hbroot Walk.nil
        have hep : (p.append e).IsPath := by
          simpa only [e,← Walk.concat_eq_append] using hpp.concat hnot hbroot
        have hen : ¬(p.append e).Nil := Walk.not_nil_of_ne (by exact h.ne.symm)
        have heU : (U.walk i).toSubgraph = (p.append e).toSubgraph := by
          rw [hUrec,hise,hR,hSi,Walk.toSubgraph_append]
          have hed : G.subgraphOfAdj ((R'.tail ⟨S.start j,R'.root_mem⟩).adj_snd R'.root_nonempty) = e.toSubgraph := by
            simp only [e,Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
            ext <;> simp [haj,hx,or_comm,and_comm]
          rw [hed,sup_comm]
        exact ⟨T.start i,e,hep.isTrail,member_of_path_subgraph U i _ hep hen heU⟩
      · have hui : (U.walk i).toSubgraph = p.toSubgraph := by
          rw [hUl i hiR' hi₀,(htrack.2 i hiR).2.2,hR,hSi]
        exact ⟨T.finish i,Walk.nil,by simpa using hpp.isTrail,
          by simpa using member_of_path_subgraph U i p hpp hpn hui⟩
  · have hqcard := cons_ncard_of_notMem h (T.walk j) hv
    refine ⟨S,by omega,hSl l hli hlj,T.finish i,Walk.nil,by simpa using hpp.isTrail,?_⟩
    exact ⟨i,Or.inl ⟨hai,hbi⟩,by simpa using hSi⟩


lemma shorten_member_preserving {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (l : Fin k) {a y b : V} (h : G.Adj a y) (p : G.Walk y b) (hpn : ¬p.Nil)
    (hp : (Walk.cons h p).IsTrail) (hm : IsMember T (Walk.cons h p))
    (hlroot : a ∉ (T.walk l).support)
    (hlnbr : ∀ x ∈ (T.walk l).support, ¬G.Adj a x) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧
      (U.walk l).toSubgraph = (T.walk l).toSubgraph ∧
      ∃ t, ∃ q : G.Walk b t, (p.append q).IsTrail ∧ IsMember U (p.append q) := by
  classical
  have hyb : y ≠ b := by
    intro hh
    subst y
    have hrev := isMember_reverse hm
    rw [Walk.reverse_cons] at hrev
    have hprev : (p.reverse.append (Walk.cons h.symm Walk.nil)).IsTrail := by
      simpa only [Walk.reverse_cons] using hp.reverse
    have hn := member_no_closed_prefix hmax p.reverse (Walk.cons h.symm Walk.nil) hprev hrev
    exact hpn (by simpa using hn)
  obtain ⟨S,hs,hSe,i,ha,hb,he⟩ := member_orient_tracked hm
  subst a b
  let j := NormalTrailSystem.owner S y
  have hjown : y = S.start j ∨ y = S.finish j := NormalTrailSystem.owner_spec S y
  have hij : i ≠ j := by
    intro hh
    rw [←hh] at hjown
    exact hjown.elim h.ne.symm hyb
  obtain ⟨U,hUs,hUj,hUi,hUe⟩ := orient_receiver S j y hjown
  obtain ⟨hi,hi'⟩ := hUi i hij
  have h' : G.Adj (U.start i) (U.start j) := by rw [hi,hUj]; exact h
  let pU := p.copy hUj.symm hi'.symm
  have hform : Walk.cons h' pU = (Walk.cons h p).copy hi.symm hi'.symm :=
    cons_copy_vertices h p hi.symm hUj.symm hi'.symm h'
  have hpU : (Walk.cons h' pU).IsTrail := by rw [hform]; simpa using hp
  have heU : (U.walk i).toSubgraph = (Walk.cons h' pU).toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hUe,he]
  have hUmax : ∀ R : NormalTrailSystem G k, R.score ≤ U.score := by
    intro R
    rw [hUs,hs]
    exact hmax R
  have hUlroot : U.start i ∉ (U.walk l).support := by
    rw [hi,← Walk.mem_verts_toSubgraph,hUe,hSe,Walk.mem_verts_toSubgraph]
    exact hlroot
  have hUlnbr : ∀ x ∈ (U.walk l).support, ¬G.Adj (U.start i) x := by
    intro x hx
    rw [← Walk.mem_verts_toSubgraph,hUe,hSe,Walk.mem_verts_toSubgraph] at hx
    rw [hi]
    exact hlnbr x hx
  obtain ⟨R,hR,hRl,t,q,hq,hmq⟩ := shorten_oriented_preserving U hUmax i j l hij h' pU hpU
    (by simpa [pU] using hpn) heU hUlroot hUlnbr
  obtain ⟨q',hq',hmq'⟩ := extension_of_copy p hUj.symm hi'.symm q hq hmq
  exact ⟨R,hR.trans (hUs.trans hs),(hRl.trans (hUe l)).trans (hSe l),t,q',hq',hmq'⟩

/-- A whole member remains fixed through shortening a prefix whose discarded
vertices all avoid its closed neighborhood. -/
lemma extend_suffix_preserving {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {a v : V} (A : G.Walk a v) :
    ∀ (T : NormalTrailSystem G k), (∀ S : NormalTrailSystem G k, S.score ≤ T.score) →
      ∀ (l : Fin k) {b : V} (B : G.Walk v b), ¬B.Nil →
        (A.append B).IsTrail → IsMember T (A.append B) →
        (∀ x ∈ A.support.dropLast, x ∉ (T.walk l).support ∧
          ∀ z ∈ (T.walk l).support, ¬G.Adj x z) →
        ∃ S : NormalTrailSystem G k, S.score = T.score ∧
          (S.walk l).toSubgraph = (T.walk l).toSubgraph ∧
          ∃ t, ∃ q : G.Walk b t, (B.append q).IsTrail ∧ IsMember S (B.append q) := by
  induction A with
  | nil =>
    intro T _ l b B _ hp hm _
    exact ⟨T,rfl,rfl,b,Walk.nil,by simpa using hp,by simpa using hm⟩
  | @cons a w v h A ih =>
    intro T hmax l b B hB hp hm hguard
    have hguard' : ∀ x ∈ a :: A.support.dropLast, x ∉ (T.walk l).support ∧
        ∀ z ∈ (T.walk l).support, ¬G.Adj x z := by
      simpa only [Walk.support_cons,List.dropLast_cons_of_ne_nil A.support_ne_nil] using hguard
    have ha := hguard' a (List.mem_cons_self ..)
    have hn : ¬(A.append B).Nil := by
      rw [Walk.nil_iff_length_eq, Walk.length_append]
      have hpos := Walk.not_nil_iff_lt_length.mp hB
      omega
    obtain ⟨U,hU,hUl,c,q,hq,hmq⟩ := shorten_member_preserving T hmax l h (A.append B) hn hp hm ha.1 ha.2
    have hUmax : ∀ R : NormalTrailSystem G k, R.score ≤ U.score := by
      intro R; rw [hU]; exact hmax R
    have hBq : ¬(B.append q).Nil := by
      rw [Walk.nil_iff_length_eq, Walk.length_append]
      have hpos := Walk.not_nil_iff_lt_length.mp hB
      omega
    have hguardU : ∀ x ∈ A.support.dropLast, x ∉ (U.walk l).support ∧
        ∀ z ∈ (U.walk l).support, ¬G.Adj x z := by
      intro x hx
      have hmem (z) : z ∈ (U.walk l).support ↔ z ∈ (T.walk l).support := by
        rw [← Walk.mem_verts_toSubgraph,hUl,Walk.mem_verts_toSubgraph]
      simpa only [hmem] using hguard' x (List.mem_cons_of_mem a hx)
    obtain ⟨S,hS,hSl,t,r,hr,hmr⟩ := ih U hUmax l (B.append q) hBq
      (by simpa only [Walk.append_assoc] using hq)
      (by simpa only [Walk.append_assoc] using hmq) hguardU
    exact ⟨S,hS.trans hU,hSl.trans hUl,t,q.append r,by simpa only [Walk.append_assoc] using hr,
      by simpa only [Walk.append_assoc] using hmr⟩

end Erdos583NonneighborShorteningDevelopment
