import Submission.Work

/-! Escape multiplicity controlled by the number of root-tail neighbors. -/

open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583Work.TrailNormalization Erdos583Work.DoubleEscape
namespace Erdos583ManyEscapeDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

lemma rotate_outgoing {V : Type*} {G : SimpleGraph V} {v z : V}
    (A : G.Walk v v) (h : G.Adj v z) (B : G.Walk z v)
    (ht : (A.append (Walk.cons h B)).IsTrail) :
    (Walk.cons h (B.append A)).IsTrail ∧
      (Walk.cons h (B.append A)).toSubgraph = (A.append (Walk.cons h B)).toSubgraph := by
  have ht' := trail_append_of_disjoint ht.of_append_right ht.of_append_left
    (append_trail_disjoint ht).symm
  exact ⟨ht',by simp [sup_comm,sup_left_comm]⟩

/-- A closed trail can start at any of its neighbors of the root, without
changing its underlying subgraph. The chosen edge need not be the first one. -/
lemma closed_trail_first_at_neighbor {V : Type*} {G : SimpleGraph V} {v z : V}
    (C : G.Walk v v) (ht : C.IsTrail) (hz : C.toSubgraph.Adj v z) :
    ∃ C' : G.Walk v v, C'.IsTrail ∧ C'.toSubgraph = C.toSubgraph ∧
      ¬C'.Nil ∧ C'.snd = z := by
  obtain ⟨a,b,h,A,B,hee,he⟩ := walk_split_at_edge C s(v,z) (C.mem_edges_toSubgraph.mp hz)
  rcases Sym2.eq_iff.mp hee with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · obtain ⟨ht',hsub⟩ := rotate_outgoing A h B (he ▸ ht)
    exact ⟨Walk.cons h (B.append A),ht',hsub.trans (congrArg Walk.toSubgraph he).symm,by simp,by simp⟩
  · have hrev : (B.reverse.append (Walk.cons h.symm A.reverse)).IsTrail := by
      have hh := (he ▸ ht).reverse
      simpa only [Walk.reverse_append,Walk.reverse_cons,← Walk.append_assoc,Walk.cons_nil_append] using hh
    obtain ⟨ht',hsub⟩ := rotate_outgoing B.reverse h.symm A.reverse hrev
    refine ⟨Walk.cons h.symm (A.reverse.append B.reverse),ht',?_,by simp,by simp⟩
    rw [hsub,he]
    simp only [Walk.toSubgraph_append,Walk.toSubgraph,Walk.toSubgraph_reverse]
    rw [subgraphOfAdj_symm h]
    ac_rfl

/-- Replace the closed root tail by any trail with the same subgraph; the
underlying normal system and every outside member remain unchanged. -/
lemma replace_root_tracked {V : Type*} {G : SimpleGraph V} {k : ℕ} {v : V} {B : Finset V}
    (R : RootedTailSystem G k v B) (C : G.Walk v v) (ht : C.IsTrail)
    (he : C.toSubgraph = (R.tail ⟨v,R.root_mem⟩).toSubgraph) (hn : ¬C.Nil) :
    ∃ S : RootedTailSystem G k v B,
      S.system = R.system ∧ S.tail ⟨v,S.root_mem⟩ = C ∧
      (∀ w : B, w.val ≠ v → S.tail w = R.tail w) ∧ AgreesOutside S R := by
  classical
  let r : B := ⟨v,R.root_mem⟩
  let q := Function.update R.tail r C
  have hqr : q r = C := by simp [q]
  have hq (w : B) (hw : w ≠ r) : q w = R.tail w := by simp [q,hw]
  have heq (w : B) : (q w).toSubgraph = (R.tail w).toSubgraph := by
    by_cases hw : w = r
    · subst w; rw [hqr]; exact he
    · rw [hq w hw]
  let S : RootedTailSystem G k v B :=
    { system := R.system, active := R.active, root_mem := R.root_mem,
      tail := q,
      trail := by
        intro w
        by_cases hw : w = r
        · subst w; rw [hqr]; exact ht
        · rw [hq w hw]; exact R.trail w
      disjoint := by
        intro w z hwz
        rw [heq w,heq z]
        exact R.disjoint hwz
      start_mem := R.start_mem, finish_mem := R.finish_mem,
      decomp := by intro i hi; rw [heq,heq]; exact R.decomp i hi
      outside := R.outside,
      root_nonempty := by change ¬(q r).Nil; rw [hqr]; exact hn }
  refine ⟨S,rfl,hqr,?_,rfl,fun _ _ ↦ ⟨rfl,rfl,rfl⟩⟩
  intro w hw
  exact hq w (fun he ↦ hw (congrArg Subtype.val he))

lemma neighbor_outside_successor_image {V : Type*} {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (f : V → V) (hf : ∀ w : B, w.val ≠ v → f w.val = (R.tail w).penultimate)
    (z : V) (hz : (R.tail ⟨v,R.root_mem⟩).toSubgraph.Adj v z) :
    z ∉ (B.erase v).image f := by
  classical
  intro hh
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hh
  obtain ⟨hwv,hwB⟩ := Finset.mem_erase.mp hw
  have he' : (R.tail ⟨w,hwB⟩).penultimate = z := (hf ⟨w,hwB⟩ hwv).symm.trans he
  have hedge : s(v,(R.tail ⟨w,hwB⟩).penultimate) ∈ (R.tail ⟨w,hwB⟩).toSubgraph.edgeSet :=
    ((R.tail ⟨w,hwB⟩).toSubgraph_adj_penultimate (Walk.not_nil_of_ne hwv)).symm
  rw [he'] at hedge
  exact Set.disjoint_left.mp (R.disjoint (fun h ↦ hwv (congrArg Subtype.val h).symm)) hz hedge

/-- There are at least as many distinct obtainable exits as the closed root
tail has neighbors at the root. Each exit has its own score-preserving realization. -/
lemma many_distinct_escapes {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) :
    ∃ E : Finset V, E.card = ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard ∧
      ∀ z ∈ E, z ∉ B ∧ ∃ S : RootedTailSystem G k v B,
        S.system.score = R.system.score ∧ (S.tail ⟨v,S.root_mem⟩).snd = z ∧ AgreesOutside S R := by
  classical
  let A := B.erase v
  let N := (R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v
  obtain ⟨f,hf,htf,_,_⟩ := successor_data R
  have hstart (z : N) : z.val ∉ A.image f := neighbor_outside_successor_image R f htf z.val z.property
  have hex (z : N) : ∃ n : ℕ, f^[n] z.val ∉ A ∧ ∀ m < n, f^[m] z.val ∈ A :=
    exists_first_exit_of_injective_successor A f hf z.val (hstart z)
  choose n hn hprev using hex
  let exit (z : N) := f^[n z] z.val
  have hinj : Function.Injective exit := by
    intro z w he
    apply Subtype.ext
    exact starts_eq_of_iterate_eq A f hf z.val w.val (hstart z) (hstart w)
      (n z) (n w) (hprev z) (hprev w) he
  have hreach (z : N) : exit z ∉ B ∧ ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v,S.root_mem⟩).snd = exit z ∧ AgreesOutside S R := by
    obtain ⟨C,hC,hCe,hCn,hCz⟩ := closed_trail_first_at_neighbor (R.tail ⟨v,R.root_mem⟩) (R.trail _) z.property
    obtain ⟨R',hR',hroot,htail,htrack⟩ := replace_root_tracked R C hC hCe hCn
    have hfirst : (R'.tail ⟨v,R'.root_mem⟩).snd = z.val := by rw [hroot,hCz]
    have htf' (w : B) (hw : w.val ≠ v) : f w.val = (R'.tail w).penultimate := by
      rw [htail w hw]; exact htf w hw
    obtain ⟨S,hS,hSfirst,hSout,hStrack⟩ := realize_escape_orbit R' f hf htf'
      (by rw [hfirst]; exact hstart z) (n z) (by rw [hfirst]; exact hn z)
      (by rw [hfirst]; exact hprev z)
    have hsnd : (S.tail ⟨v,S.root_mem⟩).snd = exit z := by rw [hSfirst,hfirst]
    exact ⟨hsnd ▸ hSout,S,by rw [hS,hR'],hsnd,agreesOutside_trans hStrack htrack⟩
  refine ⟨Finset.univ.image exit,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    exact Nat.card_eq_fintype_card.symm
  · intro z hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    exact hreach w

/-- A forbidden set smaller than the root-tail degree cannot block every
score-preserving escape realization. -/
lemma expose_escape_avoiding_finset {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B) (Z : Finset V)
    (hZ : Z.card < ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard) :
    ∃ S : RootedTailSystem G k v B,
      S.system.score = R.system.score ∧ (S.tail ⟨v,S.root_mem⟩).snd ∉ B ∧
      (S.tail ⟨v,S.root_mem⟩).snd ∉ Z ∧ AgreesOutside S R := by
  classical
  obtain ⟨E,hE,hreach⟩ := many_distinct_escapes R
  obtain ⟨z,hzE,hzZ⟩ := Finset.exists_mem_notMem_of_card_lt_card (hE.symm ▸ hZ)
  obtain ⟨hzB,S,hs,hfirst,htrack⟩ := hreach z hzE
  exact ⟨S,hs,hfirst.symm ▸ hzB,hfirst.symm ▸ hzZ,htrack⟩

/-- An escape slide changes no member other than its donor and its receiver. -/
lemma escape_slide_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {y : V}
    (h : G.Adj (T.start i) y) (p : G.Walk y (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (NormalTrailSystem.owner T y)).support) :
    ∃ S : NormalTrailSystem G k, S.score = T.score + 1 ∧
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
  obtain ⟨S,_,_,hSl,_,_,hs⟩ := slide_oriented U i j hij h' pU hpU heU
  rw [cons_ncard_of_mem h' pU hvU,cons_ncard_of_notMem h' (U.walk j) havoidU] at hs
  exact ⟨S,by omega,fun l hli hlj ↦ (hSl l hli hlj).trans (hUe l)⟩

/-- Finishing a rooted exchange changes only one outside member: the owner of
the escape vertex. All other outside subgraphs are retained at their indices. -/
lemma finish_exposed_tracked {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (hesc : (R.tail ⟨v,R.root_mem⟩).snd ∉ B) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∃ j : Fin k, j ∉ R.active ∧
        ((R.tail ⟨v,R.root_mem⟩).snd = R.system.start j ∨
          (R.tail ⟨v,R.root_mem⟩).snd = R.system.finish j) ∧
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
  obtain ⟨T,hT,hTl⟩ := escape_slide_tracked S.system i h p
    (by rw [hform]; exact hp) (by rw [hform]; exact he) hv hout
  have hjR : j ∉ R.active := htrack.1 ▸ hj
  refine ⟨T,by omega,j,hjR,?_,?_⟩
  · obtain ⟨hja,hjb,_⟩ := htrack.2 j hjR
    have hown : C.snd = S.system.start j ∨ C.snd = S.system.finish j :=
      NormalTrailSystem.owner_spec S.system C.snd
    simpa only [hfirst,hja,hjb] using hown
  · intro l hl hlj
    have hli : l ≠ i := fun hh ↦ hl (hh ▸ (htrack.1 ▸ hia))
    exact (hTl l hli hlj).trans ((htrack.2 l hl).2.2)

/-- Simultaneous whole-subgraph preservation of a finite protected outside
family, provided its endpoint set is smaller than the root-tail degree. -/
lemma repair_protected_family {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (L : Finset (Fin k)) (hL : ∀ l ∈ L, l ∉ R.active)
    (hdeg : 2*L.card < ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∀ l ∈ L, (T.walk l).toSubgraph = (R.system.walk l).toSubgraph := by
  classical
  let Z := L.image R.system.start ∪ L.image R.system.finish
  have hZ : Z.card < ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard := by
    have hc : Z.card ≤ 2*L.card := calc
      Z.card ≤ (L.image R.system.start).card + (L.image R.system.finish).card := Finset.card_union_le _ _
      _ ≤ L.card + L.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2*L.card := by omega
    exact hc.trans_lt hdeg
  obtain ⟨S,hs,hesc,havoid,htrack⟩ := expose_escape_avoiding_finset R Z hZ
  obtain ⟨T,hT,j,hj,hown,hTl⟩ := finish_exposed_tracked S hesc
  refine ⟨T,by omega,?_⟩
  intro l hl
  have hlout := hL l hl
  have hlS : l ∉ S.active := htrack.1.symm ▸ hlout
  have hlj : l ≠ j := by
    intro he
    subst j
    obtain ⟨hla,hlb,_⟩ := htrack.2 l hlout
    apply havoid
    rcases hown with hh | hh
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l,hl,hla.symm.trans hh.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l,hl,hlb.symm.trans hh.symm⟩)
  exact (hTl l hlS hlj).trans ((htrack.2 l hlout).2.2)

/-- Only endpoints adjacent to the root can own an escape. Protecting a family
therefore needs to forbid only those endpoints, rather than both ends of every
member. This is useful for pendant-leaf members. -/
lemma repair_protected_adjacent_ends {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (L : Finset (Fin k)) (hL : ∀ l ∈ L, l ∉ R.active) (Z : Finset V)
    (hZends : ∀ l ∈ L, ∀ w, (w = R.system.start l ∨ w = R.system.finish l) → G.Adj v w → w ∈ Z)
    (hdeg : Z.card < ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      ∀ l ∈ L, (T.walk l).toSubgraph = (R.system.walk l).toSubgraph := by
  classical
  obtain ⟨S,hs,hesc,havoid,htrack⟩ := expose_escape_avoiding_finset R Z hdeg
  obtain ⟨T,hT,j,hj,hown,hTl⟩ := finish_exposed_tracked S hesc
  refine ⟨T,by omega,?_⟩
  intro l hl
  have hlout := hL l hl
  have hlS : l ∉ S.active := htrack.1.symm ▸ hlout
  have hlj : l ≠ j := by
    intro he
    subst j
    obtain ⟨hla,hlb,_⟩ := htrack.2 l hlout
    apply havoid
    apply hZends l hl _
    · simpa only [hla,hlb] using hown
    · exact (S.tail ⟨v,S.root_mem⟩).adj_snd S.root_nonempty
  exact (hTl l hlS hlj).trans ((htrack.2 l hlout).2.2)

/-- A score maximum subject to preserving an outside family has a quantitative
obstruction: its nonempty closed root tail has degree at most twice the size
of that family. -/
lemma protected_maximum_root_degree_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (L : Finset (Fin k)) (hL : ∀ l ∈ L, l ∉ R.active)
    (hmax : ∀ T : NormalTrailSystem G k,
      (∀ l ∈ L, (T.walk l).toSubgraph = (R.system.walk l).toSubgraph) → T.score ≤ R.system.score) :
    ((R.tail ⟨v,R.root_mem⟩).toSubgraph.neighborSet v).ncard ≤ 2*L.card := by
  by_contra hn
  obtain ⟨T,hT,hpres⟩ := repair_protected_family R L hL (Nat.lt_of_not_ge hn)
  have hh := hmax T hpres
  omega

end Erdos583ManyEscapeDevelopment
