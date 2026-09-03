import Submission.InducedBuffer

/-! Compression of a distinguished member with a locally pendant vertex. -/
open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.VertexTracking Erdos583Work.ProtectedEdge
open Erdos583Work.SingletonRotation Erdos583InducedBufferDevelopment
namespace Erdos583LocalLeafDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma exists_lex_optimum {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (P : NormalTrailSystem G k → Prop) (T : NormalTrailSystem G k) (hT : P T)
    (f : NormalTrailSystem G k → ℕ) :
    ∃ U : NormalTrailSystem G k, P U ∧ T.score ≤ U.score ∧
      (∀ R, P R → R.score ≤ U.score) ∧
      (∀ R, P R → R.score = U.score → f U ≤ f R) := by
  classical
  let Q (m : ℕ) := ∃ S : NormalTrailSystem G k, P S ∧ S.score = m
  obtain ⟨S,hSP,hS⟩ := Nat.findGreatest_spec (P := Q) T.score_le ⟨T,hT,rfl⟩
  have hm (R) (hR : P R) : R.score ≤ S.score := by
    rw [hS]
    exact Nat.le_findGreatest R.score_le ⟨R,hR,rfl⟩
  have hex : ∃ n, ∃ U : NormalTrailSystem G k, P U ∧ U.score = S.score ∧ f U = n :=
    ⟨f S,S,hSP,rfl,rfl⟩
  obtain ⟨U,hUP,hU,hf⟩ := Nat.find_spec hex
  refine ⟨U,hUP,by rw [hU]; exact hm T hT,?_,?_⟩
  · intro R hR; rw [hU]; exact hm R hR
  · intro R hR he; rw [hf]
    exact Nat.find_min' hex ⟨R,hR,he.trans hU,rfl⟩

lemma local_leaf_neighborSet {V : Type*} {G : SimpleGraph V} {a b u v : V}
    (S : Set V) (p : G.Walk a b) (hn : ¬p.Nil)
    (hv : v ∈ p.toSubgraph.verts) (hS : p.toSubgraph.verts ⊆ S)
    (hleaf : ∀ x ∈ S, G.Adj v x → x=u) :
    p.toSubgraph.neighborSet v = {u} := by
  obtain ⟨x,hx⟩ := walk_vertex_has_subgraph_neighbor p hn hv
  have hxU : x=u := hleaf x (hS (p.toSubgraph.edge_vert hx.symm)) (p.toSubgraph.adj_sub hx)
  subst x
  ext y
  constructor
  · intro hy
    exact hleaf y (hS (p.toSubgraph.edge_vert hy.symm)) (p.toSubgraph.adj_sub hy)
  · rintro rfl; exact hx

lemma local_leaf_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V} {a b u v : V}
    (S : Set V) (p : G.Walk a b) (hp : p.IsTrail) (hn : ¬p.Nil)
    (hv : v ∈ p.toSubgraph.verts) (hS : p.toSubgraph.verts ⊆ S)
    (hleaf : ∀ x ∈ S, G.Adj v x → x=u) : a ≠ b ∧ (v=a ∨ v=b) := by
  apply (trail_neighbor_ncard_odd_iff hp v).mp
  rw [local_leaf_neighborSet S p hn hv hS hleaf]
  simp

lemma orient_finish {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (l : Fin k) (v : V)
    (hv : v=T.start l ∨ v=T.finish l) :
    ∃ U : NormalTrailSystem G k, U.score = T.score ∧ U.finish l=v ∧
      ∀ i, (U.walk i).toSubgraph = (T.walk i).toSubgraph := by
  classical
  rcases hv with hv | hv
  · obtain ⟨U,hs,hU⟩ := T.orient (fun i ↦ decide (i=l))
    exact ⟨U,hs,by simpa [hv] using (hU l).2.1,fun i ↦ (hU i).2.2⟩
  · exact ⟨T,rfl,hv.symm,fun _ ↦ rfl⟩

lemma shorten_trail_member_no_return {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k) {c : V}
    (h : G.Adj (T.start l) c) (q : G.Walk c (T.finish l))
    (hp : (Walk.cons h q).IsTrail)
    (he : (T.walk l).toSubgraph = (Walk.cons h q).toSubgraph)
    (hnot : T.start l ∉ q.support) (hcb : c ≠ T.finish l)
    (hnadj : ¬G.Adj (T.start l) (T.finish l)) :
    ∃ U : NormalTrailSystem G k, U.score=T.score ∧
      (U.walk l).toSubgraph=q.toSubgraph := by
  classical
  let j := NormalTrailSystem.owner T c
  have hjown := NormalTrailSystem.owner_spec T c
  have hlj : l ≠ j := by
    intro hh
    change c=T.start j ∨ c=T.finish j at hjown
    rw [←hh] at hjown
    exact hjown.elim h.ne.symm hcb
  obtain ⟨R,hR,hRc,hRl,hRe⟩ := orient_receiver T j c hjown
  obtain ⟨haR,hvR⟩ := hRl l hlj
  let q' := q.copy hRc.symm hvR.symm
  have h' : G.Adj (R.start l) (R.start j) := by rw [haR,hRc]; exact h
  have hform : Walk.cons h' q' = (Walk.cons h q).copy haR.symm hvR.symm :=
    cons_copy_vertices h q haR.symm hRc.symm hvR.symm h'
  have heR : (R.walk l).toSubgraph = (Walk.cons h' q').toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hRe,he]
  have hpR : (Walk.cons h' q').IsTrail := by rw [hform]; simpa only [Walk.isTrail_copy] using hp
  obtain ⟨U,hU,hUl,_⟩ := shorten_oriented_no_return R l j hlj h' q' hpR heR
    (by simpa only [q',haR,Walk.support_copy] using hnot)
    (by rw [haR,hvR]; exact hnadj)
  exact ⟨U,hU.trans hR,hUl.trans (NormalTrailSystem.walk_copy_subgraph _ _ _)⟩

lemma constrained_no_repeated_start {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k)
    (hmax : ∀ U : NormalTrailSystem G k,
      (U.walk l).toSubgraph.verts=(T.walk l).toSubgraph.verts → U.score ≤ T.score)
    {c : V} (h : G.Adj (T.start l) c) (q : G.Walk c (T.finish l))
    (hp : (Walk.cons h q).IsTrail)
    (he : (T.walk l).toSubgraph=(Walk.cons h q).toSubgraph) : T.start l ∉ q.support := by
  intro hv
  let C := Walk.cons h (q.takeUntil (T.start l) hv)
  let p := q.dropUntil (T.start l) hv
  have hform : C.append p = Walk.cons h q := by simp [C,p]
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix T l C p (by rw [hform]; exact he)
    (by rw [hform]; exact hp) (by simp [C])
  have hl : l ∈ R.active := by
    apply (R.start_mem l).mp
    rw [hR]
    exact R.root_mem
  obtain ⟨U,hU,j,hj,_,hUv⟩ := repair_active_vertices R
  have heU := hUv l (fun hh ↦ hj (hh ▸ hl))
  rw [hR] at heU hU
  have hh := hmax U heU
  omega

/-- A trail member contained in a fixed vertex set can be compressed to its
locally pendant edge, without decreasing total incidence score. Chords away
from the pendant vertex are permitted. -/
lemma compress_local_leaf {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (l : Fin k) (S : Set V) {u v : V}
    (h : G.Adj u v) (hv : v ∈ (T.walk l).toSubgraph.verts)
    (hS : (T.walk l).toSubgraph.verts ⊆ S)
    (hleaf : ∀ x ∈ S, G.Adj v x → x=u) :
    ∃ U : NormalTrailSystem G k, T.score ≤ U.score ∧
      (U.walk l).toSubgraph=G.subgraphOfAdj h := by
  classical
  let P (U : NormalTrailSystem G k) :=
    v ∈ (U.walk l).toSubgraph.verts ∧ (U.walk l).toSubgraph.verts ⊆ S
  obtain ⟨R,hRP,hTR,hmax,hmin⟩ := exists_lex_optimum P T ⟨hv,hS⟩
    (fun U ↦ (U.walk l).toSubgraph.verts.ncard)
  have hend := local_leaf_endpoint S (R.walk l) (R.isTrail l)
    (Walk.not_nil_of_ne (R.endpoints_ne l)) hRP.1 hRP.2 hleaf
  obtain ⟨U,hU,hUv,hUe⟩ := orient_finish R l v hend.2
  have hUP : P U := by simpa only [P,hUe] using hRP
  have hUmax (W : NormalTrailSystem G k) (hW : P W) : W.score ≤ U.score := by
    rw [hU]; exact hmax W hW
  have hUmin (W : NormalTrailSystem G k) (hW : P W) (hscore : W.score=U.score) :
      (U.walk l).toSubgraph.verts.ncard ≤ (W.walk l).toSubgraph.verts.ncard := by
    rw [hUe]
    exact hmin W hW (hscore.trans hU)
  obtain ⟨c,hac,q,hform⟩ := Walk.exists_eq_cons_of_ne (U.endpoints_ne l) (U.walk l)
  have hp : (Walk.cons hac q).IsTrail := hform ▸ U.isTrail l
  have he : (U.walk l).toSubgraph=(Walk.cons hac q).toSubgraph := congrArg Walk.toSubgraph hform
  have hnot := constrained_no_repeated_start U l (fun W heW ↦ hUmax W (by
    simpa only [P,heW] using hUP)) hac q hp he
  have hqS : q.toSubgraph.verts ⊆ S := by
    intro x hx
    apply hUP.2
    rw [he,cons_verts]
    exact Set.mem_insert_of_mem _ hx
  by_cases hqn : q.Nil
  · have hc := hqn.eq
    subst c
    rw [hqn.eq_nil,Walk.toSubgraph_cons_nil_eq_subgraphOfAdj] at he
    have hau : U.start l=u := hleaf _
      (hUP.2 (U.walk l).start_mem_verts_toSubgraph) (by rw [←hUv]; exact hac.symm)
    refine ⟨U,by omega,he.trans ?_⟩
    ext <;> simp [hau,hUv]
  · have hvq : v ∈ q.toSubgraph.verts := hUv ▸ q.end_mem_verts_toSubgraph
    have hcb := (local_leaf_endpoint S q ((Walk.isTrail_cons hac q).mp hp).1 hqn hvq hqS hleaf).1
    have hneigh := local_leaf_neighborSet S q hqn hvq hqS hleaf
    have huq : u ∈ q.toSubgraph.verts := by
      have hh : q.toSubgraph.Adj v u := by
        change u ∈ q.toSubgraph.neighborSet v
        rw [hneigh]; exact Set.mem_singleton _
      exact q.toSubgraph.edge_vert hh.symm
    have hau : U.start l ≠ u := fun hh ↦ hnot (hh ▸ q.mem_verts_toSubgraph.mp huq)
    have hnadj : ¬G.Adj (U.start l) (U.finish l) := by
      intro hh
      exact hau (hleaf _ (hUP.2 (U.walk l).start_mem_verts_toSubgraph) (by rw [←hUv]; exact hh.symm))
    obtain ⟨W,hW,hWl⟩ := shorten_trail_member_no_return U l hac q hp he hnot hcb hnadj
    have hWP : P W := by
      change v ∈ (W.walk l).toSubgraph.verts ∧ (W.walk l).toSubgraph.verts ⊆ S
      rw [hWl]; exact ⟨hvq,hqS⟩
    have hsize := hUmin W hWP hW
    rw [he,hWl,cons_ncard_of_notMem hac q hnot] at hsize
    omega

/-- A marked-endpoint closed segment cannot lie behind a stem whose buffer
has the far marked endpoint as a local leaf. Unlike induced-buffer repair,
this permits arbitrary chords elsewhere in the buffer. -/
lemma protected_no_closed_after_local_leaf_stem {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem G k) (i l : Fin k) (hil : i ≠ l)
    (h : G.Adj (T.start l) (T.finish l))
    (heL : (T.walk l).toSubgraph = G.subgraphOfAdj h)
    (hmax : ∀ U : NormalTrailSystem G k,
      (U.walk l).toSubgraph = G.subgraphOfAdj h → U.score ≤ T.score)
    (A : G.Walk (T.start i) (T.start l))
    (C : G.Walk (T.start l) (T.start l)) (q : G.Walk (T.start l) (T.finish i))
    (hp : (A.append (C.append q)).IsTrail)
    (hei : (T.walk i).toSubgraph = (A.append (C.append q)).toSubgraph)
    (hbuf : (A.append (Walk.cons h Walk.nil)).IsPath)
    (hleaf : ∀ x ∈ (A.append (Walk.cons h Walk.nil)).toSubgraph.verts,
      G.Adj (T.finish l) x → x=T.start l) : C.Nil := by
  classical
  by_contra hCn
  obtain ⟨S,hscore,hSi,hSl,hai,hbi⟩ := move_stem_to_singleton T i l hil h heL A (C.append q) hp hei hbuf
  let C' := C.copy hai.symm hai.symm
  let q' := q.copy hai.symm hbi.symm
  have hform : C'.append q' = (C.append q).copy hai.symm hbi.symm := by
    simp only [C',q',Walk.append_copy_copy]
  have hrep : (S.walk i).toSubgraph = (C'.append q').toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hSi]
  have hrepTrail : (C'.append q').IsTrail := by
    rw [hform]
    simpa only [Walk.isTrail_copy] using hp.of_append_right
  obtain ⟨B,R,hR,_⟩ := of_closed_prefix S i C' q' hrep hrepTrail
    (by simpa only [C',Walk.nil_copy] using hCn)
  have hlR : l ∈ R.active := by
    by_contra hl
    have hout := R.outside l hl
    rw [hR,← Walk.mem_verts_toSubgraph,hSl,hai,Walk.toSubgraph_append,Subgraph.verts_sup] at hout
    exact hout (Or.inl A.end_mem_verts_toSubgraph)
  obtain ⟨U,hU,j,hj,_,hUl⟩ := repair_active_vertices R
  have hvertices := hUl l (fun hh ↦ hj (hh ▸ hlR))
  rw [hR,hSl] at hvertices
  obtain ⟨W,hW,hWl⟩ := compress_local_leaf U l
    (A.append (Walk.cons h Walk.nil)).toSubgraph.verts h
    (by rw [hvertices]; exact (A.append (Walk.cons h Walk.nil)).end_mem_verts_toSubgraph)
    (by rw [hvertices]) hleaf
  have hcap := hmax W hWl
  rw [hR] at hU
  omega

end Erdos583LocalLeafDevelopment
