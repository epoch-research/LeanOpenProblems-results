import Submission.Work

/-! Induced-path buffers for protected normalization. -/
open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.VertexTracking Erdos583Work.ProtectedEdge
open Erdos583Work.SingletonRotation
namespace Erdos583InducedBufferDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma subgraph_coe_edge_card {V : Type*} {G : SimpleGraph V} (K : G.Subgraph) :
    Nat.card K.coe.edgeSet = K.edgeSet.ncard := by
  change K.coe.edgeSet.ncard = K.edgeSet.ncard
  rw [← K.image_coe_edgeSet_coe]
  symm
  apply Set.ncard_image_of_injective
  exact Sym2.map.injective Subtype.val_injective

lemma path_vertex_ncard {V : Type*} {G : SimpleGraph V} {a b : V}
    (q : G.Walk a b) (hq : q.IsPath) : q.toSubgraph.verts.ncard = q.length + 1 := by
  classical
  rw [Walk.verts_toSubgraph,← List.coe_toFinset,Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hq.support_nodup,Walk.length_support]

/-- An induced path is determined, among connected walk subgraphs, by its vertex
set. This is independent of the endpoints and the traversal of the other walk. -/
lemma induced_path_verts_determine {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b c d : V} (q : G.Walk a b) (hq : q.IsPath) (hind : q.toSubgraph.IsInduced)
    (p : G.Walk c d) (he : p.toSubgraph.verts = q.toSubgraph.verts) :
    p.toSubgraph = q.toSubgraph := by
  have hle : p.toSubgraph ≤ q.toSubgraph := by
    refine ⟨fun x hx ↦ he ▸ hx,?_⟩
    intro x y hxy
    exact hind (he ▸ p.toSubgraph.edge_vert hxy)
      (he ▸ p.toSubgraph.edge_vert hxy.symm) (p.toSubgraph.adj_sub hxy)
  have hlow := p.toSubgraph_connected.coe.card_vert_le_card_edgeSet_add_one
  rw [subgraph_coe_edge_card] at hlow
  change p.toSubgraph.verts.ncard ≤ p.toSubgraph.edgeSet.ncard + 1 at hlow
  rw [he,path_vertex_ncard q hq] at hlow
  have hcard : q.toSubgraph.edgeSet.ncard ≤ p.toSubgraph.edgeSet.ncard := by
    rw [path_edgeSet_ncard hq]
    omega
  have heE : p.toSubgraph.edgeSet = q.toSubgraph.edgeSet :=
    Set.eq_of_subset_of_ncard_le (Subgraph.edgeSet_mono hle) hcard
  ext x y
  · rw [he]
  · change s(x,y) ∈ p.toSubgraph.edgeSet ↔ s(x,y) ∈ q.toSubgraph.edgeSet
    rw [heE]

lemma repair_induced_path {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {v : V} {B : Finset V} (R : RootedTailSystem G k v B)
    (l : Fin k) (hl : l ∈ R.active) {a b : V} (q : G.Walk a b)
    (hq : q.IsPath) (hind : q.toSubgraph.IsInduced)
    (he : (R.system.walk l).toSubgraph = q.toSubgraph) :
    ∃ T : NormalTrailSystem G k, T.score = R.system.score + 1 ∧
      (T.walk l).toSubgraph = q.toSubgraph := by
  obtain ⟨T,hT,j,hj,_,hTv⟩ := repair_active_vertices R
  refine ⟨T,hT,induced_path_verts_determine q hq hind (T.walk l) ?_⟩
  rw [hTv l (fun hh ↦ hj (hh ▸ hl)),he]


lemma induced_tail {V : Type*} {G : SimpleGraph V} {a c b : V}
    (h : G.Adj a c) (q : G.Walk c b) (hp : (Walk.cons h q).IsPath)
    (hind : (Walk.cons h q).toSubgraph.IsInduced) : q.toSubgraph.IsInduced := by
  intro x hx y hy hxy
  have hx' : x ∈ (Walk.cons h q).toSubgraph.verts := by rw [cons_verts]; exact Set.mem_insert_of_mem _ hx
  have hy' : y ∈ (Walk.cons h q).toSubgraph.verts := by rw [cons_verts]; exact Set.mem_insert_of_mem _ hy
  have hh := hind hx' hy' hxy
  rw [Walk.toSubgraph,Subgraph.sup_adj] at hh
  rcases hh with hh | hh
  · have hnot : a ∉ q.toSubgraph.verts := by
      simpa only [Walk.mem_verts_toSubgraph] using (Walk.cons_isPath_iff h q).mp hp |>.2
    have hxya : x=a ∨ y=a := by
      rcases (show (a=x ∧ c=y) ∨ (a=y ∧ c=x) by simpa only [subgraphOfAdj_adj,Sym2.eq,Sym2.rel_iff',Prod.swap_prod_mk,Prod.mk.injEq] using hh) with hh | hh
      · exact Or.inl hh.1.symm
      · exact Or.inr hh.1.symm
    exact (hxya.elim (fun he ↦ hnot (he ▸ hx)) (fun he ↦ hnot (he ▸ hy))).elim
  · exact hh

lemma induced_nontrivial_tail_not_adj_ends {V : Type*} {G : SimpleGraph V}
    {a c b : V} (h : G.Adj a c) (q : G.Walk c b) (hq : ¬q.Nil)
    (hp : (Walk.cons h q).IsPath) (hind : (Walk.cons h q).toSubgraph.IsInduced) :
    ¬G.Adj a b := by
  intro hab
  have hK := hind (Walk.cons h q).start_mem_verts_toSubgraph
    (Walk.cons h q).end_mem_verts_toSubgraph hab
  have hcb : c=b := by simpa only [Walk.snd_cons] using hp.snd_of_toSubgraph_adj hK
  have hqp := (Walk.cons_isPath_iff h q).mp hp |>.1
  have hq' : ((q.copy rfl hcb.symm)).IsPath := by simpa only [Walk.isPath_copy] using hqp
  have hnil := (Walk.isPath_iff_eq_nil _).mp hq'
  have hn : (q.copy rfl hcb.symm).Nil := by rw [hnil]; exact Walk.Nil.nil
  exact hq (by simpa using hn)

/-- Shorten a path member whose ends are nonadjacent, with no assumption that
the whole system maximizes score. The nonempty suffix stays at its index. -/
lemma shorten_path_member_nonadj {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : NormalTrailSystem G k) (l : Fin k) {a u v : V}
    (h : G.Adj a u) (q : G.Walk u v) (hqn : ¬q.Nil)
    (hp : (Walk.cons h q).IsPath) (hnadj : ¬G.Adj a v)
    (he : (T.walk l).toSubgraph = (Walk.cons h q).toSubgraph) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      (S.walk l).toSubgraph = q.toSubgraph := by
  classical
  have hav : a ≠ v := path_endpoints_ne hp ⟨s(a,u),by simpa only [Walk.snd_cons] using (Walk.cons h q).toSubgraph_adj_snd (by simp)⟩
  have huv : u ≠ v := path_endpoints_ne ((Walk.cons_isPath_iff h q).mp hp).1 ⟨s(u,q.snd),q.toSubgraph_adj_snd hqn⟩
  have hends := endpoints_of_path_subgraph T l (Walk.cons h q) hp (by simp) he
  obtain ⟨U,hs,ha,_,hUe⟩ := orient_receiver T l a hends.1
  have hendsU := endpoints_of_path_subgraph U l (Walk.cons h q) hp (by simp) ((hUe l).trans he)
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
    exact hjown.elim h.ne.symm huv
  obtain ⟨R,hR,hRu,hRl,hRe⟩ := orient_receiver U j u hjown
  obtain ⟨hRa,hRv⟩ := hRl l hlj
  have haR : R.start l=a := hRa.trans ha
  have hvR : R.finish l=v := hRv.trans hv
  let q' := q.copy hRu.symm hvR.symm
  have h' : G.Adj (R.start l) (R.start j) := by rw [haR,hRu]; exact h
  have hform : Walk.cons h' q' = (Walk.cons h q).copy haR.symm hvR.symm :=
    cons_copy_vertices h q haR.symm hRu.symm hvR.symm h'
  have heR : (R.walk l).toSubgraph = (Walk.cons h' q').toSubgraph := by
    rw [hform,NormalTrailSystem.walk_copy_subgraph,hRe,hUe,he]
  have hqtrail : (Walk.cons h' q').IsTrail := by rw [hform]; simpa only [Walk.isTrail_copy] using hp.isTrail
  have hnot : R.start l ∉ q'.support := by
    simpa only [q',haR,Walk.support_copy] using (Walk.cons_isPath_iff h q).mp hp |>.2
  obtain ⟨S,hS,hSl,_⟩ := shorten_oriented_no_return R l j hlj h' q' hqtrail heR hnot
    (by rw [haR,hvR]; exact hnadj)
  exact ⟨S,hS.trans (hR.trans hs),hSl.trans (NormalTrailSystem.walk_copy_subgraph _ _ _)⟩

/-- Remove an arbitrary prefix of an induced path member while retaining a
nonempty suffix. Every removal preserves the global incidence score exactly. -/
lemma strip_induced_prefix {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {a u : V} (A : G.Walk a u) :
    ∀ (T : NormalTrailSystem G k) (l : Fin k) {v : V} (q : G.Walk u v),
      ¬q.Nil → (A.append q).IsPath → (A.append q).toSubgraph.IsInduced →
      (T.walk l).toSubgraph = (A.append q).toSubgraph →
      ∃ S : NormalTrailSystem G k, S.score = T.score ∧ (S.walk l).toSubgraph = q.toSubgraph := by
  induction A with
  | nil => intro T l v q _ _ _ he; exact ⟨T,rfl,he⟩
  | @cons a b u h A ih =>
    intro T l v q hqn hp hind he
    have htailn : ¬(A.append q).Nil := by
      rw [Walk.nil_iff_length_eq,Walk.length_append]
      have hh := Walk.not_nil_iff_lt_length.mp hqn
      omega
    have hp' : (Walk.cons h (A.append q)).IsPath := hp
    have hind' : (Walk.cons h (A.append q)).toSubgraph.IsInduced := hind
    obtain ⟨U,hU,hUl⟩ := shorten_path_member_nonadj T l h (A.append q) htailn hp'
      (induced_nontrivial_tail_not_adj_ends h _ htailn hp' hind') he
    obtain ⟨S,hS,hSl⟩ := ih U l q hqn ((Walk.cons_isPath_iff h _).mp hp').1
      (induced_tail h _ hp' hind') hUl
    exact ⟨S,hS.trans hU,hSl⟩


/-- Transfer an entire stem onto a singleton edge. If the resulting buffer is
a path, the transfer cannot decrease the total distinct-vertex incidence score. -/
lemma move_stem_to_singleton {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i l : Fin k) (hil : i ≠ l)
    (h : G.Adj (T.start l) (T.finish l))
    (heL : (T.walk l).toSubgraph = G.subgraphOfAdj h)
    (A : G.Walk (T.start i) (T.start l)) (p : G.Walk (T.start l) (T.finish i))
    (hp : (A.append p).IsTrail)
    (hei : (T.walk i).toSubgraph = (A.append p).toSubgraph)
    (hbuf : (A.append (Walk.cons h Walk.nil)).IsPath) :
    ∃ S : NormalTrailSystem G k, T.score ≤ S.score ∧
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk l).toSubgraph = (A.append (Walk.cons h Walk.nil)).toSubgraph ∧
      S.start i = T.start l ∧ S.finish i = T.finish i := by
  classical
  let e := Walk.cons h Walk.nil
  have hd : Disjoint (A.toSubgraph.edgeSet ∪ p.toSubgraph.edgeSet) e.toSubgraph.edgeSet := by
    rw [← Subgraph.edgeSet_sup,← Walk.toSubgraph_append,←hei,
      show e.toSubgraph = G.subgraphOfAdj h by simp [e],←heL]
    exact T.disjoint hil
  have hdnew : Disjoint p.toSubgraph.edgeSet (A.append e).toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_right.mpr ⟨(append_trail_disjoint hp).symm,(disjoint_sup_left.mp hd).2⟩
  have hu : p.toSubgraph.edgeSet ∪ (A.append e).toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk l).toSubgraph.edgeSet := by
    rw [hei,heL,Walk.toSubgraph_append,Walk.toSubgraph_append,
      Subgraph.edgeSet_sup,Subgraph.edgeSet_sup,show G.subgraphOfAdj h = e.toSubgraph by simp [e]]
    ext d
    simp only [Set.mem_union]
    tauto
  obtain ⟨S,hSi,hSl,_,hSa,hSb,hs⟩ := replace_two_starts_tracked T i l hil p (A.append e)
    hp.of_append_right hbuf.isTrail hdnew hu
  have haCard := path_vertex_ncard A hbuf.of_append_left
  have hbufCard : (A.append e).toSubgraph.verts.ncard = A.length+2 := by
    rw [path_vertex_ncard _ hbuf,Walk.length_append]
    simp
  have hpair : (G.subgraphOfAdj h).verts.ncard = 2 := by simp [h.ne]
  have hinter : 1 ≤ (A.toSubgraph.verts ∩ p.toSubgraph.verts).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨T.start l,A.end_mem_verts_toSubgraph,p.start_mem_verts_toSubgraph⟩
  have hbudget := Set.ncard_union_add_ncard_inter A.toSubgraph.verts p.toSubgraph.verts
  rw [haCard,← Subgraph.verts_sup,← Walk.toSubgraph_append] at hbudget
  rw [hei,heL,hbufCard,hpair] at hs
  refine ⟨S,by omega,hSi,hSl,?_,congrFun hSb i⟩
  simp [hSa]

/-- A marked-endpoint closed segment behind an arbitrary induced stem is
impossible at a score maximum preserving the marked singleton edge. The stem
plus that edge is the induced buffer; no global triangle-free hypothesis is
needed. This does not address stems whose buffers have chords. -/
lemma protected_no_closed_after_induced_stem {V : Type*} [Fintype V]
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
    (hind : (A.append (Walk.cons h Walk.nil)).toSubgraph.IsInduced) : C.Nil := by
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
  obtain ⟨U,hU,hUl⟩ := repair_induced_path R l hlR (A.append (Walk.cons h Walk.nil)) hbuf hind
    (by rw [hR,hSl])
  obtain ⟨W,hW,hWl⟩ := strip_induced_prefix A U l (Walk.cons h Walk.nil) (by simp) hbuf hind hUl
  have hcap := hmax W (by simpa using hWl)
  rw [hR] at hU
  omega

end Erdos583InducedBufferDevelopment
