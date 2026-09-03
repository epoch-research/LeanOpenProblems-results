import Submission.Work

/-! A prescribed edge can be made the first edge of a member of a normal path
partition. This does not establish simultaneous matching compatibility. -/

open SimpleGraph Erdos583Work Erdos583Work.TrailNormalization
namespace Erdos583ForceDevelopment

set_option maxHeartbeats 1200000

lemma extend_suffix {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {a v : V} (A : G.Walk a v) :
    ∀ (T : NormalTrailSystem G k), (∀ S : NormalTrailSystem G k, S.score ≤ T.score) →
      ∀ {b : V} (B : G.Walk v b), ¬B.Nil →
        (A.append B).IsTrail → IsMember T (A.append B) →
        ∃ S : NormalTrailSystem G k, S.score = T.score ∧
          ∃ t, ∃ q : G.Walk b t, (B.append q).IsTrail ∧ IsMember S (B.append q) := by
  induction A with
  | nil =>
    intro T _ b B _ hp hm
    exact ⟨T,rfl,b,Walk.nil,by simpa using hp,by simpa using hm⟩
  | @cons a w v h A ih =>
    intro T hmax b B hB hp hm
    have hn : ¬(A.append B).Nil := by
      rw [Walk.nil_iff_length_eq, Walk.length_append]
      have hpos := Walk.not_nil_iff_lt_length.mp hB
      omega
    obtain ⟨U,hU,c,q,hq,hmq⟩ := shorten_member T hmax h (A.append B) hn hp hm
    have hUmax : ∀ R : NormalTrailSystem G k, R.score ≤ U.score := by
      intro R; rw [hU]; exact hmax R
    have hBq : ¬(B.append q).Nil := by
      rw [Walk.nil_iff_length_eq, Walk.length_append]
      have hpos := Walk.not_nil_iff_lt_length.mp hB
      omega
    obtain ⟨S,hS,t,r,hr,hmr⟩ := ih U hUmax (B.append q) hBq
      (by simpa only [Walk.append_assoc] using hq)
      (by simpa only [Walk.append_assoc] using hmq)
    exact ⟨S,hS.trans hU,t,q.append r,by simpa only [Walk.append_assoc] using hr,
      by simpa only [Walk.append_assoc] using hmr⟩

lemma force_first_of_split {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {a u v b : V} (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b)
    (hp : (A.append (Walk.cons h B)).IsTrail)
    (hm : IsMember T (A.append (Walk.cons h B))) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      ∃ t, ∃ q : G.Walk v t, (Walk.cons h q).IsTrail ∧ IsMember S (Walk.cons h q) := by
  obtain ⟨S,hS,t,r,hr,hmr⟩ := extend_suffix A T hmax (Walk.cons h B) (by simp) hp hm
  exact ⟨S,hS,t,B.append r,hr,hmr⟩

lemma force_first_edge {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {u v : V} (h : G.Adj u v) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      ∃ t, ∃ q : G.Walk v t, (Walk.cons h q).IsTrail ∧ IsMember S (Walk.cons h q) := by
  obtain ⟨i,hi⟩ := (T.cover s(u,v)).mp h
  obtain ⟨a,b,hab,A,B,hee,he⟩ := walk_split_at_edge (T.walk i) s(u,v)
    ((T.walk i).mem_edges_toSubgraph.mp hi)
  have hp : (A.append (Walk.cons hab B)).IsTrail := he ▸ T.isTrail i
  have hm : IsMember T (A.append (Walk.cons hab B)) := he ▸ isMember_walk T i
  rcases Sym2.eq_iff.mp hee with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact force_first_of_split T hmax A h B hp hm
  · have hpr := hp.reverse
    have hmr := isMember_reverse hm
    rw [Walk.reverse_append,Walk.reverse_cons,← Walk.append_assoc,Walk.cons_nil_append] at hpr hmr
    exact force_first_of_split T hmax B.reverse h A.reverse hpr hmr

lemma max_score_member_isPath {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail) (hm : IsMember T p) : p.IsPath := by
  by_contra hn
  obtain ⟨v,A,C,B,hC,he⟩ := walk_not_path_has_closed_segment p hn
  exact no_closed_segment A T hmax C B hC (he ▸ hp) (he ▸ hm)

lemma all_odd_prescribed_first_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) {u v : V} (h : G.Adj u v) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card = Fintype.card V ∧
      ∃ t, ∃ q : G.Walk v t, (Walk.cons h q).IsPath ∧ (Walk.cons h q).toSubgraph ∈ D := by
  classical
  obtain ⟨k,hk,⟨T⟩⟩ := all_odd_normal_trail_system G ho
  obtain ⟨R,hR⟩ := T.exists_max_score
  obtain ⟨S,hS,t,q,hq,hm⟩ := force_first_edge R hR h
  have hSmax : ∀ U : NormalTrailSystem G k, U.score ≤ S.score := by
    intro U; rw [hS]; exact hR U
  have hpaths := max_score_isPath S hSmax
  let D := NormalTrailSystem.parts S
  have hgood : GoodDecomposition G D := by
    refine ⟨?_,NormalTrailSystem.parts_decomposition S⟩
    intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨_,_,_,hpaths i,rfl⟩
  have hcard : D.card = k := by
    dsimp [D,NormalTrailSystem.parts]
    rw [Finset.card_image_of_injective _ (NormalTrailSystem.subgraph_injective S)]
    simp
  have hpq := max_score_member_isPath S hSmax _ hq hm
  obtain ⟨i,_,hi⟩ := hm
  refine ⟨D,hgood,by omega,t,q,hpq,?_⟩
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩

lemma all_odd_prescribed_leaf_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) {u v : V} (h : G.Adj u v)
    (hleaf : ∀ w, G.Adj v w → w=u) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card = Fintype.card V ∧
      G.subgraphOfAdj h ∈ D := by
  obtain ⟨D,hD,hcard,t,q,hq,hmem⟩ := all_odd_prescribed_first_edge G ho h
  have hn : q.Nil := by
    by_contra hn
    have hqu : q.snd = u := hleaf _ (q.adj_snd hn)
    have hu : u ∈ q.support := hqu ▸ q.getVert_mem_support 1
    exact (Walk.cons_isPath_iff h q).mp hq |>.2 hu
  cases hn
  exact ⟨D,hD,hcard,by simpa using hmem⟩

lemma all_odd_delete_single_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) {u v : V} (h : G.Adj u v) :
    ∃ E : Finset (G.deleteEdges {s(u,v)}).Subgraph,
      GoodDecomposition (G.deleteEdges {s(u,v)}) E ∧ 2*E.card ≤ Fintype.card V := by
  classical
  obtain ⟨D,hD,hcard,t,q,hq,hmem⟩ := all_odd_prescribed_first_edge G ho h
  let J := G.deleteEdges {s(u,v)}
  have hcompat : ∀ H ∈ D, ∃ a b, ∃ p : G.Walk a b,
      p.IsPath ∧ H = p.toSubgraph ∧ ∀ d ∈ p.edges.tail.dropLast, d ∈ J.edgeSet := by
    intro H hH
    by_cases he : H = (Walk.cons h q).toSubgraph
    · refine ⟨u,t,Walk.cons h q,hq,he,?_⟩
      intro d hd
      have hdq : d ∈ q.edges := List.mem_of_mem_dropLast hd
      have hneq : d ≠ s(u,v) := fun hh ↦
        (Walk.isTrail_cons h q).mp hq.isTrail |>.2 (hh ▸ hdq)
      rw [show J = G.deleteEdges {s(u,v)} from rfl,edgeSet_deleteEdges]
      exact ⟨q.edges_subset_edgeSet hdq,by simpa using hneq⟩
    · obtain ⟨a,b,p,hp,hpe⟩ := hD.1 H hH
      refine ⟨a,b,p,hp,hpe,?_⟩
      intro d hd
      have hdp : d ∈ p.edges := List.mem_of_mem_tail (List.mem_of_mem_dropLast hd)
      have hneq : d ≠ s(u,v) := by
        intro hh
        have h1 : s(u,v) ∈ H.edgeSet := by rw [hpe]; exact p.mem_edges_toSubgraph.mpr (hh ▸ hdp)
        have h2 : s(u,v) ∈ (Walk.cons h q).toSubgraph.edgeSet := by
          simpa only [Walk.snd_cons] using (Walk.cons h q).toSubgraph_adj_snd (by simp)
        exact Set.disjoint_left.mp (hD.2.1 hH hmem he) h1 h2
      rw [show J = G.deleteEdges {s(u,v)} from rfl,edgeSet_deleteEdges]
      exact ⟨p.edges_subset_edgeSet hdp,by simpa using hneq⟩
  obtain ⟨E,hE,hEcard⟩ := hD.restrict_terminal_edges (G.deleteEdges_le {s(u,v)}) hcompat
  exact ⟨E,hE,by omega⟩

end Erdos583ForceDevelopment
