import Submission.Work

/-! A sufficient condition for Gallai's bound in Eulerian graphs: the maximum
degree is smaller than the girth. No assertion about arbitrary graphs is made. -/
namespace Erdos583EulerianGirthBoundDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma maximum_trail_endpoint_edges {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (P : G.Walk a b) (hP : P.IsTrail)
    (hm : ∀ x y (Q : G.Walk x y), Q.IsTrail → Q.length ≤ P.length)
    {x : V} (hx : G.Adj b x) : s(b,x) ∈ P.toSubgraph.edgeSet := by
  by_contra hn
  have hq : (P.concat hx).IsTrail := by
    rw [Walk.isTrail_def,Walk.edges_concat,List.concat_eq_append,List.nodup_append]
    refine ⟨hP.edges_nodup,by simp,?_⟩
    intro e he f hf hef
    have hf' : f=s(b,x) := by simpa using hf
    have heq : e=s(b,x) := hef.trans hf'
    exact hn (P.mem_edges_toSubgraph.mpr (heq ▸ he))
  have hh := hm a x (P.concat hx) hq
  simp only [Walk.length_concat] at hh
  omega

lemma connected_even_has_eulerian {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (he : ∀ v, Even (Nat.card (G.neighborSet v))) :
    ∃ r : V, ∃ P : G.Walk r r, P.IsEulerian := by
  classical
  letI : Nonempty V := hG.nonempty
  obtain ⟨a,b,P,hP,hm⟩ := Walk.exists_isTrail_forall_isTrail_length_le_length G
  have hbN : P.toSubgraph.neighborSet b=G.neighborSet b := by
    ext x
    constructor
    · exact P.toSubgraph.adj_sub
    · intro hx
      exact maximum_trail_endpoint_edges P hP hm hx
  have hab : a=b := by
    by_contra hn
    have hp := (trail_neighbor_ncard_odd_iff hP b).mpr ⟨hn,Or.inr rfl⟩
    rw [hbN] at hp
    have hh := he b
    simp only [Nat.card_coe_set_eq] at hh
    exact Nat.not_even_iff_odd.mpr hp hh
  subst b
  have hall (x : V) (hx : x ∈ P.toSubgraph.verts) (y : V) (hxy : G.Adj x y) :
      s(x,y) ∈ P.toSubgraph.edgeSet := by
    have hxP := P.mem_verts_toSubgraph.mp hx
    let Q := P.rotate hxP
    have hQ : Q.IsTrail := hP.rotate hxP
    have hQP : Q.toSubgraph=P.toSubgraph := P.toSubgraph_rotate hxP
    have hlen : Q.length=P.length := by
      rw [←trail_edgeSet_ncard Q hQ,hQP,trail_edgeSet_ncard P hP]
    have hQm : ∀ u v (R : G.Walk u v), R.IsTrail → R.length ≤ Q.length := by
      intro u v R hR
      rw [hlen]
      exact hm u v R hR
    rw [←hQP]
    exact maximum_trail_endpoint_edges Q hQ hQm hxy
  have hverts : P.toSubgraph.verts=Set.univ :=
    TrailBudget.connected_closed_set hG P.toSubgraph.verts
      ⟨a,P.start_mem_verts_toSubgraph⟩ (by
        intro x y hxy hx
        exact P.toSubgraph.edge_vert (P.toSubgraph.adj_symm (hall x hx y hxy)))
  refine ⟨a,P,hP.isEulerian_of_forall_mem ?_⟩
  intro e heG
  induction e using Sym2.ind with
  | h x y =>
    exact P.mem_edges_toSubgraph.mp (hall x (by rw [hverts]; trivial) y heG)

lemma short_trail_isPath {V : Type*} {G : SimpleGraph V} (d : ℕ)
    (hg : ∀ r (C : G.Walk r r), C.IsCycle → d < C.length)
    {a b : V} (P : G.Walk a b) (hP : P.IsTrail) (hlen : P.length ≤ d) :
    P.IsPath := by
  classical
  induction P with
  | nil => simp
  | @cons a x b h Q ih =>
    have hQt := (Walk.isTrail_cons h Q).mp hP
    have hQl : Q.length ≤ d := by
      simp only [Walk.length_cons] at hlen
      omega
    have hQ := ih hQt.1 hQl
    apply (Walk.cons_isPath_iff h Q).mpr
    refine ⟨hQ,?_⟩
    intro ha
    let R := Q.takeUntil a ha
    have hR : R.IsPath := hQ.takeUntil ha
    have hCt : (Walk.cons h R).IsTrail := by
      apply (Walk.isTrail_cons h R).mpr
      refine ⟨hR.isTrail,?_⟩
      intro he
      exact hQt.2 ((Q.edges_takeUntil_subset ha) he)
    have hC : (Walk.cons h R).IsCycle :=
      (Walk.cons_isCycle_iff R h).mpr ⟨hR,(Walk.isTrail_cons h R).mp hCt |>.2⟩
    have hbound : (Walk.cons h R).length ≤ (Walk.cons h Q).length := by
      have hh := Q.length_takeUntil_le ha
      simpa only [Walk.length_cons] using Nat.add_le_add_right hh 1
    have hh := hg a (Walk.cons h R) hC
    omega

lemma trail_path_pieces {V : Type*} [Fintype V] {G : SimpleGraph V}
    (d : ℕ)
    (hg : ∀ r (C : G.Walk r r), C.IsCycle → d < C.length)
    (k : ℕ) {a b : V} (P : G.Walk a b) (hP : P.IsTrail) (hlen : P.length ≤ d*k) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
      (⋃ H ∈ D, H.edgeSet)=P.toSubgraph.edgeSet ∧ D.card ≤ k := by
  classical
  induction k generalizing a b with
  | zero =>
    have hn : P.Nil := Walk.nil_iff_length_eq.mpr (by simpa using hlen)
    have he : P.toSubgraph.edgeSet=∅ := by
      cases hn
      simp
    exact ⟨∅,by simp,by simp [Set.PairwiseDisjoint],by simp [he],by simp⟩
  | succ k ih =>
    by_cases hl : P.length ≤ d
    · exact ⟨{P.toSubgraph},by simpa using
        (show IsPathSubgraph P.toSubgraph from ⟨a,b,P,short_trail_isPath d hg P hP hl,rfl⟩),
        by simp [Set.PairwiseDisjoint],by simp,by simp⟩
    let A := P.take d
    let B := P.drop d
    have hAB : A.append B=P := P.append_take_drop_eq d
    have hAt : A.IsTrail := Walk.IsTrail.of_append_left (hAB.symm ▸ hP)
    have hBt : B.IsTrail := Walk.IsTrail.of_append_right (hAB.symm ▸ hP)
    have hAl : A.length=d := by
      rw [Walk.take_length]
      exact min_eq_left (by omega)
    have hBl : B.length ≤ d*k := by
      simp only [B,Walk.drop_length]
      rw [Nat.mul_succ] at hlen
      omega
    have hAp : A.IsPath := short_trail_isPath d hg A hAt hAl.le
    obtain ⟨D,hD,hdis,hcover,hcard⟩ := ih B hBt hBl
    have hcross : ∀ H ∈ D, Disjoint A.toSubgraph.edgeSet H.edgeSet := by
      intro H hH
      apply Set.disjoint_left.mpr
      intro e heA heH
      have heB : e ∈ B.toSubgraph.edgeSet := by
        rw [←hcover]
        exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,heH⟩⟩
      have ht := (hAB.symm ▸ hP).edges_nodup
      rw [Walk.edges_append,List.nodup_append] at ht
      exact ht.2.2 e (A.mem_edges_toSubgraph.mp heA) e (B.mem_edges_toSubgraph.mp heB) rfl
    refine ⟨insert A.toSubgraph D,?_,?_,?_,(Finset.card_insert_le _ _).trans (by omega)⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl|hH
      · exact ⟨_,_,A,hAp,rfl⟩
      · exact hD H hH
    · rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
      exact ⟨hdis,fun H hH _ ↦ hcross H hH⟩
    · rw [Finset.set_biUnion_insert,hcover]
      calc
        A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet = (A.append B).toSubgraph.edgeSet := by simp
        _ = P.toSubgraph.edgeSet := congrArg (fun Q ↦ Q.toSubgraph.edgeSet) hAB

lemma eulerian_girth_edge_budget {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (he : ∀ v, Even (Nat.card (G.neighborSet v)))
    (d k : ℕ) (hm : G.edgeSet.ncard ≤ d*k)
    (hg : ∀ r (C : G.Walk r r), C.IsCycle → d < C.length) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  obtain ⟨r,P,hP⟩ := connected_even_has_eulerian G hG he
  have hPe : P.toSubgraph.edgeSet=G.edgeSet := by
    ext e
    exact P.mem_edges_toSubgraph.trans hP.mem_edges_iff
  have hPl : P.length=G.edgeSet.ncard := by
    rw [←trail_edgeSet_ncard P hP.isTrail,hPe]
  obtain ⟨D,hD,hdis,hcover,hcard⟩ := trail_path_pieces d hg k P hP.isTrail
    (by rwa [hPl])
  exact ⟨D,⟨hD,hdis,hcover.trans hPe⟩,hcard⟩

lemma eulerian_average_degree_girth_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (he : ∀ v, Even (Nat.card (G.neighborSet v)))
    (d : ℕ) (hm : 2*G.edgeSet.ncard ≤ d*Fintype.card V)
    (hg : ∀ r (C : G.Walk r r), C.IsCycle → d < C.length) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  have hc : Fintype.card V ≤ 2*⌈(Fintype.card V : ℚ)/2⌉₊ := by
    rw [BridgeGlue.ceil_half]
    omega
  exact eulerian_girth_edge_budget G hG he d ⌈(Fintype.card V : ℚ)/2⌉₊
    (by nlinarith) hg

lemma eulerian_high_girth_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (he : ∀ v, Even (Nat.card (G.neighborSet v)))
    (d : ℕ) (hdeg : ∀ v, Nat.card (G.neighborSet v) ≤ d)
    (hg : ∀ r (C : G.Walk r r), C.IsCycle → d < C.length) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  apply eulerian_average_degree_girth_bound G hG he d _ hg
  rw [←GlobalCritical.sum_neighbor_ncard]
  have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ hdeg v)
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm] using hh

lemma eulerian_failure_short_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (he : ∀ v, Even (Nat.card (G.neighborSet v)))
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (d : ℕ) (hm : 2*G.edgeSet.ncard ≤ d*Fintype.card V) :
    ∃ r : V, ∃ C : G.Walk r r, C.IsCycle ∧ C.length ≤ d := by
  by_contra hn
  push_neg at hn
  exact hf (eulerian_average_degree_girth_bound G hG he d hm hn)

end Erdos583EulerianGirthBoundDevelopment
