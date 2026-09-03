import Submission.CycleRing

/-!
Lifting simple kernel cycles through mutually private path replacements.
The injectivity and privacy conditions are explicit: a closed trail is not
silently treated as a simple cycle. This is auxiliary, not a linear bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.PrivatePathLifting

variable {U V : Type*} {K : SimpleGraph U} {G : SimpleGraph V}

lemma step_edge {u v : U} (c : K.Walk u v) (i : ℕ) (hi : i < c.length) :
    c.edges[i]'(by simpa using hi) = s(c.getVert i, c.getVert (i+1)) := by
  simp only [Walk.edges, List.getElem_map, Walk.darts_getElem_eq_getVert]
  rfl

lemma step_edge_mem {u v : U} (c : K.Walk u v) (i : ℕ) (hi : i < c.length) :
    s(c.getVert i, c.getVert (i+1)) ∈ c.edges := by
  rw [← step_edge c i hi]
  exact List.getElem_mem _

lemma steps_distinct {u : U} (c : K.Walk u u) (hc : c.IsCycle)
    (i j : ℕ) (hi : i < c.length) (hj : j < c.length) (hij : i ≠ j) :
    s(c.getVert i, c.getVert (i+1)) ≠ s(c.getVert j, c.getVert (j+1)) := by
  rw [← step_edge c i hi, ← step_edge c j hj]
  exact fun he => hij (hc.isTrail.edges_nodup.getElem_inj_iff.mp he)

lemma ends_injective {u : U} (c : K.Walk u u) (hc : c.IsCycle)
    (i j : ℕ) (hi : i < c.length) (hj : j < c.length)
    (he : c.getVert (i+1) = c.getVert (j+1)) : i = j := by
  have hti : i < c.support.tail.length := by simp; omega
  have htj : j < c.support.tail.length := by simp; omega
  have he' : c.support.tail[i]'hti = c.support.tail[j]'htj := by
    rw [List.getElem_tail, List.getElem_tail,
      ← c.getVert_eq_support_getElem (by omega),
      ← c.getVert_eq_support_getElem (by omega)]
    exact he
  exact hc.support_nodup.getElem_inj_iff.mp he'

/-- An edge replacement model with pairwise private path interiors. -/
structure Model (K : SimpleGraph U) (G : SimpleGraph V) where
  vertex : U → V
  vertex_injective : Function.Injective vertex
  path : ∀ {u v : U}, K.Adj u v → G.Walk (vertex u) (vertex v)
  isPath : ∀ {u v : U} (h : K.Adj u v), (path h).IsPath
  disjoint_edges : ∀ {u v a b : U} (h : K.Adj u v) (k : K.Adj a b),
    s(u,v) ≠ s(a,b) → (path h).edges.Disjoint (path k).edges
  private_intersection : ∀ {u v a b : U} (h : K.Adj u v) (k : K.Adj a b),
    s(u,v) ≠ s(a,b) → ∀ x,
      x ∈ (path h).support → x ∈ (path k).support →
      x = vertex u ∨ x = vertex v
  symmetric_edges : ∀ {u v : U} (h : K.Adj u v) (e : Sym2 V),
    e ∈ (path h).edges ↔ e ∈ (path h.symm).edges

namespace Model

variable (M : Model K G)

/-- Follow a kernel closed walk through its chosen oriented replacement paths. -/
def lift {u : U} (c : K.Walk u u) : G.Walk (M.vertex u) (M.vertex u) :=
  (CycleRing.chain (fun i => M.vertex (c.getVert i)) c.length
    (fun i hi => M.path (c.adj_getVert_succ hi))).copy
      (by simp) (by simp)

lemma mem_lift_edges {u : U} (c : K.Walk u u) (e : Sym2 V) :
    e ∈ (M.lift c).edges ↔
      ∃ i, ∃ hi : i < c.length, e ∈ (M.path (c.adj_getVert_succ hi)).edges := by
  simp only [lift, Walk.edges_copy, CycleRing.mem_edges_chain]

lemma lift_isCycle {u : U} (c : K.Walk u u) (hc : c.IsCycle) :
    (M.lift c).IsCycle := by
  have hn : 0 < c.length := by
    have hh := hc.not_nil
    simpa only [Walk.not_nil_iff_lt_length] using hh
  have hne : M.vertex (c.getVert 0) ≠ M.vertex (c.getVert 1) := by
    exact fun he => (c.adj_getVert_succ hn).ne (M.vertex_injective he)
  have he : ∀ (i : ℕ) (hi : i < c.length) (j : ℕ) (hj : j < c.length), i ≠ j →
      (M.path (c.adj_getVert_succ hi)).edges.Disjoint
        (M.path (c.adj_getVert_succ hj)).edges := by
    intro i hi j hj hij
    exact M.disjoint_edges _ _ (steps_distinct c hc i j hi hj hij)
  have ht : ∀ (i : ℕ) (hi : i < c.length) (j : ℕ) (hj : j < c.length), i ≠ j →
      (M.path (c.adj_getVert_succ hi)).support.tail.Disjoint
        (M.path (c.adj_getVert_succ hj)).support.tail := by
    intro i hi j hj hij x hxi hxj
    have hi0 : M.vertex (c.getVert i) ∉
        (M.path (c.adj_getVert_succ hi)).support.tail := by
      have hh := (M.isPath (c.adj_getVert_succ hi)).support_nodup
      rw [Walk.support_eq_cons, List.nodup_cons] at hh
      exact hh.1
    have hj0 : M.vertex (c.getVert j) ∉
        (M.path (c.adj_getVert_succ hj)).support.tail := by
      have hh := (M.isPath (c.adj_getVert_succ hj)).support_nodup
      rw [Walk.support_eq_cons, List.nodup_cons] at hh
      exact hh.1
    have hix : x = M.vertex (c.getVert (i+1)) := by
      rcases M.private_intersection _ _ (steps_distinct c hc i j hi hj hij) x
        (List.mem_of_mem_tail hxi) (List.mem_of_mem_tail hxj) with h | h
      · exact (hi0 (h ▸ hxi)).elim
      · exact h
    have hjx : x = M.vertex (c.getVert (j+1)) := by
      rcases M.private_intersection _ _ (steps_distinct c hc j i hj hi hij.symm) x
        (List.mem_of_mem_tail hxj) (List.mem_of_mem_tail hxi) with h | h
      · exact (hj0 (h ▸ hxj)).elim
      · exact h
    exact hij (ends_injective c hc i j hi hj
      (M.vertex_injective (hix.symm.trans hjx)))
  have hcycle := CycleRing.chain_isCycle (fun i => M.vertex (c.getVert i)) c.length
    (fun i hi => M.path (c.adj_getVert_succ hi)) (by simp) hn hne
    (fun i hi => M.isPath _) he ht
  have hcopy := (Walk.isCycle_copy _
    (show M.vertex (c.getVert 0) = M.vertex u by simp)).mpr hcycle
  simpa only [lift, Walk.copy_copy] using hcopy

lemma lift_disjoint {u v : U} (c : K.Walk u u) (d : K.Walk v v)
    (hd : c.edges.Disjoint d.edges) : (M.lift c).edges.Disjoint (M.lift d).edges := by
  intro e hec hed
  obtain ⟨i, hi, hei⟩ := (M.mem_lift_edges c e).mp hec
  obtain ⟨j, hj, hej⟩ := (M.mem_lift_edges d e).mp hed
  have hne : s(c.getVert i, c.getVert (i+1)) ≠ s(d.getVert j, d.getVert (j+1)) := by
    intro heq
    exact hd (step_edge_mem c i hi) (heq ▸ step_edge_mem d j hj)
  exact M.disjoint_edges _ _ hne hei hej

lemma mem_lift_edges_iff {u : U} (c : K.Walk u u) (e : Sym2 V) :
    e ∈ (M.lift c).edges ↔
      ∃ a b, ∃ h : K.Adj a b, s(a,b) ∈ c.edges ∧ e ∈ (M.path h).edges := by
  constructor
  · intro he
    obtain ⟨i, hi, hei⟩ := (M.mem_lift_edges c e).mp he
    exact ⟨c.getVert i, c.getVert (i+1), c.adj_getVert_succ hi,
      step_edge_mem c i hi, hei⟩
  · rintro ⟨a, b, h, hec, hep⟩
    obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp hec
    have hi' : i < c.length := by simpa using hi
    have hes : s(c.getVert i,c.getVert (i+1)) = s(a,b) :=
      (step_edge c i hi').symm.trans hei
    apply (M.mem_lift_edges c e).mpr
    refine ⟨i, hi', ?_⟩
    rcases Sym2.eq_iff.mp hes with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · subst a
      subst b
      exact hep
    · subst b
      subst a
      exact (M.symmetric_edges (c.adj_getVert_succ hi') e).mpr hep

/-- If the kernel is covered by two cycles, the two lifts cover every
replacement edge. The ambient graph is allowed to have isolated vertices. -/
lemma lift_pair_cover {u v : U} (c : K.Walk u u) (d : K.Walk v v)
    (hcd : ∀ e, e ∈ c.edges ∨ e ∈ d.edges ↔ e ∈ K.edgeSet)
    (hG : ∀ e ∈ G.edgeSet, ∃ a b, ∃ h : K.Adj a b, e ∈ (M.path h).edges) :
    ∀ e, e ∈ (M.lift c).edges ∨ e ∈ (M.lift d).edges ↔ e ∈ G.edgeSet := by
  intro e
  constructor
  · rintro (h | h)
    · exact (M.lift c).edges_subset_edgeSet h
    · exact (M.lift d).edges_subset_edgeSet h
  · intro he
    obtain ⟨a,b,h,hp⟩ := hG e he
    rcases (hcd s(a,b)).mpr h with hce | hde
    · exact Or.inl ((M.mem_lift_edges_iff c e).mpr ⟨a,b,h,hce,hp⟩)
    · exact Or.inr ((M.mem_lift_edges_iff d e).mpr ⟨a,b,h,hde,hp⟩)

/-- A two-cycle partition survives arbitrary mutually private subdivisions. -/
theorem two_cycle_decomposition [Fintype V] {u v : U}
    (c : K.Walk u u) (d : K.Walk v v) (hc : c.IsCycle) (hd : d.IsCycle)
    (hdis : c.edges.Disjoint d.edges)
    (hcd : ∀ e, e ∈ c.edges ∨ e ∈ d.edges ↔ e ∈ K.edgeSet)
    (hG : ∀ e ∈ G.edgeSet, ∃ a b, ∃ h : K.Adj a b, e ∈ (M.path h).edges) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ 2 := by
  let P := M.lift c
  let Q := M.lift d
  let E : Finset G.Subgraph := {P.toSubgraph, Q.toSubgraph}
  have hP : P.IsCycle := M.lift_isCycle c hc
  have hQ : Q.IsCycle := M.lift_isCycle d hd
  have hpq : P.edges.Disjoint Q.edges := M.lift_disjoint c d hdis
  have hcov := M.lift_pair_cover c d hcd hG
  have hh : ∀ H, H ∈ E ↔ H = P.toSubgraph ∨ H = Q.toSubgraph := by
    intro H
    simp [E]
  refine ⟨E, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases (hh H).mp hH with rfl | rfl
    · exact cycle_subgraph_regular G hP
    · exact cycle_subgraph_regular G hQ
  · have hdis' : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heP heQ
      exact hpq (P.mem_edges_toSubgraph.mp heP) (Q.mem_edges_toSubgraph.mp heQ)
    intro H hH J hJ hne
    rcases (hh H).mp hH with rfl | rfl <;> rcases (hh J).mp hJ with rfl | rfl
    · exact (hne rfl).elim
    · exact hdis'
    · exact hdis'.symm
    · exact (hne rfl).elim
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,hH,heH⟩
      exact H.edgeSet_subset heH
    · intro he
      rcases (hcov e).mpr he with heP | heQ
      · exact ⟨P.toSubgraph, (hh _).mpr (Or.inl rfl), P.mem_edges_toSubgraph.mpr heP⟩
      · exact ⟨Q.toSubgraph, (hh _).mpr (Or.inr rfl), Q.mem_edges_toSubgraph.mpr heQ⟩
  · exact (Finset.card_insert_le _ _).trans (by simp)

/-- Packing version: no assumption that the paths cover the ambient graph. -/
theorem two_cycle_replacement [Fintype V] {u v : U}
    (c : K.Walk u u) (d : K.Walk v v) (hc : c.IsCycle) (hd : d.IsCycle)
    (hdis : c.edges.Disjoint d.edges)
    (hcd : ∀ e, e ∈ c.edges ∨ e ∈ d.edges ↔ e ∈ K.edgeSet) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ e, e ∈ (⋃ H ∈ E, H.edgeSet) ↔
        ∃ a b, ∃ h : K.Adj a b, e ∈ (M.path h).edges) ∧ E.card ≤ 2 := by
  let P := M.lift c
  let Q := M.lift d
  let E : Finset G.Subgraph := {P.toSubgraph, Q.toSubgraph}
  have hpq : P.edges.Disjoint Q.edges := M.lift_disjoint c d hdis
  have hh : ∀ H, H ∈ E ↔ H = P.toSubgraph ∨ H = Q.toSubgraph := by
    intro H
    simp [E]
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro H hH
    rcases (hh H).mp hH with rfl | rfl
    · exact cycle_subgraph_regular G (M.lift_isCycle c hc)
    · exact cycle_subgraph_regular G (M.lift_isCycle d hd)
  · have hdis' : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heP heQ
      exact hpq (P.mem_edges_toSubgraph.mp heP) (Q.mem_edges_toSubgraph.mp heQ)
    intro H hH J hJ hne
    rcases (hh H).mp hH with rfl | rfl <;> rcases (hh J).mp hJ with rfl | rfl
    · exact (hne rfl).elim
    · exact hdis'
    · exact hdis'.symm
    · exact (hne rfl).elim
  · intro e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,hH,heH⟩
      rcases (hh H).mp hH with rfl | rfl
      · obtain ⟨a,b,h,_,hp⟩ := (M.mem_lift_edges_iff c e).mp (P.mem_edges_toSubgraph.mp heH)
        exact ⟨a,b,h,hp⟩
      · obtain ⟨a,b,h,_,hp⟩ := (M.mem_lift_edges_iff d e).mp (Q.mem_edges_toSubgraph.mp heH)
        exact ⟨a,b,h,hp⟩
    · rintro ⟨a,b,h,hp⟩
      rcases (hcd s(a,b)).mpr h with hce | hde
      · exact ⟨P.toSubgraph, (hh _).mpr (Or.inl rfl), P.mem_edges_toSubgraph.mpr
          ((M.mem_lift_edges_iff c e).mpr ⟨a,b,h,hce,hp⟩)⟩
      · exact ⟨Q.toSubgraph, (hh _).mpr (Or.inr rfl), Q.mem_edges_toSubgraph.mpr
          ((M.mem_lift_edges_iff d e).mpr ⟨a,b,h,hde,hp⟩)⟩
  · exact (Finset.card_insert_le _ _).trans (by simp)

/-- A subfamily of a global minimum cannot be larger than its two-cycle
private-path kernel replacement. -/
theorem minimum_subfamily_bound [Fintype V] {u v : U}
    (c : K.Walk u u) (d : K.Walk v v) (hc : c.IsCycle) (hd : d.IsCycle)
    (hdis : c.edges.Disjoint d.edges)
    (hcd : ∀ e, e ∈ c.edges ∨ e ∈ d.edges ↔ e ∈ K.edgeSet)
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D)
    (hmin : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (S : Finset G.Subgraph) (hS : S ⊆ D)
    (hcover : ∀ e, e ∈ (⋃ H ∈ S, H.edgeSet) ↔
      ∃ a b, ∃ h : K.Adj a b, e ∈ (M.path h).edges) : S.card ≤ 2 := by
  obtain ⟨E,hE,hdisE,hcovE,hcard⟩ := M.two_cycle_replacement c d hc hd hdis hcd
  have hcov : (⋃ H ∈ E, H.edgeSet) = ⋃ H ∈ S, H.edgeSet := by
    ext e
    exact (hcovE e).trans (hcover e).symm
  exact (minimum_cycle_subfamily G D hD hdec hmin S E hS hE hdisE hcov).trans hcard

end Model
end Erdos184.PrivatePathLifting
