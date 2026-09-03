import Submission.CountCritical

/-!
A longest-path argument gives a degree-two vertex in every nonempty even
simple graph with invariant cycle-partition count. This is a restricted-class
result; fixed-count criticality is not assumed to imply invariance.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InvariantPartitions
open StarElimination

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- The initial vertex of a longest path of positive length is supported. -/
lemma longest_path_start_supported {G : SimpleGraph V} (hne : G ≠ ⊥)
    {u v : V} (p : G.Walk u v)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    u ∈ G.support := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hl := hm a b (Walk.cons hab Walk.nil) (by simpa using hab.ne)
  cases p with
  | nil => simp at hl
  | cons h q => exact ⟨_,h⟩

/-- Every initial vertex of a longest path has degree two under the
two-vertex intersection restriction. -/
lemma longest_path_start_degree_two_of_intersection_le_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ x y (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    G.degree u = 2 := by
  have hu := longest_path_start_supported hne p hm
  have hpos := (G.degree_pos_iff_mem_support u).mpr hu
  by_cases hdu : G.degree u ≤ 2
  · obtain ⟨k,hk⟩ := he u
    omega
  have hs := longest_path_start_neighbors p hp hm
  have hneN : (Finset.univ : Finset (G.neighborSet u)).Nonempty := by
    obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj u).mp hpos
    exact ⟨⟨w,hw⟩,Finset.mem_univ _⟩
  let f : G.neighborSet u → ℕ := fun x => (p.takeUntil x.val (hs x.val x.property)).length
  obtain ⟨x,_,hx⟩ := Finset.univ.exists_max_image f hneN
  let q := p.takeUntil x.val (hs x.val x.property)
  have hq : q.IsPath := hp.takeUntil _
  have hnq : ∀ y, G.Adj u y → y ∈ q.support := by
    intro y hy
    have hle : f ⟨y,hy⟩ ≤ q.length := hx ⟨y,hy⟩ (Finset.mem_univ _)
    have hvq := q.getVert_mem_support (f ⟨y,hy⟩)
    rw [show q.getVert (f ⟨y,hy⟩) = y from
      (Walk.getVert_takeUntil (hs x.val x.property) hle).trans
        (p.getVert_length_takeUntil (hs y hy))] at hvq
    exact hvq
  have hlen : 2 ≤ q.length := by
    have hsub : G.neighborFinset u ⊆ q.support.toFinset := by
      intro y hy
      exact List.mem_toFinset.mpr (hnq y (G.mem_neighborFinset u y |>.mp hy))
    have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le q.support)
    rw [card_neighborFinset_eq_degree, Walk.length_support] at hcard
    omega
  let c := q.cons x.property.symm
  have hcy : c.IsCycle := path_close_isCycle q hq hlen x.property.symm
  have hcc := cycle_subgraph_regular G hcy
  have huC : u ∈ c.toSubgraph.verts := by
    apply c.mem_verts_toSubgraph.mpr
    simp only [c,Walk.support_cons,List.mem_cons]
    exact Or.inr q.start_mem_support
  have hnC : ∀ y, G.Adj u y → y ∈ c.toSubgraph.verts := by
    intro y hy
    apply c.mem_verts_toSubgraph.mpr
    simp only [c,Walk.support_cons,List.mem_cons]
    exact Or.inr (hnq y hy)
  obtain ⟨D,hcD,hdD,hCD,_⟩ := CountCritical.cycle_lift he c.toSubgraph hcc
  have hstar := star_card D hcD hdD u
  have htwo : 1 < (star D u).card := by omega
  obtain ⟨K,hKs,hKC⟩ := Finset.exists_mem_ne htwo c.toSubgraph
  obtain ⟨hKD,huK⟩ := (mem_star D u K).mp hKs
  have hdCK : Disjoint c.toSubgraph.edgeSet K.edgeSet := hdD.1 hCD hKD (Ne.symm hKC)
  have hdegK := (hcD K hKD).2 ⟨u,huK⟩
  rw [Subgraph.coe_degree] at hdegK
  have hnK : (K.neighborSet u).ncard = 2 := by
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hdegK
  obtain ⟨y,hy,z,hz,hyz⟩ := (Set.one_lt_ncard (s := K.neighborSet u)).mp (show 1 < (K.neighborSet u).ncard by omega)
  have huy : u ≠ y := (K.adj_sub hy).ne
  have huz : u ≠ z := (K.adj_sub hz).ne
  have hsub : ({u,y,z} : Finset V) ⊆ (c.toSubgraph.verts ∩ K.verts).toFinset := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    apply Set.mem_toFinset.mpr
    rcases hw with rfl | rfl | rfl
    · exact ⟨huC,huK⟩
    · exact ⟨hnC _ (K.adj_sub hy),K.edge_vert (K.symm hy)⟩
    · exact ⟨hnC _ (K.adj_sub hz),K.edge_vert (K.symm hz)⟩
  have hlower := Finset.card_le_card hsub
  have hupper := hi c.toSubgraph K hcc (hcD K hKD) hdCK
  have hcard : ({u,y,z} : Finset V).card = 3 := by simp [huy,huz,hyz]
  rw [hcard] at hlower
  rw [← Set.ncard_eq_toFinset_card'] at hlower
  omega

/-- Every nonempty even simple graph in which edge-disjoint cycles share at
most two vertices has a vertex of degree two. -/
lemma exists_degree_two_of_intersection_le_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2) :
    ∃ v, G.degree v = 2 := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  letI : Nonempty V := ⟨a⟩
  obtain ⟨u,v,p,hp,hm⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  exact ⟨u,longest_path_start_degree_two_of_intersection_le_two G he hne hi p hp hm⟩

lemma HasInvariantCount.exists_degree_two {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥) :
    ∃ v, G.degree v = 2 :=
  exists_degree_two_of_intersection_le_two G he hne (hi.intersection_le_two he)

/-- The intersection restriction passes to arbitrary edge subgraphs. -/
lemma intersection_le_two_of_le {A G : SimpleGraph V} (hAG : A ≤ G)
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2)
    (H K : A.Subgraph)
    (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hd : Disjoint H.edgeSet K.edgeSet) : (H.verts ∩ K.verts).ncard ≤ 2 := by
  apply hi (promote hAG H) (promote hAG K)
  · simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcH
  · simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcK
  · exact hd

/-- A linear bound under the hereditary two-vertex intersection restriction. -/
lemma bound_of_intersection_le_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v))
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      exact ⟨∅,by simp,by simp [IsDecomposition],by simp⟩
    obtain ⟨v,hv⟩ := exists_degree_two_of_intersection_le_two G he hbot hi
    obtain ⟨P,⟨hP,hc,hd,_,hcost⟩,hcard⟩ := eliminating_packing_of_degree_two G he v hv
    have hlt : (G \ unionPieces G P).support.ncard < n := by omega
    have her := even_residual_of_cycle_packing G he P hc hd
    have hir := intersection_le_two_of_le (A := G \ unionPieces G P) (G := G) sdiff_le hi
    obtain ⟨F,hcF,hdF,hbF⟩ := ih _ hlt (G \ unionPieces G P)
      (by
        intro w
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her w)
      hir rfl
    obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hc hd F (by
      intro H hH
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcF H hH) hdF
    exact ⟨D,hcD,hdD,by omega⟩

lemma HasInvariantCount.exists_bounded_decomposition {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ G.support.ncard :=
  bound_of_intersection_le_two G he (hi.intersection_le_two he)

lemma HasInvariantCount.decomposition_card_le {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : D.card ≤ G.support.ncard := by
  obtain ⟨E,hcE,hdE,hbE⟩ := hi.exists_bounded_decomposition he
  rw [hi D E hcD hdD hcE hdE]
  exact hbE

/-- Invariance passes to every edge subgraph of an even invariant graph.
The subgraph need not be assumed even: if it has two cycle partitions, those
partitions themselves provide its evenness. -/
lemma HasInvariantCount.of_le {A G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) (hAG : A ≤ G) :
    HasInvariantCount A := by
  intro D E hcD hdD hcE hdE
  let P := D.image (promote hAG)
  let Q := E.image (promote hAG)
  have hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcD J hJ
  have hcQ : ∀ H ∈ Q, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcE J hJ
  have hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact hdD.1 hJ hL (fun h => hne (congrArg (promote hAG) h))
  have hdQ : Set.PairwiseDisjoint (Q : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact hdE.1 hJ hL (fun h => hne (congrArg (promote hAG) h))
  have hcover : (⋃ H ∈ P, H.edgeSet) = ⋃ H ∈ Q, H.edgeSet := by
    have image_edges (F : Finset A.Subgraph) :
        (⋃ H ∈ F.image (promote hAG), H.edgeSet) = ⋃ H ∈ F, H.edgeSet := by
      ext e
      simp only [Set.mem_iUnion,Finset.mem_image]
      constructor
      · rintro ⟨H,⟨J,hJ,rfl⟩,heJ⟩
        exact ⟨J,hJ,heJ⟩
      · rintro ⟨J,hJ,heJ⟩
        exact ⟨promote hAG J,⟨J,hJ,rfl⟩,heJ⟩
    exact (image_edges D).trans (hdD.2.trans (hdE.2.symm.trans (image_edges E).symm))
  have hh := hi.packing_card_eq he P Q hcP hdP hcQ hdQ hcover
  simpa only [P,Q,Finset.card_image_of_injective _ (promote_injective hAG)] using hh

/-- The new restricted-class estimate bounds the exact minimum as well. -/
lemma HasInvariantCount.number_le_support {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) :
    CycleNumberSubmodularity.cycleNumber G ≤ G.support.ncard := by
  obtain ⟨D,hc,hd,hb⟩ := hi.exists_bounded_decomposition he
  exact (CountCritical.number_le G D hc hd).trans hb

universe u
/-- A conditional reduction only: count-criticality implying invariance is
an explicit, unproved premise. The conclusion is the original conjecture. -/
lemma conjecture_of_critical_invariance
    (hinv : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      CountCritical.IsCountCritical k G → HasInvariantCount G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨1,?_⟩
  intro V _ _ G he
  have hb : CycleNumberSubmodularity.cycleNumber G ≤ Fintype.card V := by
    by_cases hk : CycleNumberSubmodularity.cycleNumber G = 0
    · omega
    obtain ⟨H,hHG,hH⟩ := CountCritical.extract G he
      (CycleNumberSubmodularity.cycleNumber G) (Nat.pos_of_ne_zero hk) le_rfl
    have hh := (hinv H _ hH).number_le_support hH.1
    rw [hH.2.1] at hh
    have hn : H.support.ncard ≤ Fintype.card V := by
      simpa using Set.ncard_le_ncard (Set.subset_univ H.support)
    exact hh.trans hn
  obtain ⟨D,hc,hd,hcard⟩ := CountCritical.minimum_exists G he
  refine ⟨D,hc,hd,?_⟩
  rw [hcard,one_mul]
  exact_mod_cast hb

end Erdos184.InvariantPartitions
