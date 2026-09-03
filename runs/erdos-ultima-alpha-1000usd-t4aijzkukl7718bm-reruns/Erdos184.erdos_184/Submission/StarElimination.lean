import Submission.IncidenceForest

/-! A vertex-elimination criterion for linear cycle decompositions.
The criterion is not proved for arbitrary even graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace StarElimination

/-- A nonempty cycle packing through one vertex, exhausting that vertex,
whose cost is paid by the number of vertices it isolates. -/
def IsEliminatingPacking {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : Finset G.Subgraph) : Prop :=
  P.Nonempty ∧
  (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
  Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
  (∃ v, (∀ H ∈ P, v ∈ H.verts) ∧ v ∉ (G \ unionPieces G P).support) ∧
  P.card + (G \ unionPieces G P).support.ncard ≤ G.support.ncard

/-- The amortization step, with the existence of suitable packings left explicit. -/
lemma bound_of_eliminating_packings {V : Type*} [Fintype V]
    (helim : ∀ G : SimpleGraph V, G ≠ ⊥ → (∀ v, Even (G.degree v)) →
      ∃ P : Finset G.Subgraph, IsEliminatingPacking G P)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      exact ⟨∅, by simp, by simp [IsDecomposition], by simp⟩
    obtain ⟨P,hP,hc,hd,_,hcost⟩ := helim G hbot he
    have hp : 0 < P.card := Finset.card_pos.mpr hP
    have hlt : (G \ unionPieces G P).support.ncard < n := by omega
    have her := even_residual_of_cycle_packing G he P hc hd
    obtain ⟨F,hcF,hdF,hbF⟩ := ih _ hlt (G \ unionPieces G P)
      (by simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using her) rfl
    obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hc hd F (by
      intro H hH
      refine ⟨(hcF H hH).1, ?_⟩
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcF H hH).2 w) hdF
    exact ⟨D,hcD,hdD,by omega⟩

universe u
/-- This proves the original proposition only under the unproved general
vertex-elimination hypothesis. -/
lemma conjecture_of_eliminating_packings
    (helim : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) →
      ∃ P : Finset G.Subgraph, IsEliminatingPacking G P) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨1,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hb⟩ := bound_of_eliminating_packings (fun G => helim G) G he
  refine ⟨D,hc,hd,?_⟩
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  simpa only [one_mul] using (show (D.card : ℝ) ≤ Fintype.card V by exact_mod_cast hb.trans hs)

noncomputable def star {V : Type*} {G : SimpleGraph V} (D : Finset G.Subgraph)
    (v : V) : Finset G.Subgraph := D.filter (fun H => v ∈ H.verts)

lemma mem_star {V : Type*} {G : SimpleGraph V} (D : Finset G.Subgraph)
    (v : V) (H : G.Subgraph) : H ∈ star D v ↔ H ∈ D ∧ v ∈ H.verts := Finset.mem_filter

lemma star_subset {V : Type*} {G : SimpleGraph V} (D : Finset G.Subgraph) (v : V) :
    star D v ⊆ D := Finset.filter_subset _ _

/-- The star of a vertex in a decomposition contains exactly half its degree many pieces. -/
lemma star_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) : 2 * (star D v).card = G.degree v :=
  cycle_decomposition_vertex_count G D hc hd v

/-- A vertex is isolated after removing a subfamily exactly when all of
its incident cycle pieces belonged to that subfamily. -/
lemma isolated_iff_star_subset {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D P : Finset G.Subgraph) (hPD : P ⊆ D)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (w : V) :
    w ∉ (G \ unionPieces G P).support ↔ star D w ⊆ P := by
  constructor
  · intro hw H hH
    obtain ⟨hHD,hwH⟩ := (mem_star D w H).mp hH
    have hpos : 0 < H.coe.degree ⟨w,hwH⟩ := by
      have hh := (hc H hHD).2 ⟨w,hwH⟩
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
      omega
    obtain ⟨z,hz⟩ := (H.coe.degree_pos_iff_exists_adj ⟨w,hwH⟩).mp hpos
    have heU : s(w,z.val) ∈ (unionPieces G P).edgeSet := by
      by_contra hn
      apply hw
      refine ⟨z.val,?_⟩
      exact ⟨H.adj_sub hz,hn⟩
    rw [unionPieces_edgeSet] at heU
    simp only [Set.mem_iUnion] at heU
    obtain ⟨K,hKP,heK⟩ := heU
    have heq : H = K := by
      by_contra hne
      exact Set.disjoint_left.mp (hd.1 hHD (hPD hKP) hne) hz heK
    exact heq.symm ▸ hKP
  · intro hsub hw
    obtain ⟨z,hz⟩ := hw
    have he : s(w,z) ∈ ⋃ H ∈ D, H.edgeSet := hd.2.symm ▸ hz.1
    simp only [Set.mem_iUnion] at he
    obtain ⟨H,hHD,heH⟩ := he
    have hHP : H ∈ P := hsub ((mem_star D w H).mpr ⟨hHD,H.edge_vert heH⟩)
    apply hz.2
    change s(w,z) ∈ (unionPieces G P).edgeSet
    rw [unionPieces_edgeSet]
    simp only [Set.mem_iUnion]
    exact ⟨H,hHP,heH⟩

/-- Vertices of positive degree whose stars are contained in the chosen star
are exactly the nonisolated vertices removed by that star. -/
noncomputable def dominated {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph) (v : V) : Finset V :=
  Finset.univ.filter (fun w => w ∈ G.support ∧ star D w ⊆ star D v)

lemma dominated_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) :
    (dominated D v).card + (G \ unionPieces G (star D v)).support.ncard = G.support.ncard := by
  have hset : (dominated D v : Set V) =
      G.support \ (G \ unionPieces G (star D v)).support := by
    ext w
    simp only [dominated,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_diff]
    rw [isolated_iff_star_subset D (star D v) (star_subset D v) hc hd w]
  have h := Set.ncard_diff_add_ncard_of_subset
    (SimpleGraph.support_mono (show G \ unionPieces G (star D v) ≤ G from sdiff_le))
  rw [← hset,Set.ncard_coe_finset] at h
  exact h

/-- A sufficient finite incidence criterion for one elimination step. -/
lemma eliminating_star_of_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) (hv : v ∈ G.support)
    (hcard : (star D v).card ≤ (dominated D v).card) :
    IsEliminatingPacking G (star D v) := by
  have hpos := (G.degree_pos_iff_mem_support v).mpr hv
  have hs := star_card D hc hd v
  refine ⟨Finset.card_pos.mp (by omega),fun H hH => hc H (star_subset D v hH),
    fun H hH K hK hne => hd.1 (star_subset D v hH) (star_subset D v hK) hne,
    ⟨v,fun H hH => ((mem_star D v H).mp hH).2,?_⟩,?_⟩
  · exact (isolated_iff_star_subset D (star D v) (star_subset D v) hc hd v).mpr (by rfl)
  · have hh := dominated_card D hc hd v
    omega

/-- Degree-two vertices always supply an elimination step. -/
lemma eliminating_packing_of_degree_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∀ w, Even (G.degree w)) (v : V) (hv : G.degree v = 2) :
    ∃ P : Finset G.Subgraph, IsEliminatingPacking G P ∧ P.card = 1 := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G he
  have hs := star_card D hc hd v
  have hcard : (star D v).card = 1 := by omega
  have hvs : v ∈ G.support := (G.degree_pos_iff_mem_support v).mp (by omega)
  have hmem : v ∈ dominated D v := by simp [dominated,hvs]
  have hdom := Finset.card_pos.mpr ⟨v,hmem⟩
  exact ⟨star D v,eliminating_star_of_card_le D hc hd v hvs (by omega),hcard⟩

/-- A minimum cycle decomposition of a nonempty 4-regular graph has two
pieces sharing at least two vertices. The global minimum assumption is essential. -/
lemma regular_four_minimum_overlap {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hr : G.IsRegularOfDegree 4)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card) :
    ∃ H ∈ D, ∃ K ∈ D, H ≠ K ∧ 2 ≤ (H.verts ∩ K.verts).ncard := by
  by_contra hno
  have hlin : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).Subsingleton := by
    intro H hH K hK hne
    apply Set.ncard_le_one_iff_subsingleton.mp
    by_contra! hcard
    exact hno ⟨H,hH,K,hK,hne,hcard⟩
  have ha := CycleIncidence.minimum_linear_subfamily_acyclic D D (by rfl) hc hd hm hlin
  have hforest := forest_edge_card_lt_vertex_card (CycleIncidence.graph (fun H : D => H.val.verts)) ha
  have hinc : (CycleIncidence.graph (fun H : D => H.val.verts)).edgeFinset.card = G.edgeFinset.card := by
    rw [CycleIncidence.edge_card]
    calc
      ∑ H : D, H.val.verts.ncard = ∑ H ∈ D, H.verts.ncard :=
        (Finset.sum_subtype D (fun H => Iff.rfl) (fun H => H.verts.ncard)).symm
      _ = ∑ H ∈ D, H.edgeSet.ncard := by
        apply Finset.sum_congr rfl
        intro H hH
        exact (regular_two_edge_vertex_card H (hc H hH).2).symm
      _ = G.edgeFinset.card := decomposition_edge_card G D hd
  have hdegrees : ∀ v, G.degree v = 4 := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr v
  have hsize : G.edgeFinset.card = 2 * Fintype.card V := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hdegrees,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hsum
    omega
  rw [hinc,Fintype.card_sum,Fintype.card_coe,hsize] at hforest
  have hbound := cycle_decomposition_three_mul_card_le_edges G D hc hd
  rw [hsize] at hbound
  omega

/-- The proposed elimination step is valid for every nonempty 4-regular graph. -/
lemma eliminating_packing_of_regular_four {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hr : G.IsRegularOfDegree 4) :
    ∃ P : Finset G.Subgraph, IsEliminatingPacking G P ∧ P.card = 2 := by
  have hdegrees : ∀ v, G.degree v = 4 := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr v
  have he : ∀ v, Even (G.degree v) := by intro v; rw [hdegrees]; decide
  obtain ⟨D,hc,hd,hm⟩ := minimum_cycle_decomposition G he
  obtain ⟨H,hH,K,hK,hne,hshare⟩ := regular_four_minimum_overlap G hr D hc hd hm
  obtain ⟨v,hv,w,hw,hvw⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (show 1 < (H.verts ∩ K.verts).ncard from hshare)
  have hs : ∀ z ∈ H.verts ∩ K.verts, star D z = {H,K} := by
    intro z hz
    have hh := star_card D hc hd z
    rw [hdegrees] at hh
    have hsub : ({H,K} : Finset G.Subgraph) ⊆ star D z := by
      intro J hJ
      rcases Finset.mem_insert.mp hJ with hJ | hJ
      · subst J
        exact (mem_star D z H).mpr ⟨hH,hz.1⟩
      · have : J = K := Finset.mem_singleton.mp hJ
        subst J
        exact (mem_star D z K).mpr ⟨hK,hz.2⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)).symm
  have hsupp : ∀ z, z ∈ G.support := by
    intro z
    apply (G.degree_pos_iff_mem_support z).mp
    rw [hdegrees]
    omega
  have hvdom : v ∈ dominated D v := by simp [dominated,hsupp]
  have hwdom : w ∈ dominated D v := by
    simp only [dominated,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hsupp w,by rw [hs w hw,hs v hv]⟩
  have hdom : 2 ≤ (dominated D v).card := by
    have hh : ({v,w} : Finset V) ⊆ dominated D v := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hvdom
      · exact Finset.mem_singleton.mp hz ▸ hwdom
    simpa only [Finset.card_pair hvw] using Finset.card_le_card hh
  have hcard : (star D v).card = 2 := by rw [hs v hv,Finset.card_pair hne]
  exact ⟨star D v,eliminating_star_of_card_le D hc hd v (hsupp v) (by omega),hcard⟩

/-- In a positive regular graph, domination of cycle stars is equality.
Thus the proposed general criterion asks for a sufficiently large class
of vertices with identical incidence rows in a suitable decomposition. -/
lemma dominated_eq_incidence_class {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : ℕ) (hrpos : 0 < r) (hr : G.IsRegularOfDegree (2*r))
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) :
    dominated D v = Finset.univ.filter (fun w => star D w = star D v) := by
  have hdegrees : ∀ w, G.degree w = 2*r := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr w
  have hcard : ∀ w, (star D w).card = r := by
    intro w
    have hh := star_card D hc hd w
    rw [hdegrees] at hh
    omega
  ext w
  simp only [dominated,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨_,hsub⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard,hcard])
  · intro heq
    refine ⟨(G.degree_pos_iff_mem_support w).mp (by rw [hdegrees]; omega),by rw [heq]⟩

/-- The same star step with an arbitrary fixed amortization constant. -/
def IsAmortizedEliminatingPacking {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (P : Finset G.Subgraph) : Prop :=
  P.Nonempty ∧
  (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
  Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
  (∃ v, (∀ H ∈ P, v ∈ H.verts) ∧ v ∉ (G \ unionPieces G P).support) ∧
  P.card + C * (G \ unionPieces G P).support.ncard ≤ C * G.support.ncard

lemma bound_of_amortized_elimination {V : Type*} [Fintype V] (C : ℕ)
    (helim : ∀ G : SimpleGraph V, G ≠ ⊥ → (∀ v, Even (G.degree v)) →
      ∃ P : Finset G.Subgraph, IsAmortizedEliminatingPacking C G P)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ C * G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      exact ⟨∅,by simp,by simp [IsDecomposition],by simp⟩
    obtain ⟨P,hP,hc,hd,_,hcost⟩ := helim G hbot he
    have hp : 0 < P.card := Finset.card_pos.mpr hP
    have hlt : (G \ unionPieces G P).support.ncard < n := by
      apply Nat.lt_of_mul_lt_mul_left (a := C)
      rw [← hn]
      omega
    have her := even_residual_of_cycle_packing G he P hc hd
    obtain ⟨F,hcF,hdF,hbF⟩ := ih _ hlt (G \ unionPieces G P)
      (by simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using her) rfl
    obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hc hd F (by
      intro H hH
      refine ⟨(hcF H hH).1,?_⟩
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcF H hH).2 w) hdF
    refine ⟨D,hcD,hdD,?_⟩
    rw [hn] at hcost
    omega

/-- Any one uniform constant in the proposed star-elimination principle
would suffice. Such a constant has not been proved to exist. -/
lemma conjecture_of_amortized_elimination (C : ℕ)
    (helim : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) →
      ∃ P : Finset G.Subgraph, IsAmortizedEliminatingPacking C G P) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨C,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hb⟩ := bound_of_amortized_elimination C (fun G => helim G) G he
  refine ⟨D,hc,hd,?_⟩
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  exact_mod_cast hb.trans (Nat.mul_le_mul_left C hs)

lemma amortized_star_of_card_le {V : Type*} [Fintype V] {G : SimpleGraph V} (C : ℕ)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) (hv : v ∈ G.support)
    (hcard : (star D v).card ≤ C * (dominated D v).card) :
    IsAmortizedEliminatingPacking C G (star D v) := by
  have hpos := (G.degree_pos_iff_mem_support v).mpr hv
  have hs := star_card D hc hd v
  refine ⟨Finset.card_pos.mp (by omega),fun H hH => hc H (star_subset D v hH),
    fun H hH K hK hne => hd.1 (star_subset D v hH) (star_subset D v hK) hne,
    ⟨v,fun H hH => ((mem_star D v H).mp hH).2,?_⟩,?_⟩
  · exact (isolated_iff_star_subset D (star D v) (star_subset D v) hc hd v).mpr (by rfl)
  · have hh := congrArg (C * ·) (dominated_card D hc hd v)
    dsimp only at hh
    rw [Nat.mul_add] at hh
    omega

end StarElimination
end Erdos184
