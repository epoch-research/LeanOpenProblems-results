import Submission.Work

/-! Parity-preserving forest cores and cycle partitions of even graphs.
These do not assert that the cycles can be absorbed into the forest paths. -/

open SimpleGraph Erdos583Work
namespace Erdos583EvenDevelopment

/-- Every finite graph contains an acyclic spanning subgraph with the same
parity at every vertex. -/
lemma exists_parity_forest {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      ∀ v, (F.neighborSet v).ncard % 2 = (G.neighborSet v).ncard % 2 := by
  classical
  let Q (F : SimpleGraph V) := F ≤ G ∧
    ∀ v, (F.neighborSet v).ncard % 2 = (G.neighborSet v).ncard % 2
  have hex : ∃ n : ℕ, ∃ F : SimpleGraph V, Q F ∧ F.edgeSet.ncard = n :=
    ⟨G.edgeSet.ncard, G, ⟨le_rfl, fun _ ↦ rfl⟩, rfl⟩
  obtain ⟨F, hF, hcard⟩ := Nat.find_spec hex
  have hmin (J : SimpleGraph V) (hJ : Q J) : F.edgeSet.ncard ≤ J.edgeSet.ncard := by
    rw [hcard]
    exact Nat.find_min' hex ⟨J, hJ, rfl⟩
  refine ⟨F, hF.1, ?_, hF.2⟩
  intro a c hc
  let J := F.deleteEdges c.toSubgraph.edgeSet
  have hJ : Q J := ⟨(F.deleteEdges_le _).trans hF.1,
    fun v ↦ (delete_cycle_preserves_degree_parity hc v).trans (hF.2 v)⟩
  have hlt : J.edgeSet.ncard < F.edgeSet.ncard := by
    apply Set.ncard_lt_ncard (ht := Set.toFinite _)
    refine ⟨edgeSet_mono (F.deleteEdges_le _), ?_⟩
    intro hsub
    have he : s(a, c.snd) ∈ c.toSubgraph.edgeSet := c.toSubgraph_adj_snd hc.not_nil
    have hj := hsub (c.toSubgraph.edgeSet_subset he)
    have hj' : s(a, c.snd) ∈ F.edgeSet \ c.toSubgraph.edgeSet := by simpa [J] using hj
    exact hj'.2 he
  exact (not_lt_of_ge (hmin J hJ)) hlt

lemma neighbor_ncard_sdiff_add {V : Type*} [Finite V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (v : V) :
    ((G \ F).neighborSet v).ncard + (F.neighborSet v).ncard = (G.neighborSet v).ncard := by
  have he : (G \ F).neighborSet v = G.neighborSet v \ F.neighborSet v := by ext w; rfl
  rw [he]
  exact Set.ncard_diff_add_ncard_of_subset (fun _ hw ↦ hFG hw)

lemma sdiff_even_of_same_parity {V : Type*} [Finite V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (hp : ∀ v, (F.neighborSet v).ncard % 2 = (G.neighborSet v).ncard % 2) :
    ∀ v, Even ((G \ F).neighborSet v).ncard := by
  intro v
  have hs := neighbor_ncard_sdiff_add hFG v
  have hh := hp v
  apply Nat.even_iff.mpr
  omega

lemma acyclic_even_eq_bot {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hA : G.IsAcyclic) (heven : ∀ v, Even (G.neighborSet v).ncard) : G = ⊥ := by
  classical
  have hev (v : V) : Even (G.degree v) := by simpa only [neighborSet_ncard] using heven v
  letI : IsEmpty {v : V // Odd (G.degree v)} := ⟨fun v ↦ (Nat.not_even_iff_odd.mpr v.property) (hev v)⟩
  obtain ⟨D, hD, hn⟩ := forest_decomposition_odd G hA
  have hzero : D = ∅ := Finset.card_eq_zero.mp (by simpa using hn)
  apply edgeSet_eq_empty.mp
  simpa [hzero] using hD.2.2.symm

/-- A subgraph represented by a simple cycle. -/
def IsCycleSubgraph {V : Type*} {G : SimpleGraph V} (K : G.Subgraph) : Prop :=
  ∃ a, ∃ c : G.Walk a a, c.IsCycle ∧ K = c.toSubgraph

lemma lift_cycle_subgraph {V : Type*} {F G : SimpleGraph V} (h : F ≤ G)
    {K : F.Subgraph} (hK : IsCycleSubgraph K) : IsCycleSubgraph (K.map (Hom.ofLE h)) := by
  obtain ⟨a, c, hc, rfl⟩ := hK
  exact ⟨a, c.mapLe h, hc.mapLe h, by simp [Walk.mapLe]⟩

open scoped Classical in
lemma IsDecomposition.lift_union {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    {D : Finset F.Subgraph} (hD : IsDecomposition F D) :
    (⋃ K ∈ D.image (Subgraph.map (Hom.ofLE hFG)), K.edgeSet) = F.edgeSet := by
  classical
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨K, hK, heK⟩
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    rw [edgeSet_lift] at heK
    exact L.edgeSet_subset heK
  · intro he
    have he' : e ∈ ⋃ K ∈ D, K.edgeSet := hD.2.symm ▸ he
    simp only [Set.mem_iUnion] at he'
    obtain ⟨K, hK, heK⟩ := he'
    exact ⟨K.map (Hom.ofLE hFG), Finset.mem_image.mpr ⟨K, hK, rfl⟩,
      (edgeSet_lift hFG K).symm ▸ heK⟩

open scoped Classical in
lemma IsDecomposition.lift_pairwise {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    {D : Finset F.Subgraph} (hD : IsDecomposition F D) :
    Set.PairwiseDisjoint (D.image (Subgraph.map (Hom.ofLE hFG)) : Set G.Subgraph)
      (fun K ↦ K.edgeSet) := by
  classical
  intro K hK L hL hKL
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hL
  change Disjoint (J.map (Hom.ofLE hFG)).edgeSet (M.map (Hom.ofLE hFG)).edgeSet
  rw [edgeSet_lift, edgeSet_lift]
  exact hD.1 hJ hM (fun h ↦ hKL (congrArg (Subgraph.map (Hom.ofLE hFG)) h))

open scoped Classical in
lemma restore_subgraph_partition {V : Type*} {G : SimpleGraph V} (K : G.Subgraph)
    {D : Finset (G.deleteEdges K.edgeSet).Subgraph}
    (hD : IsDecomposition (G.deleteEdges K.edgeSet) D) :
    IsDecomposition G (insert K (D.image (Subgraph.map (Hom.ofLE (G.deleteEdges_le _))))) := by
  classical
  let E := D.image (Subgraph.map (Hom.ofLE (G.deleteEdges_le K.edgeSet)))
  have heE : (⋃ L ∈ E, L.edgeSet) = (G.deleteEdges K.edgeSet).edgeSet := IsDecomposition.lift_union _ hD
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
    refine ⟨IsDecomposition.lift_pairwise _ hD, ?_⟩
    intro L hL _
    apply Set.disjoint_left.mpr
    intro e heK heL
    have he : e ∈ ⋃ L ∈ E, L.edgeSet := Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨hL, heL⟩⟩
    rw [heE, edgeSet_deleteEdges] at he
    exact he.2 heK
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨L, _, heL⟩
      exact L.edgeSet_subset heL
    · intro he
      by_cases heK : e ∈ K.edgeSet
      · exact ⟨K, Finset.mem_insert_self _ _, heK⟩
      · have he' : e ∈ (G.deleteEdges K.edgeSet).edgeSet := by simpa using And.intro he heK
        rw [← heE] at he'
        simp only [Set.mem_iUnion] at he'
        obtain ⟨L, hL, heL⟩ := he'
        exact ⟨L, Finset.mem_insert_of_mem hL, heL⟩

/-- Every finite even graph has a partition into simple cycles. -/
lemma even_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.neighborSet v).ncard) :
    ∃ C : Finset G.Subgraph, (∀ K ∈ C, IsCycleSubgraph K) ∧ IsDecomposition G C := by
  classical
  suffices ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeSet.ncard = n →
      (∀ v, Even (G.neighborSet v).ncard) →
      ∃ C : Finset G.Subgraph, (∀ K ∈ C, IsCycleSubgraph K) ∧ IsDecomposition G C from
    this _ G rfl heven
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hn heven
    by_cases hbot : G = ⊥
    · subst G
      exact ⟨∅, by simp, by simp [IsDecomposition]⟩
    have hnotA : ¬G.IsAcyclic := fun hA ↦ hbot (acyclic_even_eq_bot G hA heven)
    simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hnotA
    obtain ⟨a, c, hc⟩ := hnotA
    let F := G.deleteEdges c.toSubgraph.edgeSet
    have hF : ∀ v, Even (F.neighborSet v).ncard := by
      intro v
      apply Nat.even_iff.mpr
      exact (delete_cycle_preserves_degree_parity hc v).trans (Nat.even_iff.mp (heven v))
    have hlt : F.edgeSet.ncard < n := by
      rw [← hn]
      apply Set.ncard_lt_ncard (ht := Set.toFinite _)
      refine ⟨edgeSet_mono (G.deleteEdges_le _), ?_⟩
      intro hsub
      have he : s(a, c.snd) ∈ c.toSubgraph.edgeSet := c.toSubgraph_adj_snd hc.not_nil
      have hj := hsub (c.toSubgraph.edgeSet_subset he)
      have hj' : s(a, c.snd) ∈ G.edgeSet \ c.toSubgraph.edgeSet := by simpa [F] using hj
      exact hj'.2 he
    obtain ⟨C, hC, hCD⟩ := ih F.edgeSet.ncard hlt F rfl hF
    refine ⟨insert c.toSubgraph (C.image (Subgraph.map (Hom.ofLE (G.deleteEdges_le _)))),
      ?_, restore_subgraph_partition _ hCD⟩
    intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact ⟨a, c, hc, rfl⟩
    · obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      exact lift_cycle_subgraph _ (hC L hL)

lemma lift_subgraph_injective {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G) :
    Function.Injective (Subgraph.map (Hom.ofLE hFG)) := by
  intro H K heq
  apply Subgraph.ext
  · have h := congrArg Subgraph.verts heq
    simpa only [Subgraph.map_verts, Hom.coe_ofLE, Set.image_id] using h
  · funext u v
    apply propext
    have h : (H.map (Hom.ofLE hFG)).Adj u v ↔ (K.map (Hom.ofLE hFG)).Adj u v := by rw [heq]
    simpa only [Subgraph.map_adj, Hom.coe_ofLE, Relation.Map, id_eq,
      exists_eq_right, exists_eq_right_right] using h

lemma neighborSet_lift {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    (K : F.Subgraph) (v : V) :
    ((K.map (Hom.ofLE hFG)).neighborSet v) = K.neighborSet v := by
  ext w
  change s(v,w) ∈ (K.map (Hom.ofLE hFG)).edgeSet ↔ s(v,w) ∈ K.edgeSet
  rw [edgeSet_lift]

open scoped Classical in
lemma endpointMultiplicity_lift {V : Type*} {F G : SimpleGraph V} (hFG : F ≤ G)
    (D : Finset F.Subgraph) (v : V) :
    endpointMultiplicity (D.image (Subgraph.map (Hom.ofLE hFG))) v = endpointMultiplicity D v := by
  classical
  unfold endpointMultiplicity
  rw [Finset.filter_image]
  simp only [neighborSet_lift]
  exact Finset.card_image_of_injective _ (lift_subgraph_injective hFG)

/-- Equality in the parity lower bound forces exactly one end at every odd
vertex and no ends at the even vertices. -/
lemma GoodDecomposition.endpointMultiplicity_of_exact_card {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : ∀ K ∈ D, K.edgeSet.Nonempty)
    (hc : 2*D.card = Fintype.card {v : V // Odd (G.degree v)}) (v : V) :
    endpointMultiplicity D v = if Odd (G.degree v) then 1 else 0 := by
  classical
  let f (x : V) := if Odd (G.degree x) then 1 else 0
  have hle (x : V) : f x ≤ endpointMultiplicity D x := by
    dsimp [f]
    split_ifs with hx
    · have ho := (hD.odd_endpointMultiplicity_iff x).mpr hx
      rw [Nat.odd_iff] at ho
      omega
    · exact Nat.zero_le _
  have hf : ∑ x : V, f x = Fintype.card {x : V // Odd (G.degree x)} := by
    simp only [f, Fintype.card_subtype, Finset.card_filter]
  have hs : ∑ x : V, f x = ∑ x : V, endpointMultiplicity D x := by
    rw [hf, hD.sum_endpointMultiplicity hne, hc]
  exact ((Finset.sum_eq_sum_iff_of_le (fun x _ ↦ hle x)).mp hs v (Finset.mem_univ _)).symm

lemma forest_normal_decomposition {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (hA : F.IsAcyclic) :
    ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧
      (∀ K ∈ D, K.edgeSet.Nonempty) ∧
      (∀ v, endpointMultiplicity D v = if Odd (F.degree v) then 1 else 0) ∧
      2*D.card = Fintype.card {v : V // Odd (F.degree v)} := by
  classical
  obtain ⟨D, hD, hmin⟩ := exists_min_decomposition F
  obtain ⟨E, hE, hEc⟩ := forest_decomposition_odd F hA
  have hn := hmin E hE
  have hl := odd_vertices_le_twice_path_count F hD
  have hc : 2*D.card = Fintype.card {v : V // Odd (F.degree v)} := by omega
  have hne : ∀ K ∈ D, K.edgeSet.Nonempty := fun K hK ↦ min_decomposition_edgeSet_nonempty hD hmin hK
  exact ⟨D, hD, hne, fun v ↦ GoodDecomposition.endpointMultiplicity_of_exact_card hD hne hc v, hc⟩

open scoped Classical in
/-- Every graph has a path-and-cycle partition whose path ends are precisely
its odd vertices. This imposes no upper bound on the number of cycle members. -/
lemma normal_path_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ P C : Finset G.Subgraph,
      (∀ K ∈ P, IsPathSubgraph K ∧ K.edgeSet.Nonempty) ∧
      (∀ K ∈ C, IsCycleSubgraph K) ∧
      IsDecomposition G (P ∪ C) ∧ Disjoint P C ∧
      (∀ v, endpointMultiplicity P v = if Odd (G.degree v) then 1 else 0) ∧
      2*P.card = Fintype.card {v : V // Odd (G.degree v)} := by
  classical
  obtain ⟨F, hFG, hA, hp⟩ := exists_parity_forest G
  obtain ⟨D, hD, hDne, hDe, hDc⟩ := forest_normal_decomposition F hA
  let R := G \ F
  obtain ⟨B, hB, hBD⟩ := even_cycle_decomposition R (sdiff_even_of_same_parity hFG hp)
  let P := D.image (Subgraph.map (Hom.ofLE hFG))
  let C := B.image (Subgraph.map (Hom.ofLE (show R ≤ G from sdiff_le)))
  have hPU : (⋃ K ∈ P, K.edgeSet) = F.edgeSet := IsDecomposition.lift_union hFG hD.2
  have hCU : (⋃ K ∈ C, K.edgeSet) = R.edgeSet := IsDecomposition.lift_union sdiff_le hBD
  have hP (K : G.Subgraph) (hK : K ∈ P) : IsPathSubgraph K ∧ K.edgeSet.Nonempty := by
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact ⟨lift_path_subgraph hFG (hD.1 L hL), (edgeSet_lift hFG L).symm ▸ hDne L hL⟩
  have hcross (K : G.Subgraph) (hK : K ∈ P) (L : G.Subgraph) (hL : L ∈ C) :
      Disjoint K.edgeSet L.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heL
    have heF : e ∈ F.edgeSet := hPU ▸ Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK, heK⟩⟩
    have heR : e ∈ R.edgeSet := hCU ▸ Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨hL, heL⟩⟩
    rw [show R.edgeSet = G.edgeSet \ F.edgeSet from edgeSet_sdiff G F] at heR
    exact heR.2 heF
  have hodd (v : V) : Odd (F.degree v) ↔ Odd (G.degree v) := by
    rw [Nat.odd_iff, Nat.odd_iff, ← neighborSet_ncard F, ← neighborSet_ncard G, hp]
  have hcFG : Fintype.card {v : V // Odd (F.degree v)} =
      Fintype.card {v : V // Odd (G.degree v)} := Fintype.card_congr (Equiv.subtypeEquivRight hodd)
  refine ⟨P, C, hP, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    exact lift_cycle_subgraph sdiff_le (hB L hL)
  · rw [Finset.coe_union, Set.pairwiseDisjoint_union]
    exact ⟨IsDecomposition.lift_pairwise hFG hD.2,
      IsDecomposition.lift_pairwise sdiff_le hBD, fun K hK L hL _ ↦ hcross K hK L hL⟩
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨K, _, heK⟩
      exact K.edgeSet_subset heK
    · intro he
      by_cases heF : e ∈ F.edgeSet
      · have hh : e ∈ ⋃ K ∈ P, K.edgeSet := hPU.symm ▸ heF
        simp only [Set.mem_iUnion] at hh
        obtain ⟨K, hK, heK⟩ := hh
        exact ⟨K, Finset.mem_union_left _ hK, heK⟩
      · have heR : e ∈ R.edgeSet := by
          rw [show R.edgeSet = G.edgeSet \ F.edgeSet from edgeSet_sdiff G F]
          exact ⟨he, heF⟩
        have hh : e ∈ ⋃ K ∈ C, K.edgeSet := hCU.symm ▸ heR
        simp only [Set.mem_iUnion] at hh
        obtain ⟨K, hK, heK⟩ := hh
        exact ⟨K, Finset.mem_union_right _ hK, heK⟩
  · apply Finset.disjoint_left.mpr
    intro K hKP hKC
    obtain ⟨e, he⟩ := (hP K hKP).2
    exact Set.disjoint_left.mp (hcross K hKP K hKC) he he
  · intro v
    change endpointMultiplicity (D.image (Subgraph.map (Hom.ofLE hFG))) v = _
    rw [endpointMultiplicity_lift, hDe]
    simp only [hodd]
  · have hPc : P.card = D.card := Finset.card_image_of_injective D (lift_subgraph_injective hFG)
    rw [hPc, hDc, hcFG]

/- A cut obstruction to the auxiliary degree-bounded cycle-addition assertion.
The original graph is not all-odd: vertices 4 and 5 have degree two. -/
namespace CycleAdditionDegreeObstruction

abbrev edgesG : Finset (Sym2 (Fin 8)) :=
  {s(0,1), s(1,2), s(1,3), s(0,4), s(4,6), s(0,5), s(5,7)}

def G : SimpleGraph (Fin 8) := fromEdgeSet (edgesG : Set (Sym2 (Fin 8)))

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edgesG : Set (Sym2 (Fin 8)))).Adj)

abbrev edgesH : Finset (Sym2 (Fin 8)) := insert s(0,6) (insert s(6,7) (insert s(0,7) edgesG))

def H : SimpleGraph (Fin 8) := fromEdgeSet (edgesH : Set (Sym2 (Fin 8)))

instance : DecidableRel H.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edgesH : Set (Sym2 (Fin 8)))).Adj)

lemma G_tree : G.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨by decide, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  decide

lemma G_three_paths : ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card = 3 := by
  obtain ⟨D, hD, hn⟩ := forest_decomposition_odd G G_tree.IsAcyclic
  have hc : Fintype.card {v : Fin 8 // Odd (G.degree v)} = 6 := by decide
  exact ⟨D, hD, by omega⟩

lemma H_boundary : (boundaryGraph H ({1,2,3} : Finset (Fin 8))).edgeSet = {s(0,1)} := by
  have he (p q : Prop) : p ≠ q ↔ ¬(p ↔ q) :=
    ⟨fun h hi ↦ h (propext hi), fun h he ↦ h (he ▸ Iff.rfl)⟩
  ext e
  induction e using Sym2.ind with
  | h a b =>
    change (H.Adj a b ∧ ((a ∈ ({1,2,3} : Finset (Fin 8))) ≠ (b ∈ ({1,2,3} : Finset (Fin 8))))) ↔
      s(a,b) = s(0,1)
    rw [he]
    revert a b
    decide

lemma H_no_three_paths : ¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ 3 := by
  classical
  rintro ⟨D, hD, hcD⟩
  obtain ⟨E, hE, hmin⟩ := exists_min_decomposition H
  have hcE : E.card ≤ 3 := (hmin D hD).trans hcD
  have hb := hE.degree_odd_cut_bound
    (fun K hK ↦ min_decomposition_edgeSet_nonempty hE hmin hK)
    ({1,2,3} : Finset (Fin 8)) (v := 0) (by decide)
  have hd : H.degree 0 = 5 := by decide
  have hs : (({1,2,3} : Finset (Fin 8)).filter fun w ↦ Odd (H.degree w)).card = 3 := by decide
  rw [hd, if_pos (by decide : Odd (5 : ℕ)), hs, H_boundary, Set.ncard_singleton] at hb
  omega

def c : H.Walk 0 0 := .cons (by decide : H.Adj 0 6)
  (.cons (by decide : H.Adj 6 7) (.cons (by decide : H.Adj 7 0) .nil))

lemma c_isCycle : c.IsCycle := by simp [c, Walk.cons_isCycle_iff, Walk.isPath_def]

lemma delete_c : H.deleteEdges c.toSubgraph.edgeSet = G := by
  ext a b
  simp only [deleteEdges_adj, Walk.mem_edges_toSubgraph]
  revert a b
  decide

lemma witness : c.IsCycle ∧ (∀ v ∈ c.support, Odd (G.degree v)) ∧
    (∀ v, H.degree v ≤ 6) ∧ G.Connected ∧
    (∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card = 3) ∧
    H.deleteEdges c.toSubgraph.edgeSet = G ∧
    ¬(∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ 3) :=
  ⟨c_isCycle, by decide, by decide, (isTree_iff_connected_and_card.mp G_tree).1, G_three_paths, delete_c, H_no_three_paths⟩

end CycleAdditionDegreeObstruction

end Erdos583EvenDevelopment
