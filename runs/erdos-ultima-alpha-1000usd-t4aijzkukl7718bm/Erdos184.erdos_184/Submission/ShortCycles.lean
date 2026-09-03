import Submission.RigidityDegree

/-! Triangle pieces in minimum decompositions, and a counting improvement.
These results do not prove a uniform linear decomposition bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ShortCycles
open Critical Rigidity MaximumCycles
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma cycle_piece_three_le_edges (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    3 ≤ H.coe.edgeFinset.card := by
  obtain ⟨v⟩ := hH.1.nonempty
  have hb := H.coe.degree_lt_card_verts v
  have hr := hH.2 v
  have he := regular_two_card_edges H (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hH.2)
  rw [subgraph_edge_card] at he
  change H.coe.edgeFinset.card = Nat.card H.verts at he
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hb hr
  omega

lemma cycle_family_three_mul_card_le_edges (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    3 * D.card ≤ (subfamilyGraph D).edgeFinset.card := by
  rw [subfamilyGraph_card_edges D hd]
  calc
    _ = ∑ _H ∈ D, 3 := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun H hH => cycle_piece_three_le_edges H (hD H hH))

lemma rigid_of_edges_eq_three_mul_number
    (he : G.edgeFinset.card = 3 * number G) : CycleRigid G := by
  intro D hD hdec
  have hb := cycle_family_three_mul_card_le_edges D hD hdec.1
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hg,he] at hb
  have hn := number_le D (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hD H hH)) hdec
  omega

/-- The union of triangle pieces of an optimum decomposition is rigid. -/
lemma triangle_subfamily_rigid (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hcD : D.card = number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (htri : ∀ H ∈ A, H.coe.edgeFinset.card = 3) :
    CycleRigid (subfamilyGraph A) := by
  have hn := Subfamilies.minimal_subfamily_number D hD hdec hcD A hAD
  have hd : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne
  apply rigid_of_edges_eq_three_mul_number
  rw [hn,subfamilyGraph_card_edges A hd]
  calc
    _ = ∑ _H ∈ A, 3 := Finset.sum_congr rfl htri
    _ = _ := by simp [Nat.mul_comm]

lemma triangle_subfamily_card_le (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hcD : D.card = number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (htri : ∀ H ∈ A, H.coe.edgeFinset.card = 3) :
    A.card ≤ Fintype.card V := by
  have hD' : ∀ H ∈ D, IsCycleOrEdge H.coe := fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hD H hH)
  have hn := Subfamilies.minimal_subfamily_number D hD' hdec hcD A hAD
  have hr := triangle_subfamily_rigid D hD' hdec hcD A hAD htri
  have he := cycle_subfamily_even A (fun H hH => hD H (hAD hH))
    (fun _ hH _ hK hne => hdec.1 (hAD hH) (hAD hK) hne)
  have hb := CycleRings.rigid_number_le_support hr (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
  rw [hn] at hb
  exact hb.trans (by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (subfamilyGraph A).support)

lemma triangle_piece_adj (H : G.Subgraph)
    (hH : H.coe.IsRegularOfDegree 2) (htri : H.coe.edgeFinset.card = 3)
    {x y : V} (hx : x ∈ H.verts) (hy : y ∈ H.verts) (hne : x ≠ y) :
    H.Adj x y := by
  have he := regular_two_card_edges H hH
  rw [subgraph_edge_card] at he
  change H.coe.edgeFinset.card = Nat.card H.verts at he
  have hc : Fintype.card H.verts = 3 := by
    rw [← Nat.card_eq_fintype_card,← he]
    exact htri
  let a : H.verts := ⟨x,hx⟩
  let b : H.verts := ⟨y,hy⟩
  have hab : b ≠ a := fun h => hne (congrArg Subtype.val h).symm
  have hsub : H.coe.neighborFinset a ⊆ Finset.univ.erase a := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨(H.coe.mem_neighborFinset a z).mp hz |>.ne.symm, Finset.mem_univ _⟩
  have heq : H.coe.neighborFinset a = Finset.univ.erase a := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hr := hH a
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr ⊢
    have hn : (Finset.univ.erase a).card = 2 := by simp [hc]
    omega
  have hb : b ∈ H.coe.neighborFinset a := by rw [heq]; exact Finset.mem_erase.mpr ⟨hab,Finset.mem_univ _⟩
  exact (H.coe.mem_neighborFinset a b).mp hb

lemma triangle_subfamily_twice_card_le (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (hcD : D.card = number G)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (htri : ∀ H ∈ A, H.coe.edgeFinset.card = 3) :
    2 * A.card ≤ Fintype.card V := by
  apply Subfamilies.minimal_linear_subfamily_bound D
    (fun H hH => Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hD H hH))
    hdec hcD A hAD (fun H hH => hD H (hAD hH))
  intro H hH K hK hne x hx y hy hxK hyK
  by_contra hxy
  have heH : s(x,y) ∈ H.edgeSet := triangle_piece_adj H (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hD H (hAD hH)).2)
    (htri H hH) hx hy hxy
  have heK : s(x,y) ∈ K.edgeSet := triangle_piece_adj K (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hD K (hAD hK)).2)
    (htri K hK) hxK hyK hxy
  exact Set.disjoint_left.mp (hdec.1 (hAD hH) (hAD hK) hne) heH heK

lemma eight_mul_number_le_twice_edges_add_card (heven : ∀ v, Even (G.degree v)) :
    8 * number G ≤ 2 * G.edgeFinset.card + Fintype.card V := by
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles heven
  let A := D.filter (fun H => H.coe.edgeFinset.card = 3)
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have htri : ∀ H ∈ A, H.coe.edgeFinset.card = 3 := fun H hH => (Finset.mem_filter.mp hH).2
  have ht := triangle_subfamily_twice_card_le D hD hdec hcard A hAD htri
  have he : G.edgeFinset.card = ∑ H ∈ D, H.coe.edgeFinset.card := by
    have hg : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
    have h := subfamilyGraph_card_edges D hdec.1
    rw [hg] at h
    exact h
  have hfour : 4 * D.card ≤ G.edgeFinset.card + A.card := by
    calc
      _ = ∑ _H ∈ D, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ H ∈ D, (H.coe.edgeFinset.card + if H.coe.edgeFinset.card = 3 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro H hH
        have h3 := cycle_piece_three_le_edges H (hD H hH)
        split_ifs <;> omega
      _ = _ := by rw [Finset.sum_add_distrib,← he]; simp [A]
  omega

lemma four_mul_number_le_edges_add_card (heven : ∀ v, Even (G.degree v)) :
    4 * number G ≤ G.edgeFinset.card + Fintype.card V := by
  have h := eight_mul_number_le_twice_edges_add_card heven
  omega

/-- A sufficient edge-excess hypothesis on arbitrary even-minimal cores.
The hypothesis itself is NOT established here. -/
lemma even_bound_of_core_triangle_excess (C : ℕ)
    (hcore : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      R.edgeFinset.card ≤ C * Fintype.card V + 3 * number R)
    (heven : ∀ v, Even (G.degree v)) :
    2 * number G ≤ (2 * C + 1) * Fintype.card V := by
  obtain ⟨R,_,hR,hn,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  have hR' : ∀ v, Even (R.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hR
  have hlo := eight_mul_number_le_twice_edges_add_card hR'
  have hhi := hcore R hR' hmin
  rw [Nat.add_mul,Nat.mul_assoc,one_mul]
  omega

/-- A hypothetical violation of the indicated linear bound has a minimal
core with large excess over three times the optimum. -/
lemma triangle_excess_core_of_large_number (C : ℕ)
    (heven : ∀ v, Even (G.degree v))
    (hlarge : (2 * C + 1) * Fintype.card V < 2 * number G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ v, Even (R.degree v)) ∧
      EvenCore.EvenMinimal R ∧ number R = number G ∧
      C * Fintype.card V + 3 * number R < R.edgeFinset.card := by
  obtain ⟨R,hRG,hR,hn,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  have hR' : ∀ v, Even (R.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hR
  have hlo := eight_mul_number_le_twice_edges_add_card hR'
  refine ⟨R,hRG,hR',hmin,hn,?_⟩
  rw [Nat.add_mul,Nat.mul_assoc,one_mul] at hlarge
  omega

universe u
open Filter in
/-- Conditional reduction only: the edge-excess assumption remains unproved. -/
lemma asymptotic_of_core_triangle_excess (C : ℕ)
    (hcore : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R →
      R.edgeFinset.card ≤ C * Fintype.card W + 3 * number R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨C+1,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  refine ⟨D,hD,hdec,?_⟩
  have hn := even_bound_of_core_triangle_excess C (fun S hS hm => hcore S hS hm) hR
  have hb : D.card ≤ (C+1) * Fintype.card W := by nlinarith
  exact_mod_cast hb

#print axioms triangle_subfamily_rigid
#print axioms triangle_subfamily_twice_card_le
#print axioms eight_mul_number_le_twice_edges_add_card
#print axioms four_mul_number_le_edges_add_card
#print axioms triangle_excess_core_of_large_number
#print axioms asymptotic_of_core_triangle_excess
end Erdos184Work.ShortCycles
