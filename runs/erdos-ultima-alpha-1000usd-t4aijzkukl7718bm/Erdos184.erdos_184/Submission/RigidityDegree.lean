import Submission.RigidTheory

/-! Private vertices in rigid cycle families, and the remaining core-rigidity reduction. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open ChordalIncidence RigidSwitching MaximumCycles
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma rigid_family_private (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph) (hDne : D.Nonempty)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∃ H ∈ D, ∃ v ∈ H.verts, ∀ K ∈ D, v ∈ K.verts → K = H := by
  letI : Nonempty D := hDne.to_subtype
  have hsize (H : D) : 3 ≤ (pieceVertices D H).card := by
    obtain ⟨v⟩ := (hD H.val H.property).1.nonempty
    have hb := H.val.coe.degree_lt_card_verts v
    have hr := (hD H.val H.property).2 v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb hr
    simp only [pieceVertices,Set.toFinset_card,← Nat.card_eq_fintype_card]
    omega
  have hinter (H K : D) (hne : H ≠ K) : (pieceVertices D H ∩ pieceVertices D K).card ≤ 2 := by
    have hb := rigid_pair_intersection_le_two hrig heven H.val K.val (hD H.val H.property) (hD K.val K.property)
      (hd H.property K.property (fun he => hne (Subtype.ext he)))
    simpa only [pieceVertices,← Set.toFinset_inter,Set.toFinset_card,← Nat.card_eq_fintype_card] using hb
  have hno := no_incidenceCycle hrig heven D hD hd
  obtain ⟨v,H,hv,hu⟩ := exists_private_vertex (pieceVertices D) hsize hinter
    (conformal_of_no_incidenceTriangle _ (fun h => hno (h.incidenceCycle _)))
    (primal_chordal_of_no_incidenceCycle _ hno).cliqueCutProperty
  refine ⟨H.val,H.property,v,Set.mem_toFinset.mp hv,?_⟩
  intro K hK hvK
  exact congrArg Subtype.val (hu ⟨K,hK⟩ (Set.mem_toFinset.mpr hvK))

lemma rigid_has_degree_two (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (hG : G ≠ ⊥) : ∃ v, G.degree v = 2 := by
  obtain ⟨D,hD,hdec,hcard⟩ := Rigidity.minimum_cycles heven
  have hDne : D.Nonempty := Finset.card_pos.mp (by
    rw [hcard]
    have hn : Critical.number G ≠ 0 := fun h => hG ((StarCharacterization.number_eq_zero_iff G).mp h)
    omega)
  obtain ⟨H,hH,v,hv,hu⟩ := rigid_family_private hrig heven D hDne hD hdec.1
  have hgraph : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hsum := subfamilyGraph_degree D hdec.1 v
  rw [hgraph] at hsum
  have hdeg (K) (hK : K ∈ D) : K.spanningCoe.degree v = if K = H then 2 else 0 := by
    have hreg := (hD K hK).2
    rw [regular_two_spanning_degree K hreg]
    have hmem : v ∈ K.verts ↔ K = H := ⟨hu K hK,fun he => he.symm ▸ hv⟩
    rw [hmem]
  refine ⟨v,?_⟩
  rw [hsum]
  calc
    (∑ K ∈ D, K.spanningCoe.degree v) = ∑ K ∈ D, if K = H then 2 else 0 := Finset.sum_congr rfl hdeg
    _ = 2 := by simp [hH]

lemma even_bound_of_core_rigidity
    (hcore : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R → Rigidity.CycleRigid R)
    (heven : ∀ v, Even (G.degree v)) : Critical.number G ≤ Fintype.card V := by
  obtain ⟨R,_,hR,hn,hmin,_⟩ := EvenCore.exists_even_minimal_core G heven
  have hR' : ∀ v, Even (R.degree v) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hR v
  have hrig := hcore R hR' hmin
  rw [← hn]
  have hb := rigid_number_le_support hrig hR'
  exact hb.trans (by simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card R.support)

universe u
/-- The structural hypothesis below remains unproved. This is a conditional
reduction, not a proof of Erdős 184. -/
lemma asymptotic_of_core_rigidity
    (hcore : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenCore.EvenMinimal R → Rigidity.CycleRigid R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨1,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdD,hcD⟩ := Rigidity.minimum_cycles hR
  refine ⟨D,hD,hdD,?_⟩
  have hb := even_bound_of_core_rigidity (fun S hS hm => hcore S hS hm) hR
  have hle : D.card ≤ Fintype.card W := by omega
  simpa only [one_mul] using (show (D.card : ℝ) ≤ (Fintype.card W : ℝ) by exact_mod_cast hle)

#print axioms rigid_has_degree_two
#print axioms asymptotic_of_core_rigidity
end Erdos184Work.CycleRings
