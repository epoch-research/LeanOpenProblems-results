import Submission.SevenColorBound

/-!
# Partial colorings with meagre holes

A proper finite coloring on a comeagre subset of the plane would suffice to color
all of the plane. This file proves that implication, not the existence of such a
six-color partial coloring. Neither target statement from Spec.lean is used.
-/

namespace Erdos508Aux

open SimpleGraph Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Every countable configuration can be translated into a comeagre subset of
the plane. No measurability of a coloring's individual color classes is required. -/
theorem exists_translate_into_of_meagre_complement
    {ι : Type*} [Countable ι] (f : ι → Plane)
    (D : Set Plane) (hD : IsMeagre Dᶜ) :
    ∃ t : Plane, ∀ i, f i + t ∈ D := by
  classical
  let bad : ι → Set Plane := fun i => (fun t => f i + t) ⁻¹' Dᶜ
  have hb : IsMeagre (⋃ i, bad i) := by
    apply isMeagre_iUnion
    intro i
    exact IsMeagre.preimage_of_isOpenMap
      (continuous_const.add continuous_id) (isOpenMap_add_left (f i)) hD
  obtain ⟨t, ht⟩ := (dense_of_mem_residual hb).nonempty
  refine ⟨t, fun i => ?_⟩
  have hi : t ∉ bad i := fun h => ht (mem_iUnion.mpr ⟨i, h⟩)
  simpa [bad] using hi

/-- Translating a finite exact unit realization into the domain of a partial
coloring gives an ordinary proper coloring of that finite graph. -/
theorem finite_unit_graph_colorable_of_meagre_holes
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (f : V → Plane)
    (hf : ∀ u v, G.Adj u v → dist (f u) (f v) = 1)
    (D : Set Plane) (hD : IsMeagre Dᶜ)
    {n : ℕ} (C : (UnitDistancePlaneGraph D).Coloring (Fin n)) :
    G.Colorable n := by
  classical
  obtain ⟨t, ht⟩ := exists_translate_into_of_meagre_complement f D hD
  let g : G →g UnitDistancePlaneGraph D := {
    toFun := fun v => ⟨f v + t, ht v⟩
    map_rel' := by
      intro u v huv
      change dist (f u + t) (f v + t) = 1
      rw [dist_add_right]
      exact hf u v huv }
  exact Colorable.of_hom g ⟨C⟩

/-- Baire translation followed by finite graph compactness. The partial coloring
and its meagre-hole condition are hypotheses, not a supplied construction. -/
theorem plane_colorable_of_partial_coloring_meagre_holes
    (D : Set Plane) (hD : IsMeagre Dᶜ)
    {n : ℕ} (C : (UnitDistancePlaneGraph D).Coloring (Fin n)) :
    planeGraph.Colorable n := by
  classical
  apply (colorable_iff_all_finite_subgraphs planeGraph n).mpr
  intro H hH
  letI : Fintype H.verts := hH.fintype
  apply finite_unit_graph_colorable_of_meagre_holes H.coe
    (fun v => v.val.val) ?_ D hD C
  intro u v huv
  exact H.adj_sub huv

/-- A sufficient disproof criterion, with an entirely unresolved partial-coloring
hypothesis. This does not prove the negation stated in Spec.lean. -/
theorem plane_not_eq_seven_of_partial_six_meagre_holes
    (D : Set Plane) (hD : IsMeagre Dᶜ)
    (C : (UnitDistancePlaneGraph D).Coloring (Fin 6)) :
    ¬ planeGraph.chromaticNumber = 7 :=
  plane_not_eq_seven_iff_colorable_six.mpr
    (plane_colorable_of_partial_coloring_meagre_holes D hD C)

/-- The meagre-hole route is equivalent to the original disproof obligation.
The reverse implication supplies no new partial coloring; it uses the whole
plane as the domain of an already given full coloring. -/
theorem plane_not_eq_seven_iff_exists_partial_six_meagre_holes :
    ¬ planeGraph.chromaticNumber = 7 ↔
      ∃ D : Set Plane, IsMeagre Dᶜ ∧ (UnitDistancePlaneGraph D).Colorable 6 := by
  classical
  constructor
  · intro h
    refine ⟨Set.univ, ?_, plane_not_eq_seven_iff_colorable_six.mp h⟩
    simpa using (IsMeagre.empty : IsMeagre (∅ : Set Plane))
  · rintro ⟨D, hD, ⟨C⟩⟩
    exact plane_not_eq_seven_of_partial_six_meagre_holes D hD C

end Erdos508Aux
