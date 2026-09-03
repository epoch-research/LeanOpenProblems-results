import Submission.Work

/-!
A measure-theoretic candidate family for Erdős Problem 595.
Only K4-freeness and basic structural facts are proved here. No claim that a
member lacks a countable triangle-free edge cover is made.
-/

open SimpleGraph Set MeasureTheory
open scoped ENNReal

namespace Erdos595Quarter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurable quarter-measure sets outside a specified ultrafilter. -/
abbrev Vertex (μ : Measure Ω) (p : Ultrafilter Ω) :=
  {A : Set Ω // MeasurableSet A ∧ μ A = (1 / 4 : ℝ≥0∞) ∧ A ∉ p}

def quarterGraph (μ : Measure Ω) (p : Ultrafilter Ω) : SimpleGraph (Vertex μ p) where
  Adj A B := Disjoint A.val B.val
  symm := fun _ _ h => h.symm
  loopless := by
    intro A h
    have he : A.val = ∅ := disjoint_self.mp h
    have hm := A.property.2.1
    rw [he, measure_empty] at hm
    have hpos : (0 : ℝ≥0∞) < 1 / 4 := by
      simpa only [one_div] using (ENNReal.inv_pos.mpr (show (4 : ℝ≥0∞) ≠ ∞ by simp))
    exact (ne_of_gt hpos) hm.symm

/-- A probability measure admits an ultrafilter containing every conull set. -/
noncomputable def conullUltrafilter (μ : Measure Ω) [IsProbabilityMeasure μ] : Ultrafilter Ω :=
  Ultrafilter.of (ae μ)

theorem conullUltrafilter_le (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (conullUltrafilter μ : Filter Ω) ≤ ae μ := Ultrafilter.of_le _

private theorem union_mem_of_quarters (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ultrafilter Ω) (hp : (p : Filter Ω) ≤ ae μ)
    (A : Fin 4 → Set Ω) (hm : ∀ i, MeasurableSet (A i))
    (hq : ∀ i, μ (A i) = (1 / 4 : ℝ≥0∞))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) : (⋃ i, A i) ∈ p := by
  have hμ : μ (⋃ i, A i) = 1 := by
    rw [measure_iUnion hd hm]
    simp only [hq, tsum_fintype]
    norm_num [Fin.sum_univ_succ]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  apply hp
  rw [mem_ae_iff, measure_compl (MeasurableSet.iUnion hm) (by rw [hμ]; simp)]
  simp [hμ]

/-- Four disjoint quarter-measure sets exhaust the space modulo null sets.
An ultrafilter containing every conull set must therefore contain one of them. -/
theorem quarterGraph_cliqueFree (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ultrafilter Ω) (hp : (p : Filter Ω) ≤ ae μ) :
    (quarterGraph μ p).CliqueFree 4 := by
  classical
  by_contra h
  let f : (⊤ : SimpleGraph (Fin 4)) ↪g quarterGraph μ p :=
    SimpleGraph.topEmbeddingOfNotCliqueFree h
  have hd : Pairwise (fun i j => Disjoint (f i).val (f j).val) := by
    intro i j hij
    exact f.map_rel_iff.mpr hij
  have hu := union_mem_of_quarters μ p hp (fun i => (f i).val)
    (fun i => (f i).property.1) (fun i => (f i).property.2.1) hd
  have hu' : (⋃ i ∈ (univ : Set (Fin 4)), (f i).val) ∈ p := by simpa using hu
  obtain ⟨i, _, hi⟩ := (p.finite_biUnion_mem_iff finite_univ).mp hu'
  exact (f i).property.2.2 hi

omit [MeasurableSpace Ω] in
private theorem not_mem_of_disjoint {p : Ultrafilter Ω} {A B : Set Ω}
    (hd : Disjoint A B) (hB : B ∈ p) : A ∉ p := by
  intro hA
  obtain ⟨x, hxA, hxB⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hA hB)
  exact Set.disjoint_left.mp hd hxA hxB

/-- A four-way equipartition gives a triangle: discard the unique part selected
by the ultrafilter and retain the other three. -/
theorem quarterGraph_not_triangleFree (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ultrafilter Ω) (hp : (p : Filter Ω) ≤ ae μ)
    (A : Fin 4 → Set Ω) (hm : ∀ i, MeasurableSet (A i))
    (hq : ∀ i, μ (A i) = (1 / 4 : ℝ≥0∞))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ¬(quarterGraph μ p).CliqueFree 3 := by
  classical
  have hu := union_mem_of_quarters μ p hp A hm hq hd
  have hu' : (⋃ i ∈ (univ : Set (Fin 4)), A i) ∈ p := by simpa using hu
  obtain ⟨k, _, hk⟩ := (p.finite_biUnion_mem_iff finite_univ).mp hu'
  let v : Fin 3 → Vertex μ p := fun i =>
    ⟨A (k.succAbove i), hm _, hq _,
      not_mem_of_disjoint (hd (Fin.succAbove_ne k i)) hk⟩
  have hv : ∀ i j : Fin 3, i ≠ j → (quarterGraph μ p).Adj (v i) (v j) := by
    intro i j hij
    exact hd (Fin.succAbove_right_injective.ne hij)
  intro h
  exact h _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨hv 0 1 (by decide), hv 0 2 (by decide), hv 1 2 (by decide)⟩)

/-- A finite collection of vertices always misses a set of positive measure.
This is a finite statement: an ultrafilter need not preserve countable unions. -/
theorem finite_union_measure_lt_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ultrafilter Ω) (hp : (p : Filter Ω) ≤ ae μ)
    (T : Finset (Vertex μ p)) : μ (⋃ A ∈ T, A.val) < 1 := by
  have hm : MeasurableSet (⋃ A ∈ T, A.val) :=
    T.measurableSet_biUnion (fun A _ => A.property.1)
  have hn : (⋃ A ∈ T, A.val) ∉ p := by
    intro h
    obtain ⟨A, _, hA⟩ := (p.finite_biUnion_mem_iff T.finite_toSet).mp h
    exact A.property.2.2 hA
  have hle : μ (⋃ A ∈ T, A.val) ≤ 1 := by
    simpa using (measure_mono (subset_univ (⋃ A ∈ T, A.val)) :
      μ (⋃ A ∈ T, A.val) ≤ μ univ)
  apply lt_of_le_of_ne hle
  intro he
  apply hn
  apply hp
  rw [mem_ae_iff, measure_compl hm (by rw [he]; simp)]
  simp [he]

#print axioms quarterGraph_cliqueFree
#print axioms quarterGraph_not_triangleFree
#print axioms finite_union_measure_lt_one

end Erdos595Quarter
