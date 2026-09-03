import Submission.BinarySumFilter

/-! Semantic specialization of the binary sum-filter obstruction to actual
cubic field norms. This does not settle Erdős Problem 714. -/
noncomputable section
open Finset SimpleGraph Classical
namespace Erdos714BinaryNormFilter
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]

/-- Extend the nonzero norm to a total unit-valued label. The value at zero
is irrelevant for connection sets excluding zero. -/
def label (z : E) : Fˣ :=
  if hz : z = 0 then 1 else Units.mk0 (Algebra.norm F z) (Algebra.norm_ne_zero_iff.mpr hz)

lemma label_val {z : E} (hz : z ≠ 0) : (label (F := F) z : F) = Algebra.norm F z := by
  simp [label, hz]

/-- The ordinary weighted norm graph with an arbitrary retained sum set. -/
def graph (D : Finset E) : SimpleGraph (Bool × (E × Fˣ)) where
  Adj u v := u.1 ≠ v.1 ∧ u.2.1 + v.2.1 ∈ D ∧
    Algebra.norm F (u.2.1 + v.2.1) = (u.2.2 : F) * (v.2.2 : F)
  symm := by intro u v h; exact ⟨h.1.symm, by simpa [add_comm,mul_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

/-- The combinatorial weighted-sum model agrees with the original norm
incidence equations, not merely with an auxiliary relation. -/
theorem graph_eq (D : Finset E) (hD : (0 : E) ∉ D) :
    graph (F := F) D = Erdos714BinarySumFilter.weightedGraph D (label (F := F)) := by
  ext u v
  simp only [graph, Erdos714BinarySumFilter.weightedGraph]
  constructor
  · rintro ⟨hside,hs,hn⟩
    refine ⟨hside,hs,Units.ext ?_⟩
    rw [label_val (fun hz => hD (hz ▸ hs))]
    exact hn
  · rintro ⟨hside,hs,hn⟩
    refine ⟨hside,hs,?_⟩
    have h := congrArg (fun z : Fˣ => (z : F)) hn
    change (label (F := F) (u.2.1 + v.2.1) : F) = (u.2.2 : F) * (v.2.2 : F) at h
    rw [label_val (fun hz => hD (hz ▸ hs))] at h
    exact h

variable [Fintype F] [Fintype E]

/-- Exact edge count for arbitrary nonzero connection sets. -/
theorem edge_count (D : Finset E) (hD : (0 : E) ∉ D) :
    (graph (F := F) D).edgeFinset.card =
      Fintype.card E * (Fintype.card F - 1) * D.card := by
  rw [graph_eq D hD, Erdos714BinarySumFilter.edge_count, Fintype.card_units]

/-- In a cubic binary extension, every K44-free sum restriction has
at most sqrt(3)*q^(13/2) edges, rather than the host's order q^7. -/
theorem cubic_bound [CharP E 2] (D : Finset E) (hD : (0 : E) ∉ D)
    (hdim : Module.finrank F E = 3)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) D)) :
    ((graph (F := F) D).edgeFinset.card : ℝ)^2 ≤ 3 * (Fintype.card F : ℝ)^13 := by
  rw [graph_eq D hD] at hfree ⊢
  apply Erdos714BinarySumFilter.cubic_scale_bound D (label (F := F))
    (Fintype.card F) (by exact Fintype.card_pos)
  · rw [Module.card_eq_pow_finrank (K := F), hdim]
  · rw [Fintype.card_units]
    exact Nat.sub_le _ _
  · exact hfree

/-- The underlying field elements of a multiplicative subgroup. -/
def subgroupSums (H : Subgroup Eˣ) : Finset E :=
  univ.image (fun u : H => ((u : Eˣ) : E))

lemma zero_not_mem_subgroupSums (H : Subgroup Eˣ) : (0 : E) ∉ subgroupSums H := by
  simp [subgroupSums, Units.ne_zero]

lemma subgroupSums_card (H : Subgroup Eˣ) :
    (subgroupSums H).card = Fintype.card H := by
  rw [subgroupSums, card_image_of_injective]
  · exact card_univ
  · intro u v h
    exact Subtype.ext (Units.ext h)

/-- Every multiplicative sum filter of sufficiently small index contains
K44. No assumption that it contains the base-field units is needed. -/
theorem subgroup_not_free [CharP E 2] (H : Subgroup Eˣ)
    (hdim : Module.finrank F E = 3)
    (hlarge : 16 * H.index^2 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := F) (subgroupSums H)) := by
  rw [graph_eq _ (zero_not_mem_subgroupSums H)]
  apply Erdos714BinarySumFilter.fixed_index_not_free
    (subgroupSums H) (label (F := F)) (Fintype.card F) H.index
  · exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
  · exact hlarge
  · rw [Module.card_eq_pow_finrank (K := F), hdim]
  · rw [Fintype.card_units]
    exact Nat.sub_le _ _
  · rw [subgroupSums_card]
    have h := H.card_mul_index
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units,
      Module.card_eq_pow_finrank (K := F) (V := E), hdim] at h
    exact h

#print axioms graph_eq
#print axioms edge_count
#print axioms cubic_bound
#print axioms subgroup_not_free
end Erdos714BinaryNormFilter
