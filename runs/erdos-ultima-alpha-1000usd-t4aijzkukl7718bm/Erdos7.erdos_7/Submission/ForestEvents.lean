import Submission.ForestCapacity

/-! Applying a compensated forest certificate to actual finite weighted events. -/
namespace Erdos7ForestEvents
open scoped BigOperators
open Erdos7ForestUnion Erdos7ForestCapacity
set_option maxHeartbeats 1500000
set_option autoImplicit false

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

lemma weighted_forest_edge_bound (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (A : ι → Ω → Prop) (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i)
    (E : Finset (ι × ι)) (hE : ∀ i j,(i,j) ∈ E ↔ parent i = some j) :
    mass μ (fun x => ∃ i,A i x) ≤
      (∑ i,mass μ (A i))-(∑ e ∈ E,mass μ (fun x => A e.1 x ∧ A e.2 x)) := by
  have hh := weighted_forest_union_bound μ hμ A parent rank hparent
  rw [parent_sum parent E hE (fun e => mass μ (fun x => A e.1 x ∧ A e.2 x))] at hh
  exact hh

/-- One forest edge can have an exceptional intersection law. All other
edges need only a product lower bound, not necessarily exact independence. -/
theorem one_exception_bound (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (A : ι → Ω → Prop) (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i)
    (E : Finset (ι × ι)) (hE : ∀ i j,(i,j) ∈ E ↔ parent i = some j)
    (f : ι × ι) (hf : f ∈ E) (overlap : ℚ)
    (hprod : ∀ e ∈ E.erase f,
      mass μ (A e.1)*mass μ (A e.2) ≤ mass μ (fun x => A e.1 x ∧ A e.2 x))
    (hexception : overlap ≤ mass μ (fun x => A f.1 x ∧ A f.2 x)) :
    mass μ (fun x => ∃ i,A i x) ≤ polynomial (E.erase f) (fun i => mass μ (A i))-overlap := by
  classical
  have hh := weighted_forest_edge_bound μ hμ A parent rank hparent E hE
  have hs := Finset.sum_le_sum hprod
  have he := Finset.sum_erase_add E (fun e => mass μ (fun x => A e.1 x ∧ A e.2 x)) hf
  unfold polynomial edgeProduct
  linarith

/-- A complete abstract event theorem: the compensation hypothesis can use
finite root geometry, while the ordinary edges use disjoint-coordinate
independence. No covering-system arithmetic is asserted here. -/
theorem compensated_forest_bound (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (A : ι → Ω → Prop) (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i)
    (E : Finset (ι × ι)) (hE : ∀ i j,(i,j) ∈ E ↔ parent i = some j)
    (f : ι × ι) (hf : f ∈ E) (w : ι → ℚ)
    (hw : ∀ i,mass μ (A i) ≤ w i) (overlap charge : ℚ)
    (hprod : ∀ e ∈ E.erase f,
      mass μ (A e.1)*mass μ (A e.2) ≤ mass μ (fun x => A e.1 x ∧ A e.2 x))
    (hexception : overlap ≤ mass μ (fun x => A f.1 x ∧ A f.2 x))
    (hcomp : charge ≤ overlap+
      ∑ i,(w i-mass μ (A i))*(1-neighbor (E.erase f) w i)) :
    mass μ (fun x => ∃ i,A i x) ≤ polynomial (E.erase f) w-charge := by
  exact compensated_overlap_bound (E.erase f) (fun i => mass μ (A i)) w hw
    (mass μ (fun x => ∃ i,A i x)) overlap charge
    (one_exception_bound μ hμ A parent rank hparent E hE f hf overlap hprod hexception) hcomp

#print axioms one_exception_bound
#print axioms compensated_forest_bound
end Erdos7ForestEvents
