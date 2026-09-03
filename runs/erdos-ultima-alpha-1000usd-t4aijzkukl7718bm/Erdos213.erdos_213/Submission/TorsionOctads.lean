import FormalConjecturesUtil

/-! Finite group obstructions for a proposed elliptic-curve octad construction.
No torsion classification theorem or conclusion about arbitrary distance sets
is asserted here. All finite certificates use kernel-checked `decide`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 10000

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

namespace Erdos213.TorsionOctads

/-- Every zero-sum eight-element subset splits into two zero-sum quadruples.
The finite formulation makes the certificates directly computable. -/
def OctadsSplit (G : Type*) [AddCommMonoid G] [Fintype G] [DecidableEq G] : Prop :=
  ∀ S ∈ (Finset.univ : Finset G).powersetCard 8,
    (∑ x ∈ S, x) = 0 → ∃ T ∈ S.powersetCard 4, (∑ x ∈ T, x) = 0

lemma split_subset {G : Type*} [AddCommMonoid G] [Fintype G] [DecidableEq G]
    (h : OctadsSplit G) (S : Finset G) (hcard : S.card = 8)
    (hsum : (∑ x ∈ S, x) = 0) :
    ∃ T : Finset G, T ⊆ S ∧ T.card = 4 ∧ (∑ x ∈ T, x) = 0 := by
  obtain ⟨T,hT,hzero⟩ := h S
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S,hcard⟩) hsum
  exact ⟨T,(Finset.mem_powersetCard.mp hT).1,
    (Finset.mem_powersetCard.mp hT).2,hzero⟩

lemma cyclic_eight : OctadsSplit (ZMod 8) := by
  unfold OctadsSplit
  decide
lemma cyclic_nine : OctadsSplit (ZMod 9) := by
  unfold OctadsSplit
  decide
lemma cyclic_ten : OctadsSplit (ZMod 10) := by
  unfold OctadsSplit
  decide
lemma cyclic_twelve : OctadsSplit (ZMod 12) := by
  unfold OctadsSplit
  decide
lemma two_four : OctadsSplit (ZMod 2 × ZMod 4) := by
  unfold OctadsSplit
  decide
lemma two_six : OctadsSplit (ZMod 2 × ZMod 6) := by
  unfold OctadsSplit
  decide
lemma two_eight : OctadsSplit (ZMod 2 × ZMod 8) := by
  unfold OctadsSplit
  decide

/-- The analogous statement fails for the infinite cyclic group. In
particular, the finite certificates are not a group-theoretic obstruction
to using rational elliptic-curve points of infinite order. -/
def integerOctad : Finset ℤ := {-8,-7,-6,2,3,4,5,7}

lemma integer_octad_certificate : integerOctad.card = 8 ∧
    (∑ x ∈ integerOctad, x) = 0 ∧
    ∀ T ∈ integerOctad.powersetCard 4, (∑ x ∈ T, x) ≠ 0 := by
  decide

#print axioms cyclic_eight
#print axioms cyclic_nine
#print axioms cyclic_ten
#print axioms cyclic_twelve
#print axioms two_four
#print axioms two_six
#print axioms two_eight
#print axioms split_subset
#print axioms integer_octad_certificate

end Erdos213.TorsionOctads
