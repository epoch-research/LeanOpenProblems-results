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

#print axioms two_six
end Erdos213.TorsionOctads
