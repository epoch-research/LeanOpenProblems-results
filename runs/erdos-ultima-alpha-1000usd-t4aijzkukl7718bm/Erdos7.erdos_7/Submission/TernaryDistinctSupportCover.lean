import FormalConjecturesUtil

/-!
A counterexample to discarding the arithmetic prime structure in the odd
covering problem. This is NOT a covering system of integers: its five
independent coordinates all have cardinality three.
-/
namespace Erdos7TernaryDistinctSupportCover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Five unary supports and two triangles sharing coordinate zero. -/
def supp : Fin 11 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 1}, {1, 2}, {0, 2}, {0, 3}, {3, 4}, {0, 4}]

/-- Values outside a box's support are irrelevant. -/
def residue : Fin 11 → Fin 5 → Fin 3 :=
  ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![1, 0, 2, 0, 0],
    ![2, 0, 0, 1, 0], ![0, 0, 0, 2, 1], ![2, 0, 0, 0, 2]]

def privatePoint : Fin 11 → Fin 5 → Fin 3 :=
  ![![0, 1, 1, 1, 1], ![1, 0, 1, 1, 1], ![1, 2, 0, 1, 1],
    ![2, 1, 1, 0, 1], ![2, 1, 1, 2, 0],
    ![1, 1, 1, 1, 1], ![1, 2, 1, 1, 1], ![1, 2, 2, 1, 1],
    ![2, 1, 1, 1, 1], ![2, 1, 1, 2, 1], ![2, 1, 1, 2, 2]]

/-- All supports are nonempty and distinct. -/
theorem support_properties :
    (∀ j, (supp j).Nonempty) ∧ Function.Injective supp := by
  decide +kernel

/-- The family contains every nonempty subset of each of its supports. -/
theorem divisor_closed :
    ∀ j, ∀ s : Finset (Fin 5), s.Nonempty → s ⊆ supp j →
      ∃ k, supp k = s := by
  decide +kernel

/-- The eleven boxes cover all 243 points of the ternary cube. -/
theorem covers :
    ∀ x : Fin 5 → Fin 3, ∃ j, ∀ i ∈ supp j, x i = residue j i := by
  decide +kernel

/-- No box can be removed from this cover. -/
theorem private_points :
    ∀ j, ∀ k, (∀ i ∈ supp k, privatePoint j i = residue k i) ↔ k = j := by
  decide +kernel

/-- Comparable distinct boxes are disjoint, as in irredundant integer covers. -/
theorem comparable_disjoint :
    ∀ j k, j ≠ k → supp j ⊆ supp k →
      ∃ i ∈ supp j, residue j i ≠ residue k i := by
  decide +kernel

/-- A single finite certificate for the general odd-alphabet counterexample. -/
theorem exists_irredundant_distinct_support_cover :
    ∃ (s : Fin 11 → Finset (Fin 5)) (a : Fin 11 → Fin 5 → Fin 3),
      Function.Injective s ∧ (∀ j, (s j).Nonempty) ∧
      (∀ x : Fin 5 → Fin 3, ∃ j, ∀ i ∈ s j, x i = a j i) ∧
      (∀ j, ∃ x : Fin 5 → Fin 3,
        ∀ k, (∀ i ∈ s k, x i = a k i) ↔ k = j) ∧
      (∀ j, ∀ t : Finset (Fin 5), t.Nonempty → t ⊆ s j → ∃ k, s k = t) := by
  exact ⟨supp, residue, support_properties.2, support_properties.1, covers,
    fun j => ⟨privatePoint j, private_points j⟩, divisor_closed⟩

#print axioms exists_irredundant_distinct_support_cover
#print axioms comparable_disjoint
end Erdos7TernaryDistinctSupportCover
