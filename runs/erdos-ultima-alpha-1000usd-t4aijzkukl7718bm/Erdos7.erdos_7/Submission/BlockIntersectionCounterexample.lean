import FormalConjecturesUtil

/-! An exact limitation of an intersection-only block relaxation.
This is NOT an arithmetic covering system. Its events are arbitrary Boolean
subsets and are not asserted to be p-adic rectangles. -/
namespace Erdos7BlockIntersectionCounterexample
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The eight nonzero shapes in a 3 by 3 exponent rectangle. -/
def shape : Fin 8 → ℕ × ℕ := ![(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def boxWeight : Fin 8 → ℕ := ![4,8,5,1,7,9,2,8]

def atom : Fin 12 → ℕ := ![0,1,3,4,5,11,13,31,36,44,109,247]
def numerator : Fin 12 → ℕ := ![12880,1560,212,2576,48,48,1104,192,596,48,288,48]

def referenceAtom : Fin 9 → ℕ := ![0,1,3,4,13,31,36,109,255]
def referenceNumerator : Fin 9 → ℕ := ![12880,1560,260,2576,1152,192,644,288,48]

def hit (mask : ℕ) (i : Fin 8) : Bool := mask.testBit i.val

def intersection {n : ℕ} (a w : Fin n → ℕ) (mask : ℕ) : ℕ :=
  ∑ i, if a i &&& mask = mask then w i else 0

def score (mask : ℕ) : ℕ := ∑ i, if hit mask i then boxWeight i else 0

def hingeCost {n : ℕ} (a w : Fin n → ℕ) : ℕ := ∑ i, w i*(score (a i)-11)

theorem masses : (∑ i, numerator i) = 19600 ∧ (∑ i, referenceNumerator i) = 19600 := by
  decide +kernel

/-- Every subset-intersection mass is bounded by the reference law, not just
pair intersections. This still does not imply the weighted convex comparison. -/
theorem all_intersections : ∀ mask : Fin 256,
    intersection atom numerator mask.val ≤ intersection referenceAtom referenceNumerator mask.val := by
  decide +kernel

theorem single_marginals : ∀ i : Fin 8,
    intersection atom numerator (2^i.val) = intersection referenceAtom referenceNumerator (2^i.val) := by
  decide +kernel

theorem costs : hingeCost atom numerator = 9392 ∧ hingeCost referenceAtom referenceNumerator = 9344 := by
  decide +kernel

/-- The reference states really are the lower exponent rectangles. -/
theorem reference_rectangles : ∀ (r : Fin 9) (i : Fin 8),
    hit (referenceAtom r) i = true ↔
      (shape i).1 ≤ r.val / 3 ∧ (shape i).2 ≤ r.val % 3 := by
  decide +kernel

/-- The abstract counterexample cannot be represented by the actual coarse
row/column rectangles. In particular the event of shape(1,1) intersects the
column of shape(0,1) at atom11 but leaves it at atom44. Two single columns at
the same digit level are either equal or disjoint. -/
theorem not_coarse_rectangle_representation {A B : Type*}
    (row : Fin 12 → A) (col : Fin 12 → B) (r : A) (c c₀ : B)
    (hD : ∀ i, hit (atom i) 3 = true ↔ row i = r ∧ col i = c)
    (hA : ∀ i, hit (atom i) 0 = true ↔ col i = c₀) : False := by
  have hD₁ : hit (atom 5) 3 = true := by decide +kernel
  have hD₂ : hit (atom 9) 3 = true := by decide +kernel
  have hA₁ : hit (atom 5) 0 = true := by decide +kernel
  have hA₂ : hit (atom 9) 0 ≠ true := by decide +kernel
  have hc : c = c₀ := ((hD 5).mp hD₁).2.symm.trans ((hA 5).mp hA₁)
  exact hA₂ ((hA 9).mpr (((hD 9).mp hD₂).2.trans hc))

/-- Exact positive gap 3/1225 for the convex hinge at11. The denominator19600
is the common total mass of both laws. -/
theorem weighted_gap :

    (hingeCost referenceAtom referenceNumerator : ℚ)/19600+3/1225 =
      (hingeCost atom numerator : ℚ)/19600 := by
  rw [costs.1, costs.2]
  norm_num

theorem not_weighted_domination :
    ¬ hingeCost atom numerator ≤ hingeCost referenceAtom referenceNumerator := by
  rw [costs.1, costs.2]
  omega

#print axioms all_intersections
#print axioms weighted_gap
#print axioms not_coarse_rectangle_representation
#print axioms not_weighted_domination
end Erdos7BlockIntersectionCounterexample
