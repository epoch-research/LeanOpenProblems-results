import Mathlib.Tactic

/-! A finite control showing why anchor-compatible elliptic parameters
cannot simply be united into a rational-distance set. This is not a bound
on all parameters, and is not a disproof of Erdős 213. -/
namespace Erdos213.CommonClassPairControl

/-- The six mixed elliptic sections specialized at b=3. -/
def parameter : Fin 6 → ℚ :=
  ![-57/119, -747/2449, 29/1271, -26441/2159,
    -43931/32231, 22174767/41060711]

def compatible (x y : ℚ) : Prop := IsSquare (2*((x*y)^2+7/2))

instance (x y : ℚ) : Decidable (compatible x y) :=
  inferInstanceAs (Decidable (IsSquare (2*((x*y)^2+7/2))))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma exact_control :
    Function.Injective parameter ∧
    (∀ i, parameter i ≠ 0 ∧ parameter i ≠ 1 ∧ parameter i ≠ -1 ∧
      parameter i ≠ 3 ∧ parameter i ≠ -3) ∧
    (∀ i, compatible (parameter i) 1 ∧ compatible (parameter i) (-1) ∧
      compatible (parameter i) 3 ∧ compatible (parameter i) (-3)) ∧
    (∀ i j, i ≠ j → ¬ compatible (parameter i) (parameter j)) := by
  decide +kernel

lemma anchor_compatibility_is_not_pair_compatibility :
    ¬ (∀ x y : ℚ, x ≠ y →
      compatible x 1 → compatible x (-1) → compatible x 3 → compatible x (-3) →
      compatible y 1 → compatible y (-1) → compatible y 3 → compatible y (-3) →
      compatible x y) := by
  intro h
  have hc := exact_control
  exact hc.2.2.2 0 1 (by decide) (h (parameter 0) (parameter 1)
    (hc.1.ne (by decide)) (hc.2.2.1 0).1 (hc.2.2.1 0).2.1
    (hc.2.2.1 0).2.2.1 (hc.2.2.1 0).2.2.2 (hc.2.2.1 1).1
    (hc.2.2.1 1).2.1 (hc.2.2.1 1).2.2.1 (hc.2.2.1 1).2.2.2)

#print axioms exact_control
#print axioms anchor_compatibility_is_not_pair_compatibility
end Erdos213.CommonClassPairControl
