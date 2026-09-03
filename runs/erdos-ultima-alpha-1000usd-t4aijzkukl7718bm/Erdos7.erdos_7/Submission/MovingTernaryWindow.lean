import FormalConjecturesUtil

/-! Local arithmetic of a moving ternary digit window. These identities do
not assert a normal form or an existence theorem for odd covering systems. -/
namespace Erdos7MovingTernaryWindow
set_option autoImplicit false
open scoped BigOperators

theorem digit_class_iff (a p r y z : ℤ) (ha : a ≠ 0) :
    a*p ∣ (r+a*y)-(r+a*z) ↔ p ∣ y-z := by
  have he : (r+a*y)-(r+a*z) = a*(y-z) := by ring
  rw [he]
  exact mul_dvd_mul_iff_left ha

theorem ternary_digit_class_iff (e : ℕ) (r y z : ℤ) :
    (3:ℤ)^(e+1) ∣ (r+3^e*y)-(r+3^e*z) ↔ (3:ℤ) ∣ y-z := by
  rw [pow_succ]
  exact digit_class_iff _ _ _ _ _ (pow_ne_zero _ (by norm_num))

theorem quotient_after_split (a b r k c : ℤ) (ha : a ≠ 0) :
    (b+k*(a*c)-r)/a = (b-r)/a+k*c := by
  have he : b+k*(a*c)-r = (b-r)+a*(k*c) := by ring
  rw [he, Int.add_mul_ediv_left _ _ ha]

theorem advance_digit (S : Set (ZMod 3)) (k t : ℤ) :
    ((k+3*t : ℤ) : ZMod 3) ∈ S ↔ (k : ZMod 3) ∈ S := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [Int.cast_add, Int.cast_mul, h3]

/-- Splitting by a cofactor coprime to three merely permutes the three
possible next digits; it does not delete or duplicate one. -/
def digitRotation (c y : ZMod 3) (hc : c ≠ 0) : Equiv.Perm (ZMod 3) :=
  (Equiv.mulLeft₀ c hc).trans (Equiv.addLeft y)

lemma digitRotation_apply (c y : ZMod 3) (hc : c ≠ 0) (k : ZMod 3) :
    digitRotation c y hc k = y+c*k := rfl

theorem digit_rotation_bijective (c y : ZMod 3) (hc : c ≠ 0) :
    Function.Bijective (fun k : ZMod 3 => y+c*k) :=
  (digitRotation c y hc).bijective

/-- Exact finite numerator used when higher ternary powers are charged to
one current digit. There is no infinite-tail approximation here. -/
theorem higher_digit_sum (e k : ℕ) :
    (2:ℤ) * (∑ t ∈ Finset.range k, (3:ℤ)^(e+1+t)) =
      (3:ℤ)^(e+1) * (3^k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih, pow_succ, pow_add (3:ℤ) (e+1) k]
      ring

#print axioms ternary_digit_class_iff
#print axioms quotient_after_split
#print axioms advance_digit
#print axioms digit_rotation_bijective
#print axioms higher_digit_sum
end Erdos7MovingTernaryWindow
