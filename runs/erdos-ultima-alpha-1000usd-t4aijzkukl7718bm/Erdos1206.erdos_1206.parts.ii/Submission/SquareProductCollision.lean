import FormalConjecturesUtil

/-! An elementary obstruction to one proposed square-class restriction.
This is not a disproof of the positive-density conjecture. -/

namespace Erdos1206

/-- A nontrivial primitive cubic collision can have a square product of roots. -/
theorem square_product_primitive_cube_collision :
    ∃ a b c d r : ℕ,
      0 < a ∧ a < b ∧ b < c ∧ c < d ∧
      a^3+d^3=b^3+c^3 ∧ a*b*c*d=r^2 ∧
      Nat.Coprime (Nat.gcd a b) (Nat.gcd c d) := by
  refine ⟨243,484,1587,1600,546480,?_⟩
  norm_num [Nat.Coprime]

/-- The same example uses only the square classes of `1` and `3`. -/
theorem cube_collision_in_two_square_classes :
    (3*9^2 : ℕ)^3 + (40^2)^3 = (22^2)^3 + (3*23^2)^3 ∧
      (3*9^2 : ℕ) ≠ 22^2 ∧ (3*9^2 : ℕ) ≠ 3*23^2 := by
  norm_num

#print axioms square_product_primitive_cube_collision
#print axioms cube_collision_in_two_square_classes

end Erdos1206
