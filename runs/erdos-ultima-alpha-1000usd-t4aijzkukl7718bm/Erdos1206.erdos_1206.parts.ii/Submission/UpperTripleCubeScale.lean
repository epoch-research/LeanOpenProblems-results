import FormalConjecturesUtil

/-! The largest three roots in a strict cubic collision lie in one fixed
power-comparability range. No density or score construction is asserted. -/
namespace Erdos1206.UpperTripleCubeScale

lemma max_square_le_middle_cube {a b c d : ℕ} (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) : d^2≤b^3 := by
  have hd : c+(d-c)=d := Nat.add_sub_of_le hcd.le
  have hid : d^3=c^3+(d-c)*(d^2+d*c+c^2) := by
    have hh : (c+(d-c))^3=c^3+(d-c)*((c+(d-c))^2+(c+(d-c))*c+c^2) := by ring
    simpa only [hd] using hh
  have hlow : d^2≤(d-c)*(d^2+d*c+c^2) := by
    calc
      _ ≤ d^2+d*c+c^2 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt hcd)
  omega

/-- Every pair among b,c,d has exponents bounded by the same 3/2 ratio.
The smallest root a need not satisfy this conclusion. -/
lemma upper_interval_power_comparable {a b c d : ℕ} (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) {m n : ℕ}
    (hm : b ≤ m ∧ m ≤ d) (hn : b ≤ n ∧ n ≤ d) : m^2 ≤ n^3 ∧ n^2 ≤ m^3 := by
  have hh := max_square_le_middle_cube hcd he
  constructor
  · exact (Nat.pow_le_pow_left hm.2 2).trans (hh.trans (Nat.pow_le_pow_left hn.1 3))
  · exact (Nat.pow_le_pow_left hn.2 2).trans (hh.trans (Nat.pow_le_pow_left hm.1 3))

#print axioms max_square_le_middle_cube
#print axioms upper_interval_power_comparable
end Erdos1206.UpperTripleCubeScale
