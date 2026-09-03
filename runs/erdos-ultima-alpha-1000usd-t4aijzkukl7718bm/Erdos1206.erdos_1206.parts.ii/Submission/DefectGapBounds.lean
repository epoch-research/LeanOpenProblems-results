import Submission.ConicGCDIdentity

/-!
Further exact information about the root-sum defect of a cubic collision.
These results do not assert a density construction or a global counting bound.
-/
namespace Erdos1206.ConicHeightProduct

lemma six_dvd_defect {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) : 6 ∣ defect a b c d := by
  have hsum := root_sum_lt hab hbc hcd he
  have h2 : 2 ∣ defect a b c d := by
    have hn (n : ℕ) : (n : ZMod 2)^3 = n := by
      have hh : ∀ x : ZMod 2, x^3=x := by decide +kernel
      exact hh n
    have hh := congrArg (fun n : ℕ => (n : ZMod 2)) he
    simp only [Nat.cast_add, Nat.cast_pow, hn] at hh
    apply (ZMod.natCast_eq_zero_iff _ 2).mp
    simp only [defect, Nat.cast_sub hsum.le, Nat.cast_add]
    exact sub_eq_zero.mpr hh.symm
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2
    (three_dvd_defect hab hbc hcd he)

/-- The two nonnegative adjacent gaps differ by exactly the root-sum defect. -/
lemma adjacent_gap_difference {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) :
    b-a = (d-c) + defect a b c d := by
  have hh := root_sum_lt hab hbc hcd he
  dsimp [defect]
  omega

/-- A small defect forces the first adjacent gap to be small relative to the
largest root. No primitivity assumption is required. -/
theorem adjacent_gap_sq_bound {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) :
    3*(b-a)^2 ≤ 7*defect a b c d*d := by
  have hd : 0 < d := by omega
  have hsum := root_sum_lt hab hbc hcd he
  have hkd := (defect_lt hab hbc hcd).le
  have hQ : 3*d^2+3*d*defect a b c d+(defect a b c d)^2 ≤ 7*d^2 := by
    have h₁ := Nat.mul_le_mul_left d hkd
    have h₂ := Nat.pow_le_pow_left hkd 2
    nlinarith
  have hxy : b-a ≤ c-a := by omega
  have hz : d ≤ b+c := by omega
  have hlower : 3*(b-a)^2*d ≤ 3*((b-a)*(c-a)*(b+c)) := by
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul_left (b-a) hxy) hz
    nlinarith only [hh]
  have hupper : 3*((b-a)*(c-a)*(b+c)) ≤
      defect a b c d*(7*d^2) := by
    rw [product_identity hab hbc hcd he]
    exact Nat.mul_le_mul_left _ hQ
  apply Nat.le_of_mul_le_mul_right (c := d) (hc := hd)
  calc
    _ ≤ 3*((b-a)*(c-a)*(b+c)) := hlower
    _ ≤ defect a b c d*(7*d^2) := hupper
    _ = _ := by ring

/-- The same bound expressed in terms of any upper bound on the defect. -/
theorem bounded_defect_adjacent_gap {a b c d K N : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) (hk : defect a b c d ≤ K) (hd : d ≤ N) :
    3*(b-a)^2 ≤ 7*K*N := by
  exact (adjacent_gap_sq_bound hab hbc hcd he).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 7 hk) hd)

/-- A determinant identity at fixed root-sum defect. The natural-number gap
parameters are cast to integers to avoid truncated subtraction. -/
theorem defect_determinant_identity {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) :
    let x : ℤ := b-a
    let y : ℤ := c-a
    let k : ℤ := defect a b c d
    12*x*y*(x-k)*(y-k) -
      3*(2*x*y-2*k*(d:ℤ)-k^2)^2 = k^4 := by
  dsimp only
  have hsum := root_sum_lt hab hbc hcd he
  have hk : ((defect a b c d : ℕ) : ℤ) = (b:ℤ)+c-a-d := by
    simp only [defect, Nat.cast_sub hsum.le, Nat.cast_add]
    ring
  have heZ : (a:ℤ)^3+d^3=b^3+c^3 := by exact_mod_cast he
  rw [hk]
  linear_combination -4*((a:ℤ)+d-b-c)*heZ

/-- A square-completion form of the determinant identity, using the integral
parameter `j=k/6`. In particular the constant in this norm equation is
independent of the size of the four roots once the defect is fixed. -/
theorem defect_norm_identity {a b c d j : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) (hj : defect a b c d = 6*j) :
    let x : ℤ := b-a
    let y : ℤ := c-a
    (x*y-6*(j:ℤ)*d-18*(j:ℤ)^2)^2+108*(j:ℤ)^4 =
      x*(x-6*(j:ℤ))*y*(y-6*(j:ℤ)) := by
  have hh := defect_determinant_identity hab hbc hcd he
  dsimp only at hh ⊢
  rw [hj] at hh
  push_cast at hh
  nlinarith only [hh]

#print axioms six_dvd_defect
#print axioms adjacent_gap_sq_bound
#print axioms bounded_defect_adjacent_gap
#print axioms defect_determinant_identity
#print axioms defect_norm_identity

end Erdos1206.ConicHeightProduct
