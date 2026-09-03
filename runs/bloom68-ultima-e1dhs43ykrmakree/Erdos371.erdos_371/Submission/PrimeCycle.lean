import FormalConjecturesUtil

/-! An auxiliary obstruction to a short directed cycle of large prime labels.
This finite lemma is not an ordinary-density cancellation theorem. -/
namespace Erdos371PrimeCycle

/-- Three oriented determinant-one edges force the first label to be no larger
than a quadratic expression in the cofactors. Primality is not needed. -/
theorem label_le_cofactor_sum (a b c d e f p q r : ℕ)
    (hc : 0 < c) (he : 0 < e)
    (h₁ : a * p + 1 = b * q)
    (h₂ : c * q + 1 = d * r)
    (h₃ : e * r + 1 = f * p) :
    p ≤ c * e + b * e + b * d := by
  have hid : a * c * e * p + (c * e + b * e + b * d) = b * d * f * p := by
    calc
      _ = c * e * (a * p + 1) + b * e + b * d := by ring
      _ = b * e * (c * q + 1) + b * d := by rw [h₁]; ring
      _ = b * d * (e * r + 1) := by rw [h₂]; ring
      _ = _ := by rw [h₃]; ring
  have hleft : p ∣ a * c * e * p := dvd_mul_left p (a * c * e)
  have htotal : p ∣ a * c * e * p + (c * e + b * e + b * d) := by
    rw [hid]
    exact dvd_mul_left p (b * d * f)
  have hsum : p ∣ c * e + b * e + b * d :=
    (Nat.dvd_add_iff_right hleft).2 htotal
  exact Nat.le_of_dvd (by positivity) hsum

/-- A cycle with all cofactors at most `M` has a label at most `3*M^2`. -/
theorem label_le_three_sq (a b c d e f p q r M : ℕ)
    (hc : 0 < c) (he : 0 < e)
    (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (h₁ : a * p + 1 = b * q)
    (h₂ : c * q + 1 = d * r)
    (h₃ : e * r + 1 = f * p) : p ≤ 3 * M ^ 2 := by
  have h := label_le_cofactor_sum a b c d e f p q r hc he h₁ h₂ h₃
  have hce := Nat.mul_le_mul hcM heM
  have hbe := Nat.mul_le_mul hbM heM
  have hbd := Nat.mul_le_mul hbM hdM
  nlinarith

#print axioms label_le_three_sq
end Erdos371PrimeCycle
