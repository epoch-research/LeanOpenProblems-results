import Submission.RothQuant

/-!
# Exact joint integrality of a Roth pair

For coprime bases `n` and `n+b`, the integer pair label and the difference of
square multiples determine both cofactors. Their simultaneous integrality is
one congruence modulo `b^3`, not independent rounding of two real quantities.
The result is an exact finite parametrization and supplies no density estimate
for the occupied congruence classes.
-/

namespace RothLattice

/-- Difference of the two square multiples. -/
def delta (n b m m' : ℤ) : ℤ := m' * (n + b) ^ 2 - m * n ^ 2

/-- Numerator reconstructing the cofactor at the left base. -/
def leftNumerator (n b k e : ℤ) : ℤ :=
  (n + b) ^ 2 * k - (2 * n + 3 * b) * e

/-- Numerator reconstructing the cofactor at the right base. -/
def rightNumerator (n b k e : ℤ) : ℤ :=
  n ^ 2 * k - (2 * n - b) * e

lemma determinant (n b : ℤ) :
    (2 * n + 3 * b) * n ^ 2 - (2 * n - b) * (n + b) ^ 2 = b ^ 3 := by
  ring

lemma leftNumerator_label (n b m m' : ℤ) :
    leftNumerator n b (RothLocal.label n (n + b) m m') (delta n b m m') =
      b ^ 3 * m := by
  unfold leftNumerator RothLocal.label delta
  ring

lemma rightNumerator_label (n b m m' : ℤ) :
    rightNumerator n b (RothLocal.label n (n + b) m m') (delta n b m m') =
      b ^ 3 * m' := by
  unfold rightNumerator RothLocal.label delta
  ring

lemma recover_label (n b k e : ℤ) :
    (2 * n + 3 * b) * rightNumerator n b k e -
      (2 * n - b) * leftNumerator n b k e = b ^ 3 * k := by
  unfold rightNumerator leftNumerator
  ring

lemma recover_delta (n b k e : ℤ) :
    (n + b) ^ 2 * rightNumerator n b k e -
      n ^ 2 * leftNumerator n b k e = b ^ 3 * e := by
  unfold rightNumerator leftNumerator
  ring

/-- One divisibility condition forces the other, by coprimality of the bases. -/
lemma dvd_right_of_dvd_left {n b k e : ℤ} (hcop : IsCoprime b (n + b))
    (hleft : b ^ 3 ∣ leftNumerator n b k e) :
    b ^ 3 ∣ rightNumerator n b k e := by
  have hmul : b ^ 3 ∣ (n + b) ^ 2 * rightNumerator n b k e := by
    have heq := recover_delta n b k e
    have hsum : (n + b) ^ 2 * rightNumerator n b k e =
        n ^ 2 * leftNumerator n b k e + b ^ 3 * e := by linarith
    rw [hsum]
    exact dvd_add (dvd_mul_of_dvd_right hleft _) (dvd_mul_right _ _)
  exact (hcop.pow (m := 3) (n := 2)).dvd_of_dvd_mul_left hmul

/-- The image of the pair-label map is the primitive congruence lattice with
modulus `b^3`. The cofactors may be arbitrary integers; interval hits impose
additional inequalities not asserted by this parametrization. -/
theorem exists_pair_iff {n b k e : ℤ} (hb : b ≠ 0) (hcop : IsCoprime b (n + b)) :
    (∃ m m' : ℤ, k = RothLocal.label n (n + b) m m' ∧ e = delta n b m m') ↔
      b ^ 3 ∣ leftNumerator n b k e := by
  constructor
  · rintro ⟨m, m', rfl, rfl⟩
    rw [leftNumerator_label]
    exact dvd_mul_right _ _
  · intro hleft
    obtain ⟨m, hm⟩ := hleft
    obtain ⟨m', hm'⟩ := dvd_right_of_dvd_left hcop ⟨m, hm⟩
    have hb3 : b ^ 3 ≠ 0 := pow_ne_zero 3 hb
    have hk : b ^ 3 * RothLocal.label n (n + b) m m' = b ^ 3 * k := by
      calc
        b ^ 3 * RothLocal.label n (n + b) m m' =
            (2 * n + 3 * b) * (b ^ 3 * m') - (2 * n - b) * (b ^ 3 * m) := by
          unfold RothLocal.label
          ring
        _ = (2 * n + 3 * b) * rightNumerator n b k e -
            (2 * n - b) * leftNumerator n b k e := by rw [hm, hm']
        _ = b ^ 3 * k := recover_label n b k e
    have he : b ^ 3 * delta n b m m' = b ^ 3 * e := by
      calc
        b ^ 3 * delta n b m m' =
            (n + b) ^ 2 * (b ^ 3 * m') - n ^ 2 * (b ^ 3 * m) := by
          unfold delta
          ring
        _ = (n + b) ^ 2 * rightNumerator n b k e -
            n ^ 2 * leftNumerator n b k e := by rw [hm, hm']
        _ = b ^ 3 * e := recover_delta n b k e
    exact ⟨m, m', (mul_left_cancel₀ hb3 hk).symm, (mul_left_cancel₀ hb3 he).symm⟩

/-- Outside the zero-gap degeneracy, the pair label and difference uniquely
specify the two integer cofactors. -/
theorem pair_unique {n b m₀ m₀' m₁ m₁' : ℤ} (hb : b ≠ 0)
    (hk : RothLocal.label n (n + b) m₀ m₀' = RothLocal.label n (n + b) m₁ m₁')
    (he : delta n b m₀ m₀' = delta n b m₁ m₁') : m₀ = m₁ ∧ m₀' = m₁' := by
  have hleft := leftNumerator_label n b m₀ m₀'
  have hright := rightNumerator_label n b m₀ m₀'
  rw [hk, he, leftNumerator_label] at hleft
  rw [hk, he, rightNumerator_label] at hright
  exact ⟨(mul_left_cancel₀ (pow_ne_zero 3 hb) hleft).symm,
    (mul_left_cancel₀ (pow_ne_zero 3 hb) hright).symm⟩

#print axioms exists_pair_iff
#print axioms pair_unique

end RothLattice
