import FormalConjecturesUtil

/-!
# Local rigidity of square multiples

There are at most two bases in a sufficiently small block whose square multiples
hit a given short interval.  The proof uses an exact integer pair label, a
scaled (division-free) estimate forcing that label to vanish, and a polynomial
identity ruling out three distinct bases with all pair labels zero.

This is a finite local theorem only.  It does not assert a squarefree-gap bound
at exponent one quarter, or the all-positive-exponents squarefree-gap conjecture.
-/

namespace RothLocal

/-- The integer label of a pair of square-multiple representations. -/
def label (u v m m' : ℤ) : ℤ :=
  (3 * v - u) * m' - (3 * u - v) * m

lemma label_swap (u v m m' : ℤ) : label v u m' m = -label u v m m' := by
  simp only [label]
  ring

/-- An exact identity expressing the pair label by the difference of the multiples. -/
lemma label_identity (u v m m' : ℤ) :
    label u v m m' * v ^ 2 =
      m * (v - u) ^ 3 + (3 * v - u) * (m' * v ^ 2 - m * u ^ 2) := by
  simp only [label]
  ring

/-- The scaled identity, with no division by the bases. -/
lemma label_scaled_identity (u v m m' : ℤ) :
    label u v m m' * (u ^ 2 * v ^ 2) =
      (m * u ^ 2) * (v - u) ^ 3 +
        (u ^ 2 * (3 * v - u)) * (m' * v ^ 2 - m * u ^ 2) := by
  simp only [label]
  ring

/-- The exact error identity relative to an arbitrary interval origin `x`. -/
lemma label_error_identity (x u v m m' : ℤ) :
    label u v m m' * u ^ 2 * v ^ 2 =
      x * (v - u) ^ 3 + (m' * v ^ 2 - x) * u ^ 2 * (3 * v - u) -
        (m * u ^ 2 - x) * v ^ 2 * (3 * u - v) := by
  simp only [label]
  ring

/-- Three distinct bases cannot have all three labels zero if the first factor is nonzero. -/
lemma no_three_zero_labels {u v w m₁ m₂ m₃ : ℤ}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hm₁ : m₁ ≠ 0)
    (huv0 : label u v m₁ m₂ = 0)
    (hvw0 : label v w m₂ m₃ = 0)
    (huw0 : label u w m₁ m₃ = 0) : False := by
  have hprod : 12 * m₁ * (u - v) * (u - w) * (v - w) = 0 := by
    simp only [label] at huv0 hvw0 huw0
    linear_combination
      (3 * v - w) * (3 * w - u) * huv0 +
      (3 * v - u) * (3 * w - u) * hvw0 -
      (3 * v - u) * (3 * w - v) * huw0
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hm₁)
      (sub_ne_zero.mpr huv)) (sub_ne_zero.mpr huw)) (sub_ne_zero.mpr hvw)) hprod

/-- Integer discreteness in a form that avoids fractions in the application. -/
private lemma integer_eq_zero_of_scaled_bounds {k P A D E : ℤ}
    (hP : 0 < P) (hA0 : 0 ≤ A) (hA : 16 * A < P) (hE : 8 * E ≤ P)
    (hDlo : -E ≤ D) (hDhi : D ≤ E) (hid : k * P = A + D) : k = 0 := by
  have hk_nonneg : 0 ≤ k := by
    by_contra hk
    have hk' : k ≤ -1 := by omega
    have hp := mul_le_mul_of_nonneg_right hk' hP.le
    nlinarith only [hp, hA0, hE, hDlo, hid, hP]
  have hk_nonpos : k ≤ 0 := by
    by_contra hk
    have hk' : 1 ≤ k := by omega
    have hp := mul_le_mul_of_nonneg_right hk' hP.le
    nlinarith only [hp, hA, hE, hDhi, hid, hP]
  omega

/-- The main term is less than `P / 16`, and the absolute error is at most `P / 8`,
where `P = u² v²`.  All estimates below are written without division. -/
private lemma label_eq_zero_of_ordered_int_bounds
    {x H N B u v m m' : ℤ}
    (hx : 0 ≤ x) (hH0 : 0 ≤ H) (hN : 0 < N)
    (hH : 64 * H ≤ N) (hB : B ≤ N)
    (hsmall : 16 * (x + H) * B ^ 3 < N ^ 4)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ N + B)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H) :
    label u v m m' = 0 := by
  have hu0 : 0 < u := hN.trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hb0 : 0 ≤ v - u := sub_nonneg.mpr huv
  have hbB : v - u ≤ B := by linarith
  have hv2 : v ≤ 2 * u := by linarith
  have hc0 : 0 ≤ 3 * v - u := by linarith
  have hu2v2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu0.le huv 2
  have hN4 : N ^ 4 ≤ u ^ 2 * v ^ 2 := by
    calc
      N ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ hN.le hu 4
      _ = u ^ 2 * u ^ 2 := by ring
      _ ≤ u ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_left hu2v2 (sq_nonneg u)
  have hA0 : 0 ≤ (m * u ^ 2) * (v - u) ^ 3 :=
    mul_nonneg (le_trans hx hm.1.le) (pow_nonneg hb0 3)
  have hA : 16 * ((m * u ^ 2) * (v - u) ^ 3) < u ^ 2 * v ^ 2 := by
    have hprod : (m * u ^ 2) * (v - u) ^ 3 ≤ (x + H) * B ^ 3 :=
      mul_le_mul hm.2 (pow_le_pow_left₀ hb0 hbB 3)
        (pow_nonneg hb0 3) (add_nonneg hx hH0)
    calc
      _ ≤ 16 * ((x + H) * B ^ 3) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ < N ^ 4 := by nlinarith only [hsmall]
      _ ≤ u ^ 2 * v ^ 2 := hN4
  have hEbase : 8 * H * (3 * v - u) ≤ u ^ 2 := by
    calc
      _ ≤ 40 * H * u := by
        nlinarith only [mul_nonneg hH0 (sub_nonneg.mpr hv2)]
      _ ≤ 64 * H * u := by nlinarith only [mul_nonneg hH0 hu0.le]
      _ ≤ u ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right (hH.trans hu) hu0.le]
  have hE : 8 * (H * u ^ 2 * (3 * v - u)) ≤ u ^ 2 * v ^ 2 := by
    calc
      _ = u ^ 2 * (8 * H * (3 * v - u)) := by ring
      _ ≤ u ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_left hEbase (sq_nonneg u)
      _ ≤ u ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_left hu2v2 (sq_nonneg u)
  have hdiff : -H ≤ m' * v ^ 2 - m * u ^ 2 ∧
      m' * v ^ 2 - m * u ^ 2 ≤ H := by
    constructor <;> linarith [hm.1, hm.2, hm'.1, hm'.2]
  have hDlo : -(H * u ^ 2 * (3 * v - u)) ≤
      (u ^ 2 * (3 * v - u)) * (m' * v ^ 2 - m * u ^ 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hdiff.1
      (mul_nonneg (sq_nonneg u) hc0)]
  have hDhi : (u ^ 2 * (3 * v - u)) * (m' * v ^ 2 - m * u ^ 2) ≤
      H * u ^ 2 * (3 * v - u) := by
    nlinarith only [mul_le_mul_of_nonneg_left hdiff.2
      (mul_nonneg (sq_nonneg u) hc0)]
  exact integer_eq_zero_of_scaled_bounds
    (mul_pos (pow_pos hu0 2) (pow_pos hv0 2)) hA0 hA hE hDlo hDhi
    (label_scaled_identity u v m m')

private lemma label_eq_zero_of_ordered_bounds
    {x H N B u v m m' : ℕ}
    (hN : 0 < N) (hH : 64 * H ≤ N) (hB : B ≤ N)
    (hsmall : 16 * (x + H) * B ^ 3 < N ^ 4)
    (hu : N ≤ u) (huv : u ≤ v) (hv : v ≤ N + B)
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H) :
    label (u : ℤ) (v : ℤ) (m : ℤ) (m' : ℤ) = 0 := by
  exact label_eq_zero_of_ordered_int_bounds (x := x) (H := H) (N := N) (B := B)
    (Nat.cast_nonneg x) (Nat.cast_nonneg H) (by exact_mod_cast hN)
    (by exact_mod_cast hH) (by exact_mod_cast hB) (by exact_mod_cast hsmall)
    (by exact_mod_cast hu) (by exact_mod_cast huv) (by exact_mod_cast hv)
    (by exact_mod_cast hm) (by exact_mod_cast hm')

/-- Any two square multiples in the short interval, with bases in the same small block,
have zero integer label.  The bases need not be ordered or distinct. -/
lemma pair_label_eq_zero {x H N B u v m m' : ℕ}
    (hN : 0 < N) (hH : 64 * H ≤ N) (hB : B ≤ N)
    (hsmall : 16 * (x + H) * B ^ 3 < N ^ 4)
    (hu : u ∈ Finset.Icc N (N + B)) (hv : v ∈ Finset.Icc N (N + B))
    (hm : x < m * u ^ 2 ∧ m * u ^ 2 ≤ x + H)
    (hm' : x < m' * v ^ 2 ∧ m' * v ^ 2 ≤ x + H) :
    label (u : ℤ) (v : ℤ) (m : ℤ) (m' : ℤ) = 0 := by
  rcases Finset.mem_Icc.mp hu with ⟨huN, huB⟩
  rcases Finset.mem_Icc.mp hv with ⟨hvN, hvB⟩
  rcases le_total u v with huv | hvu
  · exact label_eq_zero_of_ordered_bounds hN hH hB hsmall huN huv hvB hm hm'
  · have hz := label_eq_zero_of_ordered_bounds hN hH hB hsmall hvN hvu huB hm' hm
    rw [label_swap] at hz
    exact neg_eq_zero.mp hz

open Classical in
/-- At most two bases in `[N, N + B]` have a square multiple in `(x, x + H]`,
provided the interval is short and the block satisfies the cubic smallness condition. -/
theorem square_multiples_card_le_two (x H N B : ℕ)
    (hN : 0 < N) (hH : 64 * H ≤ N) (hB : B ≤ N)
    (hsmall : 16 * (x + H) * B ^ 3 < N ^ 4) :
    ((Finset.Icc N (N + B)).filter
      (fun d => ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H)).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hcard)
  rcases Finset.mem_filter.mp hu with ⟨hu, m₁, hm₁⟩
  rcases Finset.mem_filter.mp hv with ⟨hv, m₂, hm₂⟩
  rcases Finset.mem_filter.mp hw with ⟨hw, m₃, hm₃⟩
  have hm₁0 : (m₁ : ℤ) ≠ 0 := by
    have hm₁nat : m₁ ≠ 0 := by
      intro hzero
      simp [hzero] at hm₁
    exact_mod_cast hm₁nat
  exact no_three_zero_labels (u := u) (v := v) (w := w)
    (m₁ := m₁) (m₂ := m₂) (m₃ := m₃)
    (by exact_mod_cast huv) (by exact_mod_cast huw) (by exact_mod_cast hvw) hm₁0
    (pair_label_eq_zero hN hH hB hsmall hu hv hm₁ hm₂)
    (pair_label_eq_zero hN hH hB hsmall hv hw hm₂ hm₃)
    (pair_label_eq_zero hN hH hB hsmall hu hw hm₁ hm₃)

end RothLocal
