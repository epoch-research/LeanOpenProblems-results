import FormalConjecturesUtil

/-! Two independent integer pairs with arbitrarily small errors suffice for
irrationality. Producing such pairs for the target remains open here. -/
namespace IntegerFormCriterion

lemma rational_small_form_zero (r : ℚ) (a b : ℤ)
    (h : |(a : ℝ) * (r : ℝ) - b| < 1 / (r.den : ℝ)) :
    (a : ℝ) * (r : ℝ) - b = 0 := by
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hr : (r.den : ℝ) * (r : ℝ) = r.num := by
    rw [Rat.cast_def]
    field_simp
  have hid : ((a * r.num - b * r.den : ℤ) : ℝ) =
      (r.den : ℝ) * ((a : ℝ) * (r : ℝ) - b) := by
    push_cast
    rw [mul_sub, mul_left_comm, hr]
    ring
  have hz : |((a * r.num - b * r.den : ℤ) : ℝ)| < 1 := by
    rw [hid, abs_mul, abs_of_pos hden]
    simpa only [mul_comm] using (lt_div_iff₀ hden).mp h
  have hz' : |a * r.num - b * r.den| < (1 : ℤ) := by exact_mod_cast hz
  have hz0 : a * r.num - b * r.den = 0 := by
    have := abs_lt.mp hz'
    omega
  rw [hz0, Int.cast_zero] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left hden.ne'

/-- Independence of the coefficient pairs avoids having to determine the
sign or nonvanishing of either particular form in advance. -/
theorem irrational_of_independent_small_pairs (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ a b c d : ℤ,
      a * d - b * c ≠ 0 ∧ |(a : ℝ) * x - b| < ε ∧ |(c : ℝ) * x - d| < ε) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨a, b, c, d, hind, ha, hc⟩ := h (1 / r.den) (by positivity)
  have ha0 := rational_small_form_zero r a b ha
  have hc0 := rational_small_form_zero r c d hc
  apply hind
  have hz : ((a * d - b * c : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (c : ℝ) * ha0 - (a : ℝ) * hc0
  exact_mod_cast hz

end IntegerFormCriterion

#print axioms IntegerFormCriterion.irrational_of_independent_small_pairs
