import FormalConjecturesUtil

/-!
# Floors near a rational slope

A nonintegral rational value at a natural index is at least one denominator
step away from either endpoint of its unit interval.  Thus a sufficiently
small perturbation has the same floor.
-/

namespace Erdos972

/-- If `b` does not divide `a * p`, an approximation to `a / b` within
`1 / (b * p)` leaves the floor at index `p` unchanged. -/
theorem floor_mul_eq_div_of_near_rational
    (a b p : ℕ) (α : ℝ) (hb : 0 < b) (hp : 0 < p)
    (hnd : ¬ b ∣ a * p)
    (hα : |α - (a : ℝ) / (b : ℝ)| < 1 / ((b : ℝ) * (p : ℝ))) :
    Nat.floor (α * (p : ℝ)) = a * p / b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hbp : (0 : ℝ) < (b : ℝ) * (p : ℝ) := mul_pos hbR hpR
  have hscaled : |α * (p : ℝ) * (b : ℝ) - ((a * p : ℕ) : ℝ)| < 1 := by
    have hnorm : |(α - (a : ℝ) / (b : ℝ)) * ((b : ℝ) * (p : ℝ))| < 1 := by
      simpa only [abs_mul, abs_of_pos hbp] using (lt_div_iff₀ hbp).mp hα
    have heq : (α - (a : ℝ) / (b : ℝ)) * ((b : ℝ) * (p : ℝ)) =
        α * (p : ℝ) * (b : ℝ) - ((a * p : ℕ) : ℝ) := by
      push_cast
      field_simp [hbR.ne']
    rwa [heq] at hnorm
  have hrem_pos : 0 < (a * p) % b := by
    have hrem_ne : (a * p) % b ≠ 0 := by
      intro hzero
      exact hnd (Nat.dvd_of_mod_eq_zero hzero)
    omega
  have hrem_lower : (1 : ℝ) ≤ (((a * p) % b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hrem_pos)
  have hrem_upper : (((a * p) % b : ℕ) : ℝ) + 1 ≤ (b : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mod_lt (a * p) hb))
  have hdiv_nat : a * p = (a * p) / b * b + (a * p) % b := by
    calc
      a * p = (a * p) % b + b * ((a * p) / b) := (Nat.mod_add_div (a * p) b).symm
      _ = (a * p) / b * b + (a * p) % b := by ac_rfl
  have hdiv : ((a * p : ℕ) : ℝ) =
      (((a * p) / b : ℕ) : ℝ) * (b : ℝ) + (((a * p) % b : ℕ) : ℝ) := by
    exact_mod_cast hdiv_nat
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hscaled
  have hscaled_low : (((a * p) / b : ℕ) : ℝ) * (b : ℝ) ≤
      (α * (p : ℝ)) * (b : ℝ) := by
    nlinarith
  have hscaled_high : (α * (p : ℝ)) * (b : ℝ) <
      ((((a * p) / b : ℕ) : ℝ) + 1) * (b : ℝ) := by
    nlinarith
  have hlow : (((a * p) / b : ℕ) : ℝ) ≤ α * (p : ℝ) :=
    (mul_le_mul_iff_left₀ hbR).mp hscaled_low
  have hhigh : α * (p : ℝ) < (((a * p) / b : ℕ) : ℝ) + 1 :=
    (mul_lt_mul_iff_left₀ hbR).mp hscaled_high
  have hnonneg : 0 ≤ α * (p : ℝ) := (Nat.cast_nonneg _).trans hlow
  exact (Nat.floor_eq_iff hnonneg).2 ⟨hlow, hhigh⟩

#print axioms Erdos972.floor_mul_eq_div_of_near_rational

end Erdos972
