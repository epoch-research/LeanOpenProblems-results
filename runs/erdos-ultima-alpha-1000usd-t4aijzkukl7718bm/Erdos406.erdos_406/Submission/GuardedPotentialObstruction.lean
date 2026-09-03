import Submission.Work

/-! Limits of length-like potentials even when growth starts only after a
fixed exponent or divisibility guard. These results do not settle Erdős 406. -/

namespace Erdos406Work

lemma eventual_length_potential_slope_bound (q : ℕ) (hq : 0 < q)
    (V : ℕ → ℝ) (c C : ℝ) (hc : 0 ≤ c) (E : ℕ)
    (hupper : ∀ m : ℕ, E ≤ m → V (q ^ m) ≤ c * (Nat.digits 3 (q ^ m)).length + C)
    (hgrow : ∀ m : ℕ, E ≤ m → V (q ^ m) + 1 ≤ V (q ^ (m + 1))) :
    Real.log 3 ≤ c * Real.log q := by
  have hg : ∀ m : ℕ, V (q ^ E) + (m : ℝ) ≤ V (q ^ (E + m)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hh := hgrow (E + m) (by omega)
      push_cast
      simpa only [Nat.add_assoc] using (by linarith :
        V (q ^ E) + ((m : ℝ) + 1) ≤ V (q ^ (E + m + 1)))
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  by_contra hbad
  have hd : 0 < Real.log 3 - c * Real.log q := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt
    (((C - V (q ^ E) + c) * Real.log 3 + c * E * Real.log q) /
      (Real.log 3 - c * Real.log q))
  have hlarge : (C - V (q ^ E) + c) * Real.log 3 + c * E * Real.log q <
      (m : ℝ) * (Real.log 3 - c * Real.log q) := (div_lt_iff₀ hd).mp hm
  have hbound := (hg m).trans (hupper (E + m) (by omega))
  have hlen := ternary_length_pow_log_le q (E + m) hq
  have hbound' := mul_le_mul_of_nonneg_right hbound (le_of_lt hlog)
  have hlen' := mul_le_mul_of_nonneg_left hlen hc
  push_cast at hlen'
  nlinarith

/-- Restricting growth and the global length bound to multiples of a fixed
power of the multiplier still cannot yield a subcritical length slope. -/
lemma guarded_length_potential_slope_bound (q K : ℕ) (hq : 0 < q)
    (V : ℕ → ℝ) (c C : ℝ) (hc : 0 ≤ c)
    (hupper : ∀ n : ℕ, 0 < n → q ^ K ∣ n →
      V n ≤ c * (Nat.digits 3 n).length + C)
    (hgrow : ∀ n : ℕ, 0 < n → q ^ K ∣ n → V n + 1 ≤ V (q * n)) :
    Real.log 3 ≤ c * Real.log q := by
  apply eventual_length_potential_slope_bound q hq V c C hc K
  · intro m hm
    exact hupper (q ^ m) (pow_pos hq m) (pow_dvd_pow q hm)
  · intro m hm
    have hh := hgrow (q ^ m) (pow_pos hq m) (pow_dvd_pow q hm)
    simpa only [← pow_succ'] using hh

lemma guarded_bounded_correction_potential_slope_bound (q K : ℕ) (hq : 0 < q)
    (V W : ℕ → ℝ) (c C : ℝ) (hc : 0 ≤ c)
    (hform : ∀ n : ℕ, 0 < n → q ^ K ∣ n →
      V n = c * (Nat.digits 3 n).length + W n)
    (herror : ∀ n : ℕ, 0 < n → q ^ K ∣ n → |W n| ≤ C)
    (hgrow : ∀ n : ℕ, 0 < n → q ^ K ∣ n → V n + 1 ≤ V (q * n)) :
    Real.log 3 ≤ c * Real.log q := by
  apply guarded_length_potential_slope_bound q K hq V c C hc ?_ hgrow
  intro n hn hd
  rw [hform n hn hd]
  have he := (le_abs_self (W n)).trans (herror n hn hd)
  linarith

#print axioms eventual_length_potential_slope_bound
#print axioms guarded_bounded_correction_potential_slope_bound
end Erdos406Work
