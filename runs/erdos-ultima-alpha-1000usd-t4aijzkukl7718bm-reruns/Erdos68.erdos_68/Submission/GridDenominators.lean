import Submission.Development

/-!
A change in the factorial-grid approximations requires a denominator that
was not cleared by the preceding grid. This does not establish infinitely
many changes and does not settle the conjecture in Spec.lean.
-/

namespace Erdos68Development

lemma rat_factorial_rep_of_den_dvd (q : ℚ) (m : ℕ) (h : q.den ∣ m.factorial) :
    ∃ z : ℤ, q = (z : ℚ) / m.factorial := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q.num * (c : ℤ), ?_⟩
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hc0 : (c : ℚ) ≠ 0 := by
    have hp := Nat.factorial_pos m
    rw [hc] at hp
    have : c ≠ 0 := by
      intro hz
      simp [hz] at hp
    exact_mod_cast this
  rw [hc]
  conv_lhs => rw [← Rat.num_div_den q]
  push_cast
  field_simp

lemma upperApprox_change_den_not_dvd {n : ℕ} (hn : 1 ≤ n)
    (hchange : upperApprox (n + 1) ≠ upperApprox n) :
    ¬ (upperApprox (n + 1)).den ∣ (n + 1).factorial := by
  intro h
  obtain ⟨z, hz⟩ := rat_factorial_rep_of_den_dvd (upperApprox (n + 1)) (n + 1) h
  exact hchange (hz.trans (upperApprox_backward hn z hz).symm)

/-- Only a bound at change indices: no upper bound on a subsequent constant
block is supplied. -/
lemma upperApprox_change_den_large {n : ℕ} (hn : 1 ≤ n)
    (hchange : upperApprox (n + 1) ≠ upperApprox n) :
    n + 2 ≤ (upperApprox (n + 1)).den := by
  by_contra h
  apply upperApprox_change_den_not_dvd hn hchange
  exact Nat.dvd_factorial (upperApprox (n + 1)).pos (by omega)

end Erdos68Development

#print axioms Erdos68Development.upperApprox_change_den_large
