import Submission.ArithmeticProgressions

/-!
# The canonical lcm factorial budget

For a positive primitive progression, its product divided by the lcm of its
terms is an integer divisor of `(k - 1)!`. This records the full off-peak
valuation bound independently of any perfect-power assumption. It is a
supporting arithmetic theorem and does not settle the conjecture.
-/

namespace Erdos672.Progression

open scoped BigOperators

/-- The product of the terms divides their lcm times the factorial budget. -/
theorem progression_product_dvd_factorial_lcm {n d k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hc : n.gcd d = 1) :
    (∏ i : Fin k, (n + i.val * d)) ∣
      (k - 1).factorial * Finset.univ.lcm (fun i : Fin k => n + i.val * d) := by
  classical
  let t : Fin k → ℕ := fun i => term n d i.val
  let M := Finset.univ.lcm t
  have ht : ∀ i, t i ≠ 0 := fun i => (term_pos hn i.val).ne'
  have hM : M ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun i _ => ht i)
  apply (Nat.factorization_le_iff_dvd
    (Finset.prod_ne_zero_iff.mpr (fun i _ => ht i))
    (mul_ne_zero (Nat.factorial_ne_zero _) hM)).mp
  intro p
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i => (t i).factorization p) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hbudget := off_peak_sum_le_factorial hn hc p j
    (fun i => hj i (Finset.mem_univ i))
  have hjM : (t j).factorization p ≤ M.factorization p :=
    (Nat.factorization_le_iff_dvd (ht j) hM).mpr
      (Finset.dvd_lcm (Finset.mem_univ j)) p
  rw [Nat.factorization_prod_apply (fun i _ => ht i),
    Nat.factorization_mul (Nat.factorial_ne_zero _) hM]
  simp only [Finsupp.add_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  exact Nat.add_le_add hbudget hjM

/-- The full off-peak quotient is a divisor of the factorial. -/
theorem progression_lcm_quotient_dvd_factorial {n d k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hc : n.gcd d = 1) :
    ((∏ i : Fin k, (n + i.val * d)) /
      Finset.univ.lcm (fun i : Fin k => n + i.val * d)) ∣ (k - 1).factorial := by
  let t : Fin k → ℕ := fun i => n + i.val * d
  let M := Finset.univ.lcm t
  let P := ∏ i, t i
  have ht : ∀ i, t i ≠ 0 := fun i => (by dsimp [t]; omega)
  have hM : 0 < M :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _ => ht i))
  have hMP : M ∣ P := Finset.lcm_dvd_prod _ _
  have hEM : P / M * M = P := Nat.div_mul_cancel hMP
  obtain ⟨r, hr⟩ := progression_product_dvd_factorial_lcm hn hk hc
  have hr' : M * (k - 1).factorial = M * ((P / M) * r) := by
    calc
      M * (k - 1).factorial = (k - 1).factorial * M := by ring
      _ = P * r := hr
      _ = ((P / M) * M) * r := congrArg (fun x : ℕ => x * r) hEM.symm
      _ = M * ((P / M) * r) := by ring
  exact ⟨r, Nat.mul_left_cancel hM hr'⟩

/-- Application to the actual product root, without any restriction on its exponent. -/
theorem power_lcm_quotient_dvd_factorial {n d k q l : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hc : n.gcd d = 1)
    (hpower : (∏ i : Fin k, (n + i.val * d)) = q ^ l) :
    (q ^ l / Finset.univ.lcm (fun i : Fin k => n + i.val * d)) ∣
      (k - 1).factorial := by
  rw [← hpower]
  exact progression_lcm_quotient_dvd_factorial hn hk hc

end Erdos672.Progression
