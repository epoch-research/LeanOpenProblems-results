import Submission.Spec
import Submission.ArithmeticProgressions
import Submission.FourTerms

/-!
The four-term, even-exponent special case of the specification.
Neither admitted target theorem is used in these proofs.
-/

namespace Erdos672

open scoped BigOperators

/-- A product of four positive progression terms is not an even power.
The coprimality assumption is not needed for this special case. -/
theorem range_four_product_ne_even_power (n d q l : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hl : 2 ∣ l) :
    (∏ i ∈ Finset.range 4, (n + i * d)) ≠ q ^ l := by
  intro hpower
  apply Progression.range_four_product_ne_square n d (q ^ (l / 2)) hn hd
  calc
    (∏ i ∈ Finset.range 4, (n + i * d)) = q ^ l := hpower
    _ = (q ^ (l / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel hl]

/-- The finite-set formulation for length four and any even exponent. -/
theorem erdos672With_four_even (l : ℕ) (hl : 2 ∣ l) : Erdos672With 4 l := by
  intro s _ n hn d hd _ hAP q hpower
  have hprod : (∏ x ∈ s, x) = ∏ i ∈ Finset.range 4, (n + i * d) := by
    rw [Progression.product_eq_of_isAP hd hAP]
    exact Fin.prod_univ_eq_prod_range (fun i => n + i * d) 4
  apply range_four_product_ne_even_power n d q l hn hd hl
  exact hprod.symm.trans hpower

/-- In particular, the square-exponent instance of the conjecture at length four. -/
theorem erdos672With_four_square : Erdos672With 4 2 :=
  erdos672With_four_even 2 (dvd_refl 2)

end Erdos672
