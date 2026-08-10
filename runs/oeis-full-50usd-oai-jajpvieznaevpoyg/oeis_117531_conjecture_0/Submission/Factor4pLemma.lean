import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma dvd_value_of_dvd_four_p_sub_one {p q : ℕ} (hqodd : q % 2 = 1)
    (hdiv : q ∣ 4*p - 1) :
    q ∣ ((q+1)/2)^2 - ((q+1)/2) + p := by
  -- because 4*(k^2-k+p) = q^2-1+4p and q divides q^2 and 4p-1;
  -- need cancel 4 modulo odd q (coprime q 4).
  sorry
