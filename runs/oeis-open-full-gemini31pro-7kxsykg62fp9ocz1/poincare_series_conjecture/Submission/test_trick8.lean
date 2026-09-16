import Mathlib

axiom c : Nat

theorem conjecture : 0 = c := sorry

-- Wait! Is the type of the conjecture just `0 = c`? Yes.
-- If the conjecture is False, we can prove its negation.
-- BUT it's an axiom, so `c` has NO properties.
-- Is there ANY way to prove `¬ (0 = c)`?
-- If `c` has no properties, NO. Because we could interpret `c` as `0`, satisfying `0=c`.
-- But wait! Is there something special about `poincare_series_genus2_odd_unimodular_lattices` in the environment?
-- No, it's defined right there in `Spec.lean` using `axiom`!!!
-- "axiom poincare_series_genus2_odd_unimodular_lattices : PQS"
-- Wait! Is there an inconsistency in PQS?
-- No.

