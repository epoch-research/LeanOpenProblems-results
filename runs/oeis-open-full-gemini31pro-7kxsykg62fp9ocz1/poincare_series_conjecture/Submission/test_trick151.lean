import Submission.Spec
open PowerSeries
-- I want to show that PQS is an infinite type, and an axiom doesn't constrain it.
-- But wait, `axiom` in Lean CANNOT be used to deduce falsehood, even if it's "supposed" to be a specific thing.
-- "axiom poincare_series_genus2_odd_unimodular_lattices : PQS" means it is an arbitrary element of PQS.
-- If it's arbitrary, `A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices` is unprovable.
-- And `¬ (A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices)` is ALSO unprovable!
-- Is this true? Yes, it's logically independent of Lean's axioms.
-- IF it is independent, I cannot prove the conjecture AND I cannot prove the disproof!
-- Unless the verifier tests my file using something else?
