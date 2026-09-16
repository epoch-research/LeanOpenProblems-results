import Submission.Spec
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Factorization
open Nat Finset

lemma t_div_d (k m : ℕ) : (2*(k+m) - 1) * (3*(k+m)).choose (k+m) ∣ T_term k * T_term m := by
  -- We prove this by showing for all primes p, v_p(LHS) <= v_p(RHS).
  -- And we can use `Nat.dvd_of_forall_prime_pow_dvd` or similar.
  sorry
