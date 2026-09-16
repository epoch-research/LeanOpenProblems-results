import FormalConjectures.Util.ProblemImports
import Submission.Proof

open Finset Nat Set

/-- The number of divisors function $\tau(n)$. -/
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/--
$A047983(m)$ is the number of positive integers $k < m$ such that $\tau(k) = \tau(m)$.
-/
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))

/--
A338483: $a(n)$ is the smallest number having $n$ smaller numbers with the same number of divisors.
$A338483(n)$ is the smallest $m$ such that $A047983(m) = n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | A047983_count m = n}

/--
A338483: Are there prime terms greater than 31?
--/
theorem oeis_338483_conjecture_0 :
  ∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31 := by
  sorry

theorem oeis_338483_conjecture_0.disproof : ¬ (type_of% @oeis_338483_conjecture_0) := by
  exact disproof_thm
