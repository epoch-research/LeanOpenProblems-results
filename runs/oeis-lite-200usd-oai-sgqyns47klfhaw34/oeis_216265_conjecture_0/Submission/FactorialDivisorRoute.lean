import FormalConjectures.Util.ProblemImports

open Nat

-- Check available statements around factorization/dvd iff.
#check Nat.factorization_le_iff_dvd
#check Nat.dvd_iff_factorization_le
#check Finsupp.le_iff
#check Nat.factorization_factorial
#check Nat.factorization_choose
#check Nat.factorization_div
#check Nat.factorization_mul
#check Nat.factorization_eq_zero_of_not_prime
#check Nat.factorization_eq_zero_of_lt
#check Nat.factorization_factorial_eq_zero_of_lt

-- If this lemma is true, it would be useful. Let's leave as example goal for inspection.
example {N k p : ℕ} (hk : k ≤ N) (hp : p.Prime) (hle : p ≤ N - k) :
    (Nat.choose N k).factorization p ≤ ((N - k)!).factorization p := by
  -- Try the general statement; it is false for N=4,k=1,p=2 (choose=4,3!=6)
  -- so Lean should not prove it.
  by_cases hbad : N = 4 ∧ k = 1 ∧ p = 2
  · rcases hbad with ⟨rfl,rfl,rfl⟩
    norm_num at hle
  -- no proof in general
  all_goals sorry
