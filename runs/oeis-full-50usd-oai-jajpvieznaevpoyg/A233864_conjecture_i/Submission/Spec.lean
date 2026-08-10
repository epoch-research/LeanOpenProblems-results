import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A233864: $a(n) = |\left\{0 < m < 2n: m = \sigma_1(k) \text{ for some } k>0, \text{ and } 2n - 1 - m \text{ and } 2n - 1 + m \text{ are both prime}\right\}|$, where $\sigma_1(k)$ is the sum of all positive divisors of $k$.
-/
noncomputable def A233864_a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let twice_n : ℕ := 2 * n
  let N : ℕ := twice_n - 1

  -- The set of $k$ values we consider is $\{1, 2, \ldots, 2n-1\}$.
  let k_domain : Finset ℕ := Finset.Ico 1 twice_n

  -- The set of $m$ values is the image of $\sigma_1$ over the domain.
  let sigma_values : Finset ℕ := k_domain.image (sigma 1)

  (sigma_values.filter (fun m : ℕ =>
    m < twice_n ∧
    -- Ensure $N - m > 0$. Since $N=2n-1$, this is $m < 2n-1$.
    m < N ∧
    (N - m).Prime ∧
    (N + m).Prime
  )) |>.card

/--
Conjecture A233864 (i): $a(n) > 0$ for all $n > 3$.
-/
theorem A233864_conjecture_i : ∀ n : ℕ, 3 < n → A233864_a n > 0 := by
  sorry
