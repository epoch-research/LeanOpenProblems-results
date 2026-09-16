import FormalConjectures.Util.ProblemImports

open Nat

/--
A237413: Number of ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $p(k)^2 - 2$, $p(m)^2 - 2$ and $p(p(m))^2 - 2$ are all prime, where $p(j)$ denotes the $j$-th prime.
-/
noncomputable def A237413 (n : ℕ) : ℕ :=
  -- The j-th prime $p(j)$ is Nat.nth Nat.Prime (j-1).
  let p_j (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

  -- The number of ways is the sum of the indicator function over $k \in \{1, 2, \dots, n-1\}$.
  (Finset.Ico 1 n).sum fun k ↦
    let m := n - k

    let pk := p_j k
    let pm := p_j m

    -- The argument for $p(p(m))$ is $p(m)$. Since $p(m) \ge 2$, this is a valid index $\ge 1$.
    -- To use $p_j$, we need to ensure $p_m \ge 1$. $p(m)$ is a prime, so $p(m) \ge 2 > 0$.
    let ppm := p_j pm

    -- All three expressions must be prime. The conversion of Prop to 0/1 handles the counting.
    if (pk ^ 2 - 2).Prime ∧ (pm ^ 2 - 2).Prime ∧ (ppm ^ 2 - 2).Prime then 1 else 0

lemma nth_prime_two_eq_five_local : nth Nat.Prime 2 = 5 := by exact Nat.nth_prime_two_eq_five

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
theorem oeis_237413_conjecture_0 (n : ℕ) : 1 < n → A237413 n > 0 := sorry

theorem oeis_237413_conjecture_0.disproof : ¬ (type_of% @oeis_237413_conjecture_0) := by
  intro h
  have hc := h 2 (by decide)
  revert hc
  unfold A237413
  have H_ico : Finset.Ico 1 2 = {1} := rfl
  rw [H_ico, Finset.sum_singleton]
  dsimp
  have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  simp [hp0, hp1]
  intro H
  cases H
