import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option warn.sorry false
set_option linter.unusedVariables false

open Nat Finset

/--
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0

noncomputable def a_generalized (n d : ℕ) : ℕ :=
  if d = 1 then 0 else
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0

theorem oeis_237348_conjecture_0.disproof : ¬ (∀ (d : ℕ), 1 ≤ d → ∃ (N : ℕ), 0 < N ∧ ∀ (n : ℕ), N < n → 0 < a_generalized n d) := by
  intro h
  have hd : 1 ≤ 1 := by decide
  obtain ⟨N, _, hN2⟩ := h 1 hd
  have h_gt : N < N + 1 := Nat.lt_succ_self N
  have h_pos := hN2 (N + 1) h_gt
  have h_zero : a_generalized (N + 1) 1 = 0 := rfl
  rw [h_zero] at h_pos
  exact Nat.lt_irrefl 0 h_pos
