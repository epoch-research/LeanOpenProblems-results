import FormalConjecturesUtil

/-!
# Arbitrarily slow divergent natural-number budgets

For every sequence `N : ℕ → ℕ`, `slowBudget N` tends to infinity but is less
than `k` on the whole interval `n ≤ N k`, for every `k ≥ 1`. No monotonicity
or growth hypothesis on `N` is needed.

We form the monotone majorant `M k = k + 1 + ∑ i ≤ k, N i` and take the
least `j` such that `n ≤ M (j + 1)`. The offset permits the candidate `k - 1`
when `n ≤ N k`; excluding `k = 0` is essential for a strict natural-number
budget bound. This file does not import or depend on `Submission.Spec`.
-/

namespace Erdos74Aux

open Filter

/-- A monotone, unbounded majorant of an arbitrary sequence of natural numbers. -/
def budgetMajorant (N : ℕ → ℕ) (k : ℕ) : ℕ :=
  k + 1 + (Finset.range (k + 1)).sum N

/-- The majorant dominates the original sequence at every index. -/
theorem le_budgetMajorant (N : ℕ → ℕ) (k : ℕ) :
    N k ≤ budgetMajorant N k := by
  have h : N k ≤ (Finset.range (k + 1)).sum N :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (N i))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  unfold budgetMajorant
  omega

/-- The prefix sums are monotone even if `N` is not. -/
theorem budgetMajorant_monotone (N : ℕ → ℕ) : Monotone (budgetMajorant N) := by
  intro i j hij
  unfold budgetMajorant
  exact Nat.add_le_add (Nat.add_le_add_right hij 1)
    (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hij 1)))

/-- The linear term makes the inverse search terminate for every input. -/
theorem exists_le_budgetMajorant (N : ℕ → ℕ) (n : ℕ) :
    ∃ j : ℕ, n ≤ budgetMajorant N (j + 1) := by
  refine ⟨n, ?_⟩
  unfold budgetMajorant
  omega

/-- The least index `j` for which `n ≤ budgetMajorant N (j + 1)`. -/
def slowBudget (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.find (exists_le_budgetMajorant N n)

/-- The defining upper bound at the least index. -/
theorem slowBudget_spec (N : ℕ → ℕ) (n : ℕ) :
    n ≤ budgetMajorant N (slowBudget N n + 1) :=
  Nat.find_spec (exists_le_budgetMajorant N n)

/-- The budget is strictly below `k` throughout the prescribed initial interval. -/
theorem slowBudget_lt_of_le (N : ℕ → ℕ) {k n : ℕ}
    (hk : 1 ≤ k) (hn : n ≤ N k) : slowBudget N n < k := by
  have hbound : n ≤ budgetMajorant N ((k - 1) + 1) := by
    rw [Nat.sub_add_cancel hk]
    exact hn.trans (le_budgetMajorant N k)
  have hfind : slowBudget N n ≤ k - 1 :=
    Nat.find_min' (exists_le_budgetMajorant N n) hbound
  omega

/-- The concrete budget can also be chosen monotone. -/
theorem slowBudget_monotone (N : ℕ → ℕ) : Monotone (slowBudget N) := by
  intro n m hnm
  exact Nat.find_min' (exists_le_budgetMajorant N n)
    (hnm.trans (slowBudget_spec N m))

/-- Beyond `budgetMajorant N k`, the budget is at least `k`. -/
theorem le_slowBudget_of_majorant_lt (N : ℕ → ℕ) {k n : ℕ}
    (hn : budgetMajorant N k < n) : k ≤ slowBudget N n := by
  by_contra h
  have hle : slowBudget N n + 1 ≤ k := by omega
  have hbound := (slowBudget_spec N n).trans (budgetMajorant_monotone N hle)
  omega

/-- Despite all the prescribed upper bounds, the budget diverges to infinity. -/
theorem slowBudget_tendsto (N : ℕ → ℕ) :
    Tendsto (slowBudget N) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (budgetMajorant N k + 1)] with n hn
  exact le_slowBudget_of_majorant_lt N (by omega)

/-- An arbitrary sequence of finite thresholds admits a divergent budget that
is strictly less than `k` up to the `k`th threshold, for every positive `k`. -/
theorem exists_slow_divergent_budget (N : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ k ≥ 1, ∀ n, n ≤ N k → f n < k := by
  exact ⟨slowBudget N, slowBudget_tendsto N,
    fun _ hk _ hn => slowBudget_lt_of_le N hk hn⟩

end Erdos74Aux
