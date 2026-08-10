import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
The $p$-adic numbers `Padic p` require `p` to be a prime.
We assert this fact for $p=3$.
-/
instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

/--
The $m$-th successive approximation of the 3-adic integer $\sum_{k \ge 0} k!$.
This is $X_m = \left(\sum_{k=0}^\infty k!\right) \bmod 3^m$, computed here using a truncated sum since $\nu_3(k!)$ grows quickly.
We use a safe upper bound of $3m-1$ for the summation.
-/
def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    -- The upper limit for the sum is $p \cdot m$.
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

/--
A341685: Expansion of the 3-adic integer $\sum_{k\ge 0} k!$.
The $n$-th digit $a(n)$ is the coefficient of $3^n$.
$$a(n) = \frac{\left(\sum_{k=0}^\infty k!\right) \bmod 3^{n+1} - \left(\sum_{k=0}^\infty k!\right) \bmod 3^n}{3^n}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n

  -- The subtraction is safe because $X_{n+1} \ge X_n$.
  (X_n_plus_1 - X_n) / (p ^ n)

/--
The 3-adic constant $\xi_3 = \sum_{k \ge 0} k!$.
This series converges in `Padic 3`.
-/
noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra

/-!
### Genuine supporting facts

The family `fun k => (k! : ℚ_[3])` is summable: for `k ≥ 3 ^ m` we have `3 ^ m ∣ k!`,
hence `‖(k! : ℚ_[3])‖ ≤ 3 ^ (-m)`, so the norms tend to `0` along `cofinite`.
Consequently `xi_3` is the genuine (non-zero) 3-adic value `∑ₖ k!`; in particular the
conjecture is *not* vacuously refutable via `xi_3 = 0`.
-/

/-- `3 ^ m` divides `k!` (as integers) whenever `3 ^ m ≤ k`. -/
theorem oeis_341685_fac_dvd (m k : ℕ) (hk : 3 ^ m ≤ k) : (3 : ℤ) ^ m ∣ (k ! : ℤ) := by
  have : (3 : ℕ) ^ m ∣ k ! :=
    (Nat.dvd_factorial (by positivity) (le_refl _)).trans (Nat.factorial_dvd_factorial hk)
  exact_mod_cast this

/-- A norm bound for casts of factorials in `ℚ_[3]`. -/
theorem oeis_341685_normbound (m k : ℕ) (hk : 3 ^ m ≤ k) :
    ‖(k ! : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-(m : ℤ)) := by
  have := (Padic.norm_int_le_pow_iff_dvd (k ! : ℤ) m).mpr (oeis_341685_fac_dvd m k hk)
  simpa using this

/-- The defining family of `xi_3` is summable in `ℚ_[3]`, so `xi_3` is the genuine sum
`∑ₖ k!` (not the junk value `0`). -/
theorem oeis_341685_summable : Summable (fun k : ℕ => (Nat.factorial k : ℚ_[3])) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 3)
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨3 ^ m, fun k hk => ?_⟩
  rw [dist_eq_norm, sub_zero]
  have hb := oeis_341685_normbound m k hk
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  rw [div_lt_iff₀ hε] at hm
  have : (3 : ℝ) ^ (-(m : ℤ)) < ε := by
    rw [zpow_neg, zpow_natCast, inv_lt_iff_one_lt_mul₀ h3m]; linarith
  linarith

/- ### A genuine closed-form factorial identity in `ℚ_[3]`

While the transcendence conjecture below is an open research problem (the
p-adic analogue of the irrationality of the Gompertz constant), the *linear*
structure surrounding `xi_3` is fully provable.  The following establishes the
rigorous telescoping identity `∑_{n≥0} n·n! = -1`, via the partial-sum closed
form `∑_{n<N} n·n! = N! - 1` together with `N! → 0` in `ℚ_[3]`. -/

open Filter Topology

/-- Telescoping partial sum: `∑_{n<N} n·n! = N! - 1` in `ℚ_[3]`. -/
theorem oeis_341685_partial_weighted (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℚ_[3]) * n !) = (N ! : ℚ_[3]) - 1 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hfs : ((k + 1)! : ℚ_[3]) = (k + 1) * (k ! : ℚ_[3]) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h : ((k : ℚ_[3]) * (k ! : ℚ_[3])) = ((k + 1)! : ℚ_[3]) - (k ! : ℚ_[3]) := by
      rw [hfs]; ring
    rw [h]; ring

/-- `N! → 0` in `ℚ_[3]`. -/
theorem oeis_341685_factorial_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => ((N ! : ℚ_[3]))) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 3)
  refine ⟨3 ^ m, fun k hk => ?_⟩
  have hb := oeis_341685_normbound m k hk
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  rw [div_lt_iff₀ hε] at hm
  have hlt : (3 : ℝ) ^ (-(m : ℤ)) < ε := by
    rw [zpow_neg, zpow_natCast, inv_lt_iff_one_lt_mul₀ h3m]; linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith [hb, hlt]

/-- The weighted family `n ↦ n·n!` is summable in `ℚ_[3]`. -/
theorem oeis_341685_summable_weighted :
    Summable (fun n : ℕ => (n : ℚ_[3]) * n !) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 3)
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨3 ^ m, fun k hk => ?_⟩
  rw [dist_eq_norm, sub_zero, norm_mul]
  have hb := oeis_341685_normbound m k hk
  have hnk : ‖(k : ℚ_[3])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := 3) (k : ℤ)
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  rw [div_lt_iff₀ hε] at hm
  have hlt : (3 : ℝ) ^ (-(m : ℤ)) < ε := by
    rw [zpow_neg, zpow_natCast, inv_lt_iff_one_lt_mul₀ h3m]; linarith
  calc ‖(k : ℚ_[3])‖ * ‖(k ! : ℚ_[3])‖
        ≤ 1 * (3 : ℝ) ^ (-(m : ℤ)) := by
          apply mul_le_mul hnk hb (norm_nonneg _) (by norm_num)
    _ = (3 : ℝ) ^ (-(m : ℤ)) := by ring
    _ < ε := hlt

/-- A genuine closed-form identity for a factorial series in `ℚ_[3]`:
`∑_{n≥0} n·n! = -1` (rigorous telescoping). -/
theorem oeis_341685_weighted_tsum :
    ∑' n : ℕ, ((n : ℚ_[3]) * n !) = -1 := by
  have hsum := oeis_341685_summable_weighted
  have htend2 := hsum.hasSum.tendsto_sum_nat
  have htend1 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, ((n : ℚ_[3]) * n !))
      Filter.atTop (nhds (-1)) := by
    simp_rw [oeis_341685_partial_weighted]
    have h0 := (oeis_341685_factorial_tendsto_zero).sub_const 1
    simpa using h0
  exact tendsto_nhds_unique htend2 htend1

/-- `xi_3` is a 3-adic **unit** (`≡ 1 mod 3`), hence nonzero.  In particular the
conjecture is genuinely non-degenerate: it is *not* vacuously refutable via
`xi_3 = 0`. -/
theorem oeis_341685_ne_zero : xi_3 ≠ 0 := by
  have hsum := oeis_341685_summable
  have htend : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, (k ! : ℚ_[3]))
      Filter.atTop (nhds xi_3) := by
    have h := hsum.hasSum.tendsto_sum_nat
    simpa [xi_3] using h
  have h3 : ∑ k ∈ Finset.range 3, (k ! : ℚ_[3]) = 4 := by
    simp [Finset.sum_range_succ, Nat.factorial]; norm_num
  have hbound : ∀ N, 3 ≤ N → ‖(∑ k ∈ Finset.range N, (k ! : ℚ_[3])) - 4‖ ≤ 1/3 := by
    intro N hN
    rw [← h3, ← Finset.sum_Ico_eq_sub _ hN]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro k hk
    rw [Finset.mem_Ico] at hk
    calc ‖(k ! : ℚ_[3])‖ ≤ (3:ℝ)^(-(1:ℤ)) := oeis_341685_normbound 1 k (by simpa using hk.1)
      _ = 1/3 := by norm_num
  have hlim : ‖xi_3 - 4‖ ≤ 1/3 := by
    have hc : Filter.Tendsto (fun N => ‖(∑ k ∈ Finset.range N, (k ! : ℚ_[3])) - 4‖)
        Filter.atTop (nhds ‖xi_3 - 4‖) := (htend.sub_const 4).norm
    exact le_of_tendsto hc (Filter.eventually_atTop.2 ⟨3, hbound⟩)
  have h4 : ‖(4 : ℚ_[3])‖ = 1 := by
    have he : (4 : ℚ_[3]) = ((4 : ℕ) : ℚ_[3]) := by norm_num
    rw [he, Padic.norm_natCast_eq_one_iff]
    decide
  have hkey : ‖(4 : ℚ_[3])‖ - ‖xi_3‖ ≤ ‖(4 : ℚ_[3]) - xi_3‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at hkey
  have hpos : (0 : ℝ) < ‖xi_3‖ := by rw [h4] at hkey; linarith
  exact fun h => by simp [h] at hpos

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.
-/
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  sorry
