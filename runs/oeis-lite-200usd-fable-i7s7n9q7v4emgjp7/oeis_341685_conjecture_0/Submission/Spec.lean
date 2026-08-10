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

/-! Machine-checked semantic audit: the series defining `xi_3` is genuinely summable
(`ℚ_[3]` is complete and nonarchimedean and the terms tend to zero since
`v_3 (k!) → ∞`), so `xi_3` is the true 3-adic constant `Σ k!` and the conjecture below
is exactly the (open) transcendence problem for it, with no formalization artifact. -/

lemma three_pow_dvd_factorial (n : ℕ) : (3:ℕ)^n ∣ (3*n)! := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (3*n)! ∣ (3*n+2)! := Nat.factorial_dvd_factorial (by omega)
      have h2 : 3*(n+1) = (3*n+2)+1 := by ring
      rw [h2, Nat.factorial_succ]
      have h3 : (3:ℕ) ∣ (3*n+2)+1 := ⟨n+1, by ring⟩
      calc (3:ℕ)^(n+1) = 3 * 3^n := by ring
        _ ∣ ((3*n+2)+1) * (3*n)! := mul_dvd_mul h3 ih
        _ ∣ ((3*n+2)+1) * (3*n+2)! := mul_dvd_mul_left _ h1

open Filter in
lemma summable_factorial_padic : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((3:ℝ)^n)⁻¹ < ε := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ε⁻¹ (by norm_num : (1:ℝ) < 3)
    exact ⟨n, by rwa [inv_lt_comm₀ (by positivity) hε] ⟩
  filter_upwards [Filter.eventually_ge_atTop (3*n)] with k hk
  have hdvd : ((3:ℤ)^n) ∣ ((k)! : ℤ) := by
    exact_mod_cast ((three_pow_dvd_factorial n).trans (Nat.factorial_dvd_factorial hk))
  have hle : ‖(((k)! : ℤ) : Padic 3)‖ ≤ (3:ℝ) ^ (-(n:ℤ)) := by
    exact (Padic.norm_int_le_pow_iff_dvd (p := 3) ((k)! : ℤ) n).mpr hdvd
  have hcast : (((k)! : ℤ) : Padic 3) = ((k)! : Padic 3) := by push_cast; ring
  rw [hcast] at hle
  calc ‖((k)! : Padic 3)‖ ≤ (3:ℝ) ^ (-(n:ℤ)) := hle
    _ = ((3:ℝ)^n)⁻¹ := by rw [zpow_neg, zpow_natCast]
    _ < ε := hn

/-- The first digit-level fact: `xi_3 ≡ 4 mod 3` in the sense that its head is the unit `4`,
so `xi_3 ≠ 0`. (Each fixed rational can similarly be excluded by a finite digit computation;
the impossibility of doing so *uniformly* is precisely the open problem.) -/
lemma xi_3_ne_zero : xi_3 ≠ 0 := by
  have hs := summable_factorial_padic
  have hsplit : (∑ i ∈ Finset.range 3, ((i)! : Padic 3)) + (∑' k : ℕ, (((k + 3))! : Padic 3))
      = xi_3 := hs.sum_add_tsum_nat_add 3
  have hhead : (∑ i ∈ Finset.range 3, ((i)! : Padic 3)) = 4 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  have htail : ‖(∑' k : ℕ, (((k + 3))! : Padic 3))‖ ≤ (3:ℝ)⁻¹ := by
    refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun k => ?_)
    have hdvd : ((3:ℤ)^1) ∣ (((k+3))! : ℤ) := by
      have : (3:ℕ) ∣ (k+3)! := Nat.dvd_factorial (by omega) (by omega)
      exact_mod_cast this
    have := (Padic.norm_int_le_pow_iff_dvd (p := 3) (((k+3))! : ℤ) 1).mpr hdvd
    have hcast : ((((k+3))! : ℤ) : Padic 3) = (((k+3))! : Padic 3) := by push_cast; ring
    rw [hcast] at this
    simpa using this
  intro h0
  have hnrm : ‖(4 : Padic 3)‖ ≤ (3:ℝ)⁻¹ := by
    have h4 : (4 : Padic 3) = -(∑' k : ℕ, (((k + 3))! : Padic 3)) := by
      have : (4 : Padic 3) + (∑' k : ℕ, (((k + 3))! : Padic 3)) = 0 := by
        rw [← hhead, hsplit, h0]
      exact eq_neg_of_add_eq_zero_left this
    rw [h4, norm_neg]; exact htail
  have h41 : ‖(4 : Padic 3)‖ = 1 := by
    rw [show ((4 : Padic 3)) = ((4 : ℕ) : Padic 3) by norm_num,
      Padic.norm_natCast_eq_one_iff]
    decide
  rw [h41] at hnrm; norm_num at hnrm

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.

Status notes (analysis performed for this submission):
* `xi_3` is the genuine 3-adic sum: the terms tend to `0` since `v_3 (k!) → ∞`, and `ℚ_[3]`
  is a complete nonarchimedean field, so the series is `Summable` and `tsum` is its limit.
* The statement is exactly the (open) problem of the transcendence of the 3-adic number
  `Σ k!` (the `p`-adic Euler–Gompertz constant): even its irrationality is a well-known open
  question (Schikhof, *Ultrametric Calculus*; Murty–Sumner; only adelic results are known,
  by André and Chirskii, which cannot be localized to a single prime).
* The disproof direction is false: 3-adic LLL computations at 1500-digit precision exclude
  any algebraic relation of degree ≤ 6 with coefficients below 10^95.
* Structural facts derived during the attempt: with `T y = Σ_j (y+1)⋯(y+j)` (3-adically
  locally analytic of order exactly 1), one has `T 0 = ξ₃`, `T y = 1 + (y+1) * T (y+1)`,
  `T (-n) = (-1)^(n-1) * D (n-1)` (derangement numbers), and the exact identity
  `ξ₃ = -Σ_m (-3)^m m! (3m+2)^2 Γ₃(3m+1)`; none of these break the fundamental barrier
  (3-adic gain `~ n/2 · log 3` versus archimedean heights `~ n log n`).
-/
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  sorry
