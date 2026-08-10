import FormalConjectures.Util.ProblemImports


set_option warn.sorry false

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

lemma padicValNat_le_of_dvd (p : ℕ) [Fact p.Prime] {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← padicValNat_dvd_iff_le hb]
    exact dvd_trans pow_padicValNat_dvd h

lemma norm_factorial_le_pow (n : ℕ) (x : ℕ) (hx : 3 * n ≤ x) :
    ‖(x.factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (- (n : ℤ)) := by
  have h_dvd : (3 : ℤ) ^ n ∣ (x.factorial : ℤ) := by
    norm_cast
    have h_fac_ne_zero : x.factorial ≠ 0 := Nat.factorial_ne_zero x
    rw [padicValNat_dvd_iff_le h_fac_ne_zero]
    have h_div_mono : padicValNat 3 (3 * n).factorial ≤ padicValNat 3 x.factorial := by
      apply padicValNat_le_of_dvd 3 h_fac_ne_zero
      exact Nat.factorial_dvd_factorial hx
    have h_eq : padicValNat 3 (3 * n).factorial = padicValNat 3 n.factorial + n := by
      exact padicValNat_factorial_mul (p := 3) n
    omega
  have h_norm := (Padic.norm_int_le_pow_iff_dvd (x.factorial : ℤ) n).mpr h_dvd
  exact h_norm

lemma tendsto_pow_neg_3 : Filter.Tendsto (fun n : ℕ => (3 : ℝ) ^ (- (n : ℤ))) Filter.atTop (nhds 0) := by
  have h : (fun n : ℕ => (3 : ℝ) ^ (- (n : ℤ))) = (fun n : ℕ => (1 / 3 : ℝ) ^ n) := by
    ext n
    rw [zpow_neg]
    rw [zpow_natCast]
    simp [inv_pow]
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

lemma tendsto_div_3 : Filter.Tendsto (fun x : ℕ => x / 3) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  use 3 * M
  intro x hx
  omega

theorem summable_factorial_3 : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rw [Nat.cofinite_eq_atTop]
  have h_lim := Filter.Tendsto.comp tendsto_pow_neg_3 tendsto_div_3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => 0) (h := fun x => (3 : ℝ) ^ (- ((x / 3 : ℕ) : ℤ)))
  · exact tendsto_const_nhds
  · exact h_lim
  · intro x
    exact norm_nonneg _
  · intro x
    exact norm_factorial_le_pow (x / 3) x (Nat.mul_div_le x 3)

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.
-/
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  intro h
  rcases h with ⟨p, hp, heval⟩
  by_cases hdeg : p.natDegree = 0
  · -- p has degree 0, so it is a constant.
    have h_eq : p = Polynomial.C (p.coeff 0) := by
      exact Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have h_eval : Polynomial.aeval xi_3 p = algebraMap ℚ (Padic 3) (p.coeff 0) := by
      rw [h_eq]
      simp
    rw [heval] at h_eval
    have h_coeff : p.coeff 0 = 0 := by
      -- since algebraMap is injective
      have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := by
        exact FaithfulSMul.algebraMap_injective ℚ (Padic 3)
      apply h_inj
      rw [map_zero]
      exact h_eval.symm
    have h_p : p = 0 := by
      rw [h_eq, h_coeff]
      simp
    exact hp h_p
  · sorry
