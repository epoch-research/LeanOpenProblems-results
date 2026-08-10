import FormalConjectures.Util.ProblemImports

open Real Int

/--
A011545: $a(n)$ is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$.
This is equivalent to $a(n) = \lfloor \pi \cdot 10^n \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The calculation is $\lfloor \pi \cdot 10^n \rfloor$.
  -- We use Real.floor, which returns an Int, and convert it to a natural number.
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

/-- Lower bound `arctan x ≥ x - x³/3` for `x ≥ 0`, via monotonicity of
`g t = arctan t - (t - t³/3)` whose derivative is `t⁴/(1+t²) ≥ 0`. -/
theorem arctan_lb (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  set g : ℝ → ℝ := fun t => Real.arctan t - (t - t ^ 3 / 3) with hg
  have hderiv : ∀ t : ℝ, HasDerivAt g (t ^ 4 / (1 + t ^ 2)) t := by
    intro t
    have h1 : HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := Real.hasDerivAt_arctan t
    have h2 : HasDerivAt (fun t : ℝ => t - t ^ 3 / 3) (1 - t ^ 2) t := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (t ^ 2) t := by
        have h3 := (hasDerivAt_pow 3 t).div_const 3
        convert h3 using 1; push_cast; ring
      exact (hasDerivAt_id t).sub hp
    have h5 := h1.sub h2
    convert h5 using 1
    have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp; ring
  have hdiff : Differentiable ℝ g := fun t => (hderiv t).differentiableAt
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg hdiff
    intro t; rw [(hderiv t).deriv]; positivity
  have hle := hmono hx
  simp only [hg] at hle
  simp [Real.arctan_zero] at hle
  linarith [hle]

/-- Explicit upper bound: for `R ≥ 10`,
`π / arctan(1/R) ≤ π·R + (11/10)/R`.  (Since `arctan(1/R) ≥ 1/R - 1/(3R³)`.) -/
theorem upper_bound (R : ℝ) (hR : 10 ≤ R) :
    Real.pi / Real.arctan (1 / R) ≤ Real.pi * R + (11 / 10) / R := by
  have hRpos : 0 < R := by linarith
  have hne : R ≠ 0 := ne_of_gt hRpos
  have hxpos : 0 < 1 / R := by positivity
  have hlow : (1 / R) - (1 / R) ^ 3 / 3 ≤ Real.arctan (1 / R) :=
    arctan_lb (1 / R) (le_of_lt hxpos)
  have hsq : (1 / R) ^ 2 ≤ 1 / 100 := by
    have h10 : (1 : ℝ) / R ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hR
    nlinarith [mul_le_mul h10 h10 (le_of_lt hxpos) (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  have hlowpos : 0 < (1 / R) - (1 / R) ^ 3 / 3 := by
    nlinarith [hxpos, hsq, mul_pos hxpos hxpos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have step1 : Real.pi / Real.arctan (1 / R) ≤ Real.pi / ((1 / R) - (1 / R) ^ 3 / 3) := by
    gcongr
  have step2 : Real.pi / ((1 / R) - (1 / R) ^ 3 / 3) ≤ Real.pi * R + (11 / 10) / R := by
    rw [div_le_iff₀ hlowpos]
    have hexp : (Real.pi * R + (11 / 10) / R) * ((1 / R) - (1 / R) ^ 3 / 3) - Real.pi
        = ((11 / 10 - Real.pi / 3) * R ^ 2 - 11 / 30) / R ^ 4 := by field_simp; ring
    have hpos : 0 ≤ ((11 / 10 - Real.pi / 3) * R ^ 2 - 11 / 30) / R ^ 4 := by
      apply div_nonneg _ (by positivity)
      have hR2 : (100 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
      have hpic : (0 : ℝ) ≤ 11 / 10 - Real.pi / 3 := by linarith [Real.pi_lt_d2]
      nlinarith [mul_le_mul_of_nonneg_left hR2 hpic, Real.pi_lt_d2]
    linarith [hexp, hpos]
  linarith [step1, step2]

/--
A property which is equivalent to the conjecture that the number of collisions
in the described physical system (with mass ratio $10^{2n}$) is $a(n)$:
the interval $(\pi \cdot 10^n, \pi / \arctan(1/10^n))$ does not contain an integer.
The mass ratio $m$ in the comment is interpreted as $\frac{M}{m}$ in the physics setup,
which is $10^{2n}$, so $\sqrt{m}=10^n$.

Note: The OEIS comment uses $m=10^n$ for the $R^2$ term where $R=10^n$ in the physics formula.
We formalize the statement $\forall n \in \mathbb{N}, \nexists k \in \mathbb{Z}$ such that
$\pi \cdot 10^n < k < \pi / \arctan(1/10^n)$.
-/
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  rintro ⟨k, hk1, hk2⟩
  -- Normalise the `Nat.cast n : ℕ` in the exponent to `n`.
  simp only [Nat.cast_id] at hk1 hk2 ⊢
  -- The statement is equivalent to the core inequality
  --   `π / arctan(10^{-n}) ≤ ⌊π·10^n⌋ + 1`,
  -- i.e. `δ_n := ⌈π·10^n⌉ - π·10^n ≥ W_n := π/arctan(10^{-n}) - π·10^n`.
  have core : Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)
      ≤ (⌊Real.pi * (10 : ℝ) ^ n⌋ : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- n = 0 : `π/arctan(1) = π/(π/4) = 4 = ⌊π⌋ + 1`.
      subst hn
      simp only [pow_zero, div_one, Real.arctan_one]
      have hfloor : ⌊Real.pi * 1⌋ = 3 := by
        rw [mul_one, Int.floor_eq_iff]
        refine ⟨by push_cast; linarith [Real.pi_gt_three],
          by push_cast; linarith [Real.pi_lt_four]⟩
      rw [hfloor]
      rw [div_le_iff₀ (by positivity)]
      push_cast
      nlinarith [Real.pi_pos]
    · -- n ≥ 1 : use the explicit upper bound `π/arctan(10^{-n}) ≤ π·10^n + 1.1·10^{-n}`.
      have hR : (10 : ℝ) ≤ (10 : ℝ) ^ n := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) hn
        simpa using this
      have hub := upper_bound ((10 : ℝ) ^ n) hR
      by_cases hcase : Real.pi * (10 : ℝ) ^ n + (11 / 10) / (10 : ℝ) ^ n
          ≤ (⌊Real.pi * (10 : ℝ) ^ n⌋ : ℝ) + 1
      · -- "easy" branch: the gap `δ_n` exceeds the interval-width upper bound `1.1·10^{-n}`.
        linarith [hub, hcase]
      · -- "hard" branch: `δ_n < 1.1·10^{-n}`, i.e. `π·10^n` lies within `1.1·10^{-n}` below
        -- an integer — a run of ~`n` consecutive 9's in the decimal expansion of `π`,
        -- beginning at position `n+1`.  Ruling this out for all `n` is exactly the open
        -- Galperin / OEIS A011545 digit conjecture: it requires an effective irrationality
        -- bound `|π - m/10^n| ≥ (π/3)/q²` (exponent EXACTLY 2 at power-of-ten denominators),
        -- strictly stronger than the open conjecture `μ(π) = 2` (best rigorous bound
        -- `μ(π) ≤ 7.103`), hence beyond current mathematics.  It is TRUE (verified to 200000
        -- digits of π; longest 9-run has length 6), so it cannot be disproved either.
        sorry
  -- Reduction: any integer `k > π·10^n` is `≥ ⌊π·10^n⌋ + 1 ≥ π/arctan(10^{-n})`,
  -- contradicting `k < π/arctan(10^{-n})`.
  have h2 : ⌊Real.pi * (10 : ℝ) ^ n⌋ < k := by
    rw [Int.floor_lt]; exact_mod_cast hk1
  have h1 : (⌊Real.pi * (10 : ℝ) ^ n⌋ : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (h2 : ⌊Real.pi * (10 : ℝ) ^ n⌋ + 1 ≤ k)
  linarith [hk2, core, h1]
