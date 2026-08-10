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

/-
A property which is equivalent to the conjecture that the number of collisions
in the described physical system (with mass ratio $10^{2n}$) is $a(n)$:
the interval $(\pi \cdot 10^n, \pi / \arctan(1/10^n))$ does not contain an integer.
The mass ratio $m$ in the comment is interpreted as $\frac{M}{m}$ in the physics setup,
which is $10^{2n}$, so $\sqrt{m}=10^n$.

Note: The OEIS comment uses $m=10^n$ for the $R^2$ term where $R=10^n$ in the physics formula.
We formalize the statement $\forall n \in \mathbb{N}, \nexists k \in \mathbb{Z}$ such that
$\pi \cdot 10^n < k < \pi / \arctan(1/10^n)$.
-/
/-
**Reduction lemma.**  The whole conjecture is equivalent to the single inequality
`π / arctan(10⁻ⁿ) ≤ ⌈π · 10ⁿ⌉`.

Indeed, the interval `(π·10ⁿ, π/arctan(10⁻ⁿ))` is nonempty (since `arctan x < x`),
so it contains an integer iff its smallest integer `> π·10ⁿ`, namely `⌈π·10ⁿ⌉`,
is `< π/arctan(10⁻ⁿ)`.  Hence "no integer" is exactly `π/arctan(10⁻ⁿ) ≤ ⌈π·10ⁿ⌉`.

This `⌈π·10ⁿ⌉`-inequality is the content of OEIS A011545:
expanding `arctan` one finds `π/arctan(10⁻ⁿ) = π·10ⁿ + (π/3)·10⁻ⁿ + O(10⁻³ⁿ)`, so the
inequality says `⌈π·10ⁿ⌉ - π·10ⁿ ≥ (π/3)·10⁻ⁿ`, i.e. `π·10ⁿ` is at least `(π/3)·10⁻ⁿ`
below an integer.  A failure would yield a rational `M/10ⁿ` with
`0 < M/10ⁿ - π < (π/3)·10⁻²ⁿ ≈ 1.047/(10ⁿ)²`, a power-of-ten approximation of `π`
of quality `≈ 1.047/q²`.  This lies *just beyond* Legendre's theorem
(`Real.exists_rat_eq_convergent`, which needs `< 1/(2q²)`) and even beyond the
semiconvergent threshold `1/q²`.  Equivalently it asserts that `π` has no run of about
`n` nines beginning at decimal position `n+1`; ruling this out for all `n` amounts to an
effective irrationality measure `2` for `π` along powers of `10`, which is not known.
-/
/-- Lower bound `arctan y ≥ y - y³/3` for `y ≥ 0`, proved via monotonicity of
`g(x) = arctan x - (x - x³/3)`, whose derivative is `x⁴/(1+x²) ≥ 0`. -/
theorem arctan_lower (y : ℝ) (hy : 0 ≤ y) : y - y ^ 3 / 3 ≤ Real.arctan y := by
  set f : ℝ → ℝ := fun x => Real.arctan x - (x - x ^ 3 / 3) with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (x ^ 4 / (1 + x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := Real.hasDerivAt_arctan x
    have hb : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (x ^ 2) x := by
      have h3 : HasDerivAt (fun x : ℝ => x ^ 3) ((3 : ℝ) * x ^ 2) x := by
        simpa using hasDerivAt_pow 3 x
      have := h3.div_const 3
      convert this using 1; ring
    have h2 : HasDerivAt (fun x : ℝ => x - x ^ 3 / 3) (1 - x ^ 2) x :=
      (hasDerivAt_id x).sub hb
    have hsub := h1.sub h2
    convert hsub using 1
    have hpos : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    field_simp; ring
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hdiff
    intro x; rw [(hderiv x).deriv]; positivity
  have h0 : f 0 = 0 := by simp [hf]
  have hle := hmono hy
  rw [h0] at hle; simp only [hf] at hle; linarith

/-- **Reduction helper.**  For `N ≥ 1`, eliminate the transcendental `arctan` using
`arctan_lower`, reducing the interval inequality to the purely *arithmetic* core
`π / (t − t³/3) ≤ ⌈π·10ᴺ⌉` with `t = 10⁻ᴺ`. -/
theorem core_of_step2 (N : ℕ) (hN : 1 ≤ N)
    (h2 : Real.pi / (1 / (10 : ℝ) ^ N - (1 / (10 : ℝ) ^ N) ^ 3 / 3)
            ≤ ((⌈Real.pi * (10 : ℝ) ^ N⌉ : ℤ) : ℝ)) :
    Real.pi / Real.arctan (1 / (10 : ℝ) ^ N)
            ≤ ((⌈Real.pi * (10 : ℝ) ^ N⌉ : ℤ) : ℝ) := by
  set t : ℝ := 1 / (10 : ℝ) ^ N with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htle : t ≤ 1 / 10 := by
    rw [ht]
    have h10 : (10 : ℝ) ≤ (10 : ℝ) ^ N := by
      calc (10 : ℝ) = (10 : ℝ) ^ 1 := (pow_one 10).symm
        _ ≤ (10 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    exact one_div_le_one_div_of_le (by norm_num) h10
  have hcube : 0 < t - t ^ 3 / 3 := by nlinarith [ht0, htle, sq_nonneg t]
  have hal : t - t ^ 3 / 3 ≤ Real.arctan t := arctan_lower t ht0.le
  have step1 : Real.pi / Real.arctan t ≤ Real.pi / (t - t ^ 3 / 3) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hcube hal
  exact le_trans step1 h2

set_option maxHeartbeats 1000000 in
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  rintro ⟨k, hk1, hk2⟩
  -- Any integer `k` with `π·10ⁿ < k` satisfies `⌈π·10ⁿ⌉ ≤ k`.
  have hkge : (⌈Real.pi * (10 : ℝ) ^ n.cast⌉ : ℤ) ≤ k := Int.ceil_le.mpr (le_of_lt hk1)
  have hkR : ((⌈Real.pi * (10 : ℝ) ^ n.cast⌉ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkge
  -- The single inequality to which the whole conjecture reduces:
  --   `π / arctan(10⁻ⁿ) ≤ ⌈π·10ⁿ⌉`.
  -- Equivalently (expanding `arctan`): `δ_n := ⌈π·10ⁿ⌉ − π·10ⁿ ≥ (π/3)·10⁻ⁿ`.
  -- `n = 0` is exactly tight and proved outright (`arctan 1 = π/4`, `π/(π/4) = 4 = ⌈π⌉`).
  -- Each fixed `n ≥ 1` is provable from a sufficiently precise rational lower bound for `π`
  -- (`n = 1,2,3` below use Mathlib's `pi_gt_d4 / pi_lt_d4` etc.); the helper `core_of_step2`
  -- removes the transcendental `arctan`, leaving the purely arithmetic core.
  -- The UNIVERSAL statement over all `n`, however, is an effective irrationality-measure-`2`
  -- bound for `π` along powers of `10` (constant `≥ π/3 > 1`): it asserts `π` has no run of
  -- about `n` nines starting at decimal position `n+1`.  This is beyond the best known
  -- effective measure (`μ(π) ≤ 7.103`) and is not available in Mathlib; the residual
  -- `n ≥ 4` core is therefore left open below.
  have core : Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)
      ≤ ((⌈Real.pi * (10 : ℝ) ^ n.cast⌉ : ℤ) : ℝ) := by
    simp only [Nat.cast_id]
    match n with
    | 0 =>
      -- `(10:ℝ)^0 = 1`, `arctan 1 = π/4`, `π/(π/4) = 4` and `⌈π⌉ = 4`.
      have h10 : (10 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
      rw [h10, mul_one, div_one, Real.arctan_one]
      have hceil : (⌈Real.pi⌉ : ℤ) = 4 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; linarith [Real.pi_gt_three],
                by push_cast; linarith [Real.pi_lt_d2]⟩
      rw [hceil]
      have hpi : Real.pi / (Real.pi / 4) = 4 := by field_simp
      rw [hpi]; norm_num
    | 1 =>
      apply core_of_step2 1 (le_refl 1)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (1 : ℕ)⌉ : ℤ) = 32 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d2],
                by push_cast; nlinarith [Real.pi_lt_d2]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (1 : ℕ) - (1 / (10 : ℝ) ^ (1 : ℕ)) ^ 3 / 3 = 299 / 3000 by
            norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 299 / 3000)]
      push_cast; nlinarith [Real.pi_lt_d2]
    | 2 =>
      apply core_of_step2 2 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (2 : ℕ)⌉ : ℤ) = 315 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d2],
                by push_cast; nlinarith [Real.pi_lt_d2]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (2 : ℕ) - (1 / (10 : ℝ) ^ (2 : ℕ)) ^ 3 / 3
            = 29999 / 3000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 29999 / 3000000)]
      push_cast; nlinarith [Real.pi_lt_d4]
    | 3 =>
      apply core_of_step2 3 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (3 : ℕ)⌉ : ℤ) = 3142 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d4],
                by push_cast; nlinarith [Real.pi_lt_d4]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (3 : ℕ) - (1 / (10 : ℝ) ^ (3 : ℕ)) ^ 3 / 3
            = 2999999 / 3000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2999999 / 3000000000)]
      push_cast; nlinarith [Real.pi_lt_d4]
    | 4 =>
      apply core_of_step2 4 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (4 : ℕ)⌉ : ℤ) = 31416 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d4],
                by push_cast; nlinarith [Real.pi_lt_d4]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (4 : ℕ) - (1 / (10 : ℝ) ^ (4 : ℕ)) ^ 3 / 3
            = 299999999 / 3000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 299999999 / 3000000000000)]
      push_cast; nlinarith [Real.pi_lt_d6]
    | 5 =>
      apply core_of_step2 5 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (5 : ℕ)⌉ : ℤ) = 314160 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d6],
                by push_cast; nlinarith [Real.pi_lt_d4]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (5 : ℕ) - (1 / (10 : ℝ) ^ (5 : ℕ)) ^ 3 / 3
            = 29999999999 / 3000000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 29999999999 / 3000000000000000)]
      push_cast; nlinarith [Real.pi_lt_d6]
    | 6 =>
      apply core_of_step2 6 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (6 : ℕ)⌉ : ℤ) = 3141593 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d6],
                by push_cast; nlinarith [Real.pi_lt_d6]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (6 : ℕ) - (1 / (10 : ℝ) ^ (6 : ℕ)) ^ 3 / 3
            = 2999999999999 / 3000000000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2999999999999 / 3000000000000000000)]
      push_cast; nlinarith [Real.pi_lt_d20]
    | 7 =>
      apply core_of_step2 7 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (7 : ℕ)⌉ : ℤ) = 31415927 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d20],
                by push_cast; nlinarith [Real.pi_lt_d20]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (7 : ℕ) - (1 / (10 : ℝ) ^ (7 : ℕ)) ^ 3 / 3
            = 299999999999999 / 3000000000000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 299999999999999 / 3000000000000000000000)]
      push_cast; nlinarith [Real.pi_lt_d20]
    | 8 =>
      apply core_of_step2 8 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (8 : ℕ)⌉ : ℤ) = 314159266 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d20],
                by push_cast; nlinarith [Real.pi_lt_d20]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (8 : ℕ) - (1 / (10 : ℝ) ^ (8 : ℕ)) ^ 3 / 3
            = 29999999999999999 / 3000000000000000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 29999999999999999 / 3000000000000000000000000)]
      push_cast; nlinarith [Real.pi_lt_d20]
    | 9 =>
      apply core_of_step2 9 (by norm_num)
      have hceil : (⌈Real.pi * (10 : ℝ) ^ (9 : ℕ)⌉ : ℤ) = 3141592654 := by
        rw [Int.ceil_eq_iff]
        refine ⟨by push_cast; nlinarith [Real.pi_gt_d20],
                by push_cast; nlinarith [Real.pi_lt_d20]⟩
      rw [hceil]
      rw [show (1 : ℝ) / (10 : ℝ) ^ (9 : ℕ) - (1 / (10 : ℝ) ^ (9 : ℕ)) ^ 3 / 3
            = 2999999999999999999 / 3000000000000000000000000000 by norm_num]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2999999999999999999 / 3000000000000000000000000000)]
      push_cast; nlinarith [Real.pi_lt_d20]
    | (m + 10) =>
      -- The residual open core: `π / (t − t³/3) ≤ ⌈π·10^(m+10)⌉` for all `m`,
      -- i.e. `δ_{m+10} ≥ (π/3)·10⁻⁽ᵐ⁺¹⁰⁾`, an effective irrationality-measure-2 bound
      -- for `π` along powers of `10`, not available with current mathematics.
      apply core_of_step2 (m + 10) (by omega)
      sorry
  -- Combining: `k < π/arctan(10⁻ⁿ) ≤ ⌈π·10ⁿ⌉ ≤ k`, a contradiction.
  linarith [hk2, core, hkR]

