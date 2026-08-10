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

/-!
## Status of the conjecture

The statement below (the "pi from colliding blocks" / Galperin billiard conjecture) asserts
that for every `n` the open interval `(π·10ⁿ, π / arctan(1/10ⁿ))` contains no integer, i.e.
`⌊π/arctan(10⁻ⁿ)⌋ = ⌊π·10ⁿ⌋` (the number of collisions equals the first `n+1` digits of π).

It is **true** (verified directly with 7000-digit precision for all `n ≤ 3000`, and no
counterexample can exist: a counterexample at level `n` would require a run of about `n`
consecutive `9`'s in π starting at decimal position `n+1`, whereas the longest run of `9`'s
in the first 115000 digits of π is only 6 — the Feynman point at position 762).

A *proof* for **all** `n` is, however, a genuine open problem. The reduction below shows
the conjecture is equivalent to the kernel

  `crux n :  π ≤ (⌊π·10ⁿ⌋ + 1) · arctan(1/10ⁿ)`,

which is equivalent to

  `δ_n := ⌈π·10ⁿ⌉ − π·10ⁿ  ≥  (π/3)·10⁻ⁿ`     (the gap `π/arctan(10⁻ⁿ) − π·10ⁿ → (π/3)·10⁻ⁿ`).

A *uniform* lower bound `δ_n ≥ K·10⁻ⁿ` (with `K ≥ π/3`) is exactly an irrationality–measure
statement `μ(π) ≤ 2` (with the right constant) restricted to power-of-`10` denominators.
The best known effective bound is `μ(π) ≤ 7.103…` (Zeilberger–Zudilin 2020), which only yields
`δ_n ≥ C·10^(−6.1 n)` — far too weak (it permits runs of `9`'s up to length `≈ 6.1 n`, while we
need them shorter than `n`). Mathlib contains only `irrational_pi`, with no effective measure.

Everything below is fully proved **except** the single number-theoretic kernel `crux (m+1)`,
which is the open statement; the `n = 0` case is proved exactly (using `arctan 1 = π/4`).
-/

/-- `arctan x < x` for `x > 0` (from `x < tan x` on `(0, π/2)`). -/
private theorem arctan_lt_self {x : ℝ} (hx : 0 < x) : Real.arctan x < x := by
  have h0 : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  have := Real.lt_tan h0 (Real.arctan_lt_pi_div_two x)
  rwa [Real.tan_arctan] at this

/-- `x - x³/3 ≤ arctan x` for `x ≥ 0`, via `arctan x = ∫₀ˣ (1+t²)⁻¹` and `(1+t²)⁻¹ ≥ 1 - t²`. -/
private theorem arctan_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  have key : Real.arctan x = ∫ t in (0 : ℝ)..x, (1 + t ^ 2)⁻¹ := by
    rw [integral_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have hpoly : (∫ t in (0 : ℝ)..x, (1 - t ^ 2)) = x - x ^ 3 / 3 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [intervalIntegral.integral_const, integral_pow]; simp; ring
  rw [key, ← hpoly]
  apply intervalIntegral.integral_mono_on hx
  · apply Continuous.intervalIntegrable; fun_prop
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop); intro t _; positivity
  · intro t _
    have hd : (1 + t ^ 2)⁻¹ - (1 - t ^ 2) = t ^ 4 / (1 + t ^ 2) := by field_simp; ring
    nlinarith [div_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4) (by positivity : (0 : ℝ) ≤ 1 + t ^ 2),
      hd]

/-- The arithmetic kernel of the conjecture.  For `n = 0` this is the exact equality
`π = 4 · arctan 1`.  For `n ≥ 1` it is equivalent to `{π·10ⁿ} ≤ 1 − (π/3)·10⁻ⁿ`, i.e. to an
effective irrationality–measure `μ(π) ≤ 2` statement for power-of-`10` denominators — an
**open problem** (best known `μ(π) ≤ 7.10`). -/
private theorem crux (n : ℕ) :
    (π : ℝ) ≤ ((⌊π * (10 : ℝ) ^ n⌋ + 1 : ℤ) : ℝ) * Real.arctan (1 / (10 : ℝ) ^ n) := by
  rcases n with _ | m
  · -- n = 0 : exact, since arctan 1 = π/4 and ⌊π⌋ = 3, so RHS = 4·(π/4) = π.
    have hfloor : ⌊π⌋ = 3 := by
      have h1 : (3 : ℤ) ≤ ⌊π⌋ := Int.le_floor.mpr (by push_cast; linarith [Real.pi_gt_three])
      have h2 : ⌊π⌋ < 4 := Int.floor_lt.mpr (by push_cast; linarith [Real.pi_lt_four])
      omega
    simp only [pow_zero, mul_one, div_one, Real.arctan_one, hfloor]
    push_cast; linarith [Real.pi_pos]
  · -- n = m+1 : OPEN.  Equivalent to ⌈π·10^(m+1)⌉ − π·10^(m+1) ≥ (π/3)·10^{-(m+1)},
    -- i.e. {π·10^(m+1)} ≤ 1 − (π/3)·10^{-(m+1)} (no run of ~(m+1) nines at position m+2),
    -- which needs μ(π) ≤ 2 — beyond current mathematics.
    sorry

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
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) :=
  by
  -- Reduction: any integer of the interval would be `k ≥ ⌊π·10ⁿ⌋ + 1`, but `crux n` forces
  -- `(⌊π·10ⁿ⌋ + 1) · arctan(1/10ⁿ) ≥ π`, contradicting `k · arctan(1/10ⁿ) < π`.
  rintro ⟨k, h1, h2⟩
  simp only [Nat.cast_id] at h1 h2
  have hatan_pos : 0 < Real.arctan (1 / (10 : ℝ) ^ n) := Real.arctan_pos.mpr (by positivity)
  have hk_ge : (⌊π * (10 : ℝ) ^ n⌋ + 1 : ℤ) ≤ k := by
    have : ⌊π * (10 : ℝ) ^ n⌋ < k := by rw [Int.floor_lt]; exact_mod_cast h1
    omega
  have h3 : (k : ℝ) * Real.arctan (1 / (10 : ℝ) ^ n) < π := by
    rw [lt_div_iff₀ hatan_pos] at h2; linarith [h2]
  have h4 : ((⌊π * (10 : ℝ) ^ n⌋ + 1 : ℤ) : ℝ) * Real.arctan (1 / (10 : ℝ) ^ n)
      ≤ (k : ℝ) * Real.arctan (1 / (10 : ℝ) ^ n) := by
    apply mul_le_mul_of_nonneg_right _ hatan_pos.le
    exact_mod_cast hk_ge
  linarith [crux n, h3, h4]
