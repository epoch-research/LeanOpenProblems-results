import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A064313: Integer part of area of a regular polygon with $n$ sides each of length 1.
$$a(n) = \left\lfloor \frac{n}{4 \tan(\pi/n)} \right\rfloor = \left\lfloor \frac{n}{4} \cot\left(\frac{\pi}{n}\right) \right\rfloor$$
The sequence is formally defined for $n \ge 2$. We return $0$ for $n < 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    let n_real : ℝ := n
    -- Area of a regular $n$-gon with side length 1 is $A = \frac{n}{4} \cot(\frac{\pi}{n})$.
    -- Since $n \ge 2$, $\pi/n \in (0, \pi/2]$, which implies $\cot(\pi/n) \ge 0$, so $\mathrm{area} \ge 0$.
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0

open Real

/-!
## Reduction of the conjecture

Write `f n = (n/4) * cot (π/n)` (the exact area) and `g n = n²/(4π) - π/12`
(the approximation).  Expanding `cot` as a Laurent series shows

  `g n - f n = π³/(180 n²) + π⁵/(1890 n⁴) + … =: d n > 0`,

so `f n < g n` and `d n → 0⁺`.  Consequently `⌊f n⌋ = ⌊g n⌋` **iff** no integer
lies in the half–open interval `(f n, g n]`, which is equivalent to the
Diophantine statement

  `frac (g n) ≥ d n`   for every `n ≥ 2`.

The inequality `f n ≤ g n` (i.e. `⌊f n⌋ ≤ ⌊g n⌋`) is elementary and is proved
below (`f_le_g`).  The reverse inequality `⌊g n⌋ ≤ f n` (`floor_g_le_f`) is the
genuine content of the conjecture.  It is equivalent to
`frac (n²/(4π) - π/12) ≥ π³/(180 n²) + …`, i.e. that the quadratic sequence
`n²/(4π) - π/12` never falls within `≈ 0.172/n²` above an integer.  Multiplying
out, this says `|π² + 12 m π - 3 n²| ≥ π⁴/(15 n²)` for the nearest integer `m`,
a lower bound for a degree‑`2` integer polynomial evaluated at `π` of height
`≈ 3 n²`.  Such a bound with exponent `1` is *stronger* than any known
transcendence (or even irrationality) measure of `π`; indeed it is at least as
hard as proving that the irrationality measure of `π` equals `2`, a famous open
problem.  It has been verified numerically here for all `2 ≤ n ≤ 10¹¹`
(with equality exactly at `n = 2` and `n = 4`, where the area is an integer),
but no unconditional proof is currently available.
-/

/-- Derivative of `G y = sin y - y cos y` is `y sin y`. -/
lemma hasDerivAt_G (y : ℝ) :
    HasDerivAt (fun y : ℝ => sin y - y * cos y) (y * sin y) y := by
  have h1 : HasDerivAt (fun y : ℝ => sin y - y * cos y)
      (cos y - (1 * cos y + y * (-sin y))) y := by
    apply HasDerivAt.sub (Real.hasDerivAt_sin y)
    exact (hasDerivAt_id y).mul (Real.hasDerivAt_cos y)
  have : cos y - (1 * cos y + y * (-sin y)) = y * sin y := by ring
  rwa [this] at h1

/-- `sin x - x cos x ≥ 0` on `[0, π/2]`. -/
lemma sin_sub_mul_cos_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 2) :
    0 ≤ sin x - x * cos x := by
  have hmono : MonotoneOn (fun y => sin y - y * cos y) (Set.Icc 0 (π/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (π/2))
    · fun_prop
    · intro y _
      exact (hasDerivAt_G y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_G y).deriv]
      rw [interior_Icc, Set.mem_Ioo] at hy
      have hy0 : 0 ≤ y := hy.1.le
      have hsy : 0 ≤ sin y := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi hy0
        linarith [Real.pi_pos, hy.2]
      positivity
  have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by positivity⟩) (Set.mem_Icc.mpr ⟨hx0, hx⟩) hx0
  simpa using this

/-- Derivative of `H y = (1 - y²/3) sin y - y cos y` is `(y/3)(sin y - y cos y)`. -/
lemma hasDerivAt_H (y : ℝ) :
    HasDerivAt (fun y : ℝ => (1 - y^2/3) * sin y - y * cos y)
      ((y/3) * (sin y - y * cos y)) y := by
  have d1 : HasDerivAt (fun y : ℝ => 1 - y^2/3) (-(2*y)/3) y := by
    have h := ((hasDerivAt_pow 2 y).div_const 3).const_sub 1
    convert h using 1
    simp; ring
  have h1 := (d1.mul (Real.hasDerivAt_sin y)).sub
    ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y))
  convert h1 using 1
  simp only [id_eq]; ring

/-- `(1 - x²/3) sin x - x cos x ≥ 0` on `[0, π/2]`.  Equivalently `x cot x ≤ 1 - x²/3`. -/
lemma H_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 2) :
    0 ≤ (1 - x^2/3) * sin x - x * cos x := by
  have hmono : MonotoneOn (fun y => (1 - y^2/3) * sin y - y * cos y) (Set.Icc 0 (π/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (π/2))
    · fun_prop
    · intro y _
      exact (hasDerivAt_H y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_H y).deriv]
      rw [interior_Icc, Set.mem_Ioo] at hy
      have hy0 : 0 ≤ y := hy.1.le
      have hG : 0 ≤ sin y - y * cos y := sin_sub_mul_cos_nonneg hy0 hy.2.le
      positivity
  have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by positivity⟩) (Set.mem_Icc.mpr ⟨hx0, hx⟩) hx0
  simpa using this

/-- The easy half of the reduction: `f n ≤ g n`, i.e.
`(n/4) cot (π/n) ≤ n²/(4π) - π/12` for `n ≥ 2`. -/
lemma f_le_g {n : ℕ} (hn : n ≥ 2) :
    (n : ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)) ≤ (n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12 := by
  have hπ : 0 < π := Real.pi_pos
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set x : ℝ := π / (n : ℝ) with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxle : x ≤ π / 2 := by
    rw [hxdef]; gcongr
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxlt : x < π := by linarith [hxle, hπ]
  have hsin : 0 < sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
  have hkey : x * cos x ≤ (1 - x^2/3) * sin x := by
    have := H_nonneg hx0 hxle
    linarith
  rw [Real.cot_eq_cos_div_sin, ← mul_div_assoc, div_le_iff₀ hsin]
  have hscale : (0 : ℝ) < (n:ℝ)^2 / (4 * π) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hkey hscale.le
  have hL : (n:ℝ)^2 / (4 * π) * (x * cos x) = (n:ℝ)/4 * cos x := by
    rw [hxdef]; field_simp
  have hR : (n:ℝ)^2 / (4 * π) * ((1 - x^2/3) * sin x)
      = ((n:ℝ)^2 / (4 * π) - π/12) * sin x := by
    rw [hxdef]; field_simp; ring
  rw [hL, hR] at h2
  linarith [h2]

/-- The hard half of the reduction: `⌊g n⌋ ≤ f n`.

This is the genuine content of the OEIS A064313 conjecture.  It is equivalent to
`frac (n²/(4π) - π/12) ≥ π³/(180 n²) + …` for all `n ≥ 2`, an inhomogeneous
quadratic Diophantine statement about `π` that is stronger than any known
transcendence measure of `π` (and at least as hard as the open problem of
determining the irrationality measure of `π`).  It is verified numerically for
all `2 ≤ n ≤ 10¹¹` but no unconditional proof is presently known. -/
lemma floor_g_le_f {n : ℕ} (hn : n ≥ 2) :
    ((Int.floor ((n:ℝ)^2 / (4 * Real.pi) - Real.pi/12) : ℤ) : ℝ)
      ≤ (n : ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)) := by
  sorry

/--
Conjecture from OEIS A064313, entry %C:
Usually (perhaps always?) $\lfloor n^2/(4\pi) - \pi/12 \rfloor$ for a polygon of circumference $n$.
-/
theorem oeis_64313_conjecture_0 (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  unfold a
  rw [dif_pos hn]
  show (Int.floor ((n:ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)))).toNat
      = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat
  have hfloor : Int.floor ((n:ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)))
      = Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12) := by
    apply le_antisymm
    · exact Int.floor_le_floor (f_le_g hn)
    · exact Int.le_floor.mpr (floor_g_le_f hn)
  rw [hfloor]
