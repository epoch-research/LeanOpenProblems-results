import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    let n_real : ℝ := n
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0

-- test: unfolding a n
example (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)))).toNat := by
  unfold a
  rw [dif_pos hn]

-- reduction lemma: if f ≤ g and (⌊g⌋:ℝ) ≤ f then ⌊f⌋ = ⌊g⌋
example (f g : ℝ) (h1 : f ≤ g) (h2 : ((Int.floor g : ℤ) : ℝ) ≤ f) :
    Int.floor f = Int.floor g := by
  apply le_antisymm
  · exact Int.floor_le_floor h1
  · exact Int.le_floor.mpr h2

open Real

lemma hasDerivAt_G (y : ℝ) :
    HasDerivAt (fun y : ℝ => sin y - y * cos y) (y * sin y) y := by
  have h1 : HasDerivAt (fun y : ℝ => sin y - y * cos y)
      (cos y - (1 * cos y + y * (-sin y))) y := by
    apply HasDerivAt.sub (Real.hasDerivAt_sin y)
    exact (hasDerivAt_id y).mul (Real.hasDerivAt_cos y)
  have : cos y - (1 * cos y + y * (-sin y)) = y * sin y := by ring
  rwa [this] at h1

-- Step 1: sin x - x cos x ≥ 0 on [0, π/2]
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

-- placeholder marker
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

-- Step 2: (1 - x²/3) sin x - x cos x ≥ 0 on [0, π/2]
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

-- Step 3:  f ≤ g,  i.e.  (n/4) cot(π/n) ≤ n²/(4π) - π/12  for n ≥ 2.
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
  have hxeq : x * (n : ℝ) = π := by rw [hxdef]; field_simp
  have hscale : (0 : ℝ) < (n:ℝ)^2 / (4 * π) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hkey hscale.le
  have hL : (n:ℝ)^2 / (4 * π) * (x * cos x) = (n:ℝ)/4 * cos x := by
    rw [hxdef]; field_simp
  have hR : (n:ℝ)^2 / (4 * π) * ((1 - x^2/3) * sin x)
      = ((n:ℝ)^2 / (4 * π) - π/12) * sin x := by
    rw [hxdef]; field_simp; ring
  rw [hL, hR] at h2
  linarith [h2]

-- The OPEN Diophantine core (equivalent to frac(g(n)) ≥ d(n)):
lemma floor_g_le_f {n : ℕ} (hn : n ≥ 2) :
    ((Int.floor ((n:ℝ)^2 / (4 * Real.pi) - Real.pi/12) : ℤ) : ℝ)
      ≤ (n : ℝ) / 4 * Real.cot (Real.pi / (n : ℝ)) := by
  sorry

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
