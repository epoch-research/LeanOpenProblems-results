import FormalConjectures.Util.ProblemImports

open scoped Real
open Real Set

/--
A064313: Integer part of area of a regular polygon with $n$ sides each of length 1.
$$a(n) = \left\lfloor \frac{n}{4 \tan(\pi/n)} \right\rfloor = \left\lfloor \frac{n}{4} \cot\left(\frac{\pi}{n}\right) \right\rfloor$$
The sequence is formally defined for $n \ge 2$. We return $0$ for $n < 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n ≥ 2 then
    let n_real : ℝ := n
    -- Area of a regular $n$-gon with side length 1 is $A = \frac{n}{4} \cot(\frac{\pi}{n})$.
    -- Since $n \ge 2$, $\pi/n \in (0, \pi/2]$, which implies $\cot(\pi/n) \ge 0$, so $\mathrm{area} \ge 0$.
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0

lemma sin_sub_cos_pos {z : ℝ} (hz1 : 0 < z) (hz2 : z < π / 2) : 0 < sin z - z * cos z := by
  have h_cos : 0 < cos z := cos_pos_of_mem_Ioo ⟨by linarith, hz2⟩
  have h_tan : z < tan z := lt_tan hz1 hz2
  rw [tan_eq_sin_div_cos] at h_tan
  have : 0 < sin z / cos z - z := by linarith
  have : 0 < (sin z / cos z - z) * cos z := mul_pos this h_cos
  have h_eq : (sin z / cos z - z) * cos z = sin z - z * cos z := by
    rw [sub_mul, div_mul_cancel₀ _ h_cos.ne']
  rwa [h_eq] at this

lemma f_hasDerivAt (z : ℝ) :
    HasDerivAt (fun z => sin z * (1 - z ^ 2 / 3) - z * cos z) (z / 3 * (sin z - z * cos z)) z := by
  have h_z_sq : HasDerivAt (fun z => z ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h_z_sq_div : HasDerivAt (fun z => z ^ 2 / 3) (2 * z / 3) z := by
    simpa using h_z_sq.div_const 3
  have h_sub : HasDerivAt (fun z => 1 - z ^ 2 / 3) (-2 * z / 3) z := by
    have h_aux := (hasDerivAt_const z 1).sub h_z_sq_div
    convert h_aux using 1
    ring
  have h_mul1 : HasDerivAt (fun z => sin z * (1 - z ^ 2 / 3)) (cos z * (1 - z ^ 2 / 3) + sin z * (-2 * z / 3)) z :=
    (hasDerivAt_sin z).mul h_sub
  have h_mul2 : HasDerivAt (fun z => z * cos z) (cos z - z * sin z) z := by
    simpa using (hasDerivAt_id' z).mul (hasDerivAt_cos z)
  have h_all : HasDerivAt (fun z => sin z * (1 - z ^ 2 / 3) - z * cos z)
    ((cos z * (1 - z ^ 2 / 3) + sin z * (-2 * z / 3)) - (cos z - z * sin z)) z :=
    h_mul1.sub h_mul2
  convert h_all using 1
  ring

lemma f_deriv (z : ℝ) :
    deriv (fun z => sin z * (1 - z ^ 2 / 3) - z * cos z) z = z / 3 * (sin z - z * cos z) :=
  (f_hasDerivAt z).deriv

lemma f_strictMono :
    StrictMonoOn (fun z => sin z * (1 - z ^ 2 / 3) - z * cos z) (Icc 0 (π / 3)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (π / 3))
  · fun_prop
  · rw [interior_Icc]
    intro z hz
    rw [f_deriv]
    have h_pi_div : π / 3 < π / 2 := by
      have h_pi := pi_pos
      linarith
    have hz1 : 0 < z := hz.1
    have hz2 : z < π / 2 := hz.2.trans h_pi_div
    have h_pos1 : 0 < z / 3 := by linarith
    have h_pos2 : 0 < sin z - z * cos z := sin_sub_cos_pos hz1 hz2
    exact mul_pos h_pos1 h_pos2

lemma f_nonneg {z : ℝ} (hz : z ∈ Icc 0 (π / 3)) : 0 ≤ sin z * (1 - z ^ 2 / 3) - z * cos z := by
  have h_zero : (0 : ℝ) ∈ Icc 0 (π / 3) := by
    rw [mem_Icc]
    refine ⟨by linarith, ?_⟩
    have h_pi := pi_pos
    linarith
  have h_mono := f_strictMono h_zero hz
  rcases eq_or_lt_of_le hz.1 with rfl | hz_pos
  · simp
  · have : (0 : ℝ) < z := hz_pos
    have h_lt := h_mono this
    have h_val : (fun z => sin z * (1 - z ^ 2 / 3) - z * cos z) 0 = 0 := by simp
    rw [h_val] at h_lt
    exact h_lt.le

lemma cot_le_inv_sub_div {z : ℝ} (hz : z ∈ Ioc 0 (π / 3)) : Real.cot z ≤ 1 / z - z / 3 := by
  have hz_cc : z ∈ Icc 0 (π / 3) := ⟨hz.1.le, hz.2⟩
  have h_nonneg := f_nonneg hz_cc
  have h_sin_pos : 0 < sin z := by
    apply sin_pos_of_mem_Ioo
    constructor
    · exact hz.1
    · have h_pi_div : π / 3 < π := by
        have h_pi := pi_pos
        linarith
      exact hz.2.trans_lt h_pi_div
  have h_z_pos : 0 < z := hz.1
  rw [Real.cot_eq_cos_div_sin]
  have h1 : cos z * z ≤ sin z * (1 - z ^ 2 / 3) := by
    have h_aux : z * cos z ≤ sin z * (1 - z ^ 2 / 3) := by linarith
    rwa [mul_comm] at h_aux
  have h3 : (sin z * (1 - z ^ 2 / 3)) / z = sin z * (1 / z - z / 3) := by
    field_simp [h_z_pos.ne']
  have h2 : cos z ≤ (1 / z - z / 3) * sin z := by
    have h_aux : cos z ≤ (sin z * (1 - z ^ 2 / 3)) / z := (le_div_iff₀ h_z_pos).mpr h1
    rw [h3] at h_aux
    rwa [mul_comm] at h_aux
  exact (div_le_iff₀ h_sin_pos).mpr h2

lemma area_le_bound (n : ℕ) (hn : n ≥ 3) :
    let n_real : ℝ := n
    n_real / 4 * Real.cot (Real.pi / n_real) ≤ n_real^2 / (4 * Real.pi) - Real.pi / 12 := by
  intro n_real
  have h_n_pos : 0 < n_real := by
    have h_cast : (3 : ℝ) ≤ n_real := by
      change (3 : ℝ) ≤ (n : ℝ)
      exact_mod_cast hn
    linarith
  have h_z : Real.pi / n_real ∈ Ioc 0 (π / 3) := by
    constructor
    · exact div_pos pi_pos h_n_pos
    · have h_cast : (3 : ℝ) ≤ n_real := by
        change (3 : ℝ) ≤ (n : ℝ)
        exact_mod_cast hn
      exact div_le_div₀ pi_pos.le le_rfl (by norm_num) h_cast
  have h_cot := cot_le_inv_sub_div h_z
  have h_mul_pos : 0 < n_real / 4 := by linarith
  have h_le := mul_le_mul_of_nonneg_left h_cot h_mul_pos.le
  have h_rhs : (n_real / 4) * (1 / (π / n_real) - (π / n_real) / 3) = n_real^2 / (4 * π) - π / 12 := by
    field_simp [h_n_pos.ne', pi_pos.ne']
    ring
  rw [h_rhs] at h_le
  exact h_le

lemma cot_gt_inv_sub_z {z : ℝ} (hz1 : 0 < z) (hz2 : z < 1) (hz_pi : z < π) : Real.cot z > 1 / z - z := by
  have h_sin_lt : sin z < z := sin_lt hz1
  have h_cos_ge : cos z ≥ 1 - z ^ 2 / 2 := one_sub_sq_div_two_le_cos
  have h_sin_pos : 0 < sin z := sin_pos_of_mem_Ioo ⟨hz1, hz_pi⟩
  have h_z2_le_one : z ^ 2 < 1 := by
    nlinarith
  have h_sub_pos : 0 < 1 - z ^ 2 := by linarith
  have h_left : sin z * (1 - z ^ 2) < z * (1 - z ^ 2) := mul_lt_mul_of_pos_right h_sin_lt h_sub_pos
  have h_right : z * cos z ≥ z * (1 - z ^ 2 / 2) := mul_le_mul_of_nonneg_left h_cos_ge hz1.le
  have h_all2 : sin z * (1 - z ^ 2) < z * cos z := by
    calc sin z * (1 - z ^ 2)
      _ < z * (1 - z ^ 2) := h_left
      _ ≤ z * (1 - z ^ 2 / 2) := by nlinarith
      _ ≤ z * cos z := h_right
  rw [Real.cot_eq_cos_div_sin]
  have h_div_eq : 1 / z - z = (1 - z ^ 2) / z := by
    field_simp [hz1.ne']
  rw [h_div_eq]
  have h_num : 0 < z * cos z - sin z * (1 - z ^ 2) := by linarith
  have h_div_sub : cos z / sin z - (1 - z ^ 2) / z > 0 := by
    field_simp [hz1.ne', h_sin_pos.ne']
    linarith [h_num]
  linarith

lemma area_gt_bound_sub_one (n : ℕ) (hn : n ≥ 4) :
    let n_real : ℝ := n
    n_real^2 / (4 * Real.pi) - Real.pi / 12 < n_real / 4 * Real.cot (Real.pi / n_real) + 1 := by
  intro n_real
  have h_n_pos : 0 < n_real := by
    have h_cast : (4 : ℝ) ≤ n_real := by
      change (4 : ℝ) ≤ (n : ℝ)
      exact_mod_cast hn
    linarith
  have h_z : Real.pi / n_real ∈ Ioo 0 (1 : ℝ) := by
    constructor
    · exact div_pos pi_pos h_n_pos
    · have h_cast : (4 : ℝ) ≤ n_real := by
        change (4 : ℝ) ≤ (n : ℝ)
        exact_mod_cast hn
      have h_pi_lt_four : Real.pi < 4 := by
        have := Real.pi_lt_d2
        linarith
      have h_le : Real.pi / n_real ≤ Real.pi / 4 := div_le_div₀ pi_pos.le le_rfl (by norm_num) h_cast
      linarith
  have h_cot := cot_gt_inv_sub_z h_z.1 h_z.2 (by
    have h_n_gt_one : 1 < n_real := by
      have h_cast : (4 : ℝ) ≤ n_real := by
        change (4 : ℝ) ≤ (n : ℝ)
        exact_mod_cast hn
      linarith
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    exact div_lt_self pi_pos h_n_gt_one)
  have h_mul_pos : 0 < n_real / 4 := by linarith
  have h_lt := mul_lt_mul_of_pos_left h_cot h_mul_pos
  have h_rhs : (n_real / 4) * (1 / (π / n_real) - (π / n_real)) = n_real^2 / (4 * π) - π / 4 := by
    field_simp [h_n_pos.ne', pi_pos.ne']
  rw [h_rhs] at h_lt
  have h_pi_lt : π / 4 < π / 12 + 1 := by
    have h_pi_lt_four : Real.pi < 4 := by
      have := Real.pi_lt_d2
      linarith
    linarith
  linarith

lemma floor_eq_of_no_int {x y : ℝ}
    (h_le : x ≤ y) (h_no : ∀ k : ℤ, ¬ (x < (k : ℝ) ∧ (k : ℝ) ≤ y)) :
    Int.floor x = Int.floor y := by
  have h1 : Int.floor x ≤ Int.floor y := Int.floor_mono h_le
  have h2 : Int.floor y ≤ Int.floor x := by
    rw [Int.le_floor]
    by_contra h
    push_neg at h
    exact h_no (Int.floor y) ⟨h, Int.floor_le _⟩
  exact le_antisymm h1 h2


/--
Conjecture from OEIS A064313, entry %C:
Usually (perhaps always?) $\lfloor n^2/(4\pi) - \pi/12 \rfloor$ for a polygon of circumference $n$.
-/
theorem oeis_64313_conjecture_0 (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  unfold a
  simp only [if_pos hn]

#print axioms oeis_64313_conjecture_0

