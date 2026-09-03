import Submission.MultiplicativeLargeSieve

/-!
# An incomplete primitive character-sum bound

Pólya–Vinogradov follows from the primitive Gauss-sum identity, geometric
sums, and the elementary harmonic-sum estimate. These are analytic upper
bounds, not the prime-count lower bounds required for Erdős 821.
-/

open scoped BigOperators
open Finset

namespace Erdos821.AnalyticSieve

lemma norm_wave (n : ℤ) (x : ℝ) : ‖wave n x‖ = 1 := by
  unfold wave
  rw [Complex.norm_exp]
  simp

lemma wave_nat_eq_pow (n : ℕ) (x : ℝ) : wave n x = wave 1 x ^ n := by
  unfold wave
  simp only [Int.cast_natCast, Int.cast_one, one_mul]
  rw [mul_assoc, Complex.exp_nat_mul]

lemma norm_wave_one_sub_one (x : ℝ) :
    ‖wave 1 x - 1‖ = |2 * Real.sin (Real.pi * x)| := by
  have heq : wave 1 x = Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
    unfold wave
    push_cast
    congr 1
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]

lemma norm_geometric_mul_le (z : ℂ) (hz : ‖z‖ = 1) (L : ℕ) :
    ‖∑ n ∈ range L, z ^ n‖ * ‖z - 1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

lemma norm_geometric_wave_le_left (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1 / 2)
    (L : ℕ) :
    ‖∑ n ∈ range L, wave 1 x ^ n‖ ≤ 1 / (2 * x) := by
  have hs := Real.mul_le_sin (x := Real.pi * x) (by positivity)
    (by nlinarith [Real.pi_pos])
  have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by
    field_simp
  rw [heq] at hs
  have hd : 4 * x ≤ ‖wave 1 x - 1‖ := by
    rw [norm_wave_one_sub_one, abs_of_nonneg (by linarith : 0 ≤ 2 * Real.sin (Real.pi * x))]
    linarith
  have h := (mul_le_mul_of_nonneg_left hd (norm_nonneg (∑ n ∈ range L, wave 1 x ^ n))).trans
    (norm_geometric_mul_le _ (norm_wave 1 x) L)
  apply (le_div_iff₀ (by positivity : 0 < 2 * x)).mpr
  nlinarith

lemma norm_geometric_wave_le_right (x : ℝ) (hx : 1 / 2 ≤ x) (hx' : x < 1)
    (L : ℕ) :
    ‖∑ n ∈ range L, wave 1 x ^ n‖ ≤ 1 / (2 * (1 - x)) := by
  have hx0 : 0 < 1 - x := sub_pos.mpr hx'
  have hs := Real.mul_le_sin (x := Real.pi * (1 - x)) (by positivity)
    (by nlinarith [Real.pi_pos])
  have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by
    field_simp
  rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.sin_pi_sub] at hs
  have hd : 4 * (1 - x) ≤ ‖wave 1 x - 1‖ := by
    rw [norm_wave_one_sub_one, abs_of_nonneg (by linarith : 0 ≤ 2 * Real.sin (Real.pi * x))]
    linarith
  have h := (mul_le_mul_of_nonneg_left hd (norm_nonneg (∑ n ∈ range L, wave 1 x ^ n))).trans
    (norm_geometric_mul_le _ (norm_wave 1 x) L)
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - x))).mpr
  nlinarith

lemma norm_geometric_wave_le (x : ℝ) (hx : 0 < x) (hx' : x < 1) (L : ℕ) :
    ‖∑ n ∈ range L, wave 1 x ^ n‖ ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
  have hx0 : 0 < 1 - x := sub_pos.mpr hx'
  rcases le_total x (1 / 2) with h | h
  · exact (norm_geometric_wave_le_left x hx h L).trans (le_add_of_nonneg_right (by positivity))
  · exact (norm_geometric_wave_le_right x h hx' L).trans (le_add_of_nonneg_left (by positivity))

noncomputable def intervalWaveSum (M : ℤ) (L : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ range L, wave (M + n) x

lemma intervalWaveSum_eq (M : ℤ) (L : ℕ) (x : ℝ) :
    intervalWaveSum M L x = wave M x * ∑ n ∈ range L, wave 1 x ^ n := by
  simp only [intervalWaveSum, wave_add, wave_nat_eq_pow, Finset.mul_sum]

lemma norm_intervalWaveSum_rational_le {q a : ℕ} (ha : 0 < a) (haq : a < q)
    (M : ℤ) (L : ℕ) :
    ‖intervalWaveSum M L ((a : ℝ) / q)‖ ≤
      (q : ℝ) / 2 * ((a : ℝ)⁻¹ + ((q - a : ℕ) : ℝ)⁻¹) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (ha.trans haq)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have haq' : (a : ℝ) < q := by exact_mod_cast haq
  rw [intervalWaveSum_eq, norm_mul, norm_wave, one_mul]
  convert norm_geometric_wave_le ((a : ℝ) / q) (by positivity)
    ((div_lt_one hq).mpr haq') L using 1
  rw [Nat.cast_sub haq.le]
  field_simp

lemma reciprocal_reflect_sum (q : ℕ) :
    (∑ a ∈ Icc 1 (q - 1), ((q - a : ℕ) : ℝ)⁻¹) =
      ∑ a ∈ Icc 1 (q - 1), (a : ℝ)⁻¹ := by
  apply Finset.sum_bij (fun a _ => q - a)
  · intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  · intro a ha b hb hab
    simp only [mem_Icc] at ha hb
    omega
  · intro b hb
    refine ⟨q - b, ?_, ?_⟩
    · simp only [mem_Icc] at hb ⊢
      omega
    · simp only [mem_Icc] at hb
      omega
  · intro a ha
    rfl

lemma reciprocal_pair_sum (q : ℕ) :
    (∑ a ∈ Icc 1 (q - 1), ((a : ℝ)⁻¹ + ((q - a : ℕ) : ℝ)⁻¹)) =
      2 * (harmonic (q - 1) : ℝ) := by
  rw [Finset.sum_add_distrib, reciprocal_reflect_sum]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  ring

section FixedModulus

variable {q : ℕ} [NeZero q]

lemma sum_unit_values_le (hq : 2 ≤ q) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ u : (ZMod q)ˣ, f u.val.val) ≤ ∑ a ∈ Icc 1 (q - 1), f a := by
  classical
  letI : Fact (1 < q) := ⟨hq⟩
  have hinj : Function.Injective (fun u : (ZMod q)ˣ => u.val.val) :=
    fun u v h => Units.val_injective (ZMod.val_injective q h)
  calc
    _ = ∑ a ∈ univ.image (fun u : (ZMod q)ˣ => u.val.val), f a := by
      rw [Finset.sum_image]
      exact fun u _ v _ h => hinj h
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        have hpos : 0 < u.val.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero)
        have hlt := u.val.val_lt
        simp only [mem_Icc]
        omega
      · exact fun a _ _ => hf a

lemma sum_norm_intervalWaveSum_units_le (hq : 2 ≤ q) (M : ℤ) (L : ℕ) :
    (∑ u : (ZMod q)ˣ, ‖intervalWaveSum M L ((u.val.val : ℝ) / q)‖) ≤
      (q : ℝ) * (harmonic (q - 1) : ℝ) := by
  letI : Fact (1 < q) := ⟨hq⟩
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, (q : ℝ) / 2 *
        ((u.val.val : ℝ)⁻¹ + ((q - u.val.val : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro u hu
      exact norm_intervalWaveSum_rational_le
        (Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero)) u.val.val_lt M L
    _ = (q : ℝ) / 2 * ∑ u : (ZMod q)ˣ,
        ((u.val.val : ℝ)⁻¹ + ((q - u.val.val : ℕ) : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ (q : ℝ) / 2 * ∑ a ∈ Icc 1 (q - 1),
        ((a : ℝ)⁻¹ + ((q - a : ℕ) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_unit_values_le hq (fun a : ℕ => (a : ℝ)⁻¹ + ((q - a : ℕ) : ℝ)⁻¹) (fun a => by positivity)) (by positivity)
    _ = _ := by rw [reciprocal_pair_sum]; ring

noncomputable def intervalCharacterSum (χ : DirichletCharacter ℂ q) (M : ℤ) (L : ℕ) : ℂ :=
  ∑ n ∈ range L, χ ((M + n : ℤ) : ZMod q)

lemma primitive_intervalCharacterSum_gauss {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (M : ℤ) (L : ℕ) :
    intervalCharacterSum χ⁻¹ M L * gaussSum χ ZMod.stdAddChar =
      ∑ u : (ZMod q)ˣ, χ u * intervalWaveSum M L ((u.val.val : ℝ) / q) := by
  calc
    _ = ∑ n ∈ range L, gaussSum χ (ZMod.stdAddChar.mulShift ((M + n : ℤ) : ZMod q)) := by
      simp only [intervalCharacterSum, Finset.sum_mul, gaussSum_mulShift_of_isPrimitive _ hχ]
    _ = ∑ u : ZMod q, χ u *
        (∑ n ∈ range L, ZMod.stdAddChar (((M + n : ℤ) : ZMod q) * u)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ u : (ZMod q)ˣ, χ u *
        (∑ n ∈ range L, ZMod.stdAddChar (((M + n : ℤ) : ZMod q) * (u : ZMod q))) :=
      sum_eq_sum_units _ (fun u hu => by rw [χ.map_nonunit hu, zero_mul])
    _ = _ := by simp only [stdAddChar_int_mul, intervalWaveSum]

lemma primitive_gaussSum_norm {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [← primitive_gaussSum_norm_sq hχ, Real.sqrt_sq (norm_nonneg _)]

/-- Pólya–Vinogradov with a harmonic-number bound, uniformly over all
integer shifts and all natural interval lengths. -/
theorem polya_vinogradov_harmonic (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (M : ℤ) (L : ℕ) :
    ‖intervalCharacterSum χ M L‖ ≤ Real.sqrt q * (harmonic (q - 1) : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have h := congrArg norm (primitive_intervalCharacterSum_gauss (primitive_inv hχ) M L)
  simp only [inv_inv, norm_mul, primitive_gaussSum_norm (primitive_inv hχ)] at h
  have hb : ‖intervalCharacterSum χ M L‖ * Real.sqrt q ≤
      (q : ℝ) * (harmonic (q - 1) : ℝ) := by
    rw [h]
    calc
      _ ≤ ∑ u : (ZMod q)ˣ, ‖χ⁻¹ u * intervalWaveSum M L ((u.val.val : ℝ) / q)‖ :=
        norm_sum_le _ _
      _ = ∑ u : (ZMod q)ˣ, ‖intervalWaveSum M L ((u.val.val : ℝ) / q)‖ := by
        simp only [norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
      _ ≤ _ := sum_norm_intervalWaveSum_units_le hq M L
  apply (mul_le_mul_iff_left₀ hsqrt).mp
  calc
    _ ≤ (q : ℝ) * (harmonic (q - 1) : ℝ) := hb
    _ = (Real.sqrt q * (harmonic (q - 1) : ℝ)) * Real.sqrt q := by
      rw [mul_assoc, mul_comm (harmonic (q - 1) : ℝ), ← mul_assoc, ← pow_two, Real.sq_sqrt hqpos.le]

/-- A logarithmic form of Pólya–Vinogradov for primitive characters of
modulus at least two. -/
theorem polya_vinogradov (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (M : ℤ) (L : ℕ) :
    ‖intervalCharacterSum χ M L‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  apply (polya_vinogradov_harmonic hq hχ M L).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ 1 + Real.log (q - 1 : ℕ) := harmonic_le_one_add_log _
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply Real.log_le_log
      · exact_mod_cast (show 0 < q - 1 by omega)
      · exact_mod_cast Nat.sub_le q 1

end FixedModulus

end Erdos821.AnalyticSieve
