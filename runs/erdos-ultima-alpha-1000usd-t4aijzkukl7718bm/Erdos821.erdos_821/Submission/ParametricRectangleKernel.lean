import Submission.SmallPrimeMeanRate

/-!
# Parametric two-cofactor scales approaching the four-sevenths level

For fixed k>=5 take L=2^((7k+7)m), Q=2^((8k+4)m), and
A=2^((14k+16)m). The input range 2^m<p<=2^(2m) then fits in A,
and Q has ambient exponent (8k+4)/(14k+16), tending to 4/7.
Only the congruence error kernel is treated here.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def parametricInterval (k m : ℕ) : ℕ := 2^((7*k+7)*m)
noncomputable def parametricModulus (k m : ℕ) : ℕ := 2^((8*k+4)*m)
noncomputable def parametricAmbient (k m : ℕ) : ℕ := 2^((14*k+16)*m)

lemma parametric_harmonic_bound (k m : ℕ) :
    1+(harmonic (parametricModulus k m) : ℝ) ≤ 8*((k : ℝ)+1)*((m : ℝ)+1) := by
  have hh := harmonic_two_pow_le ((8*k+4)*m)
  change 1+(harmonic (2^((8*k+4)*m)) : ℝ) ≤ _
  push_cast at hh
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) m]

lemma parametric_rectangle_kernel (k m : ℕ) (hk : 3 ≤ k) :
    rectangleMeanKernel (parametricModulus k m) (parametricInterval k m)
      (parametricInterval k m) ≤
      300*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m) := by
  let H : ℝ := harmonic (parametricModulus k m)
  have hH : 0 ≤ H := harmonic_natCast_nonneg _
  have hH1 := parametric_harmonic_bound k m
  change 1+H ≤ _ at hH1
  have hHb : H ≤ 8*((k : ℝ)+1)*((m : ℝ)+1) := by linarith
  have hK : modulusBound (parametricModulus k m) ≤ 2*(2 : ℝ)^((6*k+3)*m) := by
    simpa only [parametricModulus, show 4*((2*k+1)*m)=(8*k+4)*m by ring,
      show 3*((2*k+1)*m)=(6*k+3)*m by ring] using modulusBound_power_four ((2*k+1)*m)
  have hBQ : (parametricInterval k m : ℝ)+parametricModulus k m ≤ 2*(2 : ℝ)^((8*k+4)*m) := by
    have hb : (2 : ℝ)^((7*k+7)*m) ≤ (2 : ℝ)^((8*k+4)*m) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m (by omega))
    dsimp [parametricInterval,parametricModulus]
    push_cast
    linarith
  have hp : (2 : ℝ)^((6*k+3)*m)*(2 : ℝ)^((8*k+4)*m) = (2 : ℝ)^((14*k+7)*m) := by
    rw [← pow_add]
    congr 1
    ring
  have hsmall : (2 : ℝ)^((7*k+7)*m) ≤ (2 : ℝ)^((14*k+7)*m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m (by omega))
  have hm1 : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hk1 : 1 ≤ (k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmm : (m : ℝ)+1 ≤ ((m : ℝ)+1)^2 := by nlinarith
  have hkk : (k : ℝ)+1 ≤ ((k : ℝ)+1)^2 := by nlinarith
  have hfirst : modulusBound (parametricModulus k m)*
      ((parametricInterval k m : ℝ)+parametricModulus k m)*(1+H)^2 ≤
      256*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m) := by
    calc
      _ ≤ (2*(2 : ℝ)^((6*k+3)*m))*(2*(2 : ℝ)^((8*k+4)*m))*
          (8*((k : ℝ)+1)*((m : ℝ)+1))^2 := by gcongr
      _ = _ := by
        rw [show (2*(2 : ℝ)^((6*k+3)*m))*(2*(2 : ℝ)^((8*k+4)*m)) =
          4*((2 : ℝ)^((6*k+3)*m)*(2 : ℝ)^((8*k+4)*m)) by ring, hp]
        ring
  have hsecond : (parametricInterval k m : ℝ)*H ≤
      8*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m) := by
    calc
      _ ≤ (parametricInterval k m : ℝ)*(8*((k : ℝ)+1)*((m : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hHb (Nat.cast_nonneg _)
      _ ≤ (2 : ℝ)^((14*k+7)*m)*(8*((k : ℝ)+1)^2*((m : ℝ)+1)^2) := by
        dsimp [parametricInterval]
        push_cast
        gcongr
      _ = _ := by ring
  unfold rectangleMeanKernel
  change _+_ ≤ _
  nlinarith only [hfirst,hsecond,
    show 0 ≤ ((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m) by positivity]

lemma parametric_modulus_small_rpow (k m : ℕ) :
    (parametricModulus k m : ℝ)^(1/(8*(k : ℝ)+4)) = (2 : ℝ)^m := by
  simp only [parametricModulus,Nat.cast_pow,Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num)]
  have he : (((8*k+4)*m : ℕ) : ℝ)*(1/(8*(k : ℝ)+4)) = (m : ℝ) := by
    push_cast
    field_simp
  rw [he,Real.rpow_natCast]

lemma parametric_rectangle_kernel_rate (k m : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 ≤ B) :
    B*(parametricModulus k m : ℝ)^(1/(8*(k : ℝ)+4))*
      rectangleMeanKernel (parametricModulus k m) (parametricInterval k m)
        (parametricInterval k m) ≤
      (300*B*((k : ℝ)+1)^2*((m : ℝ)+1)^2/(2 : ℝ)^m)*(parametricInterval k m : ℝ)^2 := by
  rw [parametric_modulus_small_rpow]
  calc
    _ ≤ B*(2 : ℝ)^m*(300*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m)) :=
      mul_le_mul_of_nonneg_left (parametric_rectangle_kernel k m hk) (by positivity)
    _ = (300*B*((k : ℝ)+1)^2*((m : ℝ)+1)^2)*(2 : ℝ)^((14*k+8)*m) := by
      rw [show B*(2 : ℝ)^m*(300*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(2 : ℝ)^((14*k+7)*m)) =
        (300*B*((k : ℝ)+1)^2*((m : ℝ)+1)^2)*((2 : ℝ)^m*(2 : ℝ)^((14*k+7)*m)) by ring,
        ← pow_add]
      congr 2
      ring
    _ ≤ (300*B*((k : ℝ)+1)^2*((m : ℝ)+1)^2)*(2 : ℝ)^((14*k+13)*m) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m (show 14*k+8 ≤ 14*k+13 by omega)))
        (by positivity)
    _ = _ := by
      have he : (parametricInterval k m : ℝ)^2 = (2 : ℝ)^m*(2 : ℝ)^((14*k+13)*m) := by
        simp only [parametricInterval,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,← pow_add]
        congr 1
        ring
      rw [he]
      field_simp

lemma parametric_nonunit_rate (k m : ℕ) :
    (harmonic (parametricModulus k m) : ℝ)/(2 : ℝ)^m ≤
      8*((k : ℝ)+1)*((m : ℝ)+1)^2/(2 : ℝ)^m := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := parametric_harmonic_bound k m
  have hm : ((m : ℝ)+1) ≤ ((m : ℝ)+1)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hs := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8*((k : ℝ)+1) by positivity)
  linarith

lemma parametric_ambient_power_relation (k m : ℕ) :
    parametricModulus k m^(14*k+16) = parametricAmbient k m^(8*k+4) := by
  simp only [parametricModulus,parametricAmbient,← pow_mul]
  congr 1
  ring

lemma parametric_ambient_above_half (k m : ℕ) (hk : 5 ≤ k) (hm : 1 ≤ m) :
    parametricAmbient k m+1 < parametricModulus k m^2 := by
  have hA : 1 < parametricAmbient k m := by
    unfold parametricAmbient
    exact Nat.one_lt_pow (by positivity) (by decide)
  have hh : 2*parametricAmbient k m ≤ parametricModulus k m^2 := by
    unfold parametricAmbient parametricModulus
    rw [← pow_succ',← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have hm' := Nat.mul_le_mul_right m (show 14*k+17 ≤ (8*k+4)*2 by omega)
    nlinarith
  omega

lemma parametric_rectangle_product_bound (k m p a b : ℕ) (hp : p ≤ 2^(2*m))
    (ha : a ≤ parametricInterval k m) (hb : b ≤ parametricInterval k m) :
    a*b*p ≤ parametricAmbient k m := by
  apply (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hp).trans_eq
  simp only [parametricInterval,parametricAmbient,← pow_add]
  congr 1
  ring

lemma parametric_ambient_log_le (k m : ℕ) :
    1+Real.log (parametricAmbient k m : ℝ) ≤ (14*(k : ℝ)+17)*((m : ℝ)+1) := by
  simp only [parametricAmbient,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have ht : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq (by norm_num)
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ (((14*k+16)*m : ℕ) : ℝ) by positivity)
  push_cast at hh ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]

lemma parametric_level_lt_four_sevenths (k : ℕ) :
    (8*(k : ℝ)+4)/(14*(k : ℝ)+16) < 4/7 := by
  apply (div_lt_iff₀ (by positivity)).mpr
  linarith

lemma exists_parametric_level_above (θ : ℝ) (hθ : θ < 4/7) :
    ∃ k : ℕ, 5 ≤ k ∧ θ < (8*(k : ℝ)+4)/(14*(k : ℝ)+16) := by
  have hd : 0 < 8-14*θ := by linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (max 5 ((16*θ-4)/(8-14*θ)))
  have hk5 : (5 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hbound := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hk)
  refine ⟨k, by exact_mod_cast hk5.le, ?_⟩
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith

lemma parametric_modulus_eq_rpow (k m : ℕ) :
    (parametricModulus k m : ℝ) =
      (parametricAmbient k m : ℝ)^((8*(k : ℝ)+4)/(14*(k : ℝ)+16)) := by
  simp only [parametricModulus,parametricAmbient,Nat.cast_pow,Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num)]
  have he : (((14*k+16)*m : ℕ) : ℝ)*((8*(k : ℝ)+4)/(14*(k : ℝ)+16)) =
      (((8*k+4)*m : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he,Real.rpow_natCast]

lemma parametric_modulus_gt_rpow (k m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (hθ : θ < (8*(k : ℝ)+4)/(14*(k : ℝ)+16)) :
    (parametricAmbient k m : ℝ)^θ < parametricModulus k m := by
  have hA : (1 : ℝ) < parametricAmbient k m := by
    unfold parametricAmbient
    exact_mod_cast (Nat.one_lt_pow (by positivity : (14*k+16)*m ≠ 0) (by decide : 1 < 2))
  rw [parametric_modulus_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt hA hθ

end Erdos821.Kloosterman
