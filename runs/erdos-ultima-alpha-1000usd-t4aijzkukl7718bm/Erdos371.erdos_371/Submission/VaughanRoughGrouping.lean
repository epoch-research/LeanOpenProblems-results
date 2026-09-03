import Submission.VaughanSmoothAnnihilation

/-! The exact dependence of the long Vaughan coefficient on a rough
multiplicative factor. This is an identity, not an estimate of its signed mean. -/
namespace Erdos371
open Finset
set_option autoImplicit false

lemma truncated_convolution_mul_rough (U m r : ℕ) (f g : ArithmeticFunction ℝ)
    (hm : 0 < m) (hr0 : 0 < r)
    (hr : ∀ p, p.Prime → p ∣ r → U < p) :
    (arithmeticTruncate U f*g) (m*r) =
      ∑ d ∈ (Icc 1 U).filter (fun d => d ∣ m), f d*g ((m/d)*r) := by
  rw [truncated_convolution_apply U (m*r) f g (Nat.mul_pos hm hr0).ne']
  have he : (Icc 1 U).filter (fun d => d ∣ m*r) =
      (Icc 1 U).filter (fun d => d ∣ m) := by
    ext d
    simp only [mem_filter,mem_Icc]
    constructor
    · rintro ⟨hd,hdm⟩
      exact ⟨hd,small_divisor_of_mul_rough U m r d hd.1 hd.2 hr hdm⟩
    · rintro ⟨hd,hdm⟩
      exact ⟨hd,hdm.trans (dvd_mul_right m r)⟩
  rw [he]
  apply sum_congr rfl
  intro d hd
  have hd := (mem_filter.mp hd).2
  rw [mul_comm m r,Nat.mul_div_assoc r hd,mul_comm r]

lemma truncated_zeta_mul_rough (U m r : ℕ) (f : ArithmeticFunction ℝ)
    (hm : 0 < m) (hr0 : 0 < r)
    (hr : ∀ p, p.Prime → p ∣ r → U < p) :
    (arithmeticTruncate U f*ArithmeticFunction.zeta) (m*r) =
      (arithmeticTruncate U f*ArithmeticFunction.zeta) m := by
  rw [truncated_convolution_mul_rough U m r f ArithmeticFunction.zeta hm hr0 hr,
    truncated_convolution_apply U m f ArithmeticFunction.zeta hm.ne']
  apply sum_congr rfl
  intro d hd
  obtain ⟨hd,hdm⟩ := mem_filter.mp hd
  have hmd := Nat.div_pos (Nat.le_of_dvd hm hdm) (mem_Icc.mp hd).1
  simp [ArithmeticFunction.zeta_apply,hmd.ne',(Nat.mul_pos hmd hr0).ne']

lemma truncated_log_mul_rough (U m r : ℕ) (f : ArithmeticFunction ℝ)
    (hm : 0 < m) (hr0 : 0 < r)
    (hr : ∀ p, p.Prime → p ∣ r → U < p) :
    (arithmeticTruncate U f*ArithmeticFunction.log) (m*r) =
      (arithmeticTruncate U f*ArithmeticFunction.log) m +
        (arithmeticTruncate U f*ArithmeticFunction.zeta) m*Real.log r := by
  rw [truncated_convolution_mul_rough U m r f ArithmeticFunction.log hm hr0 hr,
    truncated_convolution_apply U m f ArithmeticFunction.log hm.ne',
    truncated_convolution_apply U m f ArithmeticFunction.zeta hm.ne',sum_mul,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hd,hdm⟩ := mem_filter.mp hd
  have hmd := Nat.div_pos (Nat.le_of_dvd hm hdm) (mem_Icc.mp hd).1
  have hmdr : ((m/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmd.ne'
  have hrr : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
  simp only [ArithmeticFunction.log_apply,Nat.cast_mul,Real.log_mul hmdr hrr]
  simp [ArithmeticFunction.zeta_apply,hmd.ne',mul_add]

lemma double_truncated_zeta_mul_rough (U V m r : ℕ) (f g : ArithmeticFunction ℝ)
    (hm : 0 < m) (hr0 : 0 < r)
    (hr : ∀ p, p.Prime → p ∣ r → max U V < p) :
    (arithmeticTruncate U f*arithmeticTruncate V g*ArithmeticFunction.zeta) (m*r) =
      (arithmeticTruncate U f*arithmeticTruncate V g*ArithmeticFunction.zeta) m := by
  have hrU : ∀ p, p.Prime → p ∣ r → U < p :=
    fun p hp hpr => (le_max_left U V).trans_lt (hr p hp hpr)
  have hrV : ∀ p, p.Prime → p ∣ r → V < p :=
    fun p hp hpr => (le_max_right U V).trans_lt (hr p hp hpr)
  rw [mul_assoc,truncated_convolution_mul_rough U m r f _ hm hr0 hrU,
    truncated_convolution_apply U m f _ hm.ne']
  apply sum_congr rfl
  intro d hd
  obtain ⟨hd,hdm⟩ := mem_filter.mp hd
  rw [truncated_zeta_mul_rough V (m/d) r g
    (Nat.div_pos (Nat.le_of_dvd hm hdm) (mem_Icc.mp hd).1) hr0 hrV]

/-- Outside the direct Mangoldt terms, adding a rough factor changes the
long coefficient by exactly one logarithmic multiple of a truncated divisor sum.
The factor m need not itself be smooth or small. -/
theorem vaughanLongFunction_mul_rough (U V m r : ℕ)
    (hm : 0 < m) (hr0 : 0 < r)
    (hr : ∀ p, p.Prime → p ∣ r → max U V < p) :
    vaughanLongFunction U V (m*r) = vaughanLongFunction U V m +
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) (m*r) -
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) m -
      (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        ArithmeticFunction.zeta) m*Real.log r := by
  have hmr := congrArg (fun f : ArithmeticFunction ℝ => f (m*r))
    (vonMangoldt_truncated_identity U V)
  have hm' := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (vonMangoldt_truncated_identity U V)
  change ArithmeticFunction.vonMangoldt (m*r) =
    arithmeticTruncate V ArithmeticFunction.vonMangoldt (m*r) +
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log) (m*r) -
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) (m*r) +
    vaughanLongFunction U V (m*r) at hmr
  change ArithmeticFunction.vonMangoldt m =
    arithmeticTruncate V ArithmeticFunction.vonMangoldt m +
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log) m -
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) m +
    vaughanLongFunction U V m at hm'
  rw [truncated_log_mul_rough U m r _ hm hr0
    (fun p hp hpr => (le_max_left U V).trans_lt (hr p hp hpr)),
    double_truncated_zeta_mul_rough U V m r _ _ hm hr0 hr] at hmr
  change vaughanLongFunction U V (m*r) = vaughanLongFunction U V m +
    (ArithmeticFunction.vonMangoldt (m*r)-arithmeticTruncate V ArithmeticFunction.vonMangoldt (m*r)) -
    (ArithmeticFunction.vonMangoldt m-arithmeticTruncate V ArithmeticFunction.vonMangoldt m) - _
  linarith

/-- Canonical smooth/rough grouping, with the smooth coefficient unrestricted
in size. No signed cancellation of its average is claimed. -/
theorem vaughanLongFunction_smooth_rough_formula (U V q : ℕ) (hq : 0 < q) :
    let m := smoothPrimePart (max U V) q
    let r := roughPrimePart (max U V) q
    vaughanLongFunction U V q = vaughanLongFunction U V m +
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) q -
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) m -
      (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        ArithmeticFunction.zeta) m*Real.log r := by
  dsimp only
  have he : smoothPrimePart (max U V) q*roughPrimePart (max U V) q = q := by
    rw [mul_comm,roughPrimePart_mul_smoothPrimePart _ _ hq.ne']
  have h := vaughanLongFunction_mul_rough U V
    (smoothPrimePart (max U V) q) (roughPrimePart (max U V) q)
    (smoothPrimePart_pos (max U V) q) (roughPrimePart_pos (max U V) q)
    (fun p hp hpr => roughPrimePart_prime_large (max U V) q p hp hpr)
  simpa only [he] using h

lemma vonMangoldt_mul_coprime_zero (m r : ℕ) (hm : 1 < m) (hr : 1 < r)
    (hcop : m.Coprime r) : ArithmeticFunction.vonMangoldt (m*r) = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  rcases (hcop.isPrimePow_dvd_mul hpow).mp (dvd_refl (m*r)) with h | h
  · have hle := Nat.le_of_dvd (show 0 < m by omega) h
    nlinarith
  · have hle := Nat.le_of_dvd (show 0 < r by omega) h
    nlinarith

/-- On a genuine coprime mixed product, only a coefficient depending on m
and a logarithmic multiple of the small-divisor sum remain. -/
theorem vaughanLongFunction_mixed_rough (U V m r : ℕ)
    (hm : 1 < m) (hr0 : 1 < r) (hcop : m.Coprime r)
    (hr : ∀ p, p.Prime → p ∣ r → max U V < p) :
    vaughanLongFunction U V (m*r) = vaughanLongFunction U V m -
      (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) m -
      (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        ArithmeticFunction.zeta) m*Real.log r := by
  rw [vaughanLongFunction_mul_rough U V m r (by omega) (by omega) hr]
  have hz : (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) (m*r) = 0 := by
    change ArithmeticFunction.vonMangoldt (m*r) -
      (if m*r≤V then ArithmeticFunction.vonMangoldt (m*r) else 0) = 0
    simp [vonMangoldt_mul_coprime_zero m r hm hr0 hcop]
  rw [hz,add_zero]

/-- After normalization, the mixed coefficient is a constant plus an inverse
logarithm in the rough factor. Its roughness restriction is still present. -/
theorem vaughanLongFunction_mixed_rough_normalized (U V m r : ℕ)
    (hm : 1 < m) (hr0 : 1 < r) (hcop : m.Coprime r)
    (hr : ∀ p, p.Prime → p ∣ r → max U V < p) :
    let A := (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      ArithmeticFunction.zeta) m
    vaughanLongFunction U V (m*r)/Real.log (m*r : ℕ) = -A +
      (vaughanLongFunction U V m -
        (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt) m +
        A*Real.log m)/Real.log (m*r : ℕ) := by
  dsimp only
  rw [vaughanLongFunction_mixed_rough U V m r hm hr0 hcop hr]
  have hlog : Real.log (m*r : ℕ) ≠ 0 := (Real.log_pos (by
    exact_mod_cast (show 1 < m*r by nlinarith))).ne'
  have hmr : Real.log (m*r : ℕ) = Real.log m+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (show m ≠ 0 by omega))
      (by exact_mod_cast (show r ≠ 0 by omega))]
  field_simp
  rw [hmr]
  ring

#print axioms vaughanLongFunction_mul_rough
#print axioms vaughanLongFunction_smooth_rough_formula
#print axioms vaughanLongFunction_mixed_rough_normalized
end Erdos371
