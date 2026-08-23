import FormalConjectures.PrimeSignScratch

open Finset
open scoped BigOperators

namespace GlobalSign

noncomputable def prodChar {m n : ℕ} (χ : DirichletCharacter ℂ m)
    (ψ : DirichletCharacter ℂ n) : DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (dvd_mul_right m n) χ *
    DirichletCharacter.changeLevel (dvd_mul_left n m) ψ

private lemma cast_fst_crt {m n : ℕ} (h : m.Coprime n) (x : ZMod (m*n)) :
    (ZMod.chineseRemainder h x).1 = ZMod.cast x := by
  simp [ZMod.chineseRemainder, Prod.fst_zmod_cast]

private lemma cast_snd_crt {m n : ℕ} (h : m.Coprime n) (x : ZMod (m*n)) :
    (ZMod.chineseRemainder h x).2 = ZMod.cast x := by
  simp [ZMod.chineseRemainder, Prod.snd_zmod_cast]

lemma prodChar_apply {m n : ℕ} (h : m.Coprime n) [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) (x : ZMod (m*n)) :
    prodChar χ ψ x = χ (ZMod.cast x) * ψ (ZMod.cast x) := by
  by_cases hx : IsUnit x
  · rw [prodChar, MulChar.mul_apply]
    conv_lhs =>
      enter [1]
      rw [← hx.unit_spec, χ.changeLevel_eq_cast_of_dvd]
    conv_lhs =>
      enter [2]
      rw [← hx.unit_spec, ψ.changeLevel_eq_cast_of_dvd]
    simp only [IsUnit.unit_spec]
  · rw [MulChar.map_nonunit _ hx]
    have hp : ¬(IsUnit (ZMod.cast x : ZMod m) ∧ IsUnit (ZMod.cast x : ZMod n)) := by
      intro hp
      have hu : IsUnit (ZMod.chineseRemainder h x) := by
        rw [Prod.isUnit_iff]
        simpa [cast_fst_crt h x, cast_snd_crt h x] using hp
      have huv : IsUnit ((ZMod.chineseRemainder h).symm (ZMod.chineseRemainder h x)) :=
        hu.map (ZMod.chineseRemainder h).symm
      exact hx (by simpa using huv)
    by_cases hm : IsUnit (ZMod.cast x : ZMod m)
    · have hn : ¬ IsUnit (ZMod.cast x : ZMod n) := fun hn ↦ hp ⟨hm, hn⟩
      rw [MulChar.map_nonunit ψ hn, mul_zero]
    · rw [MulChar.map_nonunit χ hm, zero_mul]

private def bezA (m n : ℕ) : ℤ := m.gcdA n
private def bezB (m n : ℕ) : ℤ := m.gcdB n

private lemma bezout_eq_one {m n : ℕ} (h : m.Coprime n) :
    (m : ℤ) * bezA m n + (n : ℤ) * bezB m n = 1 := by
  simpa [bezA, bezB, h.gcd_eq_one] using (Nat.gcd_eq_gcd_ab m n).symm

noncomputable def crtAddChar {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    AddChar (ZMod (m * n)) ℂ :=
  ((ZMod.stdAddChar.mulShift ((bezB m n : ℤ) : ZMod m)).compAddMonoidHom
      ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom).toAddMonoidHom) *
  ((ZMod.stdAddChar.mulShift ((bezA m n : ℤ) : ZMod n)).compAddMonoidHom
      ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom).toAddMonoidHom)

private lemma crtAddChar_apply_one {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n) : crtAddChar h (1 : ZMod (m*n)) =
      (ZMod.stdAddChar : AddChar (ZMod (m*n)) ℂ) 1 := by
  have hrhs : (ZMod.stdAddChar : AddChar (ZMod (m*n)) ℂ) 1 =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m*n : ℂ)) := by
    rw [show (1 : ZMod (m*n)) = ((1 : ℤ) : ZMod (m*n)) by norm_num,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hrhs]
  simp [crtAddChar, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  have hb := bezout_eq_one h
  have hmn1 : 1 < m * n := by nlinarith
  haveI : Fact (1 < m * n) := ⟨hmn1⟩
  norm_num
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  push_cast
  field_simp
  norm_num
  have hb' : bezB m n * (n : ℤ) + (m : ℤ) * bezA m n = 1 := by
    linear_combination hb
  exact_mod_cast hb'

private lemma crtAddChar_eq_std {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n) : crtAddChar h = ZMod.stdAddChar := by
  apply AddChar.ext _ _
  intro x
  rw [← ZMod.natCast_zmod_val x]
  have heq : (x.val : ZMod (m*n)) = x.val • (1 : ZMod (m*n)) := by simp
  rw [heq, AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow,
    crtAddChar_apply_one h hm1 hn1]


lemma gaussSum_prodChar {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) :
    gaussSum (prodChar χ ψ) ZMod.stdAddChar =
      gaussSum χ (ZMod.stdAddChar.mulShift ((bezB m n : ℤ) : ZMod m)) *
      gaussSum ψ (ZMod.stdAddChar.mulShift ((bezA m n : ℤ) : ZMod n)) := by
  rw [← crtAddChar_eq_std h hm1 hn1]
  simp only [gaussSum]
  rw [← (ZMod.chineseRemainder h).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [prodChar_apply h, crtAddChar, AddChar.mul_apply,
    AddChar.compAddMonoidHom_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply, Prod.fst, Prod.snd]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hmcast : ZMod.cast ((ZMod.chineseRemainder h).symm.toEquiv (a, b)) = a := by
    rw [← cast_fst_crt h]
    exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
  have hncast : ZMod.cast ((ZMod.chineseRemainder h).symm.toEquiv (a, b)) = b := by
    rw [← cast_snd_crt h]
    exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
  have hχ := congrArg χ hmcast
  have hψ := congrArg ψ hncast
  have hpa :
      ((RingHom.fst (ZMod m) (ZMod n)).comp
        (ZMod.chineseRemainder h).toRingHom).toAddMonoidHom
          ((ZMod.chineseRemainder h).symm.toEquiv (a, b)) = a := by
    exact congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
  have hpb :
      ((RingHom.snd (ZMod m) (ZMod n)).comp
        (ZMod.chineseRemainder h).toRingHom).toAddMonoidHom
          ((ZMod.chineseRemainder h).symm.toEquiv (a, b)) = b := by
    exact congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
  rw [hχ, hψ, hpa, hpb]
  ring

private lemma bezB_mul {m n : ℕ} (h : m.Coprime n) :
    (((bezB m n : ℤ) : ZMod m) * (n : ZMod m)) = 1 := by
  have hb := congrArg (fun z : ℤ ↦ (z : ZMod m)) (bezout_eq_one h)
  simpa [Int.cast_add, Int.cast_mul, Nat.cast_ofNat, mul_comm] using hb

private lemma bezA_mul {m n : ℕ} (h : m.Coprime n) :
    (((bezA m n : ℤ) : ZMod n) * (m : ZMod n)) = 1 := by
  have hb := congrArg (fun z : ℤ ↦ (z : ZMod n)) (bezout_eq_one h)
  simpa [Int.cast_add, Int.cast_mul, Nat.cast_ofNat, mul_comm] using hb

private lemma quadratic_eq_of_mul_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsQuadratic) {x y : ZMod N} (hxy : x * y = 1) : χ x = χ y := by
  have hc := congrArg χ hxy
  rw [map_mul, map_one] at hc
  rcases hχ x with hx | hx | hx <;>
    rcases hχ y with hy | hy | hy <;> simp_all

lemma gaussSum_prodChar_quadratic {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n)
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic) :
    gaussSum (prodChar χ ψ) ZMod.stdAddChar =
      χ (n : ZMod m) * ψ (m : ZMod n) *
        (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) := by
  rw [gaussSum_prodChar h hm1 hn1]
  rw [gaussSum_mulShift_of_isPrimitive _ hχp,
    gaussSum_mulShift_of_isPrimitive _ hψp]
  rw [hχq.inv, hψq.inv]
  have hχB := quadratic_eq_of_mul_eq_one χ hχq (bezB_mul h)
  have hψA := quadratic_eq_of_mul_eq_one ψ hψq (bezA_mul h)
  rw [hχB, hψA]
  ring

private lemma cpow_half_nat_eq_sqrt (k : ℕ) :
    (k : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt k : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  change (((k : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt (k : ℝ) : ℂ)
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)]
  rw [← Real.sqrt_eq_rpow]

private lemma sqrt_mul_nat (m n : ℕ) :
    (Real.sqrt (m*n) : ℂ) = (Real.sqrt m : ℂ) * (Real.sqrt n : ℂ) := by
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg m)]
  norm_num

lemma prodChar_even_even {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : χ.Even) (hψ : ψ.Even) : (prodChar χ ψ).Even := by
  change prodChar χ ψ (-1) = 1
  rw [prodChar_apply h]
  simpa [DirichletCharacter.Even] using congrArg₂ (· * ·) hχ hψ

lemma prodChar_even_odd {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : χ.Even) (hψ : ψ.Odd) : (prodChar χ ψ).Odd := by
  change prodChar χ ψ (-1) = -1
  rw [prodChar_apply h]
  rw [show χ (ZMod.cast (-1 : ZMod (m*n))) = 1 by simpa [DirichletCharacter.Even] using hχ,
    show ψ (ZMod.cast (-1 : ZMod (m*n))) = -1 by simpa [DirichletCharacter.Odd] using hψ]
  ring

lemma prodChar_odd_even {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : χ.Odd) (hψ : ψ.Even) : (prodChar χ ψ).Odd := by
  change prodChar χ ψ (-1) = -1
  rw [prodChar_apply h]
  rw [show χ (ZMod.cast (-1 : ZMod (m*n))) = -1 by simpa [DirichletCharacter.Odd] using hχ,
    show ψ (ZMod.cast (-1 : ZMod (m*n))) = 1 by simpa [DirichletCharacter.Even] using hψ]
  ring

lemma prodChar_odd_odd {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : χ.Odd) (hψ : ψ.Odd) : (prodChar χ ψ).Even := by
  change prodChar χ ψ (-1) = 1
  rw [prodChar_apply h]
  rw [show χ (ZMod.cast (-1 : ZMod (m*n))) = -1 by simpa [DirichletCharacter.Odd] using hχ,
    show ψ (ZMod.cast (-1 : ZMod (m*n))) = -1 by simpa [DirichletCharacter.Odd] using hψ]
  ring

private lemma gauss_eq_even_of_root_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (he : χ.Even) (hr : χ.rootNumber = 1) :
    gaussSum χ ZMod.stdAddChar = (Real.sqrt N : ℂ) := by
  rw [DirichletCharacter.rootNumber, if_pos he, pow_zero, div_one,
    cpow_half_nat_eq_sqrt] at hr
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N)).ne'
  field_simp at hr
  simpa using hr

private lemma gauss_eq_odd_of_root_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (ho : χ.Odd) (hr : χ.rootNumber = 1) :
    gaussSum χ ZMod.stdAddChar = (Real.sqrt N : ℂ) * Complex.I := by
  rw [DirichletCharacter.rootNumber, if_neg ho.not_even, pow_one,
    cpow_half_nat_eq_sqrt] at hr
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N)).ne'
  field_simp [Complex.I_ne_zero, hs] at hr
  simpa [mul_comm] using hr

lemma rootNumber_prod_even_even {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχe : χ.Even) (hψe : ψ.Even)
    (hχr : χ.rootNumber = 1) (hψr : ψ.rootNumber = 1)
    (hrec : χ (n : ZMod m) * ψ (m : ZMod n) = 1) :
    (prodChar χ ψ).rootNumber = 1 := by
  haveI : NeZero (m*n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [DirichletCharacter.rootNumber, if_pos (prodChar_even_even h hχe hψe), pow_zero,
    div_one, gaussSum_prodChar_quadratic h hm1 hn1 χ ψ hχp hψp hχq hψq,
    hrec, one_mul, gauss_eq_even_of_root_one hχe hχr,
    gauss_eq_even_of_root_one hψe hψr, cpow_half_nat_eq_sqrt]
  rw [show Real.sqrt ((m*n : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]]
  rw [Complex.ofReal_mul]
  apply div_self
  exact mul_ne_zero
    (by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos m)).ne')
    (by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos n)).ne')

lemma rootNumber_prod_even_odd {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχe : χ.Even) (hψo : ψ.Odd)
    (hχr : χ.rootNumber = 1) (hψr : ψ.rootNumber = 1)
    (hrec : χ (n : ZMod m) * ψ (m : ZMod n) = 1) :
    (prodChar χ ψ).rootNumber = 1 := by
  haveI : NeZero (m*n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [DirichletCharacter.rootNumber, if_neg (prodChar_even_odd h hχe hψo).not_even,
    pow_one, gaussSum_prodChar_quadratic h hm1 hn1 χ ψ hχp hψp hχq hψq,
    hrec, one_mul, gauss_eq_even_of_root_one hχe hχr,
    gauss_eq_odd_of_root_one hψo hψr, cpow_half_nat_eq_sqrt]
  rw [show Real.sqrt ((m*n : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)], Complex.ofReal_mul]
  have hm0 : (Real.sqrt m : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos m)).ne'
  have hn0 : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos n)).ne'
  field_simp [hm0, hn0, Complex.I_ne_zero]

lemma rootNumber_prod_odd_even {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχo : χ.Odd) (hψe : ψ.Even)
    (hχr : χ.rootNumber = 1) (hψr : ψ.rootNumber = 1)
    (hrec : χ (n : ZMod m) * ψ (m : ZMod n) = 1) :
    (prodChar χ ψ).rootNumber = 1 := by
  haveI : NeZero (m*n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [DirichletCharacter.rootNumber, if_neg (prodChar_odd_even h hχo hψe).not_even,
    pow_one, gaussSum_prodChar_quadratic h hm1 hn1 χ ψ hχp hψp hχq hψq,
    hrec, one_mul, gauss_eq_odd_of_root_one hχo hχr,
    gauss_eq_even_of_root_one hψe hψr, cpow_half_nat_eq_sqrt]
  rw [show Real.sqrt ((m*n : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)], Complex.ofReal_mul]
  have hm0 : (Real.sqrt m : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos m)).ne'
  have hn0 : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos n)).ne'
  field_simp [hm0, hn0, Complex.I_ne_zero]

lemma rootNumber_prod_odd_odd {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm1 : 1 < m) (hn1 : 1 < n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχo : χ.Odd) (hψo : ψ.Odd)
    (hχr : χ.rootNumber = 1) (hψr : ψ.rootNumber = 1)
    (hrec : χ (n : ZMod m) * ψ (m : ZMod n) = -1) :
    (prodChar χ ψ).rootNumber = 1 := by
  haveI : NeZero (m*n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [DirichletCharacter.rootNumber, if_pos (prodChar_odd_odd h hχo hψo), pow_zero,
    div_one, gaussSum_prodChar_quadratic h hm1 hn1 χ ψ hχp hψp hχq hψq,
    hrec, gauss_eq_odd_of_root_one hχo hχr,
    gauss_eq_odd_of_root_one hψo hψr, cpow_half_nat_eq_sqrt]
  rw [show Real.sqrt ((m*n : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)], Complex.ofReal_mul]
  field_simp
  rw [Complex.I_sq]
  ring_nf
  have hm0 : (Real.sqrt m : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos m)).ne'
  have hn0 : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos n)).ne'
  field_simp [hm0, hn0]





end GlobalSign
