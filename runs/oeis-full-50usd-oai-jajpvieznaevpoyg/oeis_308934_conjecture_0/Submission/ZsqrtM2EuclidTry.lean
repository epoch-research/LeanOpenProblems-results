import FormalConjectures.Util.ProblemImports

open Zsqrtd Complex
local notation "ℤ√-2" => Zsqrtd (-2)

noncomputable def zsqrtM2toComplex (z : ℤ√-2) : ℂ := z.re + z.im * (Real.sqrt 2) * Complex.I

lemma zsqrtM2toComplex_re (z : ℤ√-2) : (zsqrtM2toComplex z).re = z.re := by
  simp [zsqrtM2toComplex]

lemma zsqrtM2toComplex_im (z : ℤ√-2) : (zsqrtM2toComplex z).im = z.im * Real.sqrt 2 := by
  simp [zsqrtM2toComplex, mul_assoc]

lemma zsqrtM2_norm_complex (z : ℤ√-2) : Complex.normSq (zsqrtM2toComplex z) = z.norm := by
  rw [Complex.normSq_apply, zsqrtM2toComplex_re, zsqrtM2toComplex_im]
  rw [Zsqrtd.norm]
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := by norm_num [sq]
  norm_num
  ring_nf
  rw [sq, hs]
  norm_num
  ring

#check Rat.round
#check abs_sub_round
#check Zsqrtd.ext
#check Zsqrtd.re_mul
#check Zsqrtd.im_mul
