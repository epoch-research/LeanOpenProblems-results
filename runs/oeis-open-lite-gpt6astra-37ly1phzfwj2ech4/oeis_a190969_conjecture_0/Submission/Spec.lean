import FormalConjectures.Util.ProblemImports

/--
A190969: The sequence defined by the linear recurrence relation
$$a(n) = 5 a(n-1) - 8 a(n-2)$$
with initial conditions $a(0)=0$ and $a(1)=1$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

section

namespace PSWork
open PowerSeries
open scoped PowerSeries

variable {K : Type*} [Field K] [CharZero K]

lemma order_zero_of_const_ne_zero {f : K⟦X⟧} (hf : constantCoeff f ≠ 0) : f.order = 0 := by
  apply order_eq_nat.mpr
  exact ⟨by simpa only [coeff_zero_eq_constantCoeff] using hf, by omega⟩

lemma order_derivative {f : K⟦X⟧} (hf : f ≠ 0) (h0 : constantCoeff f = 0) :
    (d⁄dX K f).order + 1 = f.order := by
  let n := f.order.toNat
  have hn : f.order = (n : ℕ∞) := (coe_toNat_order hf).symm
  have hn0 : n ≠ 0 := by
    have hh := coeff_order hf
    intro heq
    change coeff n f ≠ 0 at hh
    rw [heq, coeff_zero_eq_constantCoeff, h0] at hh
    exact hh rfl
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hD : (d⁄dX K f).order = (m : ℕ∞) := by
    apply order_eq_nat.mpr
    constructor
    · rw [coeff_derivative]
      apply mul_ne_zero
      · simpa only [show f.order.toNat = n from rfl, hm, Nat.succ_eq_add_one] using coeff_order hf
      · exact_mod_cast Nat.succ_ne_zero m
    · intro i hi
      rw [coeff_derivative]
      have hci : coeff (i + 1) f = 0 := by
        apply coeff_of_lt_order
        rw [hn, hm]
        exact_mod_cast (show i + 1 < m + 1 by omega)
      rw [hci, zero_mul]
  rw [hD, hn, hm]
  simp

lemma quartic_ode_unique {a c : K} (hc : c ≠ 0) {f g : K⟦X⟧}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf1 : coeff 1 f = c) (hg1 : coeff 1 g = c)
    (hf : (d⁄dX K f) ^ 2 * (1 - 2 * C a * X ^ 2 + X ^ 4) =
      C (c ^ 2) * (1 - 2 * C a * f ^ 2 + f ^ 4))
    (hg : (d⁄dX K g) ^ 2 * (1 - 2 * C a * X ^ 2 + X ^ 4) =
      C (c ^ 2) * (1 - 2 * C a * g ^ 2 + g ^ 4)) : f = g := by
  by_contra hfg
  have hfg0 : f - g ≠ 0 := sub_ne_zero.mpr hfg
  have h0 : constantCoeff (f - g) = 0 := by simp [hf0, hg0]
  have hd := order_derivative hfg0 h0
  have hsum : (d⁄dX K f + d⁄dX K g).order = 0 := by
    apply order_zero_of_const_ne_zero
    simp only [map_add, ← coeff_zero_eq_constantCoeff, coeff_derivative, zero_add,
      Nat.cast_one, Nat.cast_zero, zero_add, mul_one, hf1, hg1]
    simpa only [two_mul] using mul_ne_zero (two_ne_zero : (2 : K) ≠ 0) hc
  have hquartic : (1 - 2 * C a * X ^ 2 + X ^ 4 : K⟦X⟧).order = 0 := by
    apply order_zero_of_const_ne_zero
    simp
  have heq : d⁄dX K (f - g) * (d⁄dX K f + d⁄dX K g) *
      (1 - 2 * C a * X ^ 2 + X ^ 4) =
      (f - g) * (C (c ^ 2) * (f + g) * (-2 * C a + f ^ 2 + g ^ 2)) := by
    rw [map_sub]
    linear_combination hf - hg
  have ho := congrArg PowerSeries.order heq
  rw [order_mul, order_mul, hsum, hquartic, add_zero, add_zero, order_mul] at ho
  have hle : (f - g).order ≤ (d⁄dX K (f - g)).order := by
    rw [ho]
    exact le_self_add
  have hn := coe_toNat_order hfg0
  have hd0 : (d⁄dX K (f - g)).order ≠ ⊤ := by
    intro hh
    rw [hh, top_add] at hd
    exact (order_eq_top.not.mpr hfg0) hd.symm
  have hnD := ENat.coe_toNat_eq_self.mpr hd0
  rw [← hn, ← hnD] at hle hd
  norm_cast at hle hd
  omega

lemma constantCoeff_subst_self {h : K⟦X⟧} (hh : constantCoeff h = 0) (f : K⟦X⟧) :
    constantCoeff (subst h f) = constantCoeff f := by
  change MvPowerSeries.constantCoeff (subst h f) = constantCoeff f
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' hh)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro d hd
    have hh' : MvPowerSeries.constantCoeff h = 0 := hh
    simp [hh', hd]

noncomputable def sqrtQuartic (a : K) : K⟦X⟧ :=
  subst (-2 * C a * X ^ 2 + X ^ 4) (binomialSeries K (1 / 2 : ℚ))

lemma sqrtQuartic_const (a : K) : constantCoeff (sqrtQuartic a) = 1 := by
  unfold sqrtQuartic
  rw [constantCoeff_subst_self (by simp)]
  simp

lemma sqrtQuartic_sq (a : K) : (sqrtQuartic a) ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4 := by
  let h : K⟦X⟧ := -2 * C a * X ^ 2 + X ^ 4
  have hh : HasSubst h := HasSubst.of_constantCoeff_zero' (by simp [h])
  change (subst h (binomialSeries K (1 / 2 : ℚ))) ^ 2 = _
  rw [← subst_pow hh, pow_two, ← binomialSeries_add]
  norm_num only [show (1 / 2 + 1 / 2 : ℚ) = 1 by norm_num]
  rw [show (1 : ℚ) = (1 : ℕ) by norm_num, binomialSeries_nat]
  rw [pow_one, subst_add hh]
  have hone : subst h (1 : K⟦X⟧) = 1 := by
    rw [← coe_substAlgHom (R := K) hh]
    exact map_one _
  rw [hone, subst_X hh]
  dsimp [h]
  ring

end PSWork

end

section

namespace CompositionWork
open PowerSeries Finset
open scoped PowerSeries BigOperators
variable {R : Type*} [CommRing R]

lemma subst_C {f : R⟦X⟧} (hf : HasSubst f) (a : R) : subst f (C a) = C a := by
  simpa only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, coe_substAlgHom] using
    (substAlgHom (R := R) hf).commutes a

lemma coeff_pow_eq_zero {f : R⟦X⟧} (hf : constantCoeff f = 0) {n k : ℕ} (h : n < k) :
    coeff n (f ^ k) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero k hf)

lemma coeff_subst_sum {f : R⟦X⟧} (hf : constantCoeff f = 0) (g : R⟦X⟧)
    (n l : ℕ) (hn : n < l) :
    coeff n (subst f g) = ∑ k ∈ range l, coeff k g * coeff n (f ^ k) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hf)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra hkl
  have hle : l ≤ k := by simpa only [Finset.mem_coe, mem_range, not_lt] using hkl
  exact hk (by simp [coeff_pow_eq_zero hf (lt_of_lt_of_le hn hle)])

lemma coeff_subst_eq_coeff_sum {f : R⟦X⟧} (hf : constantCoeff f = 0) (g : R⟦X⟧)
    (n l : ℕ) (hn : n < l) :
    coeff n (subst f g) = coeff n (∑ k ∈ range l, C (coeff k g) * f ^ k) := by
  rw [coeff_subst_sum hf g n l hn, map_sum]
  simp only [coeff_C_mul]

lemma coeff_subst_mul {f : R⟦X⟧} (hf : constantCoeff f = 0) (g h : R⟦X⟧)
    (n l : ℕ) (hn : n < l) :
    coeff n (subst f g * h) = ∑ k ∈ range l, coeff k g * coeff n (f ^ k * h) := by
  have heq : coeff n (subst f g * h) =
      coeff n ((∑ k ∈ range l, C (coeff k g) * f ^ k) * h) := by
    rw [coeff_mul, coeff_mul]
    apply sum_congr rfl
    intro ij hij
    have hi : ij.1 < l := by have := Finset.mem_antidiagonal.mp hij; omega
    rw [coeff_subst_eq_coeff_sum hf g ij.1 l hi]
  rw [heq, sum_mul, map_sum]
  simp only [mul_assoc, coeff_C_mul]

lemma derivative_subst {f : R⟦X⟧} (hf : constantCoeff f = 0) (g : R⟦X⟧) :
    d⁄dX R (subst f g) = subst f (d⁄dX R g) * d⁄dX R f := by
  ext n
  rw [coeff_derivative, coeff_subst_sum hf g (n + 1) (n + 2) (by omega),
    coeff_subst_mul hf (d⁄dX R g) (d⁄dX R f) n (n + 1) (by omega), sum_mul]
  have hh : ∀ k, coeff k g * coeff (n + 1) (f ^ k) * (n + 1 : R) =
      coeff k g * coeff n (d⁄dX R (f ^ k)) := by
    intro k
    rw [coeff_derivative]
    ring
  simp_rw [hh]
  rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [Derivation.leibniz_pow, coeff_derivative]
  simp only [Nat.add_sub_cancel, smul_eq_mul]
  rw [map_nsmul, nsmul_eq_mul]
  push_cast
  ring

lemma coeff_pow_self {f : R⟦X⟧} (hf : constantCoeff f = 0) (n : ℕ) :
    coeff n (f ^ n) = coeff 1 f ^ n := by
  obtain ⟨g, hg⟩ := (X_dvd_iff.mpr hf)
  rw [hg, mul_pow, coeff_X_pow_mul' , if_pos (le_refl _), Nat.sub_self, coeff_zero_eq_constantCoeff]
  simp only [map_pow]
  congr 1
  have hc : coeff 1 (X * g) = coeff 0 g := by simpa using coeff_X_pow_mul g 1 0
  rw [hc, coeff_zero_eq_constantCoeff]

end CompositionWork

end

section

namespace AdditionWork

section Algebra
variable {R : Type*} [CommRing R]

lemma addition_numerator_identity (a u v U V : R)
    (hu : U ^ 2 = 1 - 2 * a * u ^ 2 + u ^ 4)
    (hv : V ^ 2 = 1 - 2 * a * v ^ 2 + v ^ 4) :
    (U * V * (1 + u ^ 2 * v ^ 2) + 2 * u * v * (u ^ 2 + v ^ 2 - a * (1 + u ^ 2 * v ^ 2))) ^ 2 =
      (1 - u ^ 2 * v ^ 2) ^ 4 - 2 * a * (u * V + v * U) ^ 2 * (1 - u ^ 2 * v ^ 2) ^ 2 +
      (u * V + v * U) ^ 4 := by
  linear_combination
    (-U^2*v^4-4*U*V*u*v^3+V^2*u^4*v^4-4*V^2*u^2*v^2+V^2+
      2*a*u^4*v^6-2*a*u^2*v^4+2*a*v^2-u^4*v^4-v^4) * hu +
    (-4*U*V*u^3*v-V^2*u^4+6*a*u^4*v^2+u^8*v^4-4*u^6*v^2-4*u^2*v^2+1) * hv

lemma addition_differential_identity (a u v U V : R)
    (hu : U ^ 2 = 1 - 2 * a * u ^ 2 + u ^ 4) :
    (U * V + v * (-2 * a * u + 2 * u ^ 3)) * (1 - u ^ 2 * v ^ 2) -
      (u * V + v * U) * (-2 * u * v ^ 2 * U) =
    U * V * (1 + u ^ 2 * v ^ 2) + 2 * u * v * (u ^ 2 + v ^ 2 - a * (1 + u ^ 2 * v ^ 2)) := by
  linear_combination 2 * u * v ^ 3 * hu

end Algebra

open PowerSeries
open scoped PowerSeries
variable {K : Type*} [Field K] [CharZero K]

structure EndPair (a : K) (y : K⟦X⟧) (c : K) where
  f : K⟦X⟧
  Y : K⟦X⟧
  f0 : constantCoeff f = 0
  Y0 : constantCoeff Y = 1
  curve : Y ^ 2 = 1 - 2 * C a * f ^ 2 + f ^ 4
  diff : d⁄dX K f * y = C c * Y

namespace EndPair

lemma diffY {a c : K} {y : K⟦X⟧} (e : EndPair a y c) :
    d⁄dX K e.Y * y = C c * (-2 * C a * e.f + 2 * e.f ^ 3) := by
  have h := congrArg (d⁄dX K) e.curve
  have hY : e.Y ≠ 0 := by intro hz; have := e.Y0; simp [hz] at this
  have h2 : (2 : K⟦X⟧) ≠ 0 := by
    intro hh
    have := congrArg (constantCoeff (R := K)) hh
    simp only [map_ofNat, map_zero] at this
    norm_num at this
  apply mul_left_cancel₀ (mul_ne_zero h2 hY)
  have hd := e.diff
  simp only [pow_two, map_add, map_sub, Derivation.leibniz, Derivation.map_one_eq_zero,
    smul_eq_mul, derivative_C] at h
  have hfour : d⁄dX K (e.f ^ 4) = 4 * e.f ^ 3 * d⁄dX K e.f := by
    rw [Derivation.leibniz_pow]
    simp [nsmul_eq_mul]
    ring
  rw [hfour] at h
  have h2C : d⁄dX K (2 : K⟦X⟧) = 0 := by
    simpa only [map_ofNat] using derivative_C (2 : K)
  rw [h2C] at h
  linear_combination y * h + (-4 * C a * e.f + 4 * e.f ^ 3) * hd

noncomputable def add {a c d : K} {y : K⟦X⟧} (e : EndPair a y c) (h : EndPair a y d) :
    EndPair a y (c + d) := by
  let u := e.f
  let v := h.f
  let U := e.Y
  let V := h.Y
  let D := 1 - u ^ 2 * v ^ 2
  let N := u * V + v * U
  let M := U * V * (1 + u ^ 2 * v ^ 2) + 2 * u * v * (u ^ 2 + v ^ 2 - C a * (1 + u ^ 2 * v ^ 2))
  have hD0 : constantCoeff D = 1 := by simp [D, u, v, e.f0, h.f0]
  have hD : D ≠ 0 := by intro hz; simp [hz] at hD0
  have hDD : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel D (by rw [hD0]; exact one_ne_zero)
  let F := N * D⁻¹
  let YY := M * (D⁻¹)^2
  have hF : F * D = N := by simp only [F, mul_assoc, hDD, mul_one]
  have hY : YY * D ^ 2 = M := by
    change (M * (D⁻¹)^2) * D^2 = M
    rw [mul_assoc, ← mul_pow, hDD, one_pow, mul_one]
  have hcurve := addition_numerator_identity (C a) u v U V e.curve h.curve
  refine ⟨F, YY, ?_, ?_, ?_, ?_⟩
  · simp [F, N, u, v, e.f0, h.f0]
  · simp [YY, M, D, u, v, U, V, e.f0, h.f0, e.Y0, h.Y0]
  · apply mul_right_cancel₀ (pow_ne_zero 4 hD)
    calc
      YY ^ 2 * D ^ 4 = (YY * D ^ 2) ^ 2 := by ring
      _ = M ^ 2 := by rw [hY]
      _ = D ^ 4 - 2 * C a * N ^ 2 * D ^ 2 + N ^ 4 := hcurve
      _ = (1 - 2 * C a * F ^ 2 + F ^ 4) * D ^ 4 := by rw [← hF]; ring
  · have heY := e.diffY
    have hhY := h.diffY
    have he := e.diff
    have hh := h.diff
    have hDdiff : d⁄dX K D * y =
        C c * (-2 * u * v ^ 2 * U) + C d * (-2 * v * u ^ 2 * V) := by
      dsimp [D]
      simp only [map_sub, Derivation.map_one_eq_zero, pow_two, Derivation.leibniz, smul_eq_mul]
      dsimp [u, v, U, V] at *
      linear_combination (-2 * e.f * h.f ^ 2) * he + (-2 * h.f * e.f ^ 2) * hh
    have hNdiff : d⁄dX K N * y =
        C c * (U * V + v * (-2 * C a * u + 2 * u ^ 3)) +
        C d * (V * U + u * (-2 * C a * v + 2 * v ^ 3)) := by
      dsimp [N]
      simp only [map_add, Derivation.leibniz, smul_eq_mul]
      dsimp [u, v, U, V] at *
      linear_combination h.Y * he + e.f * hhY + e.Y * hh + h.f * heY
    have hid1 := addition_differential_identity (C a) u v U V e.curve
    have hid2 := addition_differential_identity (C a) v u V U h.curve
    have hnd : d⁄dX K N * y * D - N * (d⁄dX K D * y) = C (c + d) * M := by
      rw [hNdiff, hDdiff, map_add]
      dsimp [D, N, M]
      linear_combination C c * hid1 + C d * hid2
    have hfd := congrArg (d⁄dX K) hF
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hfd
    apply mul_right_cancel₀ (pow_ne_zero 2 hD)
    calc
      (d⁄dX K F * y) * D ^ 2 =
          d⁄dX K N * y * D - N * (d⁄dX K D * y) := by
        rw [← hfd, ← hF]
        ring
      _ = C (c + d) * M := hnd
      _ = (C (c + d) * YY) * D ^ 2 := by rw [← hY]; ring

end EndPair
end AdditionWork

end

section

namespace CMWork

section CMAlgebra
variable {R : Type*} [CommRing R]

lemma quartic_isogeny_identity (a w x : R)
    (h₁ : a * w ^ 2 = a + 3) (h₂ : w ^ 4 = 8 * (a + 1)) :
    (1 + x ^ 2) ^ 4 - 2 * a * (w * x) ^ 2 * (1 + x ^ 2) ^ 2 + (w * x) ^ 4 =
      (1 - x ^ 2) ^ 2 * (1 - 2 * a * x ^ 2 + x ^ 4) := by
  linear_combination -2 * x ^ 2 * (1 + x ^ 2) ^ 2 * h₁ + x ^ 4 * h₂

lemma cm_parameters (a w : R) (hw : w ^ 2 - w + 2 = 0)
    (ha : 8 * a = -3 * (w + 2)) :
    8 * (a * w ^ 2 - a - 3) = 0 ∧ w ^ 4 - 8 * (a + 1) = 0 := by
  constructor
  · linear_combination (w ^ 2 - 1) * ha - 3 * (w + 3) * hw
  · linear_combination (w ^ 2 + w - 1) * hw - ha

end CMAlgebra

section CMField
variable {K : Type*} [Field K] [CharZero K]

lemma cm_quartic_isogeny (w x : K) (hw : w ^ 2 - w + 2 = 0)
    (hx : 1 + x ^ 2 ≠ 0) :
    1 - 2 * (-3 * (w + 2) / 8) * (w * x / (1 + x ^ 2)) ^ 2 +
        (w * x / (1 + x ^ 2)) ^ 4 =
      ((1 - x ^ 2) / (1 + x ^ 2) ^ 2) ^ 2 *
        (1 - 2 * (-3 * (w + 2) / 8) * x ^ 2 + x ^ 4) := by
  have ha : 8 * (-3 * (w + 2) / 8) = -3 * (w + 2) := by ring
  obtain ⟨h₁, h₂⟩ := cm_parameters (-3 * (w + 2) / 8) w hw ha
  have h₁' : (-3 * (w + 2) / 8) * w ^ 2 = -3 * (w + 2) / 8 + 3 := by
    have h8 : (8 : K) ≠ 0 := by norm_num
    have hh := (mul_eq_zero.mp h₁).resolve_left h8
    linear_combination hh
  have h₂' : w ^ 4 = 8 * (-3 * (w + 2) / 8 + 1) := sub_eq_zero.mp h₂
  have h := quartic_isogeny_identity (-3 * (w + 2) / 8) w x h₁' h₂'
  field_simp
  linear_combination 8 * h

end CMField
end CMWork

end

section

namespace EndomorphismWork
open PowerSeries AdditionWork
open scoped PowerSeries
variable {K : Type*} [Field K] [CharZero K]

lemma sq_unique {f g : K⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (hsq : f ^ 2 = g ^ 2) : f = g := by
  have hprod : (f - g) * (f + g) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hprod with hh | hh
  · exact sub_eq_zero.mp hh
  · have hh' := congrArg (constantCoeff (R := K)) hh
    simp only [map_add, map_zero, hf, hg] at hh'
    norm_num at hh'

namespace EndPair

def cast {a c d : K} {y : K⟦X⟧} (hc : c = d) (e : EndPair a y c) : EndPair a y d := hc ▸ e

@[simp] lemma cast_f {a c d : K} {y : K⟦X⟧} (hc : c = d) (e : EndPair a y c) :
    (cast hc e).f = e.f := by subst d; rfl

noncomputable def zero (a : K) (y : K⟦X⟧) : EndPair a y 0 where
  f := 0
  Y := 1
  f0 := by simp
  Y0 := by simp
  curve := by simp
  diff := by simp

noncomputable def neg {a c : K} {y : K⟦X⟧} (e : EndPair a y c) : EndPair a y (-c) where
  f := -e.f
  Y := e.Y
  f0 := by simp [e.f0]
  Y0 := e.Y0
  curve := by simpa only [neg_sq, show (-e.f)^4 = e.f^4 by ring] using e.curve
  diff := by simpa only [map_neg, neg_mul] using congrArg Neg.neg e.diff

noncomputable def ident (a : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4) : EndPair a y 1 where
  f := X
  Y := y
  f0 := by simp
  Y0 := hy0
  curve := hy
  diff := by simp

lemma coeff_one {a c : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1) (e : EndPair a y c) :
    coeff 1 e.f = c := by
  have hh := congrArg (constantCoeff (R := K)) e.diff
  simp only [map_mul, hy0, e.Y0, constantCoeff_C, mul_one] at hh
  simpa only [← coeff_zero_eq_constantCoeff, coeff_derivative, zero_add, Nat.cast_one, Nat.cast_zero, mul_one, zero_add] using hh

lemma ode {a c : K} {y : K⟦X⟧} (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4)
    (e : EndPair a y c) :
    (d⁄dX K e.f) ^ 2 * (1 - 2 * C a * X ^ 2 + X ^ 4) =
      C (c ^ 2) * (1 - 2 * C a * e.f ^ 2 + e.f ^ 4) := by
  rw [← hy, ← mul_pow, e.diff, mul_pow, ← map_pow, e.curve]

lemma unique_f {a c : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4) (e h : EndPair a y c) : e.f = h.f := by
  by_cases hc : c = 0
  · have hyne : y ≠ 0 := by intro hh; simp [hh] at hy0
    have heD : d⁄dX K e.f = 0 := by
      have hh := e.diff
      simp only [hc, map_zero, zero_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_right hyne
    have hhD : d⁄dX K h.f = 0 := by
      have hh := h.diff
      simp only [hc, map_zero, zero_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_right hyne
    exact PowerSeries.derivative.ext (heD.trans hhD.symm) (e.f0.trans h.f0.symm)
  · exact PSWork.quartic_ode_unique hc e.f0 h.f0 (coeff_one hy0 e) (coeff_one hy0 h)
      (ode hy e) (ode hy h)

lemma Y_eq_subst {a c : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4) (e : EndPair a y c) :
    e.Y = subst e.f y := by
  have hsubst : HasSubst e.f := HasSubst.of_constantCoeff_zero' e.f0
  apply sq_unique e.Y0
  · rw [PSWork.constantCoeff_subst_self e.f0, hy0]
  · have hh := congrArg (substAlgHom (R := K) hsubst) hy
    simp only [map_pow, map_add, map_sub, map_mul, map_one, map_ofNat,
      coe_substAlgHom, CompositionWork.subst_C hsubst, subst_X hsubst, Algebra.algebraMap_self_apply] at hh
    rw [e.curve, hh]

noncomputable def comp {a c d : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4) (e : EndPair a y c) (h : EndPair a y d) :
    EndPair a y (c * d) := by
  have hsubst : HasSubst h.f := HasSubst.of_constantCoeff_zero' h.f0
  refine ⟨subst h.f e.f, subst h.f e.Y, ?_, ?_, ?_, ?_⟩
  · rw [PSWork.constantCoeff_subst_self h.f0, e.f0]
  · rw [PSWork.constantCoeff_subst_self h.f0, e.Y0]
  · have hh := congrArg (substAlgHom (R := K) hsubst) e.curve
    simpa only [map_pow, map_add, map_sub, map_mul, map_one, map_ofNat,
      coe_substAlgHom, CompositionWork.subst_C hsubst, Algebra.algebraMap_self_apply] using hh
  · rw [CompositionWork.derivative_subst h.f0, mul_assoc, h.diff,
      Y_eq_subst hy0 hy h]
    have hh := congrArg (substAlgHom (R := K) hsubst) e.diff
    simp only [map_mul, coe_substAlgHom, CompositionWork.subst_C hsubst, Algebra.algebraMap_self_apply] at hh
    rw [mul_left_comm, hh, map_mul]
    ring

lemma commute {a c d : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4) (e : EndPair a y c) (h : EndPair a y d) :
    subst h.f e.f = subst e.f h.f := by
  let he := comp hy0 hy e h
  let hh := comp hy0 hy h e
  let hh' : EndPair a y (c*d) := cast (mul_comm d c) hh
  exact (unique_f hy0 hy he hh').trans (cast_f (mul_comm d c) hh)

noncomputable def cm (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4)
    (hw1 : a * w ^ 2 = a + 3) (hw2 : w ^ 4 = 8 * (a + 1)) : EndPair a y w := by
  let D : K⟦X⟧ := 1 + X^2
  let N : K⟦X⟧ := C w * X
  let M : K⟦X⟧ := (1-X^2)*y
  let F := N * D⁻¹
  let YY := M * (D⁻¹)^2
  have hD0 : constantCoeff D = 1 := by simp [D]
  have hD : D ≠ 0 := by intro hz; simp [hz] at hD0
  have hDD : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel D (by rw [hD0]; exact one_ne_zero)
  have hF : F * D = N := by simp only [F, mul_assoc, hDD, mul_one]
  have hY : YY * D ^ 2 = M := by
    change (M * (D⁻¹)^2) * D^2 = M
    rw [mul_assoc, ← mul_pow, hDD, one_pow, mul_one]
  refine ⟨F, YY, ?_, ?_, ?_, ?_⟩
  · simp [F, N]
  · simp [YY, M, D, hy0]
  · have h1 : C a * (C w)^2 = C a + 3 := by
      simpa only [map_add, map_ofNat, map_mul, map_pow] using congrArg C hw1
    have h2 : (C w)^4 = 8 * (C a + 1) := by
      simpa only [map_add, map_one, map_ofNat, map_mul, map_pow] using congrArg C hw2
    have hcurve := CMWork.quartic_isogeny_identity (C a) (C w) X h1 h2
    apply mul_right_cancel₀ (pow_ne_zero 4 hD)
    calc
      YY ^ 2 * D ^ 4 = (YY * D ^ 2) ^ 2 := by ring
      _ = M ^ 2 := by rw [hY]
      _ = D ^ 4 - 2 * C a * N ^ 2 * D ^ 2 + N ^ 4 := by
        change ((1-X^2)*y)^2 = _
        rw [mul_pow, hy]
        exact hcurve.symm
      _ = (1 - 2 * C a * F ^ 2 + F ^ 4) * D ^ 4 := by rw [← hF]; ring
  · have hfd := congrArg (d⁄dX K) hF
    have hDdiff : d⁄dX K D = 2 * X := by
      simp [D, pow_two, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero]
      ring
    have hNdiff : d⁄dX K N = C w := by simp [N, Derivation.leibniz, smul_eq_mul]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDdiff, hNdiff] at hfd
    apply mul_right_cancel₀ (pow_ne_zero 2 hD)
    calc
      (d⁄dX K F * y) * D^2 = (C w * D - N * (2*X)) * y := by
        rw [← hF]
        linear_combination D * y * hfd
      _ = C w * M := by dsimp [D, N, M]; ring
      _ = (C w * YY) * D^2 := by rw [← hY]; ring

end EndPair
end EndomorphismWork

end

section

namespace RationalWork
open PowerSeries AdditionWork
open scoped PowerSeries
variable {K : Type*} [Field K]

noncomputable def rational : Subring K⟦X⟧ where
  carrier := {f | ∃ N D : Polynomial K, D.eval 0 ≠ 0 ∧ f * (D : K⟦X⟧) = N}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨N, D, hD, he⟩ ⟨M, E, hE, hh⟩
    refine ⟨N*E+M*D, D*E, by simpa using mul_ne_zero hD hE, ?_⟩
    simp only [Polynomial.coe_mul, Polynomial.coe_add]
    linear_combination (E : K⟦X⟧)*he+(D : K⟦X⟧)*hh
  mul_mem' := by
    rintro f g ⟨N, D, hD, he⟩ ⟨M, E, hE, hh⟩
    refine ⟨N*M, D*E, by simpa using mul_ne_zero hD hE, ?_⟩
    simp only [Polynomial.coe_mul]
    rw [← he, ← hh]
    ring
  neg_mem' := by
    rintro f ⟨N, D, hD, he⟩
    refine ⟨-N, D, hD, ?_⟩
    simpa only [Polynomial.coe_neg, neg_mul] using congrArg Neg.neg he

lemma polynomial_mem (P : Polynomial K) : (P : K⟦X⟧) ∈ rational (K := K) :=
  ⟨P, 1, by simp, by simp⟩

lemma C_mem (a : K) : C a ∈ rational (K := K) := by
  simpa using polynomial_mem (Polynomial.C a)

lemma X_mem : (X : K⟦X⟧) ∈ rational (K := K) := by
  simpa using polynomial_mem (Polynomial.X : Polynomial K)

lemma inv_mem {f : K⟦X⟧} (hf : f ∈ rational (K := K)) (h0 : constantCoeff f ≠ 0) :
    f⁻¹ ∈ rational (K := K) := by
  obtain ⟨N, D, hD, he⟩ := hf
  have hN : N.eval 0 ≠ 0 := by
    have hh := congrArg (constantCoeff (R := K)) he
    simp only [map_mul, Polynomial.constantCoeff_coe] at hh
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hD ⊢
    rw [← hh]
    exact mul_ne_zero (by simpa only [coeff_zero_eq_constantCoeff] using h0) hD
  refine ⟨D, N, hN, ?_⟩
  rw [← he, ← mul_assoc, PowerSeries.inv_mul_cancel f h0, one_mul]

section Grading
variable {R : Type*} [CommRing R]

/-- The two parity pieces of the quadratic algebra generated by `y`. -/
def Grade (S : Subring R) (y : R) (b : Bool) (f : R) : Prop :=
  if b then ∃ u ∈ S, f = y*u else f ∈ S

lemma grade_false {S : Subring R} {y f : R} (hf : f ∈ S) : Grade S y false f := hf
lemma grade_y (S : Subring R) (y : R) : Grade S y true y := ⟨1, S.one_mem, by simp⟩
lemma grade_zero (S : Subring R) (y : R) (b : Bool) : Grade S y b 0 := by
  cases b
  · exact S.zero_mem
  · exact ⟨0, S.zero_mem, by simp⟩

lemma grade_add {S : Subring R} {y f g : R} {b : Bool}
    (hf : Grade S y b f) (hg : Grade S y b g) : Grade S y b (f+g) := by
  cases b
  · exact S.add_mem hf hg
  · obtain ⟨u, hu, rfl⟩ := hf
    obtain ⟨v, hv, rfl⟩ := hg
    exact ⟨u+v, S.add_mem hu hv, by ring⟩

lemma grade_neg {S : Subring R} {y f : R} {b : Bool}
    (hf : Grade S y b f) : Grade S y b (-f) := by
  cases b
  · exact S.neg_mem hf
  · obtain ⟨u, hu, rfl⟩ := hf
    exact ⟨-u, S.neg_mem hu, by ring⟩

lemma grade_mul {S : Subring R} {y f g : R} {b c : Bool} (hy : y^2 ∈ S)
    (hf : Grade S y b f) (hg : Grade S y c g) : Grade S y (b ^^ c) (f*g) := by
  cases b <;> cases c
  · exact S.mul_mem hf hg
  · obtain ⟨v, hv, rfl⟩ := hg
    exact ⟨f*v, S.mul_mem hf hv, by ring⟩
  · obtain ⟨u, hu, rfl⟩ := hf
    exact ⟨u*g, S.mul_mem hu hg, by ring⟩
  · obtain ⟨u, hu, rfl⟩ := hf
    obtain ⟨v, hv, rfl⟩ := hg
    have heq : y*u*(y*v) = y^2*u*v := by ring
    change y*u*(y*v) ∈ S
    rw [heq]
    exact S.mul_mem (S.mul_mem hy hu) hv

lemma grade_sq {S : Subring R} {y f : R} {b : Bool} (hy : y^2 ∈ S)
    (hf : Grade S y b f) : f^2 ∈ S := by
  have hh := grade_mul hy hf hf
  simpa only [Bool.xor_self, Grade, Bool.false_eq_true, ↓reduceIte, ← pow_two] using hh

end Grading

variable [CharZero K]

/-- Parity is recorded on the ordinate; the abscissa has the opposite parity. -/
def Rep {a c : K} {y : K⟦X⟧} (e : EndPair a y c) (b : Bool) : Prop :=
  Grade rational y (!b) e.f ∧ Grade rational y b e.Y

lemma add_rep {a c d : K} {y : K⟦X⟧} (hy : y^2 ∈ rational (K := K))
    {e : EndPair a y c} {h : EndPair a y d} {b v : Bool}
    (he : Rep e b) (hh : Rep h v) : Rep (e.add h) (b ^^ v) := by
  have h2 : (2 : K⟦X⟧) ∈ rational (K := K) := by simpa only [map_ofNat] using C_mem (2 : K)
  have hU := grade_sq hy he.1
  have hV := grade_sq hy hh.1
  have hUV := (rational (K := K)).mul_mem hU hV
  have hden := (rational (K := K)).sub_mem (rational (K := K)).one_mem hUV
  have hden0 : constantCoeff (1-e.f^2*h.f^2) ≠ 0 := by simp [e.f0, h.f0]
  have hinv := inv_mem hden hden0
  have hinv2 := (rational (K := K)).pow_mem hinv 2
  have ht1 : Grade rational y (!(b ^^ v)) (e.f*h.Y) := by
    have ht := grade_mul hy he.1 hh.2
    cases b <;> cases v <;> exact ht
  have ht2 : Grade rational y (!(b ^^ v)) (h.f*e.Y) := by
    have ht := grade_mul hy hh.1 he.2
    cases b <;> cases v <;> exact ht
  have hnum := grade_add ht1 ht2
  have hf := grade_mul hy hnum (grade_false (y := y) hinv)
  have hYs := grade_mul hy he.2 hh.2
  have hFs : Grade rational y (b ^^ v) (e.f*h.f) := by
    have ht := grade_mul hy he.1 hh.1
    cases b <;> cases v <;> exact ht
  have hA := (rational (K := K)).add_mem (rational (K := K)).one_mem hUV
  have hB := (rational (K := K)).sub_mem ((rational (K := K)).add_mem hU hV)
    ((rational (K := K)).mul_mem (C_mem a) hA)
  have hterm1 := grade_mul hy hYs (grade_false (y := y) hA)
  have hterm2 := grade_mul hy (grade_false (y := y) h2) hFs
  have hterm2' := grade_mul hy hterm2 (grade_false (y := y) hB)
  simp only [Bool.xor_false, Bool.false_xor] at hf hterm1 hterm2'
  have hnumY := grade_add hterm1 hterm2'
  have hYY := grade_mul hy hnumY (grade_false (y := y) hinv2)
  simp only [Bool.xor_false] at hYY
  constructor
  · exact hf
  · change Grade rational y (b ^^ v) _
    convert hYY using 1 <;> simp only [EndPair.add] <;> ring

open EndomorphismWork

lemma rep_cast {a c d : K} {y : K⟦X⟧} (hc : c=d) {e : EndPair a y c} {b : Bool}
    (he : Rep e b) : Rep (EndomorphismWork.EndPair.cast hc e) b := by subst d; exact he

lemma rep_zero (a : K) (y : K⟦X⟧) : Rep (EndomorphismWork.EndPair.zero a y) false :=
  ⟨grade_zero _ _ true, (rational (K := K)).one_mem⟩

lemma rep_neg {a c : K} {y : K⟦X⟧} {e : EndPair a y c} {b : Bool} (he : Rep e b) :
    Rep (EndomorphismWork.EndPair.neg e) b := ⟨grade_neg he.1, he.2⟩

lemma rep_ident (a : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4) :
    Rep (EndomorphismWork.EndPair.ident a y hy0 hy) true := ⟨X_mem, grade_y _ _⟩

lemma rep_cm (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4)
    (hw1 : a*w^2 = a+3) (hw2 : w^4 = 8*(a+1)) :
    Rep (EndomorphismWork.EndPair.cm a w y hy0 hy hw1 hw2) true := by
  have hden : (1+X^2 : K⟦X⟧) ∈ rational :=
    (rational (K := K)).add_mem (rational (K := K)).one_mem ((rational (K := K)).pow_mem X_mem 2)
  have hi := inv_mem hden (by simp)
  constructor
  · exact (rational (K := K)).mul_mem ((rational (K := K)).mul_mem (C_mem w) X_mem) hi
  · refine ⟨(1-X^2)*((1+X^2 : K⟦X⟧)⁻¹)^2, ?_, ?_⟩
    · exact (rational (K := K)).mul_mem
        ((rational (K := K)).sub_mem (rational (K := K)).one_mem ((rational (K := K)).pow_mem X_mem 2))
        ((rational (K := K)).pow_mem hi 2)
    · change ((1-X^2)*y)*((1+X^2 : K⟦X⟧)⁻¹)^2 = _
      ring

lemma exists_nat_mul {a c : K} {y : K⟦X⟧} (hy : y^2 ∈ rational (K := K))
    {e : EndPair a y c} {b : Bool} (he : Rep e b) (n : ℕ) :
    ∃ (b' : Bool) (h : EndPair a y ((n:K)*c)), Rep h b' := by
  induction n with
  | zero =>
    refine ⟨false, EndomorphismWork.EndPair.cast (by simp) (EndomorphismWork.EndPair.zero a y), ?_⟩
    exact rep_cast _ (rep_zero a y)
  | succ n ih =>
    obtain ⟨b', h, hh⟩ := ih
    refine ⟨b' ^^ b, EndomorphismWork.EndPair.cast (by push_cast; ring) (h.add e), ?_⟩
    exact rep_cast _ (add_rep hy hh he)

lemma exists_int_mul {a c : K} {y : K⟦X⟧} (hy : y^2 ∈ rational (K := K))
    {e : EndPair a y c} {b : Bool} (he : Rep e b) (z : ℤ) :
    ∃ (b' : Bool) (h : EndPair a y ((z:K)*c)), Rep h b' := by
  cases z with
  | ofNat n =>
    obtain ⟨b', h, hh⟩ := exists_nat_mul hy he n
    refine ⟨b', EndomorphismWork.EndPair.cast (by simp) h, ?_⟩
    exact rep_cast _ hh
  | negSucc n =>
    obtain ⟨b', h, hh⟩ := exists_nat_mul hy he (n+1)
    refine ⟨b', EndomorphismWork.EndPair.cast (by push_cast; ring) (EndomorphismWork.EndPair.neg h), ?_⟩
    exact rep_cast _ (rep_neg hh)

lemma exists_odd_even_map (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4)
    (hw1 : a*w^2 = a+3) (hw2 : w^4 = 8*(a+1))
    (u v : ℤ) (hu : Odd u) (hv : Even v) :
    ∃ e : EndPair a y ((u:K)+(v:K)*w), Rep e true := by
  have hyrat : y^2 ∈ rational (K := K) := by
    rw [hy]
    exact (rational (K := K)).add_mem
      ((rational (K := K)).sub_mem (rational (K := K)).one_mem
        ((rational (K := K)).mul_mem
          ((rational (K := K)).mul_mem (by simpa only [map_ofNat] using C_mem (2:K)) (C_mem a))
          ((rational (K := K)).pow_mem X_mem 2))) ((rational (K := K)).pow_mem X_mem 4)
  obtain ⟨t, ht⟩ := hu
  obtain ⟨s, hs⟩ := hv
  obtain ⟨bt, et, het⟩ := exists_int_mul hyrat (rep_ident a y hy0 hy) t
  obtain ⟨bs, es, hes⟩ := exists_int_mul hyrat (rep_cm a w y hy0 hy hw1 hw2) s
  let ee := ((et.add et).add (EndomorphismWork.EndPair.ident a y hy0 hy)).add (es.add es)
  have herep : Rep ee true := by
    have hh := add_rep hyrat (add_rep hyrat (add_rep hyrat het het) (rep_ident a y hy0 hy))
      (add_rep hyrat hes hes)
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false] using hh
  have hec : ((t:K)*1+(t:K)*1+1)+((s:K)*w+(s:K)*w) = (u:K)+(v:K)*w := by
    rw [ht, hs]
    push_cast
    ring
  exact ⟨EndomorphismWork.EndPair.cast hec ee, rep_cast hec herep⟩

end RationalWork

end

section

namespace MultiplicityWork
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

lemma wronskian_rootMultiplicity (B D : K[X]) (r : K) (hB : B ≠ 0)
    (hr : B.eval r = 0) (hD : D.eval r ≠ 0) :
    B.derivative * D - B * D.derivative ≠ 0 ∧
    (B.derivative * D - B * D.derivative).rootMultiplicity r + 1 = B.rootMultiplicity r := by
  classical
  have hm : 0 < B.rootMultiplicity r := (rootMultiplicity_pos hB).mpr hr
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  obtain ⟨Q, hBQ, hQ⟩ := B.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hB r
  have hQr : Q.eval r ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot] using hQ
  rw [hk] at hBQ
  let T : K[X] := C (k+1 : K) * Q * D + (X-C r)*(Q.derivative*D-Q*D.derivative)
  have hTr : T.eval r ≠ 0 := by
    simp only [T, eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) hQr) hD
  have hT : T ≠ 0 := by intro hh; simp [hh] at hTr
  have hW : B.derivative * D - B * D.derivative = (X-C r)^k * T := by
    rw [hBQ, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
    simp only [sub_zero, mul_one, Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [pow_succ (X-C r) k]
    dsimp [T]
    push_cast
    ring
  have hW0 : B.derivative * D - B * D.derivative ≠ 0 := by
    rw [hW]
    exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero r)) hT
  refine ⟨hW0, ?_⟩
  rw [hW, mul_comm, rootMultiplicity_mul_X_sub_C_pow hT,
    rootMultiplicity_eq_zero hTr, hk]
  omega

lemma simple_rootMultiplicity {G : K[X]} {r : K} (hr : G.eval r = 0)
    (hder : G.derivative.eval r ≠ 0) : G.rootMultiplicity r = 1 := by
  have hG : G ≠ 0 := by intro hh; simp [hh] at hder
  have hpos := (rootMultiplicity_pos hG).mpr hr
  have hd := derivative_rootMultiplicity_of_root hr
  rw [rootMultiplicity_eq_zero hder] at hd
  omega

noncomputable def quartic (a : K) : K[X] := 1 - 2 * C a * X^2 + X^4

noncomputable def homogeneous (a : K) (N D : K[X]) : K[X] := D^4 - 2*C a*N^2*D^2 + N^4

noncomputable def wronskian (N D : K[X]) : K[X] := N.derivative*D-N*D.derivative

@[simp] lemma eval_quartic (a r : K) : (quartic a).eval r = 1-2*a*r^2+r^4 := by
  simp [quartic]

@[simp] lemma eval_quartic_derivative (a r : K) :
    (quartic a).derivative.eval r = -4*a*r+4*r^3 := by
  simp [quartic, derivative_pow, derivative_mul]
  ring

lemma quartic_simple {a r : K} (ha : a^2 ≠ 1) (hr : 1-2*a*r^2+r^4 = 0) :
    -4*a*r+4*r^3 ≠ 0 := by
  intro hh
  have hprod : r * (r^2-a) = 0 := by linear_combination hh / 4
  rcases mul_eq_zero.mp hprod with h0 | h0
  · simp [h0] at hr
  · apply ha
    have heq := sub_eq_zero.mp h0
    linear_combination -hr + (r^2-a)*heq

lemma branch_wronskian_nonzero (N D : K[X]) (a c r : K) (hc : c ≠ 0)
    (hB : N-C r*D ≠ 0) (hD : D.eval r ≠ 0)
    (hg : 1-2*a*r^2+r^4 = 0) (hg' : -4*a*r+4*r^3 ≠ 0)
    (hfix : N.eval r = r*D.eval r)
    (hode : wronskian N D ^ 2 * quartic a = C (c^2) * homogeneous a N D) :
    (wronskian N D).eval r ≠ 0 := by
  let B := N-C r*D
  let Q := N^3+C r*N^2*D+C (r^2-2*a)*N*D^2+C (r^3-2*a*r)*D^3
  have hBr : B.eval r = 0 := by simp [B, hfix]
  have hW : wronskian B D = wronskian N D := by
    simp only [wronskian, B, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
    ring
  have hQr : Q.eval r = (-4*a*r+4*r^3)*(D.eval r)^3 := by
    simp only [Q, eval_add, eval_mul, eval_pow, eval_C, hfix]
    ring
  have hQeval : Q.eval r ≠ 0 := by rw [hQr]; exact mul_ne_zero hg' (pow_ne_zero _ hD)
  have hQ : Q ≠ 0 := by intro hh; simp [hh] at hQeval
  have hBQ : homogeneous a N D = B*Q := by
    dsimp [homogeneous, B, Q]
    have hh := congrArg (C (R := K)) hg
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at hh
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination D^4 * hh
  obtain ⟨hWne, hWmult⟩ := wronskian_rootMultiplicity B D r hB hBr hD
  change wronskian B D ≠ 0 at hWne
  change (wronskian B D).rootMultiplicity r + 1 = B.rootMultiplicity r at hWmult
  rw [hW] at hWne hWmult
  have hG : quartic a ≠ 0 := by
    intro hh
    have := congrArg (fun P : K[X] => P.derivative.eval r) hh
    simp only [derivative_zero, eval_zero, eval_quartic_derivative] at this
    exact hg' this
  have hGmult : (quartic a).rootMultiplicity r = 1 :=
    simple_rootMultiplicity (by simpa using hg) (by simpa using hg')
  have hCc : C (c^2) ≠ (0 : K[X]) := C_ne_zero.mpr (pow_ne_zero 2 hc)
  have hhm := congrArg (rootMultiplicity r) hode
  rw [hBQ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hWne) hG), pow_two,
    rootMultiplicity_mul (mul_ne_zero hWne hWne), hGmult,
    rootMultiplicity_mul (mul_ne_zero hCc (mul_ne_zero hB hQ)),
    rootMultiplicity_C, rootMultiplicity_mul (mul_ne_zero hB hQ),
    rootMultiplicity_eq_zero hQeval] at hhm
  have hz : (wronskian N D).rootMultiplicity r = 0 := by
    dsimp only [B] at hWmult
    omega
  intro hroot
  have hpos := (rootMultiplicity_pos hWne).mpr hroot
  omega

lemma branch_multiplier (N D : K[X]) (a c r : K) (hc : c ≠ 0)
    (hB : N-C r*D ≠ 0) (hD : D.eval r ≠ 0)
    (hg : 1-2*a*r^2+r^4 = 0) (hg' : -4*a*r+4*r^3 ≠ 0)
    (hfix : N.eval r = r*D.eval r)
    (hode : wronskian N D ^ 2 * quartic a = C (c^2) * homogeneous a N D) :
    (wronskian N D).eval r / D.eval r^2 = c^2 := by
  have hW := branch_wronskian_nonzero N D a c r hc hB hD hg hg' hfix hode
  have he := congrArg (fun P : K[X] => P.derivative.eval r) hode
  simp only [derivative_mul, derivative_pow, derivative_C, eval_add, eval_mul,
    eval_pow, eval_C, eval_zero, zero_mul, add_zero, eval_quartic, hg, mul_zero, zero_add,
    eval_quartic_derivative] at he
  have hE : (homogeneous a N D).derivative.eval r =
      (-4*a*r+4*r^3)*D.eval r^2*(wronskian N D).eval r := by
    simp only [homogeneous, derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_C, derivative_ofNat, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_zero, eval_ofNat, zero_mul,
      add_zero, zero_add, wronskian, hfix]
    linear_combination 4*D.eval r^3*D.derivative.eval r*hg
  rw [hE] at he
  apply (div_eq_iff (pow_ne_zero _ hD)).mpr
  apply mul_left_cancel₀ (mul_ne_zero hW hg')
  linear_combination he

end MultiplicityWork

end

section

namespace RepresentationWork
open PowerSeries AdditionWork
open scoped PowerSeries
variable {K : Type*} [Field K]

lemma reduced_rep {f : K⟦X⟧} (hf : f ∈ RationalWork.rational (K := K)) :
    ∃ N D : Polynomial K, D.Monic ∧ IsCoprime N D ∧ D.eval 0 ≠ 0 ∧ f*(D:K⟦X⟧) = N := by
  obtain ⟨N, D, hD0, hND⟩ := hf
  have hD : D ≠ 0 := by intro hh; simp [hh] at hD0
  let r : RatFunc K := algebraMap _ _ N / algebraMap _ _ D
  have hdd : r.denom ∣ D := (RatFunc.denom_dvd hD).mpr ⟨N, rfl⟩
  have hnd : r.num * D = N * r.denom := (RatFunc.num_mul_eq_mul_denom_iff hD).mpr rfl
  refine ⟨r.num, r.denom, RatFunc.monic_denom r, RatFunc.isCoprime_num_denom r, ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := hdd
    rw [hQ, Polynomial.eval_mul] at hD0
    exact (mul_ne_zero_iff.mp hD0).1
  · have hD' : (D : K⟦X⟧) ≠ 0 := by
      intro hh
      exact hD (Polynomial.coe_injective K (by simpa using hh))
    apply mul_right_cancel₀ hD'
    have hh := congrArg (fun P : Polynomial K => (P : K⟦X⟧)) hnd
    simp only [Polynomial.coe_mul] at hh
    rw [hh, ← hND]
    ring

lemma subst_polynomial {Q : Polynomial K} (hQ : HasSubst (Q : K⟦X⟧)) (P : Polynomial K) :
    subst (Q : K⟦X⟧) (P : K⟦X⟧) = (P.comp Q : Polynomial K) := by
  rw [subst_coe hQ, Polynomial.comp_eq_aeval]
  exact congrArg (fun F : Polynomial K →ₐ[K] K⟦X⟧ => F P)
    (Polynomial.aeval_algHom (Polynomial.coeToPowerSeries.algHom K) Q)

variable [CharZero K]

lemma endPair_odd {a c : K} {y : K⟦X⟧} (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4) (e : EndPair a y c) : subst (-X) e.f = -e.f := by
  let h := EndomorphismWork.EndPair.neg (EndomorphismWork.EndPair.ident a y hy0 hy)
  have hh := EndomorphismWork.EndPair.commute hy0 hy e h
  change subst (-X) e.f = subst e.f (-X) at hh
  rw [hh, ← coe_substAlgHom (HasSubst.of_constantCoeff_zero' e.f0), map_neg]
  rw [coe_substAlgHom, subst_X (HasSubst.of_constantCoeff_zero' e.f0)]

lemma reduced_odd {f : K⟦X⟧} (hfodd : subst (-X) f = -f)
    {N D : Polynomial K} (hDmon : D.Monic) (hcop : IsCoprime N D)
    (hD0 : D.eval 0 ≠ 0) (hND : f*(D:K⟦X⟧) = N) :
    D.comp (-Polynomial.X) = D ∧ N.comp (-Polynomial.X) = -N := by
  have hD : D ≠ 0 := hDmon.ne_zero
  have hsub : HasSubst (-X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hpoly (P : Polynomial K) : subst (-X : K⟦X⟧) (P : K⟦X⟧) =
      ((P.comp (-Polynomial.X)) : Polynomial K) := by
    simpa only [Polynomial.coe_neg, Polynomial.coe_X] using
      subst_polynomial (Q := -Polynomial.X) (by simpa using hsub) P
  have he := congrArg (substAlgHom (R := K) hsub) hND
  simp only [map_mul, coe_substAlgHom, hfodd, hpoly] at he
  have hcross : N * D.comp (-Polynomial.X) = -(N.comp (-Polynomial.X) * D) := by
    apply Polynomial.coe_injective K
    simp only [Polynomial.coe_mul, Polynomial.coe_neg]
    rw [← hND, ← he]
    ring
  have hdvd : D ∣ D.comp (-Polynomial.X) := by
    apply hcop.symm.dvd_of_dvd_mul_left
    rw [hcross]
    exact dvd_neg.mpr (dvd_mul_left D _)
  have hdeg : (D.comp (-Polynomial.X)).natDegree ≤ D.natDegree := by
    simp [Polynomial.natDegree_comp]
  have hscale := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hDmon hdvd hdeg
  have heval := congrArg (Polynomial.eval (0:K)) hscale
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_zero,
    Polynomial.eval_mul, Polynomial.eval_C] at heval
  have hlc : (D.comp (-Polynomial.X)).leadingCoeff = 1 := by
    apply mul_right_cancel₀ hD0
    simpa only [one_mul] using heval.symm
  have hDeq : D.comp (-Polynomial.X) = D := by simpa only [hlc, map_one, one_mul] using hscale
  refine ⟨hDeq, ?_⟩
  apply mul_right_cancel₀ hD
  rw [← neg_mul, hDeq] at hcross
  linear_combination hcross

lemma reduced_degree_parity {N D : Polynomial K} (hN : N ≠ 0) (hD : D ≠ 0)
    (hDeven : D.comp (-Polynomial.X) = D) (hNodd : N.comp (-Polynomial.X) = -N) :
    Even D.natDegree ∧ Odd N.natDegree := by
  have hDlc := congrArg Polynomial.leadingCoeff hDeven
  have hNlc := congrArg Polynomial.leadingCoeff hNodd
  simp only [Polynomial.comp_neg_X_leadingCoeff_eq, Polynomial.leadingCoeff_neg] at hDlc hNlc
  constructor
  · apply (neg_one_pow_eq_one_iff_even (by norm_num : (-1:K) ≠ 1)).mp
    apply mul_left_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hD)
    simpa [mul_comm] using hDlc
  · apply (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1:K) ≠ 1)).mp
    apply mul_left_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hN)
    simpa [mul_comm] using hNlc

lemma polynomial_ode {a c : K} {y : K⟦X⟧}
    (hy : y^2 = 1-2*C a*X^2+X^4) (e : EndPair a y c) {N D : Polynomial K}
    (hND : e.f*(D:K⟦X⟧) = N) :
    MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      Polynomial.C (c^2) * MultiplicityWork.homogeneous a N D := by
  have htwo : ((2 : Polynomial K) : K⟦X⟧) = 2 := map_ofNat Polynomial.coeToPowerSeries.ringHom 2
  apply Polynomial.coe_injective K
  simp only [MultiplicityWork.wronskian, MultiplicityWork.quartic, MultiplicityWork.homogeneous,
    Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X, htwo]
  have hD := congrArg (d⁄dX K) hND
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_coe, derivative_coe] at hD
  have hW : (N.derivative:K⟦X⟧)*(D:K⟦X⟧)-(N:K⟦X⟧)*(D.derivative:K⟦X⟧) =
      d⁄dX K e.f * (D:K⟦X⟧)^2 := by
    rw [← hD, ← hND]
    ring
  rw [hW, mul_pow, ← hND]
  have hh := EndomorphismWork.EndPair.ode hy e
  linear_combination (D:K⟦X⟧)^4 * hh

end RepresentationWork

end

section

namespace FixedPointWork
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K]

lemma eval_derivative_roots [DecidableEq K] {H : K[X]} (hsplit : H.Splits)
    (hsep : H.Separable) {r : K} (hr : r ∈ H.roots.toFinset) :
    H.derivative.eval r = H.leadingCoeff * ∏ s ∈ H.roots.toFinset.erase r, (r-s) := by
  have hr' : r ∈ H.roots := by simpa using hr
  have hh : (H.roots.erase r).Nodup := (Polynomial.nodup_roots hsep).erase r
  calc
    H.derivative.eval r =
        H.leadingCoeff * ((H.roots.erase r).map (r - ·)).prod := by
      conv_lhs => rw [hsplit.eq_prod_roots]
      rw [derivative_C_mul, eval_mul, eval_C, eval_multiset_prod_X_sub_C_derivative hr']
    _ = _ := by
      rw [Finset.prod_eq_multiset_prod]
      simp only [Finset.erase_val, Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots hsep)]

lemma sum_eval_div_derivative [DecidableEq K] {H P : K[X]} (hH : H ≠ 0)
    (hsplit : H.Splits) (hsep : H.Separable) (hP : P.degree < H.degree) :
    ∑ r ∈ H.roots.toFinset, P.eval r / H.derivative.eval r =
      P.coeff (H.natDegree - 1) / H.leadingCoeff := by
  have hcard : H.roots.toFinset.card = H.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hsplit.natDegree_eq_card_roots]
  have hcoeff := Lagrange.coeff_eq_sum (s := H.roots.toFinset) (v := id)
    (Function.injective_id.injOn) (P := P) (by rw [hcard, ← degree_eq_natDegree hH]; exact hP)
  rw [hcard] at hcoeff
  rw [hcoeff, sum_div]
  apply sum_congr rfl
  intro r hr
  rw [eval_derivative_roots hsplit hsep hr]
  dsimp
  ring

lemma finite_fixed_point_sum [DecidableEq K] (N D : K[X])
    (hH : X * D - N ≠ 0) (hsplit : (X * D - N).Splits)
    (hsep : (X * D - N).Separable) (hDdeg : D.degree < (X * D - N).degree)
    (hD : ∀ r ∈ (X * D - N).roots.toFinset, D.eval r ≠ 0) :
    (∑ r ∈ (X * D - N).roots.toFinset,
      1 / (1 - (N.derivative.eval r * D.eval r - N.eval r * D.derivative.eval r) / D.eval r ^ 2)) =
      D.coeff ((X * D - N).natDegree - 1) / (X * D - N).leadingCoeff := by
  rw [← sum_eval_div_derivative hH hsplit hsep hDdeg]
  apply sum_congr rfl
  intro r hr
  have hr0 : (X * D - N).eval r = 0 := (mem_roots hH).mp (by simpa using hr)
  simp only [eval_sub, eval_mul, eval_X] at hr0
  have hn : N.eval r = r * D.eval r := by linear_combination -hr0
  simp only [derivative_sub, derivative_mul, derivative_X, one_mul, eval_sub, eval_add,
    eval_mul, eval_X]
  rw [hn]
  have hd := hD r hr
  field_simp
  ring

lemma fixedpoint_trace {ι : Type*} [Fintype ι] (c : K) (hc : c^2 ≠ 1) (lam : ι → K)
    (hlam : ∀ i, lam i = c ∨ lam i = -c ∨ lam i = c^2)
    (hsum : ∑ i, 1/(1-lam i) = 1) :
    ∃ t : ℤ, c^2+(t:K)*c+(Fintype.card ι : K)-1 = 0 := by
  classical
  have hc1 : 1-c ≠ 0 := by
    intro hh
    have := sub_eq_zero.mp hh
    apply hc
    rw [← this, one_pow]
  have hc2 : 1+c ≠ 0 := by
    intro hh
    have heq : c = -1 := eq_neg_of_add_eq_zero_right hh
    apply hc
    rw [heq]
    ring
  have hc3 : 1-c^2 ≠ 0 := sub_ne_zero.mpr hc.symm
  have hlocal : ∀ i, ∃ t : ℤ, (1-c^2)*(1/(1-lam i)) = 1+(t:K)*c := by
    intro i
    rcases hlam i with hi | hi | hi
    · refine ⟨1, ?_⟩
      rw [hi]
      push_cast
      field_simp
      ring
    · refine ⟨-1, ?_⟩
      rw [hi]
      push_cast
      simp only [sub_neg_eq_add]
      field_simp
      ring
    · refine ⟨0, ?_⟩
      rw [hi]
      simp [hc3]
  choose t ht using hlocal
  refine ⟨∑ i, t i, ?_⟩
  have hs := sum_congr rfl (fun i (_ : i ∈ (univ : Finset ι)) => ht i)
  rw [← mul_sum, hsum, mul_one, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    mul_one, ← sum_mul, ← Int.cast_sum] at hs
  linear_combination -hs

lemma fixedpoint_degree [CharZero K] {ι : Type*} [Fintype ι] (c : K) (hc : c^2 ≠ 1)
    (hnonrat : ∀ q : ℚ, algebraMap ℚ K q ≠ c)
    (tr : ℤ) (norm : ℕ) (hmin : c^2-(tr:K)*c+(norm:K) = 0)
    (lam : ι → K) (hlam : ∀ i, lam i = c ∨ lam i = -c ∨ lam i = c^2)
    (hsum : ∑ i, 1/(1-lam i) = 1) : Fintype.card ι = norm+1 := by
  obtain ⟨t, ht⟩ := fixedpoint_trace c hc lam hlam hsum
  have hlin : ((t+tr:ℤ):K)*c = (norm:K)+1-(Fintype.card ι:K) := by
    push_cast
    linear_combination ht-hmin
  have hz : t+tr = 0 := by
    by_contra hne
    have hne' : ((t+tr:ℤ):K) ≠ 0 := by exact_mod_cast hne
    apply hnonrat (((norm:ℚ)+1-(Fintype.card ι:ℚ))/(t+tr))
    simp only [map_div₀, map_add, map_sub, map_natCast, map_intCast, map_one]
    push_cast at hne'
    apply (div_eq_iff hne').mpr
    push_cast at hlin ⊢
    linear_combination -hlin
  rw [hz, Int.cast_zero, zero_mul] at hlin
  have hh : (Fintype.card ι:K) = (norm:K)+1 := by linear_combination hlin
  exact_mod_cast hh

end FixedPointWork

end

section

namespace DegreeWork
open Polynomial MultiplicityWork
variable {K : Type*} [Field K] [CharZero K]

lemma theta_coeff (P : K[X]) (n : ℕ) : (X*P.derivative).coeff n = (n:K)*P.coeff n := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

lemma theta_degree_le (P : K[X]) : (X*P.derivative).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [theta_coeff, coeff_eq_zero_of_natDegree_lt hn, mul_zero]

lemma wronskian_degree (N D : K[X]) (hN : N ≠ 0) (hD : D ≠ 0)
    (hne : N.natDegree ≠ D.natDegree) :
    (MultiplicityWork.wronskian N D).natDegree+1 = N.natDegree+D.natDegree ∧
    (MultiplicityWork.wronskian N D).leadingCoeff = ((N.natDegree:K)-(D.natDegree:K))*N.leadingCoeff*D.leadingCoeff := by
  let T := (X*N.derivative)*D-N*(X*D.derivative)
  have hT : T = X*MultiplicityWork.wronskian N D := by dsimp [T, MultiplicityWork.wronskian]; ring
  have hdeg : T.natDegree ≤ N.natDegree+D.natDegree := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (natDegree_mul_le.trans (Nat.add_le_add_right (theta_degree_le N) _))
      (natDegree_mul_le.trans (Nat.add_le_add_left (theta_degree_le D) _))
  have hcoeff : T.coeff (N.natDegree+D.natDegree) =
      ((N.natDegree:K)-(D.natDegree:K))*N.leadingCoeff*D.leadingCoeff := by
    simp only [T, coeff_sub]
    rw [coeff_mul_add_eq_of_natDegree_le (theta_degree_le N) (le_refl _),
      coeff_mul_add_eq_of_natDegree_le (le_refl _) (theta_degree_le D), theta_coeff, theta_coeff,
      coeff_natDegree, coeff_natDegree]
    ring
  have hcoeff0 : T.coeff (N.natDegree+D.natDegree) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hne)) (leadingCoeff_ne_zero.mpr hN))
      (leadingCoeff_ne_zero.mpr hD)
  have hTdeg : T.natDegree = N.natDegree+D.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hcoeff0
  have hTne : T ≠ 0 := by intro hh; simp [hh] at hcoeff0
  have hWne : MultiplicityWork.wronskian N D ≠ 0 := by intro hh; simp [hT, hh] at hTne
  constructor
  · rw [hT, natDegree_mul (X_ne_zero) hWne, natDegree_X] at hTdeg
    omega
  · have hlead : T.leadingCoeff = (MultiplicityWork.wronskian N D).leadingCoeff := by rw [hT, leadingCoeff_mul, leadingCoeff_X, one_mul]
    rw [← hlead, leadingCoeff, hTdeg, hcoeff]

lemma homogeneous_degree_left (a : K) (N D : K[X]) (hD : D ≠ 0)
    (hdeg : N.natDegree < D.natDegree) :
    (homogeneous a N D).natDegree = 4*D.natDegree ∧
    (homogeneous a N D).leadingCoeff = D.leadingCoeff^4 := by
  have hcross : (2*C a*N^2*D^2 : K[X]).natDegree ≤ 2*N.natDegree+2*D.natDegree := by
    calc
      _ ≤ (2*C a*N^2).natDegree+(D^2).natDegree := natDegree_mul_le
      _ ≤ (2*C a).natDegree+(N^2).natDegree+(D^2).natDegree := Nat.add_le_add_right natDegree_mul_le _
      _ ≤ 2*N.natDegree+2*D.natDegree := by
        have hzero : (2*C a : K[X]).natDegree = 0 := by
          rw [show (2*C a : K[X]) = C (2*a) by rw [map_mul, map_ofNat]]
          exact natDegree_C _
        simp [hzero, natDegree_pow]
  have hsmall : (-2*C a*N^2*D^2+N^4 : K[X]).natDegree < (D^4).natDegree := by
    have hn : (-2*C a*N^2*D^2 : K[X]).natDegree = (2*C a*N^2*D^2 : K[X]).natDegree := by
      rw [show (-2*C a*N^2*D^2 : K[X]) = -(2*C a*N^2*D^2) by ring, natDegree_neg]
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    rw [hn, natDegree_pow, natDegree_pow]
    omega
  have heq : homogeneous a N D = D^4+(-2*C a*N^2*D^2+N^4) := by dsimp [homogeneous]; ring
  rw [heq]
  constructor
  · rw [natDegree_add_eq_left_of_natDegree_lt hsmall, natDegree_pow]
  · rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hsmall), leadingCoeff_pow]

lemma homogeneous_degree_right (a : K) (N D : K[X]) (hN : N ≠ 0)
    (hdeg : D.natDegree < N.natDegree) :
    (homogeneous a N D).natDegree = 4*N.natDegree ∧
    (homogeneous a N D).leadingCoeff = N.leadingCoeff^4 := by
  have heq : homogeneous a N D = homogeneous a D N := by dsimp [homogeneous]; ring
  rw [heq]
  exact homogeneous_degree_left a D N hN hdeg

lemma quartic_degree (a : K) : (quartic a).natDegree = 4 ∧ (quartic a).leadingCoeff = 1 := by
  have hsmall : (1-2*C a*X^2 : K[X]).natDegree < (X^4 : K[X]).natDegree := by
    have hh : (1-2*C a*X^2 : K[X]).natDegree ≤ 2 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le (by simp)
      apply natDegree_mul_le.trans
      have hzero : (2*C a : K[X]).natDegree = 0 := by
        rw [show (2*C a : K[X]) = C (2*a) by rw [map_mul, map_ofNat]]
        exact natDegree_C _
      simp [hzero]
    simpa using lt_of_le_of_lt hh (by decide : 2 < 4)
  constructor
  · exact (natDegree_add_eq_right_of_natDegree_lt hsmall).trans (by simp)
  · exact (leadingCoeff_add_of_degree_lt (degree_lt_degree hsmall)).trans (by simp)

lemma degree_difference_one (N D : K[X]) (a c : K) (hN : N ≠ 0) (hD : D ≠ 0)
    (hc : c ≠ 0) (hne : N.natDegree ≠ D.natDegree)
    (hode : MultiplicityWork.wronskian N D ^ 2 * quartic a = C (c^2) * homogeneous a N D) :
    N.natDegree+1 = D.natDegree ∨ D.natDegree+1 = N.natDegree := by
  have hW := wronskian_degree N D hN hD hne
  have hWd : MultiplicityWork.wronskian N D ≠ 0 := by
    have hlead : (MultiplicityWork.wronskian N D).leadingCoeff ≠ 0 := by
      rw [hW.2]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hne)) (leadingCoeff_ne_zero.mpr hN))
        (leadingCoeff_ne_zero.mpr hD)
    exact leadingCoeff_ne_zero.mp hlead
  have hq := quartic_degree a
  have hq0 : quartic a ≠ 0 := by intro hh; simp [hh] at hq
  have hc0 : C (c^2) ≠ (0:K[X]) := C_ne_zero.mpr (pow_ne_zero 2 hc)
  have hh := congrArg Polynomial.natDegree hode
  rw [natDegree_mul (pow_ne_zero _ hWd) hq0, natDegree_pow, hq.1, natDegree_C_mul (pow_ne_zero 2 hc)] at hh
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hE := homogeneous_degree_left a N D hD hlt
    rw [hE.1] at hh
    omega
  · have hE := homogeneous_degree_right a N D hN hgt
    rw [hE.1] at hh
    omega

end DegreeWork

end

section

namespace NormDegreeWork
open Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

noncomputable def multiplier (N D : K[X]) (r : K) : K :=
  (MultiplicityWork.wronskian N D).eval r / D.eval r^2

lemma nonconstant (N D : K[X]) (hN : N ≠ 0) (hne : N.natDegree ≠ D.natDegree) (r : K) :
    N-C r*D ≠ 0 := by
  intro hh
  have heq := sub_eq_zero.mp hh
  by_cases hr : r = 0
  · simp only [hr, map_zero, zero_mul] at heq
    exact hN heq
  · apply hne
    rw [heq, natDegree_C_mul hr]

lemma fixed_denominator_ne_zero (N D : K[X]) (hcop : IsCoprime N D) (r : K)
    (hfix : (X*D-N).eval r = 0) : D.eval r ≠ 0 := by
  intro hD
  simp only [eval_sub, eval_mul, eval_X, hD, mul_zero, zero_sub, neg_eq_zero] at hfix
  obtain ⟨A, B, hAB⟩ := hcop
  have hh := congrArg (eval r) hAB
  simp only [eval_add, eval_mul, hfix, hD, mul_zero, zero_add, eval_one] at hh
  exact zero_ne_one hh

lemma finite_multiplier (N D : K[X]) (a c : K) (hN : N ≠ 0) (hc : c ≠ 0)
    (ha : a^2 ≠ 1) (hne : N.natDegree ≠ D.natDegree) (hcop : IsCoprime N D)
    (hode : MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      C (c^2) * MultiplicityWork.homogeneous a N D)
    (r : K) (hfix : (X*D-N).eval r = 0) :
    multiplier N D r = c ∨ multiplier N D r = -c ∨ multiplier N D r = c^2 := by
  have hD := fixed_denominator_ne_zero N D hcop r hfix
  have hNr : N.eval r = r*D.eval r := by
    simp only [eval_sub, eval_mul, eval_X] at hfix
    linear_combination -hfix
  by_cases hg : 1-2*a*r^2+r^4 = 0
  · exact Or.inr (Or.inr (MultiplicityWork.branch_multiplier N D a c r hc
      (nonconstant N D hN hne r) hD hg (MultiplicityWork.quartic_simple ha hg) hNr hode))
  · have hh := congrArg (eval r) hode
    simp only [eval_mul, eval_pow, eval_C, MultiplicityWork.eval_quartic,
      MultiplicityWork.homogeneous, eval_add, eval_sub, eval_ofNat, hNr] at hh
    have hs : multiplier N D r ^ 2 = c^2 := by
      have hsq : (MultiplicityWork.wronskian N D).eval r ^ 2 = c^2*(D.eval r)^4 := by
        apply mul_right_cancel₀ hg
        linear_combination hh
      dsimp [multiplier]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hD))).mpr
      simpa only [← pow_mul, show 2*2=4 by rfl] using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).imp_right Or.inl

lemma multiplier_ne_one {c l : K} (hc : c^2 ≠ 1) (hl : l = c ∨ l = -c ∨ l = c^2) : l ≠ 1 := by
  intro hh
  rcases hl with hl | hl | hl
  · apply hc
    rw [← hl, hh, one_pow]
  · apply hc
    have hcs : (-c)^2 = (1:K)^2 := congrArg (fun x:K => x^2) (hl.symm.trans hh)
    simpa only [neg_sq, one_pow] using hcs
  · exact hc (hl.symm.trans hh)

lemma fixed_derivative_ne_zero (N D : K[X]) (r : K) (hD : D.eval r ≠ 0)
    (hfix : (X*D-N).eval r = 0) (hl : multiplier N D r ≠ 1) : (X*D-N).derivative.eval r ≠ 0 := by
  intro hh
  apply hl
  have hn : N.eval r = r*D.eval r := by
    simp only [eval_sub, eval_mul, eval_X] at hfix
    linear_combination -hfix
  simp only [derivative_sub, derivative_mul, derivative_X, one_mul, eval_sub, eval_add, eval_mul, eval_X] at hh
  dsimp [multiplier, MultiplicityWork.wronskian]
  simp only [eval_sub, eval_mul, hn]
  field_simp
  linear_combination -hh

lemma infinity_multiplier (N D : K[X]) (a c : K) (hN : N ≠ 0) (hD : D ≠ 0)
    (hdeg : D.natDegree+1 = N.natDegree)
    (hode : MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      C (c^2) * MultiplicityWork.homogeneous a N D) :
    D.leadingCoeff/N.leadingCoeff = c ∨ D.leadingCoeff/N.leadingCoeff = -c := by
  have hW := DegreeWork.wronskian_degree N D hN hD (by omega)
  have hE := DegreeWork.homogeneous_degree_right a N D hN (by omega)
  have hq := DegreeWork.quartic_degree a
  have hlead := congrArg Polynomial.leadingCoeff hode
  rw [leadingCoeff_mul, leadingCoeff_pow, hq.2, mul_one, leadingCoeff_mul, leadingCoeff_C, hE.2, hW.2] at hlead
  have hcast : (N.natDegree:K)-(D.natDegree:K) = 1 := by rw [← hdeg]; push_cast; ring
  rw [hcast, one_mul] at hlead
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  apply (mul_right_cancel₀ (pow_ne_zero 4 (leadingCoeff_ne_zero.mpr hN)))
  field_simp
  linear_combination hlead

lemma H_degree_finite (N D : K[X]) (hD : D ≠ 0) (hdeg : N.natDegree+1 = D.natDegree) :
    (X*D-N).natDegree = D.natDegree+1 ∧ (X*D-N).leadingCoeff = D.leadingCoeff := by
  have hh : N.natDegree < (X*D).natDegree := by rw [natDegree_X_mul hD]; omega
  constructor
  · rw [natDegree_sub_eq_left_of_natDegree_lt hh, natDegree_X_mul hD]
  · rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree hh), leadingCoeff_mul, leadingCoeff_X, one_mul]

lemma H_degree_infinity (N D : K[X]) (hN : N ≠ 0) (hD : D ≠ 0)
    (hdeg : D.natDegree+1 = N.natDegree) (hlc : D.leadingCoeff ≠ N.leadingCoeff) :
    (X*D-N).natDegree = N.natDegree ∧ (X*D-N).leadingCoeff = D.leadingCoeff-N.leadingCoeff := by
  have hdeg' : (X*D).degree = N.degree := by
    rw [degree_eq_natDegree (mul_ne_zero X_ne_zero hD), degree_eq_natDegree hN, natDegree_X_mul hD, hdeg]
  have hlead : (X*D).leadingCoeff ≠ N.leadingCoeff := by simpa using hlc
  constructor
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply (natDegree_sub_le _ _).trans
      rw [natDegree_X_mul hD, hdeg, max_self]
    · have hXD : (X*D).coeff N.natDegree = D.leadingCoeff := by
        rw [← hdeg, ← natDegree_X_mul hD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_X, one_mul]
      rw [coeff_sub, hXD, coeff_natDegree]
      exact sub_ne_zero.mpr hlc
  · simpa using leadingCoeff_sub_of_degree_eq hdeg' hlead

section AlgebraicallyClosed
variable [IsAlgClosed K]

lemma fixed_separable (N D : K[X]) (a c : K) (hN : N ≠ 0) (hc : c ≠ 0)
    (ha : a^2 ≠ 1) (hc1 : c^2 ≠ 1) (hne : N.natDegree ≠ D.natDegree) (hcop : IsCoprime N D)
    (hode : MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      C (c^2) * MultiplicityWork.homogeneous a N D) : (X*D-N).Separable := by
  change IsCoprime (X*D-N) (X*D-N).derivative
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
  intro r
  by_cases hr : (X*D-N).eval r = 0
  · right
    have hh := fixed_derivative_ne_zero N D r (fixed_denominator_ne_zero N D hcop r hr) hr
      (multiplier_ne_one hc1 (finite_multiplier N D a c hN hc ha hne hcop hode r hr))
    simpa using hh
  · left
    simpa using hr

lemma finite_root_sum [DecidableEq K] (N D : K[X])
    (hdeg : (X*D-N).natDegree = D.natDegree+1) (hsep : (X*D-N).Separable)
    (hcop : IsCoprime N D) :
    (∑ r ∈ (X*D-N).roots.toFinset, 1/(1-multiplier N D r)) = D.leadingCoeff/(X*D-N).leadingCoeff := by
  have hH : X*D-N ≠ 0 := by intro hh; simp [hh] at hdeg
  have hDdeg : D.degree < (X*D-N).degree := degree_lt_degree (by rw [hdeg]; omega)
  have hh := FixedPointWork.finite_fixed_point_sum N D hH (IsAlgClosed.splits _) hsep hDdeg
    (fun r hr => fixed_denominator_ne_zero N D hcop r ((mem_roots hH).mp (by simpa using hr)))
  simpa only [multiplier, MultiplicityWork.wronskian, eval_sub, eval_mul, hdeg, Nat.add_sub_cancel,
    coeff_natDegree] using hh

lemma norm_degree (N D : K[X]) (a c : K) (hN : N ≠ 0) (hD : D ≠ 0) (hc : c ≠ 0)
    (ha : a^2 ≠ 1) (hc1 : c^2 ≠ 1) (hne : N.natDegree ≠ D.natDegree) (hcop : IsCoprime N D)
    (hnonrat : ∀ q : ℚ, algebraMap ℚ K q ≠ c)
    (tr : ℤ) (norm : ℕ) (hmin : c^2-(tr:K)*c+(norm:K) = 0)
    (hode : MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      C (c^2) * MultiplicityWork.homogeneous a N D) : max N.natDegree D.natDegree = norm := by
  classical
  have hsep := fixed_separable N D a c hN hc ha hc1 hne hcop hode
  rcases DegreeWork.degree_difference_one N D a c hN hD hc hne hode with hdeg | hdeg
  · have hHd := H_degree_finite N D hD hdeg
    have hH : X*D-N ≠ 0 := by intro hh; simp [hh] at hHd
    let I := {r : K // r ∈ (X*D-N).roots.toFinset}
    letI : Fintype I := (X*D-N).roots.toFinset.fintypeCoeSort
    have hcard : Fintype.card I = D.natDegree+1 := by
      have hcard0 : Fintype.card I = (X*D-N).roots.toFinset.card := Fintype.card_coe _
      rw [hcard0]
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
        ← (IsAlgClosed.splits (X*D-N)).natDegree_eq_card_roots, hHd.1]
    have hlam : ∀ i : I, multiplier N D i = c ∨ multiplier N D i = -c ∨ multiplier N D i = c^2 := by
      intro i
      exact finite_multiplier N D a c hN hc ha hne hcop hode i
        ((mem_roots hH).mp (Multiset.mem_toFinset.mp i.2))
    have hsum : ∑ i : I, 1/(1-multiplier N D i) = 1 := by
      have hs0 : (∑ i:I, 1/(1-multiplier N D i)) =
          ∑ r ∈ (X*D-N).roots.toFinset, 1/(1-multiplier N D r) :=
        Finset.sum_coe_sort (X*D-N).roots.toFinset (fun r : K => 1/(1-multiplier N D r))
      rw [hs0, finite_root_sum N D hHd.1 hsep hcop, hHd.2,
        div_self (leadingCoeff_ne_zero.mpr hD)]
    have hcard' := FixedPointWork.fixedpoint_degree c hc1 hnonrat tr norm hmin (fun i:I => multiplier N D i) hlam hsum
    rw [hcard] at hcard'
    rw [max_eq_right (by omega)]
    omega
  · have hinf := infinity_multiplier N D a c hN hD hdeg hode
    have hinf_ne : D.leadingCoeff/N.leadingCoeff ≠ 1 := multiplier_ne_one hc1 (hinf.imp_right Or.inl)
    have hlc : D.leadingCoeff ≠ N.leadingCoeff := by
      intro hh
      apply hinf_ne
      rw [hh, div_self (leadingCoeff_ne_zero.mpr hN)]
    have hHd := H_degree_infinity N D hN hD hdeg hlc
    have hHd' : (X*D-N).natDegree = D.natDegree+1 := hHd.1.trans hdeg.symm
    have hH : X*D-N ≠ 0 := by intro hh; simp [hh] at hHd'
    let I := {r : K // r ∈ (X*D-N).roots.toFinset}
    letI : Fintype I := (X*D-N).roots.toFinset.fintypeCoeSort
    have hcard : Fintype.card (Option I) = N.natDegree+1 := by
      rw [Fintype.card_option]
      have hcard0 : Fintype.card I = (X*D-N).roots.toFinset.card := Fintype.card_coe _
      rw [hcard0]
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
        ← (IsAlgClosed.splits (X*D-N)).natDegree_eq_card_roots, hHd.1]
    let lam : Option I → K := fun i => match i with
      | none => D.leadingCoeff/N.leadingCoeff
      | some r => multiplier N D r
    have hlam : ∀ i, lam i = c ∨ lam i = -c ∨ lam i = c^2 := by
      intro i
      cases i with
      | none => exact hinf.imp_right Or.inl
      | some i =>
        exact finite_multiplier N D a c hN hc ha hne hcop hode i
          ((mem_roots hH).mp (Multiset.mem_toFinset.mp i.2))
    have hsum : ∑ i, 1/(1-lam i) = 1 := by
      rw [Fintype.sum_option]
      change 1/(1-D.leadingCoeff/N.leadingCoeff) + (∑ i:I, 1/(1-multiplier N D i)) = 1
      have hs0 : (∑ i:I, 1/(1-multiplier N D i)) =
          ∑ r ∈ (X*D-N).roots.toFinset, 1/(1-multiplier N D r) :=
        Finset.sum_coe_sort (X*D-N).roots.toFinset (fun r : K => 1/(1-multiplier N D r))
      rw [hs0, finite_root_sum N D hHd' hsep hcop, hHd.2]
      have hnlc := leadingCoeff_ne_zero.mpr hN
      have hdlc := sub_ne_zero.mpr hlc
      have hndlc := sub_ne_zero.mpr hlc.symm
      field_simp
      ring
    have hcard' := FixedPointWork.fixedpoint_degree c hc1 hnonrat tr norm hmin lam hlam hsum
    rw [hcard] at hcard'
    rw [max_eq_left (by omega)]
    omega

end AlgebraicallyClosed
lemma norm_degree_general (N D : K[X]) (a c : K) (hN : N ≠ 0) (hD : D ≠ 0) (hc : c ≠ 0)
    (ha : a^2 ≠ 1) (hc1 : c^2 ≠ 1) (hne : N.natDegree ≠ D.natDegree) (hcop : IsCoprime N D)
    (hnonrat : ∀ q : ℚ, algebraMap ℚ K q ≠ c)
    (tr : ℤ) (norm : ℕ) (hmin : c^2-(tr:K)*c+(norm:K) = 0)
    (hode : MultiplicityWork.wronskian N D ^ 2 * MultiplicityWork.quartic a =
      C (c^2) * MultiplicityWork.homogeneous a N D) : max N.natDegree D.natDegree = norm := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hi : Function.Injective φ := RingHom.injective φ
  have hode' := congrArg (Polynomial.map φ) hode
  simp only [MultiplicityWork.wronskian, MultiplicityWork.quartic, MultiplicityWork.homogeneous,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_one, Polynomial.map_ofNat, Polynomial.map_X,
    ← Polynomial.derivative_map, map_pow] at hode'
  have hmin' := congrArg φ hmin
  simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_natCast, map_zero] at hmin'
  have hnonrat' : ∀ q : ℚ, algebraMap ℚ (AlgebraicClosure K) q ≠ φ c := by
    intro q hh
    apply hnonrat q
    apply hi
    simpa only [φ, ← IsScalarTower.algebraMap_apply ℚ K (AlgebraicClosure K)] using hh
  have ha' : (φ a)^2 ≠ 1 := by
    intro hh
    apply ha
    apply hi
    simpa only [map_pow, map_one] using hh
  have hc1' : (φ c)^2 ≠ 1 := by
    intro hh
    apply hc1
    apply hi
    simpa only [map_pow, map_one] using hh
  have hh := norm_degree (N.map φ) (D.map φ) (φ a) (φ c)
    ((Polynomial.map_ne_zero_iff hi).mpr hN) ((Polynomial.map_ne_zero_iff hi).mpr hD)
    ((map_ne_zero_iff φ hi).mpr hc) ha' hc1'
    (by simpa only [Polynomial.natDegree_map_eq_of_injective hi] using hne)
    (hcop.map (Polynomial.mapRingHom φ)) hnonrat' tr norm hmin' (by simpa only [MultiplicityWork.wronskian,
      MultiplicityWork.quartic, MultiplicityWork.homogeneous, map_pow] using hode')
  simpa only [Polynomial.natDegree_map_eq_of_injective hi] using hh

end NormDegreeWork

end

section

namespace ReciprocityWork
open scoped PowerSeries LaurentSeries RatFunc
variable {K : Type*} [Field K]

lemma invX_injective : Function.Injective (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K) : Polynomial K →ₐ[K] RatFunc K) := by
  apply transcendental_iff_injective.mp
  intro hh
  exact (RatFunc.transcendental_X (K := K)) (IsAlgebraic.inv_iff.mp hh)

noncomputable def invertX : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ invX_injective)

lemma invertX_poly (P : Polynomial K) : invertX (algebraMap _ (RatFunc K) P) =
    Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K) P := by
  have hh := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ invX_injective) P 1
  simpa only [map_one, div_one, invertX] using hh

@[simp] lemma invertX_X : invertX (RatFunc.X : RatFunc K) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, invertX_poly, Polynomial.aeval_X]
  rfl

@[simp] lemma invertX_C (c : K) : invertX (RatFunc.C c) = RatFunc.C c :=
  invertX.commutes c

noncomputable def psAlg : K⟦X⟧ →ₐ[K] K⸨X⸩ where
  toRingHom := HahnSeries.ofPowerSeries ℤ K
  commutes' c := by
    change HahnSeries.ofPowerSeries ℤ K (PowerSeries.C c) = algebraMap K K⸨X⸩ c
    rw [PowerSeries.coe_C, LaurentSeries.algebraMap_apply]

lemma psAlg_poly (P : Polynomial K) : psAlg (P : K⟦X⟧) =
    algebraMap (RatFunc K) K⸨X⸩ (algebraMap _ (RatFunc K) P) := RatFunc.coe_coe P

noncomputable def ratAlg : RatFunc K →ₐ[K] K⸨X⸩ where
  toRingHom := algebraMap (RatFunc K) K⸨X⸩
  commutes' c := by
    change algebraMap (RatFunc K) K⸨X⸩ (RatFunc.C c) = algebraMap K K⸨X⸩ c
    rw [← RatFunc.algebraMap_C, ← psAlg_poly, Polynomial.coe_C]
    exact psAlg.commutes c

lemma ratAlg_poly (P : Polynomial K) : ratAlg (algebraMap _ (RatFunc K) P) =
    psAlg (P : K⟦X⟧) := (psAlg_poly P).symm

lemma psAlg_injective : Function.Injective (psAlg (K := K)) := HahnSeries.ofPowerSeries_injective
lemma ratAlg_injective : Function.Injective (ratAlg (K := K)) := RingHom.injective ratAlg.toRingHom

lemma ratAlg_C (c : K) : ratAlg (RatFunc.C c) = psAlg (PowerSeries.C c) := by
  rw [← RatFunc.algebraMap_C, ratAlg_poly, Polynomial.coe_C]

lemma ratAlg_X : ratAlg (RatFunc.X : RatFunc K) = psAlg (PowerSeries.X : K⟦X⟧) := by
  rw [← RatFunc.algebraMap_X, ratAlg_poly, Polynomial.coe_X]

lemma rep_embedding (f : K⟦X⟧) (N D : Polynomial K) (hD : D ≠ 0)
    (hrep : f*(D:K⟦X⟧) = N) :
    psAlg f = ratAlg (algebraMap _ (RatFunc K) N/algebraMap _ (RatFunc K) D) := by
  rw [map_div₀, ratAlg_poly, ratAlg_poly]
  apply (eq_div_iff ?_).mpr
  · rw [← map_mul, hrep]
  · apply (map_ne_zero_iff psAlg.toRingHom psAlg_injective).mpr
    exact fun hh => hD (Polynomial.coe_injective K (by simpa using hh))

lemma subst_embedding (f : K⟦X⟧) (F : RatFunc K) (hf : psAlg f = ratAlg F)
    (h0 : PowerSeries.constantCoeff f = 0) (P : Polynomial K) :
    psAlg (PowerSeries.subst f (P : K⟦X⟧)) = ratAlg (Polynomial.aeval F P) := by
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' h0),
    ← Polynomial.aeval_algHom_apply psAlg, hf, Polynomial.aeval_algHom_apply ratAlg]

lemma invertX_aeval (t : RatFunc K) (P : Polynomial K) :
    invertX (Polynomial.aeval t P) = Polynomial.aeval (invertX t) P :=
  (Polynomial.aeval_algHom_apply invertX t P).symm

noncomputable def basicMap (w : K) : RatFunc K := RatFunc.C w * RatFunc.X/(1+RatFunc.X^2)

lemma invertX_basicMap (w : K) : invertX (basicMap w) = basicMap w := by
  simp only [basicMap, map_div₀, map_mul, map_add, map_one, map_pow, invertX_C, invertX_X]
  field_simp [RatFunc.X_ne_zero]
  rw [add_comm]

variable [CharZero K]

lemma commute_dichotomy (f g : K⟦X⟧) (w : K) (hw : w ≠ 0) (N D : Polynomial K)
    (hf0 : PowerSeries.constantCoeff f = 0) (hg0 : PowerSeries.constantCoeff g = 0)
    (hD0 : D.eval 0 ≠ 0) (hrep : f*(D:K⟦X⟧) = N)
    (hg : g*(1+PowerSeries.X^2) = PowerSeries.C w*PowerSeries.X)
    (hcomm : PowerSeries.subst g f = PowerSeries.subst f g) :
    let t := algebraMap _ (RatFunc K) N / algebraMap _ (RatFunc K) D
    t = invertX t ∨ t*invertX t = 1 := by
  let t : RatFunc K := algebraMap _ _ N/algebraMap _ _ D
  have hD : D ≠ 0 := by intro hh; simp [hh] at hD0
  have hf := rep_embedding f N D hD hrep
  change psAlg f = ratAlg t at hf
  have hDg : (1+Polynomial.X^2 : Polynomial K) ≠ 0 := by
    intro hh
    have := congrArg (Polynomial.eval (0:K)) hh
    norm_num at this
  have hg' : psAlg g = ratAlg (basicMap w) := by
    have hrep' : g*((1+Polynomial.X^2 : Polynomial K):K⟦X⟧) =
        ((Polynomial.C w*Polynomial.X : Polynomial K):K⟦X⟧) := by
      simpa only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_pow,
        Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C] using hg
    simpa only [map_add, map_one, map_pow, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      basicMap] using rep_embedding g _ _ hDg hrep'
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hsN := congrArg (PowerSeries.substAlgHom (R := K) hgs) hrep
  simp only [map_mul, PowerSeries.coe_substAlgHom] at hsN
  have hsg := congrArg (PowerSeries.substAlgHom (R := K) hfs) hg
  simp only [map_mul, map_add, map_one, map_pow, PowerSeries.coe_substAlgHom,
    CompositionWork.subst_C hfs, PowerSeries.subst_X hfs] at hsg
  rw [← hcomm] at hsg
  have heq : (PowerSeries.C w*f)*PowerSeries.subst g (D:K⟦X⟧) =
      (1+f^2)*PowerSeries.subst g (N:K⟦X⟧) := by
    rw [← hsN, ← hsg]
    ring
  have hfield : RatFunc.C w*t*Polynomial.aeval (basicMap w) D =
      (1+t^2)*Polynomial.aeval (basicMap w) N := by
    apply ratAlg_injective
    have hh := congrArg psAlg heq
    simp only [map_mul, map_add, map_one, map_pow, ratAlg_C, ← hf,
      subst_embedding g (basicMap w) hg' hg0] at hh ⊢
    exact hh
  have hfield' := congrArg invertX hfield
  simp only [map_mul, map_add, map_one, map_pow, invertX_C, invertX_aeval, invertX_basicMap] at hfield'
  have hDn : Polynomial.aeval (basicMap w) D ≠ 0 := by
    intro hh
    have hh' := congrArg ratAlg hh
    rw [← subst_embedding g (basicMap w) hg' hg0 D, map_zero] at hh'
    have hzero := psAlg_injective (hh'.trans (map_zero psAlg).symm)
    have hc := congrArg (PowerSeries.constantCoeff (R := K)) hzero
    rw [PSWork.constantCoeff_subst_self hg0, Polynomial.constantCoeff_coe, map_zero,
      Polynomial.coeff_zero_eq_eval_zero] at hc
    exact hD0 hc
  have hw' : RatFunc.C w ≠ 0 := (map_ne_zero_iff RatFunc.C RatFunc.C_injective).mpr hw
  have hfactor : (t-invertX t)*(1-t*invertX t) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hw' hDn)
    linear_combination (1+invertX t^2)*hfield-(1+t^2)*hfield'
  rcases mul_eq_zero.mp hfactor with hh | hh
  · exact Or.inl (sub_eq_zero.mp hh)
  · exact Or.inr (sub_eq_zero.mp hh).symm

lemma invertX_poly_reverse (P : Polynomial K) :
    invertX (algebraMap _ (RatFunc K) P) =
      algebraMap _ (RatFunc K) P.reverse / RatFunc.X^P.natDegree := by
  letI : Invertible (RatFunc.X⁻¹ : RatFunc K) := invertibleOfNonzero (inv_ne_zero RatFunc.X_ne_zero)
  have hh := Polynomial.eval₂_reverse_mul_pow (algebraMap K (RatFunc K)) (RatFunc.X⁻¹ : RatFunc K) P
  simp only [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def,
    RatFunc.aeval_X_left_eq_algebraMap, inv_pow] at hh
  rw [invertX_poly, ← hh, div_eq_mul_inv]

lemma invertX_ratio (N D : Polynomial K) (hD : D ≠ 0) (hdeg : D.natDegree+1=N.natDegree) :
    invertX (algebraMap _ (RatFunc K) N/algebraMap _ (RatFunc K) D) =
      algebraMap _ (RatFunc K) N.reverse/(RatFunc.X*algebraMap _ (RatFunc K) D.reverse) := by
  have hDr : algebraMap _ (RatFunc K) D.reverse ≠ 0 := RatFunc.algebraMap_ne_zero
    (Polynomial.reverse_eq_zero.not.mpr hD)
  rw [map_div₀, invertX_poly_reverse, invertX_poly_reverse, ← hdeg, pow_succ]
  field_simp [RatFunc.X_ne_zero, hDr]

lemma ratio_not_invertX (N D : Polynomial K) (hN : N ≠ 0) (hD0 : D.eval 0 ≠ 0)
    (hdeg : D.natDegree+1=N.natDegree) :
    algebraMap _ (RatFunc K) N/algebraMap _ (RatFunc K) D ≠
      invertX (algebraMap _ (RatFunc K) N/algebraMap _ (RatFunc K) D) := by
  have hD : D ≠ 0 := by intro hh; simp [hh] at hD0
  have hDr := RatFunc.algebraMap_ne_zero (Polynomial.reverse_eq_zero.not.mpr hD)
  intro hh
  rw [invertX_ratio N D hD hdeg] at hh
  have heq := (div_eq_div_iff (RatFunc.algebraMap_ne_zero hD) (mul_ne_zero RatFunc.X_ne_zero hDr)).mp hh
  have hpoly : N*(Polynomial.X*D.reverse) = N.reverse*D := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, RatFunc.algebraMap_X] using heq
  have h := congrArg (Polynomial.eval (0:K)) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul, mul_zero] at h
  have hNr0 : N.reverse.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hN
  exact (mul_ne_zero hNr0 hD0) h.symm

lemma reciprocal_polynomials (f g : K⟦X⟧) (w : K) (hw : w ≠ 0) (N D : Polynomial K)
    (hN : N ≠ 0) (hf0 : PowerSeries.constantCoeff f = 0) (hg0 : PowerSeries.constantCoeff g = 0)
    (hD0 : D.eval 0 ≠ 0) (hrep : f*(D:K⟦X⟧) = N) (hdeg : D.natDegree+1=N.natDegree)
    (hg : g*(1+PowerSeries.X^2) = PowerSeries.C w*PowerSeries.X)
    (hcomm : PowerSeries.subst g f = PowerSeries.subst f g) :
    N*N.reverse = Polynomial.X*D*D.reverse := by
  have hD : D ≠ 0 := by intro hh; simp [hh] at hD0
  have hdich := commute_dichotomy f g w hw N D hf0 hg0 hD0 hrep hg hcomm
  have ht := hdich.resolve_left (ratio_not_invertX N D hN hD0 hdeg)
  rw [invertX_ratio N D hD hdeg, div_mul_div_comm] at ht
  have hDr := RatFunc.algebraMap_ne_zero (Polynomial.reverse_eq_zero.not.mpr hD)
  have hh := (div_eq_one_iff_eq (mul_ne_zero (RatFunc.algebraMap_ne_zero hD)
    (mul_ne_zero RatFunc.X_ne_zero hDr))).mp ht
  apply RatFunc.algebraMap_injective K
  simp only [map_mul, RatFunc.algebraMap_X]
  rw [hh]
  ring

lemma reciprocal_normal_form (N D : Polynomial K) (hN : N ≠ 0) (hN0 : N.coeff 0 = 0)
    (hD0 : D.coeff 0 ≠ 0) (hcop : IsCoprime N D) (hdeg : D.natDegree+1=N.natDegree)
    (hrecip : N*N.reverse = Polynomial.X*D*D.reverse) :
    ∃ eps : K, eps^2 = 1 ∧ N = Polynomial.C eps*Polynomial.X*D.reverse ∧
      D = Polynomial.C eps*N.reverse := by
  have hD : D ≠ 0 := by intro hh; simp [hh] at hD0
  have hNr : N.reverse ≠ 0 := Polynomial.reverse_eq_zero.not.mpr hN
  have hdiv : D ∣ N.reverse := by
    apply hcop.symm.dvd_of_dvd_mul_left
    rw [hrecip]
    exact dvd_mul_of_dvd_left (dvd_mul_left D _) _
  have hNt : N.natTrailingDegree ≠ 0 := Polynomial.natTrailingDegree_ne_zero.mpr ⟨hN, hN0⟩
  have hdegR : N.reverse.natDegree ≤ D.natDegree := by rw [Polynomial.reverse_natDegree]; omega
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by intro hh; simp [hh] at hQ; exact hN hQ
  have hQdeg : Q.natDegree = 0 := by
    rw [hQ, Polynomial.natDegree_mul hD hQ0] at hdegR
    omega
  let q := Q.coeff 0
  have hQconst : Q = Polynomial.C q := Polynomial.eq_C_of_natDegree_eq_zero hQdeg
  have hscale : N.reverse = Polynomial.C q*D := by rw [hQ, hQconst]; ring
  have hq : q ≠ 0 := by intro hh; simp [hQconst, hh] at hQ0
  have hCq : Polynomial.C q ≠ (0:Polynomial K) := Polynomial.C_ne_zero.mpr hq
  have hscaleN : Polynomial.C q*N = Polynomial.X*D.reverse := by
    apply mul_right_cancel₀ hD
    rw [hscale] at hrecip
    linear_combination hrecip
  have hc := congrArg (fun P : Polynomial K => P.coeff 0) hscale
  simp only [Polynomial.coeff_zero_reverse, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero] at hc
  have hlead := congrArg Polynomial.leadingCoeff hscaleN
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X,
    one_mul, Polynomial.reverse_leadingCoeff] at hlead
  have hDtrail : D.trailingCoeff = D.coeff 0 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hD0)]
  rw [hDtrail, hc] at hlead
  have hq2 : q^2 = 1 := by
    apply mul_right_cancel₀ hD0
    linear_combination hlead
  refine ⟨q, hq2, ?_, ?_⟩
  · apply mul_left_cancel₀ hCq
    rw [hscaleN]
    have hh := congrArg (Polynomial.C (R := K)) hq2
    simp only [map_pow, map_one] at hh
    linear_combination -(Polynomial.X*D.reverse)*hh
  · rw [hscale, ← mul_assoc, ← pow_two, ← map_pow, hq2, map_one, one_mul]

end ReciprocityWork

end

section

namespace IntegralWork
open PowerSeries AdditionWork
open scoped PowerSeries BigOperators
variable {K : Type*} [Field K]

noncomputable def coefficients (S : Subring K) : Subring K⟦X⟧ where
  carrier := {f | ∀ n, coeff n f ∈ S}
  zero_mem' := by intro n; simp
  one_mem' := by intro n; rw [coeff_one]; split_ifs <;> simp
  add_mem' := by intro f g hf hg n; rw [map_add]; exact S.add_mem (hf n) (hg n)
  neg_mem' := by intro f hf n; rw [map_neg]; exact S.neg_mem (hf n)
  mul_mem' := by
    intro f g hf hg n
    rw [coeff_mul]
    exact S.sum_mem (fun ij hij => S.mul_mem (hf ij.1) (hg ij.2))

lemma C_mem {S : Subring K} {a : K} (ha : a ∈ S) : C a ∈ coefficients S := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem

lemma X_mem (S : Subring K) : (X : K⟦X⟧) ∈ coefficients S := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

lemma inv_mem {S : Subring K} {f : K⟦X⟧} (hf : f ∈ coefficients S)
    (h0 : (constantCoeff f)⁻¹ ∈ S) : f⁻¹ ∈ coefficients S := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inv]
    split_ifs
    · exact h0
    · apply S.mul_mem (S.neg_mem h0)
      apply S.sum_mem
      intro ij hij
      split_ifs with hlt
      · exact S.mul_mem (hf ij.1) (ih ij.2 hlt)
      · exact S.zero_mem

lemma subst_mem {S : Subring K} {f g : K⟦X⟧} (hf : f ∈ coefficients S)
    (hg : g ∈ coefficients S) (h0 : constantCoeff f = 0) : subst f g ∈ coefficients S := by
  intro n
  rw [CompositionWork.coeff_subst_sum h0 g n (n+1) (by omega)]
  apply S.sum_mem
  intro k hk
  exact S.mul_mem (hg k) ((coefficients S).pow_mem hf k n)

variable [CharZero K]

lemma sqrtQuartic_mem (S : Subring K) (hhalf : (1/2:K) ∈ S) {a : K} (ha : a ∈ S) :
    PSWork.sqrtQuartic a ∈ coefficients S := by
  let t : K⟦X⟧ := -2*C a*X^2+X^4
  let half : K⟦X⟧ := C (1/2:K)
  let q : K⟦X⟧ := PowerSeries.map (Nat.castRingHom K) catalanSeries
  let b := -(half^2*t)
  let s := subst b q
  let y := 1+half*t*s
  have ht0 : constantCoeff t = 0 := by simp [t]
  have hb0 : constantCoeff b = 0 := by simp [b, ht0]
  have hh : 2*half = 1 := by
    have hc := congrArg (C (R := K)) (show (2:K)*(1/2)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hc
  have hq : q^2*X+1=q := by
    have hc := congrArg (PowerSeries.map (Nat.castRingHom K)) catalanSeries_sq_mul_X_add_one
    simpa only [map_add, map_one, map_mul, map_pow, map_X] using hc
  have hs := congrArg (substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' hb0)) hq
  simp only [map_add, map_one, map_mul, map_pow, coe_substAlgHom,
    subst_X (HasSubst.of_constantCoeff_zero' hb0)] at hs
  change s^2*b+1=s at hs
  have hy0 : constantCoeff y = 1 := by simp [y, ht0]
  have hysq : y^2 = 1-2*C a*X^2+X^4 := by
    change (1+half*t*s)^2 = _
    have heq : (1+half*t*s)^2 = 1+t := by
      dsimp only [b] at hs
      linear_combination -t*hs+t*s*hh
    rw [heq]
    dsimp only [t]
    ring
  have heq : PSWork.sqrtQuartic a = y := EndomorphismWork.sq_unique (PSWork.sqrtQuartic_const a) hy0
    ((PSWork.sqrtQuartic_sq a).trans hysq.symm)
  rw [heq]
  have hhalfm : half ∈ coefficients S := C_mem hhalf
  have h2 : (2:K⟦X⟧) ∈ coefficients S := by
    simpa only [map_ofNat] using C_mem (S := S) (show (2:K) ∈ S by exact natCast_mem S 2)
  have ht : t ∈ coefficients S := (coefficients S).add_mem
    ((coefficients S).mul_mem ((coefficients S).mul_mem ((coefficients S).neg_mem h2) (C_mem ha))
      ((coefficients S).pow_mem (X_mem S) 2)) ((coefficients S).pow_mem (X_mem S) 4)
  have hbm : b ∈ coefficients S := (coefficients S).neg_mem
    ((coefficients S).mul_mem ((coefficients S).pow_mem hhalfm 2) ht)
  have hqm : q ∈ coefficients S := by
    intro n
    simp only [q, coeff_map, catalanSeries_coeff]
    exact natCast_mem S _
  have hsm : s ∈ coefficients S := subst_mem hbm hqm hb0
  exact (coefficients S).add_mem (coefficients S).one_mem
    ((coefficients S).mul_mem ((coefficients S).mul_mem hhalfm ht) hsm)

def IntegralPair (S : Subring K) {a c : K} {y : K⟦X⟧} (e : EndPair a y c) : Prop :=
  e.f ∈ coefficients S ∧ e.Y ∈ coefficients S

lemma add_integral (S : Subring K) {a c d : K} {y : K⟦X⟧} (ha : a ∈ S)
    {e : EndPair a y c} {h : EndPair a y d} (he : IntegralPair S e) (hh : IntegralPair S h) :
    IntegralPair S (e.add h) := by
  have h2 : (2:K⟦X⟧) ∈ coefficients S := by
    simpa only [map_ofNat] using C_mem (S := S) (show (2:K) ∈ S from natCast_mem S 2)
  have he2 := (coefficients S).pow_mem he.1 2
  have hh2 := (coefficients S).pow_mem hh.1 2
  have hp := (coefficients S).mul_mem he2 hh2
  have hden := (coefficients S).sub_mem (coefficients S).one_mem hp
  have hden0 : constantCoeff (1-e.f^2*h.f^2) = 1 := by simp [e.f0, h.f0]
  have hdinv := inv_mem hden (by rw [hden0, inv_one]; exact S.one_mem)
  constructor
  · exact (coefficients S).mul_mem ((coefficients S).add_mem
      ((coefficients S).mul_mem he.1 hh.2) ((coefficients S).mul_mem hh.1 he.2)) hdinv
  · change _ ∈ coefficients S
    apply (coefficients S).mul_mem _ ((coefficients S).pow_mem hdinv 2)
    apply (coefficients S).add_mem
    · exact (coefficients S).mul_mem ((coefficients S).mul_mem he.2 hh.2)
        ((coefficients S).add_mem (coefficients S).one_mem hp)
    · exact (coefficients S).mul_mem ((coefficients S).mul_mem ((coefficients S).mul_mem h2 he.1) hh.1)
        ((coefficients S).sub_mem ((coefficients S).add_mem he2 hh2)
          ((coefficients S).mul_mem (C_mem ha) ((coefficients S).add_mem (coefficients S).one_mem hp)))

lemma integral_cast (S : Subring K) {a c d : K} {y : K⟦X⟧} (hc : c=d)
    {e : EndPair a y c} (he : IntegralPair S e) :
    IntegralPair S (EndomorphismWork.EndPair.cast hc e) := by subst d; exact he

lemma integral_zero (S : Subring K) (a : K) (y : K⟦X⟧) :
    IntegralPair S (EndomorphismWork.EndPair.zero a y) :=
  ⟨(coefficients S).zero_mem, (coefficients S).one_mem⟩

lemma integral_neg (S : Subring K) {a c : K} {y : K⟦X⟧} {e : EndPair a y c}
    (he : IntegralPair S e) : IntegralPair S (EndomorphismWork.EndPair.neg e) :=
  ⟨(coefficients S).neg_mem he.1, he.2⟩

lemma integral_ident (S : Subring K) (a : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4) (hym : y ∈ coefficients S) :
    IntegralPair S (EndomorphismWork.EndPair.ident a y hy0 hy) := ⟨X_mem S, hym⟩

lemma integral_cm (S : Subring K) (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4) (hw : w ∈ S) (hym : y ∈ coefficients S)
    (hw1 : a*w^2 = a+3) (hw2 : w^4 = 8*(a+1)) :
    IntegralPair S (EndomorphismWork.EndPair.cm a w y hy0 hy hw1 hw2) := by
  have hden : (1+X^2 : K⟦X⟧) ∈ coefficients S :=
    (coefficients S).add_mem (coefficients S).one_mem ((coefficients S).pow_mem (X_mem S) 2)
  have hi := inv_mem hden (by simpa using S.one_mem)
  constructor
  · exact (coefficients S).mul_mem ((coefficients S).mul_mem (C_mem hw) (X_mem S)) hi
  · exact (coefficients S).mul_mem
      ((coefficients S).mul_mem ((coefficients S).sub_mem (coefficients S).one_mem
        ((coefficients S).pow_mem (X_mem S) 2)) hym) ((coefficients S).pow_mem hi 2)

lemma exists_nat_integral (S : Subring K) {a c : K} {y : K⟦X⟧} (ha : a ∈ S)
    {e : EndPair a y c} (he : IntegralPair S e) (n : ℕ) :
    ∃ h : EndPair a y ((n:K)*c), IntegralPair S h := by
  induction n with
  | zero =>
    refine ⟨EndomorphismWork.EndPair.cast (by simp) (EndomorphismWork.EndPair.zero a y), ?_⟩
    exact integral_cast S _ (integral_zero S a y)
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨EndomorphismWork.EndPair.cast (by push_cast; ring) (h.add e), ?_⟩
    exact integral_cast S _ (add_integral S ha hh he)

lemma exists_int_integral (S : Subring K) {a c : K} {y : K⟦X⟧} (ha : a ∈ S)
    {e : EndPair a y c} (he : IntegralPair S e) (z : ℤ) :
    ∃ h : EndPair a y ((z:K)*c), IntegralPair S h := by
  cases z with
  | ofNat n =>
    obtain ⟨h, hh⟩ := exists_nat_integral S ha he n
    refine ⟨EndomorphismWork.EndPair.cast (by simp) h, ?_⟩
    exact integral_cast S _ hh
  | negSucc n =>
    obtain ⟨h, hh⟩ := exists_nat_integral S ha he (n+1)
    refine ⟨EndomorphismWork.EndPair.cast (by push_cast; ring) (EndomorphismWork.EndPair.neg h), ?_⟩
    exact integral_cast S _ (integral_neg S hh)

lemma endPair_integral (S : Subring K) (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y^2 = 1-2*C a*X^2+X^4) (ha : a ∈ S) (hw : w ∈ S) (hym : y ∈ coefficients S)
    (hw1 : a*w^2 = a+3) (hw2 : w^4 = 8*(a+1)) (u v : ℤ)
    (e : EndPair a y ((u:K)+(v:K)*w)) : IntegralPair S e := by
  obtain ⟨e1, he1⟩ := exists_int_integral S ha (integral_ident S a y hy0 hy hym) u
  obtain ⟨e2, he2⟩ := exists_int_integral S ha (integral_cm S a w y hy0 hy hw hym hw1 hw2) v
  let h := EndomorphismWork.EndPair.cast (show ((u:K)*1+(v:K)*w) = (u:K)+(v:K)*w by ring) (e1.add e2)
  have hh : IntegralPair S h := integral_cast S _ (add_integral S ha he1 he2)
  have heq := EndomorphismWork.EndPair.unique_f hy0 hy e h
  have hYeq : e.Y = h.Y := EndomorphismWork.sq_unique e.Y0 h.Y0 (by rw [e.curve, h.curve, heq])
  exact ⟨heq ▸ hh.1, hYeq ▸ hh.2⟩

end IntegralWork

end

section

namespace O7Work
open QuadraticAlgebra

abbrev O := QuadraticAlgebra ℤ (-2) 1
abbrev F := QuadraticAlgebra ℚ (-2) 1

instance irreducible_quad : Fact (∀ r : ℚ, r ^ 2 ≠ -2 + 1 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg (2 * r - 1)]⟩

lemma norm_O (z : O) : z.norm = z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2 := by
  simp [QuadraticAlgebra.norm_def]; ring

lemma norm_F (z : F) : z.norm = z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2 := by
  simp [QuadraticAlgebra.norm_def]; ring

lemma norm_nonneg (z : O) : 0 ≤ z.norm := by
  rw [norm_O]
  nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]

lemma norm_eq_zero (z : O) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [norm_O] at hz
    have hi : z.im = 0 := by
      have : z.im ^ 2 = 0 := by nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
      exact pow_eq_zero this
    have hr : z.re = 0 := by simpa [hi] using hz
    ext <;> simp [hr, hi]
  · rintro rfl
    simp

lemma norm_pos {z : O} (hz : z ≠ 0) : 0 < z.norm :=
  lt_of_le_of_ne (norm_nonneg z) (Ne.symm (mt (norm_eq_zero z).mp hz))

def toF : O →+* F where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring

@[simp] lemma toF_re (z : O) : (toF z).re = z.re := rfl
@[simp] lemma toF_im (z : O) : (toF z).im = z.im := rfl

lemma toF_injective : Function.Injective toF := by
  intro x y h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  simp only [toF_re, toF_im] at hr hi
  ext
  · exact_mod_cast hr
  · exact_mod_cast hi

@[simp] lemma norm_toF (z : O) : (toF z).norm = (z.norm : ℚ) := by
  simp [norm_F, norm_O]

noncomputable def nearest (z : F) : O :=
  let v := round z.im
  ⟨round (z.re + (z.im - v) / 2), v⟩

lemma nearest_error (z : F) : (z - toF (nearest z)).norm < 1 := by
  have hs := abs_sub_round z.im
  have ht := abs_sub_round (z.re + (z.im - (round z.im : ℚ)) / 2)
  have hs' := (abs_le.mp hs)
  have ht' := (abs_le.mp ht)
  have hs2 : (z.im - (round z.im : ℚ)) ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith [hs'.1] : 0 ≤ z.im - (round z.im : ℚ) + 1 / 2)
      (by linarith [hs'.2] : 0 ≤ 1 / 2 - (z.im - (round z.im : ℚ)))]
  have ht2 : (z.re + (z.im - (round z.im : ℚ)) / 2 -
      (round (z.re + (z.im - (round z.im : ℚ)) / 2) : ℚ)) ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith [ht'.1] : 0 ≤ z.re + (z.im - (round z.im : ℚ)) / 2 -
      (round (z.re + (z.im - (round z.im : ℚ)) / 2) : ℚ) + 1 / 2)
      (by linarith [ht'.2] : 0 ≤ 1 / 2 - (z.re + (z.im - (round z.im : ℚ)) / 2 -
      (round (z.re + (z.im - (round z.im : ℚ)) / 2) : ℚ)))]
  simp only [norm_F, re_sub, im_sub, toF_re, toF_im, nearest]
  nlinarith

noncomputable instance : Div O := ⟨fun x y => nearest (toF x / toF y)⟩
noncomputable instance : Mod O := ⟨fun x y => x - y * (x / y)⟩

lemma div_def (x y : O) : x / y = nearest (toF x / toF y) := rfl
lemma mod_def (x y : O) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : O) {y : O} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hyF : toF y ≠ 0 := by
    intro h
    apply hy
    apply toF_injective
    simpa using h
  have heq : toF (x % y) = toF y * (toF x / toF y - toF (x / y)) := by
    simp only [mod_def, map_sub, map_mul]
    field_simp
  have hn : 0 < (toF y).norm := by
    rw [norm_toF]
    exact_mod_cast norm_pos hy
  have h : (toF (x % y)).norm < (toF y).norm := by
    rw [heq, map_mul]
    have herr : (toF x / toF y - toF (x / y)).norm < 1 := by
      exact nearest_error (toF x / toF y)
    nlinarith
  simpa only [norm_toF, Int.cast_lt] using h

lemma norm_natAbs (z : O) : (z.norm.natAbs : ℤ) = z.norm :=
  Int.natAbs_of_nonneg (norm_nonneg z)

noncomputable instance euclideanDomain : EuclideanDomain O :=
  { inferInstanceAs (CommRing O), inferInstanceAs (Nontrivial O) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro x
      simp only [div_def, map_zero, div_zero, nearest]
      norm_num
      rfl
    quotient_mul_add_remainder_eq := by intro x y; simp only [mod_def]; ring
    r := fun x y => x.norm.natAbs < y.norm.natAbs
    r_wellFounded := (measure (fun x : O => x.norm.natAbs)).wf
    remainder_lt := by
      intro x y hy
      apply Int.ofNat_lt.mp
      simpa only [norm_natAbs] using norm_mod_lt x hy
    mul_left_not_lt := by
      intro x y hy
      apply not_lt_of_ge
      rw [map_mul, Int.natAbs_mul]
      apply le_mul_of_one_le_right (Nat.zero_le _)
      apply Int.ofNat_le.mp
      rw [norm_natAbs]
      exact norm_pos hy }

lemma isUnit_iff_norm_eq_one (z : O) : IsUnit z ↔ z.norm = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  have hn := norm_nonneg z
  omega


lemma exists_norm_prime_of_not_irreducible {p : ℕ} (hp : p.Prime)
    (hpi : ¬Irreducible (p : O)) : ∃ z : O, z.norm = p := by
  have hpu : ¬IsUnit (p : O) := by
    rw [isUnit_iff_norm_eq_one, QuadraticAlgebra.norm_natCast]
    have h2 := hp.two_le
    norm_cast
    nlinarith
  obtain ⟨a, b, hab, hau, hbu⟩ :
      ∃ a b : O, (p : O) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  have ha1 : a.norm.natAbs ≠ 1 := by
    intro h
    apply hau
    rw [isUnit_iff_norm_eq_one]
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simpa only [norm_natAbs, Nat.cast_one] using this
  have hb1 : b.norm.natAbs ≠ 1 := by
    intro h
    apply hbu
    rw [isUnit_iff_norm_eq_one]
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simpa only [norm_natAbs, Nat.cast_one] using this
  have hn : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
    have h := congrArg (fun z : O => z.norm.natAbs) hab
    simpa only [QuadraticAlgebra.norm_natCast, map_mul, Int.natAbs_mul,
      Int.natAbs_pow, Int.natAbs_natCast] using h.symm
  have h := (hp.mul_eq_prime_sq_iff ha1 hb1).mp hn
  refine ⟨a, ?_⟩
  have hh := congrArg (fun n : ℕ => (n : ℤ)) h.1
  simpa only [norm_natAbs] using hh

lemma exists_norm_prime_of_root {p : ℕ} (hp : p.Prime)
    (s : ZMod p) (hs : s ^ 2 - s + 2 = 0) : ∃ z : O, z.norm = p := by
  letI : Fact p.Prime := ⟨hp⟩
  apply exists_norm_prime_of_not_irreducible hp
  intro hpi
  have pp : Prime (p : O) := hpi.prime
  let t : ℤ := s.val
  have hs' : (p : ℤ) ∣ t ^ 2 - t + 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [t, ZMod.natCast_zmod_val] using hs
  have hd : (p : O) ∣ ((t : O) - omega) * ((t : O) - star omega) := by
    obtain ⟨c, hc⟩ := hs'
    refine ⟨(c : O), ?_⟩
    have hh : ((t : O) - omega) * ((t : O) - star omega) =
        ((t ^ 2 - t + 2 : ℤ) : O) := by
      ext <;> simp [pow_two] <;> ring
    rw [hh, hc]
    push_cast
    rfl
  have hnot1 : ¬ (p : ℤ) ∣ 1 := by
    exact_mod_cast hp.not_dvd_one
  rcases pp.dvd_mul.mp hd with h | h
  · obtain ⟨z, hz⟩ := h
    have hh := congrArg QuadraticAlgebra.im hz
    simp only [im_sub, im_intCast, omega_im, zero_sub, im_mul, im_natCast,
      re_natCast, zero_mul, add_zero, mul_zero] at hh
    apply hnot1
    have : (p : ℤ) ∣ -1 := ⟨z.im, hh⟩
    simpa using this
  · obtain ⟨z, hz⟩ := h
    have hh := congrArg QuadraticAlgebra.im hz
    simp only [im_sub, im_intCast, im_star, omega_im, neg_neg, sub_neg_eq_add,
      zero_add, im_mul, im_natCast, re_natCast, zero_mul, add_zero, mul_zero] at hh
    exact hnot1 ⟨z.im, hh⟩


lemma root_of_split_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsplit : p % 7 ∈ ({1, 2, 4} : Set ℕ)) :
    ∃ s : ZMod p, s ^ 2 - s + 2 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hsq7 : IsSquare (p : ZMod 7) := by
    rw [← ZMod.natCast_mod p 7]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsplit
    rcases hsplit with h | h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨3, by decide⟩
    · rw [h]; exact ⟨2, by decide⟩
  have hchar := (FiniteField.isSquare_odd_prime_iff (F := ZMod 7)
    (by norm_num [ZMod.ringChar_zmod_n]) hp2).mp hsq7
  have hn : quadraticChar (ZMod p) (-7) ≠ -1 := by
    have hc : ZMod.χ₄ (7 : ZMod 4) = (-1 : ℤ) := by decide
    simpa only [ZMod.card, Nat.cast_ofNat, hc, Int.cast_neg, Int.cast_one, neg_one_mul] using hchar
  have hsq : IsSquare (-7 : ZMod p) := by
    by_contra h
    exact hn (quadraticChar_neg_one_iff_not_isSquare.mpr h)
  obtain ⟨r, hr⟩ := hsq.exists_sq
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  refine ⟨(1 + r) / 2, ?_⟩
  field_simp
  linear_combination -hr

lemma exists_norm_split_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsplit : p % 7 ∈ ({1, 2, 4} : Set ℕ)) : ∃ z : O, z.norm = p := by
  obtain ⟨s, hs⟩ := root_of_split_prime hp hp2 hsplit
  exact exists_norm_prime_of_root hp s hs

end O7Work

end

section

namespace PadicSetupWork
open Polynomial
variable {p : ℕ} [Fact p.Prime]

lemma root_derivative_ne_zero (hp7 : p ≠ 7) (s : ZMod p) (hs : s^2-s+2 = 0) : 2*s-1 ≠ 0 := by
  intro hh
  have h7 : (7:ZMod p) = 0 := by linear_combination 4*hs-(2*s-1)*hh
  have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).mp h7
  exact hp7 ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd |>.resolve_left ((Fact.out : p.Prime).ne_one))

lemma hensel_root (hp7 : p ≠ 7) (s : ZMod p) (hs : s^2-s+2 = 0) :
    ∃ w : ℤ_[p], w^2-w+2 = 0 := by
  let z : ℤ := s.val
  let F : Polynomial ℤ := X^2-X+2
  have hdiv : (p:ℤ) ∣ z^2-z+2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [z] using hs
  have hnotdiv : ¬ (p:ℤ) ∣ 2*z-1 := by
    intro hh
    have hh' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh
    apply root_derivative_ne_zero hp7 s hs
    simpa [z] using hh'
  have hnF : ‖F.aeval (z:ℤ_[p])‖ < 1 := by
    have hh := PadicInt.norm_intCast_lt_one_iff (p := p) (z := z^2-z+2) |>.mpr hdiv
    simpa [F, map_ofNat] using hh
  have hnD : ‖F.derivative.aeval (z:ℤ_[p])‖ = 1 := by
    have hnorm : ¬ ‖((2*z-1:ℤ):ℤ_[p])‖ < 1 := by
      rw [PadicInt.norm_intCast_lt_one_iff]
      exact hnotdiv
    have hh : ‖((2*z-1:ℤ):ℤ_[p])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt hnorm)
    simpa [F, derivative_pow, map_ofNat] using hh
  obtain ⟨w, hw, _⟩ := hensels_lemma (F := F) (a := (z:ℤ_[p])) (by rw [hnD, one_pow]; exact hnF)
  exact ⟨w, by simpa [F, map_ofNat] using hw⟩

lemma norm_prime_im_ne_zero {p : ℕ} (hp : p.Prime) (z : O7Work.O) (hz : z.norm = p) : z.im ≠ 0 := by
  intro hi
  rw [O7Work.norm_O, hi] at hz
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hz
  have hh := congrArg Int.natAbs hz
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hh
  exact hp.not_isSquare ⟨z.re.natAbs, by simpa only [pow_two] using hh.symm⟩

lemma norm_prime_parity {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (z : O7Work.O) (hz : z.norm = p) :
    Odd z.re ∧ Even z.im := by
  have hpodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  rw [O7Work.norm_O] at hz
  have hh := congrArg (fun x : ℤ => x % 2) hz
  have hre := Int.emod_nonneg z.re (by decide : (2:ℤ) ≠ 0)
  have hre' := Int.emod_lt_of_pos z.re (by decide : (0:ℤ) < 2)
  have him := Int.emod_nonneg z.im (by decide : (2:ℤ) ≠ 0)
  have him' := Int.emod_lt_of_pos z.im (by decide : (0:ℤ) < 2)
  simp only [pow_two] at hh
  rw [Int.add_emod, Int.add_emod (z.re*z.re) (z.re*z.im) 2, Int.mul_emod z.re z.re, Int.mul_emod z.re z.im,
    Int.mul_emod 2 (z.im*z.im)] at hh
  norm_num only [Int.emod_self, zero_mul, Int.zero_emod, Int.emod_emod, add_zero,
    Int.natCast_emod, hpodd, Nat.cast_one] at hh
  have hmodp : (p:ℤ)%2 = 1 := by exact_mod_cast hpodd
  rw [hmodp] at hh
  have hr : z.re % 2 = 1 := by
    interval_cases hr : z.re % 2 <;> interval_cases hi : z.im % 2 <;> norm_num [hr] at * <;> omega
  have hi : z.im % 2 = 0 := by
    by_contra hne
    have hi1 : z.im % 2 = 1 := by omega
    rw [hr, hi1] at hh
    norm_num at hh
  exact ⟨Int.odd_iff.mpr hr, Int.even_iff.mpr hi⟩

section Evaluation
variable {K : Type*} [Field K] [CharZero K]

noncomputable def evalF (w : K) (hw : w^2-w+2 = 0) : O7Work.F →ₐ[ℚ] K :=
  QuadraticAlgebra.lift ⟨w, by simp only [Algebra.smul_def, map_neg, map_ofNat, map_one]; linear_combination hw⟩

lemma evalF_apply (w : K) (hw : w^2-w+2 = 0) (z : O7Work.F) :
    evalF w hw z = algebraMap ℚ K z.re + algebraMap ℚ K z.im * w := by
  simp [evalF, QuadraticAlgebra.lift, Algebra.smul_def]

lemma evalF_nonrational (w : K) (hw : w^2-w+2 = 0) (z : O7Work.O) (hz : z.im ≠ 0) :
    ∀ q : ℚ, algebraMap ℚ K q ≠ (z.re:K)+(z.im:K)*w := by
  intro q hq
  let φ := evalF w hw
  have hh : φ (algebraMap ℚ O7Work.F q) = φ (O7Work.toF z) := by
    rw [φ.commutes]
    simpa only [φ, evalF_apply, O7Work.toF_re, O7Work.toF_im, map_intCast] using hq
  have hh' := (RingHom.injective φ.toRingHom) hh
  have hi := congrArg QuadraticAlgebra.im hh'
  simp only [QuadraticAlgebra.algebraMap_im, O7Work.toF_im] at hi
  exact hz (by exact_mod_cast hi.symm)

lemma trace_identity (w : K) (hw : w^2-w+2 = 0) (z : O7Work.O) :
    ((z.re:K)+(z.im:K)*w)^2-((2*z.re+z.im:ℤ):K)*((z.re:K)+(z.im:K)*w)+(z.norm:K) = 0 := by
  rw [O7Work.norm_O]
  push_cast
  linear_combination (z.im:K)^2*hw

end Evaluation

lemma choose_nonunit_factor (x y : ℤ_[p]) (hxy : x*y = p) :
    (IsUnit y ∧ ¬IsUnit x) ∨ (IsUnit x ∧ ¬IsUnit y) := by
  have hirr := PadicInt.irreducible_p (p := p)
  have hh := hirr.isUnit_or_isUnit hxy.symm
  have hnot : ¬ (IsUnit x ∧ IsUnit y) := by
    rintro ⟨hx, hy⟩
    exact hirr.not_isUnit (hxy ▸ hx.mul hy)
  tauto

lemma split_scalar (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hmod : p % 7 ∈ ({1,2,4}:Set ℕ)) :
    ∃ (w : ℤ_[p]) (z : O7Work.O),
      w^2-w+2 = 0 ∧ z.norm = p ∧ Odd z.re ∧ Even z.im ∧ z.im ≠ 0 ∧
      IsUnit ((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w)) ∧
      ¬ IsUnit ((z.re:ℤ_[p])+(z.im:ℤ_[p])*w) := by
  obtain ⟨s, hs⟩ := O7Work.root_of_split_prime (Fact.out : p.Prime) hp2 hmod
  obtain ⟨w, hw⟩ := hensel_root hp7 s hs
  obtain ⟨z, hz⟩ := O7Work.exists_norm_split_prime (Fact.out : p.Prime) hp2 hmod
  have hprod : ((z.re:ℤ_[p])+(z.im:ℤ_[p])*w)*((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w)) = p := by
    have hn := congrArg (fun x:ℤ => (x:ℤ_[p])) hz
    rw [O7Work.norm_O] at hn
    push_cast at hn
    linear_combination hn-(z.im:ℤ_[p])^2*hw
  rcases choose_nonunit_factor _ _ hprod with hh | hh
  · exact ⟨w,z,hw,hz,(norm_prime_parity Fact.out hp2 z hz).1,
      (norm_prime_parity Fact.out hp2 z hz).2,norm_prime_im_ne_zero Fact.out z hz,hh⟩
  · refine ⟨1-w,z,?_,hz,(norm_prime_parity Fact.out hp2 z hz).1,
      (norm_prime_parity Fact.out hp2 z hz).2,norm_prime_im_ne_zero Fact.out z hz,?_,hh.2⟩
    · linear_combination hw
    · simpa only [sub_sub_cancel] using hh.1

end PadicSetupWork

end

section

namespace LegendreWork
open Polynomial Finset
open scoped BigOperators

noncomputable def d (n k : ℕ) : ℤ := n.choose k * (n + k).choose k

lemma d_zero (n : ℕ) : d n 0 = 1 := by simp [d]
lemma d_eq_zero {n k : ℕ} (h : n < k) : d n k = 0 := by
  simp [d, Nat.choose_eq_zero_of_lt h]

lemma d_recur (n k : ℕ) :
    (k + 1 : ℤ) ^ 2 * d n (k + 1) =
      ((n : ℤ) * (n + 1) - k * (k + 1)) * d n k := by
  by_cases hkn : k ≤ n
  · have h₁ : (n.choose (k + 1) : ℤ) * (k + 1) = n.choose k * (n - k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    have h₂ : (n + k + 1 : ℤ) * (n + k).choose k =
        ((n + k + 1).choose (k + 1) : ℤ) * (k + 1) := by
      exact_mod_cast Nat.succ_mul_choose_eq (n + k) k
    rw [Nat.cast_sub hkn] at h₁
    simp only [Nat.add_assoc] at h₂
    simp only [d, Nat.add_assoc]
    linear_combination (k + 1 : ℤ) * ((n + (k + 1)).choose (k + 1) : ℤ) * h₁ -
      (n.choose k : ℤ) * ((n : ℤ) - k) * h₂
  · have hn : n < k := by omega
    rw [d_eq_zero hn, d_eq_zero (by omega : n < k + 1)]
    ring

noncomputable def L (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (d n k) * X ^ k

noncomputable def R (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (d n k * Nat.centralBinom k) * X ^ k

lemma coeff_L (n k : ℕ) : (L n).coeff k = d n k := by
  simp only [L, finset_sum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < n + 1
  · simp [hk]
  · simp [hk, d_eq_zero (by omega : n < k)]

lemma coeff_R (n k : ℕ) : (R n).coeff k = d n k * Nat.centralBinom k := by
  simp only [R, finset_sum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < n + 1
  · simp [hk]
  · simp [hk, d_eq_zero (by omega : n < k)]

noncomputable def theta (P : ℤ[X]) : ℤ[X] := X * derivative P

lemma coeff_theta (P : ℤ[X]) (k : ℕ) : (theta P).coeff k = (k : ℤ) * P.coeff k := by
  cases k with
  | zero => simp [theta]
  | succ k => simp [theta, coeff_X_mul, coeff_derivative, mul_comm]

lemma theta_add (P Q : ℤ[X]) : theta (P + Q) = theta P + theta Q := by
  simp [theta, mul_add]
lemma theta_sub (P Q : ℤ[X]) : theta (P - Q) = theta P - theta Q := by
  simp [theta, mul_sub]
lemma theta_C_mul (c : ℤ) (P : ℤ[X]) : theta (C c * P) = C c * theta P := by
  simp [theta]; ring

lemma ode_L (n : ℕ) :
    theta (theta (L n)) - X *
      (C ((n : ℤ) * (n + 1)) * L n - theta (theta (L n)) - theta (L n)) = 0 := by
  ext k
  cases k with
  | zero => simp [coeff_sub, coeff_theta]
  | succ k =>
      simp only [coeff_sub, coeff_X_mul, coeff_C_mul, coeff_theta, coeff_L, coeff_zero,
        Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]
      linear_combination d_recur n k

lemma coeff_R_recur (n k : ℕ) :
    (k + 1 : ℤ) ^ 3 * (R n).coeff (k + 1) =
      2 * (2 * k + 1) * ((n : ℤ) * (n + 1) - k * (k + 1)) * (R n).coeff k := by
  have h₁ := d_recur n k
  have h₂ : (k + 1 : ℤ) * Nat.centralBinom (k + 1) =
      2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  rw [coeff_R, coeff_R]
  linear_combination (k + 1 : ℤ) * (Nat.centralBinom (k + 1) : ℤ) * h₁ +
    (((n : ℤ) * (n + 1) - k * (k + 1)) * d n k) * h₂

lemma ode_R (n : ℕ) :
    theta (theta (theta (R n))) + 2 * X *
      (2 * theta (theta (theta (R n))) + 3 * theta (theta (R n)) +
        C (1 - 2 * (n : ℤ) * (n + 1)) * theta (R n) -
        C ((n : ℤ) * (n + 1)) * R n) = 0 := by
  ext k
  cases k with
  | zero => simp [coeff_theta, mul_assoc, coeff_add]
  | succ k =>
      rw [mul_comm (2 : ℤ[X]) X, mul_assoc]
      simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_theta, coeff_zero,
        Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]
      simp only [show (2 : ℤ[X]) = C 2 by rfl, show (3 : ℤ[X]) = C 3 by rfl,
        coeff_C_mul, coeff_add, coeff_sub, coeff_theta]
      linear_combination coeff_R_recur n k


noncomputable def symOp (M : ℤ) (P : ℤ[X]) : ℤ[X] :=
  theta (theta (theta P)) +
  X * (C 2 * theta (theta (theta P)) + C 3 * theta (theta P) +
    C (1 - 4 * M) * theta P - C (2 * M) * P) +
  X ^ 2 * (theta (theta (theta P)) + C 3 * theta (theta P) +
    C (2 - 4 * M) * theta P - C (4 * M) * P)

lemma symOp_sub (M : ℤ) (P Q : ℤ[X]) : symOp M (P - Q) = symOp M P - symOp M Q := by
  simp only [symOp, theta_sub]
  ring

lemma symOp_unique_zero (M : ℤ) (P : ℤ[X]) (h0 : P.coeff 0 = 0)
    (hP : symOp M P = 0) : P = 0 := by
  have h1 : P.coeff 1 = 0 := by
    have hh := congrArg (fun Q : ℤ[X] => Q.coeff 1) hP
    simp only [symOp, coeff_add, coeff_sub, coeff_C_mul, coeff_theta, coeff_X_mul,
      coeff_zero, Nat.cast_one, Nat.cast_zero, zero_mul, mul_zero, sub_zero,
      one_mul, zero_add, add_zero, h0] at hh
    simpa [coeff_X_pow_mul'] using hh
  have hc : ∀ n, P.coeff n = 0 ∧ P.coeff (n + 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hh := congrArg (fun Q : ℤ[X] => Q.coeff (n + 2)) hP
      have hX : ∀ Q : ℤ[X], (X * Q).coeff (n + 2) = Q.coeff (n + 1) :=
        fun Q => coeff_X_mul Q (n + 1)
      simp only [symOp, coeff_add, coeff_sub, coeff_C_mul, coeff_theta, hX,
        coeff_X_pow_mul, coeff_zero, ih.1, ih.2, mul_zero, sub_zero, add_zero,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hh
      have hnon : ((n : ℤ) + 2) ^ 3 ≠ 0 := by positivity
      apply (mul_eq_zero.mp (show ((n : ℤ) + 2) ^ 3 * P.coeff (n + 1 + 1) = 0 by
        convert hh using 1 <;> ring)).resolve_left hnon
  ext n
  simpa using (hc n).1

lemma symOp_unique (M : ℤ) (P Q : ℤ[X]) (h0 : P.coeff 0 = Q.coeff 0)
    (hP : symOp M P = 0) (hQ : symOp M Q = 0) : P = Q := by
  apply sub_eq_zero.mp
  apply symOp_unique_zero M (P - Q)
  · simp [h0]
  · rw [symOp_sub, hP, hQ, sub_self]

lemma symOp_derivative (M : ℤ) (P : ℤ[X]) :
    symOp M P = X *
      ((X * (1 + X)) ^ 2 * derivative (derivative (derivative P)) +
        3 * (X * (1 + X)) * (1 + 2 * X) * derivative (derivative P) +
        (C (2 - 4 * M) * (X * (1 + X)) + (1 + 2 * X) ^ 2) * derivative P -
        C (2 * M) * (1 + 2 * X) * P) := by
  simp only [symOp, theta, derivative_mul, derivative_add, derivative_X,
    one_mul, derivative_C, zero_mul, zero_add, derivative_ofNat]
  simp only [map_sub, map_mul, map_add, map_one, map_ofNat]
  ring


lemma ode_L_derivative (n : ℕ) :
    (X * (1 + X)) * derivative (derivative (L n)) +
      (1 + 2 * X) * derivative (L n) - C ((n : ℤ) * (n + 1)) * L n = 0 := by
  have h : X * ((X * (1 + X)) * derivative (derivative (L n)) +
      (1 + 2 * X) * derivative (L n) - C ((n : ℤ) * (n + 1)) * L n) = 0 := by
    convert ode_L n using 1
    simp only [theta, derivative_mul, derivative_X, one_mul]
    ring
  exact (mul_eq_zero.mp h).resolve_left X_ne_zero

lemma symOp_sq_L (n : ℕ) : symOp ((n : ℤ) * (n + 1)) ((L n) ^ 2) = 0 := by
  have h := ode_L_derivative n
  have hd := congrArg derivative h
  rw [symOp_derivative]
  simp only [pow_two, derivative_add, derivative_sub, derivative_mul, derivative_X,
    derivative_C, derivative_ofNat, derivative_one, derivative_zero, mul_zero, zero_mul, add_zero,
    zero_add, mul_one, one_mul] at hd ⊢
  simp only [map_sub, map_mul, map_add, map_one, map_ofNat] at h hd ⊢
  linear_combination X * (2 * (X * (1 + X)) * L n) * hd +
    X * (6 * (X * (1 + X)) * derivative (L n) + 2 * (1 + 2 * X) * L n) * h

lemma ode_R_derivative (n : ℕ) :
    X ^ 2 * (1 + 4 * X) * derivative (derivative (derivative (R n))) +
      3 * X * (1 + 6 * X) * derivative (derivative (R n)) +
      (1 + C (12 - 4 * (n : ℤ) * (n + 1)) * X) * derivative (R n) -
      C (2 * (n : ℤ) * (n + 1)) * R n = 0 := by
  have h : X * (X ^ 2 * (1 + 4 * X) * derivative (derivative (derivative (R n))) +
      3 * X * (1 + 6 * X) * derivative (derivative (R n)) +
      (1 + C (12 - 4 * (n : ℤ) * (n + 1)) * X) * derivative (R n) -
      C (2 * (n : ℤ) * (n + 1)) * R n) = 0 := by
    convert ode_R n using 1
    simp only [theta, derivative_mul, derivative_add, derivative_X, one_mul,
      map_add, map_sub, map_mul, map_one, map_ofNat]
    ring
  exact (mul_eq_zero.mp h).resolve_left X_ne_zero

lemma symOp_comp_R (n : ℕ) :
    symOp ((n : ℤ) * (n + 1)) ((R n).comp (X * (1 + X))) = 0 := by
  have h := congrArg (fun P : ℤ[X] => P.comp (X * (1 + X))) (ode_R_derivative n)
  simp only [add_comp, sub_comp, mul_comp, pow_comp, C_comp, X_comp, zero_comp,
    one_comp, ofNat_comp] at h
  rw [symOp_derivative]
  simp only [derivative_comp, derivative_add, derivative_sub, derivative_mul,
    derivative_X, derivative_C, derivative_ofNat, derivative_one, derivative_zero,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
  simp only [map_sub, map_mul, map_add, map_one, map_ofNat, Nat.cast_ofNat] at h ⊢
  linear_combination X * (1 + 2 * X) * h

lemma clausen (n : ℕ) : (L n) ^ 2 = (R n).comp (X * (1 + X)) := by
  apply symOp_unique ((n : ℤ) * (n + 1))
  · simp only [coeff_zero_eq_eval_zero, eval_pow, eval_comp, eval_mul, eval_X, zero_mul]
    rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, coeff_L, coeff_R]
    simp [d_zero]
  · exact symOp_sq_L n
  · exact symOp_comp_R n


lemma d_contiguous (n k : ℕ) :
    (n + 1 - k : ℤ) * d (n + 1) k = (n + 1 + k : ℤ) * d n k := by
  by_cases hk : k ≤ n + 1
  · have h₁ : (n.choose k : ℤ) * (n + 1) =
        ((n + 1).choose k : ℤ) * (n + 1 - k : ℕ) := by
      exact_mod_cast Nat.choose_mul_succ_eq n k
    have h₂ : ((n + k).choose k : ℤ) * (n + k + 1) =
        ((n + k + 1).choose k : ℤ) * (n + 1) := by
      have hh := Nat.choose_mul_succ_eq (n + k) k
      rw [show n + k + 1 - k = n + 1 by omega] at hh
      exact_mod_cast hh
    simp only [Nat.cast_sub hk, Nat.cast_add, Nat.cast_one] at h₁
    simp only [show n + 1 + k = n + k + 1 by omega, d]
    linear_combination -((n + k + 1).choose k : ℤ) * h₁ - (n.choose k : ℤ) * h₂
  · rw [d_eq_zero (by omega : n + 1 < k), d_eq_zero (by omega : n < k)]
    ring

lemma d_diagonal (n : ℕ) : d n n = Nat.centralBinom n := by
  simp [d, Nat.centralBinom, two_mul]

lemma L_recur (n : ℕ) :
    C (n + 2 : ℤ) * L (n + 2) =
      C (2 * n + 3 : ℤ) * (1 + 2 * X) * L (n + 1) - C (n + 1 : ℤ) * L n := by
  ext k
  cases k with
  | zero => simp [coeff_L, d_zero]; ring
  | succ k =>
    have hexpand : C (2 * n + 3 : ℤ) * (1 + 2 * X) * L (n + 1) =
        C (2 * n + 3 : ℤ) * L (n + 1) +
          C (2 * (2 * n + 3) : ℤ) * (X * L (n + 1)) := by
      simp only [map_mul, map_add, map_ofNat]
      ring
    rw [hexpand]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_L]
    by_cases hk : k + 1 ≤ n + 1
    · have h₁ := d_contiguous n (k + 1)
      have h₂ := d_contiguous (n + 1) (k + 1)
      have h₃ := d_recur (n + 1) k
      simp only [Nat.cast_add, Nat.cast_one] at h₁ h₂ h₃
      have heq : ((n : ℤ) + 1 - k) * ((n : ℤ) + 2 + k) *
          ((n + 2 : ℤ) * d (n + 2) (k + 1) -
            ((2 * n + 3 : ℤ) * d (n + 1) (k + 1) +
              (2 * (2 * n + 3) : ℤ) * d (n + 1) k - (n + 1 : ℤ) * d n (k + 1))) = 0 := by
        linear_combination (n + 2 : ℤ) * (n + 2 + k : ℤ) * h₂ -
          (n + 1 : ℤ) * (n + 1 - k : ℤ) * h₁ + (2 * (2 * n + 3) : ℤ) * h₃
      have hn₁ : (n + 1 - k : ℤ) ≠ 0 := by omega
      have hn₂ : (n + 2 + k : ℤ) ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (mul_ne_zero hn₁ hn₂))
    · by_cases he : k = n + 1
      · subst k
        rw [d_eq_zero (by omega : n + 1 < n + 1 + 1),
          d_eq_zero (by omega : n < n + 1 + 1)]
        simp only [show n + 1 + 1 = n + 2 by omega, d_diagonal, mul_zero, zero_add, sub_zero]
        have h : (n + 2 : ℤ) * Nat.centralBinom (n + 2) =
            2 * (2 * n + 3 : ℤ) * Nat.centralBinom (n + 1) := by
          exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
        exact h
      · have hn : n + 2 < k + 1 := by omega
        rw [d_eq_zero hn, d_eq_zero (by omega : n + 1 < k + 1),
          d_eq_zero (by omega : n + 1 < k), d_eq_zero (by omega : n < k + 1)]
        ring

end LegendreWork

end

section

namespace GeneratingWork
open Finset PowerSeries
open scoped BigOperators PowerSeries

variable {K : Type*} [Field K] [CharZero K]

lemma eval₂_intCast (x : K) (z : ℤ) :
    (z : Polynomial ℤ).eval₂ (Int.castRingHom K) x = (z : K) := by
  exact map_intCast (Polynomial.eval₂RingHom (Int.castRingHom K) x) z

noncomputable def P (n : ℕ) (a : K) : K :=
  (LegendreWork.L n).eval₂ (Int.castRingHom K) ((a - 1) / 2)

@[simp] lemma P_zero (a : K) : P 0 a = 1 := by
  simp [P, LegendreWork.L, LegendreWork.d]

@[simp] lemma P_one (a : K) : P 1 a = a := by
  norm_num [P, LegendreWork.L, LegendreWork.d, Finset.sum_range_succ]
  ring

lemma P_recur (n : ℕ) (a : K) :
    (n + 2 : K) * P (n + 2) a =
      (2 * n + 3 : K) * a * P (n + 1) a - (n + 1 : K) * P n a := by
  have h := congrArg (fun Q : Polynomial ℤ => Q.eval₂ (Int.castRingHom K) ((a - 1) / 2))
    (LegendreWork.L_recur n)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    map_add, map_mul, map_natCast, map_ofNat, map_one, Polynomial.eval₂_natCast] at h
  simp only [P]
  linear_combination h

lemma P_recur' (n : ℕ) (a : K) :
    (n + 1 : K) * P (n + 1) a =
      (2 * n + 1 : K) * a * P n a - (n : K) * P (n - 1) a := by
  cases n with
  | zero => simp
  | succ n =>
      have h := P_recur n a
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      linear_combination h

lemma P_clausen (n : ℕ) (a : K) :
    P n a ^ 2 = ∑ k ∈ range (n + 1),
      (LegendreWork.d n k : K) * (Nat.centralBinom k : K) * ((a ^ 2 - 1) / 4) ^ k := by
  have h := congrArg (fun Q : Polynomial ℤ => Q.eval₂ (Int.castRingHom K) ((a - 1) / 2))
    (LegendreWork.clausen n)
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  have hx : (a - 1) / 2 * (1 + (a - 1) / 2) = (a ^ 2 - 1) / 4 := by ring
  rw [hx] at h
  simpa [P, LegendreWork.R, Polynomial.eval₂_finset_sum, map_mul, eval₂_intCast] using h

noncomputable def G (a : K) : K⟦X⟧ := mk (fun n => P n a)
@[simp] lemma coeff_G (a : K) (n : ℕ) : coeff n (G a) = P n a := coeff_mk _ _
@[simp] lemma const_G (a : K) : constantCoeff (G a) = 1 := by
  simp [← coeff_zero_eq_constantCoeff]

lemma coeff_X_mul (f : K⟦X⟧) (n : ℕ) : coeff (n + 1) (X * f) = coeff n f := by
  simpa using coeff_X_pow_mul f 1 n

lemma G_ode (a : K) :
    (1 - 2 * C a * X + X ^ 2) * (d⁄dX K (G a)) = (C a - X) * G a := by
  suffices hh : d⁄dX K (G a) - C a * G a +
      X * (G a - 2 * C a * d⁄dX K (G a)) + X ^ 2 * d⁄dX K (G a) = 0 by
    linear_combination hh
  ext n
  cases n with
  | zero =>
    have hD0 : constantCoeff (d⁄dX K (G a)) = a := by
      rw [← coeff_zero_eq_constantCoeff, coeff_derivative]
      simp
    simp [hD0]
  | succ n =>
    cases n with
    | zero =>
      have h := P_recur 0 a
      simp only [map_add, map_sub, coeff_X_mul, coeff_C_mul, coeff_derivative,
        map_zero, coeff_G, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
        P_zero, P_one, mul_one] at *
      have hz : coeff 1 (X ^ 2 * d⁄dX K (G a)) = 0 := by
        simp [coeff_X_pow_mul']
      rw [hz]
      have ht : coeff 0 (2 * C a * d⁄dX K (G a)) = 2 * a ^ 2 := by
        rw [mul_assoc]
        change coeff 0 (C 2 * (C a * d⁄dX K (G a))) = _
        simp only [coeff_C_mul, coeff_derivative, coeff_G]
        simp
        ring
      rw [ht]
      linear_combination h
    | succ n =>
      have h := P_recur' (n + 2) a
      simp only [Nat.succ_eq_add_one, Nat.add_assoc] at *
      have hX : ∀ f : K⟦X⟧, coeff (n + 2) (X * f) = coeff (n + 1) f :=
        fun f => coeff_X_mul f (n + 1)
      simp only [map_add, map_sub, hX, coeff_C_mul, coeff_X_pow_mul, coeff_derivative,
        map_zero, coeff_G, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      have ht : coeff (n + 1) (2 * C a * d⁄dX K (G a)) =
          2 * a * (P (n + 2) a * (n + 2 : K)) := by
        rw [mul_assoc]
        change coeff (n + 1) (C 2 * (C a * d⁄dX K (G a))) = _
        simp only [coeff_C_mul, coeff_derivative, coeff_G, Nat.cast_add, Nat.cast_one]
        ring
      rw [ht]
      simp only [Nat.cast_add, Nat.cast_ofNat, show n + 2 - 1 = n + 1 by omega] at h
      linear_combination h

lemma G_sq (a : K) : (G a) ^ 2 * (1 - 2 * C a * X + X ^ 2) = 1 := by
  apply PowerSeries.derivative.ext
  · have h := G_ode a
    simp only [show (2 : K⟦X⟧) = C 2 by rfl, pow_two, map_add, map_sub, derivative_X,
      derivative_C, Derivation.map_one_eq_zero, Derivation.leibniz, smul_eq_mul, mul_zero,
      zero_mul, zero_add, add_zero, mul_one, one_mul] at *
    simp only [map_ofNat] at *
    linear_combination 2 * G a * h
  · simp

noncomputable def Gquartic (a : K) : K⟦X⟧ := expand 2 (by decide) (G a)

@[simp] lemma coeff_Gquartic_even (a : K) (n : ℕ) : coeff (2 * n) (Gquartic a) = P n a := by
  simp [Gquartic]

@[simp] lemma const_Gquartic (a : K) : constantCoeff (Gquartic a) = 1 := by
  simp [Gquartic]

lemma Gquartic_sq (a : K) :
    (Gquartic a) ^ 2 * (1 - 2 * C a * X ^ 2 + X ^ 4) = 1 := by
  have h := congrArg (expand (R := K) 2 (by decide)) (G_sq a)
  simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, expand_C, expand_X] at h
  simpa only [Gquartic, ← pow_mul, show 2 * 2 = 4 by rfl] using h

end GeneratingWork

end

section

namespace CMRationalWork
open PowerSeries AdditionWork
open scoped PowerSeries
variable {K : Type*} [Field K] [CharZero K]

lemma cm_parameters (w : K) (hw : w^2-w+2 = 0) :
    let a := -3*(w+2)/8
    a*w^2 = a+3 ∧ w^4 = 8*(a+1) ∧ a^2 ≠ 1 ∧ w ≠ 0 := by
  let a := -3*(w+2)/8
  obtain ⟨hh1, hh2⟩ := CMWork.cm_parameters a w hw (by dsimp [a]; ring)
  have h1 : a*w^2 = a+3 := by
    have hh := (mul_eq_zero.mp hh1).resolve_left (by norm_num : (8:K) ≠ 0)
    linear_combination hh
  have hmin : 8*a^2+15*a+9 = 0 := by
    dsimp [a]
    linear_combination (9/8:K)*hw
  have ha : a^2 ≠ 1 := by
    intro hh
    have hh' : a^2 = (1:K)^2 := by simpa using hh
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh' with hh | hh
    · rw [hh] at hmin
      norm_num at hmin
    · rw [hh] at hmin
      norm_num at hmin
  have hw0 : w ≠ 0 := by intro hh; rw [hh] at hw; norm_num at hw
  exact ⟨h1,sub_eq_zero.mp hh2,ha,hw0⟩

lemma nonrational_ne_zero {c : K} (hc : ∀q:ℚ, algebraMap ℚ K q ≠ c) : c ≠ 0 := by
  simpa only [map_zero, ne_eq, eq_comm] using hc 0

lemma nonrational_sq_ne_one {c : K} (hc : ∀q:ℚ, algebraMap ℚ K q ≠ c) : c^2 ≠ 1 := by
  intro hh
  have hh' : c^2 = (1:K)^2 := by simpa using hh
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh' with hh | hh
  · exact hc 1 (by simpa using hh.symm)
  · exact hc (-1) (by simpa using hh.symm)

lemma inverse_sqrt (a : K) : GeneratingWork.Gquartic a * PSWork.sqrtQuartic a = 1 := by
  apply EndomorphismWork.sq_unique
  · simp [PSWork.sqrtQuartic_const]
  · simp
  · rw [mul_pow, PSWork.sqrtQuartic_sq]
    simpa using GeneratingWork.Gquartic_sq a

lemma endPair_differential {a c : K} (e : EndPair a (PSWork.sqrtQuartic a) c) :
    subst e.f (GeneratingWork.Gquartic a) * d⁄dX K e.f = C c * GeneratingWork.Gquartic a := by
  have hy := inverse_sqrt a
  have hy0 := PSWork.sqrtQuartic_const a
  have hysq := PSWork.sqrtQuartic_sq a
  have hY := EndomorphismWork.EndPair.Y_eq_subst hy0 hysq e
  have hs := congrArg (substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' e.f0)) hy
  simp only [map_mul, map_one, coe_substAlgHom, ← hY] at hs
  calc
    subst e.f (GeneratingWork.Gquartic a) * d⁄dX K e.f =
        subst e.f (GeneratingWork.Gquartic a) * (d⁄dX K e.f * PSWork.sqrtQuartic a) *
          GeneratingWork.Gquartic a := by linear_combination -(subst e.f (GeneratingWork.Gquartic a) * d⁄dX K e.f)*hy
    _ = C c * GeneratingWork.Gquartic a := by rw [e.diff]; linear_combination C c*GeneratingWork.Gquartic a*hs

lemma Gquartic_integral (S : Subring K) {a : K} (hhalf : (1/2:K) ∈ S) (ha : a ∈ S) :
    GeneratingWork.Gquartic a ∈ IntegralWork.coefficients S := by
  have hi := IntegralWork.inv_mem (IntegralWork.sqrtQuartic_mem S hhalf ha)
    (by rw [PSWork.sqrtQuartic_const, inv_one]; exact S.one_mem)
  have heq : GeneratingWork.Gquartic a = (PSWork.sqrtQuartic a)⁻¹ := by
    have hh := inverse_sqrt a
    have h0 : constantCoeff (PSWork.sqrtQuartic a) ≠ 0 := by rw [PSWork.sqrtQuartic_const]; exact one_ne_zero
    calc
      GeneratingWork.Gquartic a = GeneratingWork.Gquartic a * (PSWork.sqrtQuartic a * (PSWork.sqrtQuartic a)⁻¹) := by
        rw [PowerSeries.mul_inv_cancel _ h0, mul_one]
      _ = _ := by rw [← mul_assoc, hh, one_mul]
  rwa [heq]

lemma exists_rational_prime_map (w : K) (hw : w^2-w+2 = 0) (z : O7Work.O)
    (hz0 : z.im ≠ 0) (hu : Odd z.re) (hv : Even z.im) (p : ℕ) (hp : Odd p) (hnorm : z.norm = p) :
    let a := -3*(w+2)/8
    let c := (z.re:K)+(z.im:K)*w
    ∃ (e : EndPair a (PSWork.sqrtQuartic a) c) (N D : Polynomial K) (eps : K),
      e.f*(D:K⟦X⟧) = N ∧ D.eval 0 ≠ 0 ∧ IsCoprime N D ∧
      N.natDegree = p ∧ D.natDegree+1 = p ∧ eps^2 = 1 ∧
      N = Polynomial.C eps*Polynomial.X*D.reverse ∧ D = Polynomial.C eps*N.reverse := by
  let a := -3*(w+2)/8
  let c := (z.re:K)+(z.im:K)*w
  have hcR := PadicSetupWork.evalF_nonrational w hw z hz0
  have hc0 : c ≠ 0 := nonrational_ne_zero hcR
  have hc1 : c^2 ≠ 1 := nonrational_sq_ne_one hcR
  obtain ⟨hw1, hw2, ha, hw0⟩ := cm_parameters w hw
  have hy0 := PSWork.sqrtQuartic_const a
  have hysq := PSWork.sqrtQuartic_sq a
  obtain ⟨e, he⟩ := RationalWork.exists_odd_even_map a w (PSWork.sqrtQuartic a) hy0 hysq hw1 hw2 z.re z.im hu hv
  obtain ⟨N,D,hDmon,hcop,hD0,hrep⟩ := RepresentationWork.reduced_rep he.1
  have hD : D ≠ 0 := hDmon.ne_zero
  have he1 : coeff 1 e.f = c := EndomorphismWork.EndPair.coeff_one hy0 e
  have hN : N ≠ 0 := by
    intro hh
    rw [hh, Polynomial.coe_zero] at hrep
    have hD' : (D:K⟦X⟧) ≠ 0 := fun hz => hD (Polynomial.coe_injective K (by simpa using hz))
    have he0 := (mul_eq_zero.mp hrep).resolve_right hD'
    rw [he0, map_zero] at he1
    exact hc0 he1.symm
  have hN0 : N.coeff 0 = 0 := by
    have hh := congrArg (constantCoeff (R := K)) hrep
    simpa only [map_mul, e.f0, zero_mul, Polynomial.constantCoeff_coe] using hh.symm
  obtain ⟨hDeven,hNodd⟩ := RepresentationWork.reduced_odd (RepresentationWork.endPair_odd hy0 hysq e)
    hDmon hcop hD0 hrep
  obtain ⟨hDpar,hNpar⟩ := RepresentationWork.reduced_degree_parity hN hD hDeven hNodd
  have hne : N.natDegree ≠ D.natDegree := by intro hh; rw [hh] at hNpar; exact (Nat.not_even_iff_odd.mpr hNpar) hDpar
  have hode := RepresentationWork.polynomial_ode hysq e hrep
  have hmin : c^2-((2*z.re+z.im:ℤ):K)*c+(p:K) = 0 := by
    have hh := PadicSetupWork.trace_identity w hw z
    simpa only [hnorm, Int.cast_natCast] using hh
  have hmax := NormDegreeWork.norm_degree_general N D a c hN hD hc0 ha hc1 hne hcop hcR (2*z.re+z.im) p hmin hode
  have hgap : D.natDegree+1=N.natDegree := by
    rcases DegreeWork.degree_difference_one N D a c hN hD hc0 hne hode with h | h
    · rw [max_eq_right (by omega)] at hmax
      rw [hmax] at hDpar
      exact ((Nat.not_even_iff_odd.mpr hp) hDpar).elim
    · exact h
  have hNp : N.natDegree = p := by rw [max_eq_left (by omega)] at hmax; exact hmax
  let g := EndomorphismWork.EndPair.cm a w (PSWork.sqrtQuartic a) hy0 hysq hw1 hw2
  have hg : g.f*(1+X^2) = C w*X := by
    change (C w*X*(1+X^2)⁻¹)*(1+X^2) = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have hcomm := EndomorphismWork.EndPair.commute hy0 hysq e g
  have hrec := ReciprocityWork.reciprocal_polynomials e.f g.f w hw0 N D hN e.f0 g.f0 hD0 hrep hgap hg hcomm
  obtain ⟨eps,heps,hNrec,hDrec⟩ := ReciprocityWork.reciprocal_normal_form N D hN hN0
    (by rwa [← Polynomial.coeff_zero_eq_eval_zero] at hD0) hcop hgap hrec
  exact ⟨e,N,D,eps,hrep,hD0,hcop,hNp,hgap.trans hNp,heps,hNrec,hDrec⟩

end CMRationalWork

end

section

namespace NormalizationWork
open Polynomial Finset
open scoped BigOperators PowerSeries
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma coeff_product_bound (f : K⟦X⟧) (D : K[X]) (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ i ≤ n, ‖PowerSeries.coeff i f‖ ≤ r) (hD : ∀ i, ‖D.coeff i‖ ≤ 1) :
    ‖PowerSeries.coeff n (f*(D:K⟦X⟧))‖ ≤ r := by
  rw [PowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr
  intro ij hij
  rw [Polynomial.coeff_coe, norm_mul]
  have hi : ij.1 ≤ n := by have := Finset.mem_antidiagonal.mp hij; omega
  exact (mul_le_mul (hf ij.1 hi) (hD ij.2) (norm_nonneg _) hr).trans (by simp)

lemma eps_norm {eps : K} (h : eps^2 = 1) : ‖eps‖ = 1 := by
  have hh := congrArg norm h
  simp only [norm_pow, norm_one] at hh
  nlinarith [norm_nonneg eps]

lemma scale_reciprocal (N D : K[X]) (eps s : K)
    (hN : N=C eps*X*D.reverse) (hD : D=C eps*N.reverse) :
    C s*N = C eps*X*(C s*D).reverse ∧ C s*D = C eps*(C s*N).reverse := by
  rw [reverse_mul_of_domain, reverse_C, reverse_mul_of_domain, reverse_C]
  constructor
  · rw [hN]; ring
  · rw [hD]; ring

lemma normalize_reciprocal (f : K⟦X⟧) (N D : K[X]) (eps : K) (p : ℕ)
    (hN : N ≠ 0) (hdegN : N.natDegree=p) (hdegD : D.natDegree+1=p)
    (hrep : f*(D:K⟦X⟧) = N) (heps : eps^2=1)
    (hNrec : N=C eps*X*D.reverse) (hDrec : D=C eps*N.reverse)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : ∀ i < p, ‖PowerSeries.coeff i f‖ ≤ r) :
    ∃ N' D' : K[X],
      f*(D':K⟦X⟧) = N' ∧ N'.natDegree=p ∧ D'.natDegree+1=p ∧
      D'.coeff 0=1 ∧ N'.coeff p=eps ∧
      (∀ i, ‖N'.coeff i‖ ≤ 1) ∧ (∀ i, ‖D'.coeff i‖ ≤ 1) ∧
      N'=C eps*X*D'.reverse ∧ D'=C eps*N'.reverse := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (range (p+1)) (fun i => ‖N.coeff i‖)
    (by simp)
  have himax : ∀ j, ‖N.coeff j‖ ≤ ‖N.coeff i‖ := by
    intro j
    by_cases hj : j ≤ p
    · exact hmax j (mem_range.mpr (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
      exact norm_nonneg _
  have hi0 : N.coeff i ≠ 0 := by
    intro hh
    have hle := himax p
    rw [hh, norm_zero] at hle
    have hz : N.coeff p = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    rw [← hdegN, coeff_natDegree] at hz
    exact hN (leadingCoeff_eq_zero.mp hz)
  have hinorm : 0 < ‖N.coeff i‖ := norm_pos_iff.mpr hi0
  let s := (N.coeff i)⁻¹
  have hs : s ≠ 0 := inv_ne_zero hi0
  let A := C s*N
  let B := C s*D
  have hA : ∀ j, ‖A.coeff j‖ ≤ 1 := by
    intro j
    rw [show A=C s*N from rfl, coeff_C_mul, norm_mul, show ‖s‖=‖N.coeff i‖⁻¹ by simp [s], mul_comm]
    exact (div_le_one hinorm).mpr (himax j)
  have hB : ∀ j, ‖B.coeff j‖ ≤ 1 := by
    intro j
    have hDj : D.coeff j = eps*N.coeff (revAt N.natDegree j) := by rw [hDrec, coeff_C_mul, coeff_reverse]
    rw [show B=C s*D from rfl, coeff_C_mul, hDj, norm_mul, norm_mul, eps_norm heps, one_mul]
    change ‖s‖*‖N.coeff (revAt N.natDegree j)‖ ≤ 1
    simpa only [A, coeff_C_mul, norm_mul] using hA (revAt N.natDegree j)
  have hAB : f*(B:K⟦X⟧) = A := by
    dsimp [A,B]
    simp only [Polynomial.coe_mul, Polynomial.coe_C]
    rw [mul_left_comm, hrep]
  have hAi : A.coeff i = 1 := by rw [show A=C s*N from rfl, coeff_C_mul]; exact inv_mul_cancel₀ hi0
  have hip : i = p := by
    have hip : i ≤ p := by simpa using mem_range.mp hi
    by_contra hne
    have hil : i < p := by omega
    have hbound : ‖A.coeff i‖ ≤ r := by
      rw [← Polynomial.coeff_coe, ← hAB]
      exact coeff_product_bound f B i r hr0 (fun j hj => hf j (by omega)) hB
    rw [hAi, norm_one] at hbound
    exact (not_le_of_gt hr1) hbound
  have hAp : A.coeff p = 1 := hip ▸ hAi
  have hdegA : A.natDegree=p := by change (C s*N).natDegree=p; rw [natDegree_C_mul hs, hdegN]
  have hdegB : B.natDegree+1=p := by change (C s*D).natDegree+1=p; rw [natDegree_C_mul hs, hdegD]
  obtain ⟨hArec,hBrec⟩ := scale_reciprocal N D eps s hNrec hDrec
  have hB0 : B.coeff 0 = eps := by
    change (C s*D).coeff 0 = _
    rw [hBrec, coeff_C_mul, coeff_zero_reverse]
    change eps*A.leadingCoeff = eps
    rw [leadingCoeff, hdegA, hAp, mul_one]
  have heps0 : eps ≠ 0 := by intro hh; rw [hh, zero_pow (by decide : 2≠0)] at heps; exact zero_ne_one heps
  refine ⟨C eps*A,C eps*B,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Polynomial.coe_mul, Polynomial.coe_C]
    rw [mul_left_comm, hAB]
  · rw [natDegree_C_mul heps0, hdegA]
  · rw [natDegree_C_mul heps0, hdegB]
  · rw [coeff_C_mul,hB0,←pow_two,heps]
  · rw [coeff_C_mul,hAp,mul_one]
  · intro j; rw [coeff_C_mul,norm_mul,eps_norm heps,one_mul]; exact hA j
  · intro j; rw [coeff_C_mul,norm_mul,eps_norm heps,one_mul]; exact hB j
  · exact (scale_reciprocal A B eps eps hArec hBrec).1
  · exact (scale_reciprocal A B eps eps hArec hBrec).2

end NormalizationWork

end

section

namespace ApproxWork
open scoped BigOperators
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Congruence measured by a nonarchimedean norm. -/
def Cong (r : ℝ) (n : ℕ) (x y : K) : Prop := ‖x-y‖ ≤ r^n

namespace Cong
variable {r : ℝ} {n m : ℕ} {x y z u v a : K}
lemma refl (hr : 0 ≤ r) (n : ℕ) (x : K) : Cong r n x x := by simp [Cong, pow_nonneg hr]
lemma symm (h : Cong r n x y) : Cong r n y x := by simpa only [Cong, norm_sub_rev] using h
lemma trans (h : Cong r n x y) (h' : Cong r n y z) : Cong r n x z := by
  change ‖x-z‖ ≤ _
  have heq : x-z = (x-y)+(y-z) := by ring
  rw [heq]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')
lemma of_eq (hr : 0 ≤ r) (h : x=y) : Cong r n x y := h ▸ refl hr n y
lemma add (h : Cong r n x y) (h' : Cong r n u v) : Cong r n (x+u) (y+v) := by
  change ‖(x+u)-(y+v)‖ ≤ _
  rw [show (x+u)-(y+v) = (x-y)+(u-v) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')
lemma neg (h : Cong r n x y) : Cong r n (-x) (-y) := by simpa only [Cong, neg_sub_neg, norm_sub_rev] using h
lemma sub (h : Cong r n x y) (h' : Cong r n u v) : Cong r n (x-u) (y-v) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg
lemma mono (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h : Cong r n x y) (hmn : m ≤ n) : Cong r m x y :=
  le_trans h (pow_le_pow_of_le_one hr0 hr1 hmn)
lemma mul_left (h : Cong r n x y) (ha : ‖a‖ ≤ r^m) : Cong r (m+n) (a*x) (a*y) := by
  change ‖a*x-a*y‖ ≤ _
  rw [← mul_sub, norm_mul, pow_add]
  exact mul_le_mul ha h (norm_nonneg _) (le_trans (norm_nonneg _) ha)
lemma mul_right (h : Cong r n x y) (ha : ‖a‖ ≤ r^m) : Cong r (n+m) (x*a) (y*a) := by
  simpa only [mul_comm, Nat.add_comm] using h.mul_left ha
lemma mul_left_unit (h : Cong r n x y) (ha : ‖a‖ ≤ 1) : Cong r n (a*x) (a*y) := by
  simpa only [zero_add] using h.mul_left (m := 0) (by simpa using ha)
lemma mul_right_unit (h : Cong r n x y) (ha : ‖a‖ ≤ 1) : Cong r n (x*a) (y*a) := by
  simpa only [mul_comm] using h.mul_left_unit ha
lemma mul (h : Cong r n x y) (h' : Cong r n u v) (hx : ‖x‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    Cong r n (x*u) (y*v) := (h'.mul_left_unit hx).trans (h.mul_right_unit hv)
lemma sq (h : Cong r n x y) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : Cong r n (x^2) (y^2) := by
  simpa only [pow_two] using h.mul h hx hy
lemma sq_scaled (h : Cong r n x y) (hx : ‖x‖ ≤ r^m) (hy : ‖y‖ ≤ r^m) :
    Cong r (n+m) (x^2) (y^2) := by
  change ‖x^2-y^2‖ ≤ _
  rw [show x^2-y^2=(x-y)*(x+y) by ring, norm_mul, pow_add]
  exact mul_le_mul h ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy))
    (norm_nonneg _) (le_trans (norm_nonneg _) h)
lemma sum {ι : Type*} (s : Finset ι) {f g : ι → K} (hr : 0 ≤ r)
    (h : ∀ i ∈ s, Cong r n (f i) (g i)) : Cong r n (∑i∈s, f i) (∑i∈s,g i) := by
  change ‖(∑i∈s,f i)-(∑i∈s,g i)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) h
lemma norm_bound (h : Cong r n x y) (hy : ‖y‖ ≤ r^n) : ‖x‖ ≤ r^n := by
  have heq : x = (x-y)+y := by ring
  rw [heq]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h hy)
end Cong

lemma unit_add_bound {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x+y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
lemma unit_sub_bound {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x-y‖ ≤ 1 := by
  simpa only [sub_eq_add_neg, norm_neg] using unit_add_bound hx (by simpa only [norm_neg] using hy)
lemma unit_mul_bound {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x*y‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans (by simp)
lemma unit_pow_bound {x : K} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x^n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hx

lemma prod_first_order {ι : Type*} (s : Finset ι) (t : ι → K) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (ht : ∀i∈s, ‖t i‖ ≤ r^n) :
    Cong r (2*n) (∏i∈s, (1+t i)) (1+∑i∈s,t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.refl hr0 (2*n) (1:K)
  | @insert a s ha ih =>
    have hta : ‖t a‖ ≤ r^n := ht a (by simp)
    have hts : ∀i∈s, ‖t i‖ ≤ r^n := fun i hi => ht i (by simp [hi])
    have ih' := ih hts
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hmul := ih'.mul_left_unit (unit_add_bound (x := (1:K)) (by simp) (hta.trans (pow_le_one₀ hr0 hr1)))
    apply hmul.trans
    change ‖(1+t a)*(1+∑i∈s,t i)-(1+(t a+∑i∈s,t i))‖ ≤ r^(2*n)
    rw [show (1+t a)*(1+∑i∈s,t i)-(1+(t a+∑i∈s,t i)) = t a*∑i∈s,t i by ring,
      norm_mul, two_mul, pow_add]
    exact mul_le_mul hta (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) hts)
      (norm_nonneg _) (pow_nonneg hr0 _)

end ApproxWork

end

section

namespace AnalyticCoeffWork
open PowerSeries Finset ApproxWork
open scoped PowerSeries BigOperators
variable {K : Type*} [NormedField K] [CharZero K] [IsUltrametricDist K]

lemma coeff_pow_bound (f : K⟦X⟧) (hf0 : constantCoeff f = 0) (p : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hf : ∀i<p, ‖coeff i f‖ ≤ r) (k n : ℕ) (hn : n+1 < p+k) :
    ‖coeff n (f^k)‖ ≤ r^k := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      simpa using hf n (by omega)
    rw [pow_succ, coeff_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _)
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    by_cases hj : ij.2=0
    · simp only [hj, coeff_zero_eq_constantCoeff, hf0, mul_zero, norm_zero]
      exact pow_nonneg hr _
    by_cases hi : ij.1<k
    · rw [CompositionWork.coeff_pow_eq_zero hf0 hi, zero_mul, norm_zero]
      exact pow_nonneg hr _
    rw [norm_mul, pow_succ]
    exact mul_le_mul (ih ij.1 (by omega)) (hf ij.2 (by omega)) (norm_nonneg _) (pow_nonneg hr _)

lemma log_coeff (f G : K⟦X⟧) (c : K) (hf0 : constantCoeff f = 0)
    (hdiff : subst f G*d⁄dX K f = C c*G) (n : ℕ) (hn : 0<n) :
    (∑k∈range n, coeff k G/(k+1:K)*coeff n (f^(k+1))) = c*coeff (n-1) G/(n:K) := by
  have hn0 : (n:K) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hd := congrArg (coeff (n-1)) hdiff
  rw [CompositionWork.coeff_subst_mul hf0 G (d⁄dX K f) (n-1) n (by omega), coeff_C_mul] at hd
  apply (eq_div_iff hn0).mpr
  rw [sum_mul]
  calc
    (∑k∈range n, (coeff k G/(k+1:K)*coeff n (f^(k+1)))*(n:K)) =
        ∑k∈range n, coeff k G*coeff (n-1) (f^k*d⁄dX K f) := by
      apply sum_congr rfl
      intro k hk
      have hder := congrArg (coeff (n-1)) (Derivation.leibniz_pow (d⁄dX K) f (k+1))
      rw [coeff_derivative] at hder
      simp only [show n-1+1=n by omega, Nat.add_sub_cancel, smul_eq_mul] at hder
      rw [map_nsmul, nsmul_eq_mul] at hder
      have hnc : ((n-1:ℕ):K)+1=(n:K) := by exact_mod_cast (Nat.sub_add_cancel (show 1≤n by omega))
      rw [hnc] at hder
      have hk0 : (k+1:K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      field_simp
      push_cast at hder
      linear_combination coeff k G*hder
    _ = _ := hd

lemma log_tail (f G : K⟦X⟧) (c : K) (hf0 : constantCoeff f = 0) (hG0 : coeff 0 G = 1)
    (hdiff : subst f G*d⁄dX K f = C c*G) (n : ℕ) (hn : 0<n) :
    coeff n f-c*coeff (n-1) G/(n:K) =
      -(∑k∈range (n-1), coeff (k+1) G/(k+2:K)*coeff n (f^(k+2))) := by
  have hh := log_coeff f G c hf0 hdiff n hn
  rw [show n=(n-1)+1 by omega, sum_range_succ'] at hh
  simp only [Nat.sub_add_cancel (show 1≤n by omega), Nat.cast_zero, zero_add, Nat.cast_one,
    div_one, pow_one, hG0, one_mul] at hh
  convert (eq_neg_of_add_eq_zero_left (show (coeff n f-c*coeff (n-1) G/(n:K))+
      (∑k∈range (n-1), coeff (k+1) G/(k+2:K)*coeff n (f^(k+2))) = 0 by
      push_cast at hh
      simp only [Nat.add_assoc, add_assoc, one_add_one_eq_two] at hh
      linear_combination hh)) using 1

lemma low_log_approx (f G : K⟦X⟧) (c : K) (p : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hf0 : constantCoeff f = 0) (hG0 : coeff 0 G = 1)
    (hG : ∀k, ‖coeff k G‖ ≤ 1) (hf : ∀i<p, ‖coeff i f‖ ≤ r)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖=1)
    (hdiff : subst f G*d⁄dX K f = C c*G) (n : ℕ) (hn : 0<n) (hnp : n<p) :
    Cong r 2 (coeff n f) (c*coeff (n-1) G/(n:K)) := by
  change ‖coeff n f-c*coeff (n-1) G/(n:K)‖ ≤ r^2
  rw [log_tail f G c hf0 hG0 hdiff n hn, norm_neg]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _)
  intro k hk
  have hkn : k+2 ≤ n := by have := mem_range.mp hk; omega
  have hku : ‖(k+2:K)‖=1 := by exact_mod_cast hunit (k+2) (by omega) (by omega)
  rw [norm_mul, norm_div, hku, div_one]
  have hb := coeff_pow_bound f hf0 p r hr0 hf (k+2) n (by omega)
  calc
    _ ≤ 1*r^(k+2) := mul_le_mul (hG _) hb (norm_nonneg _) zero_le_one
    _ ≤ r^2 := by rw [one_mul]; exact pow_le_pow_of_le_one hr0 hr1 (by omega)

lemma top_log_approx (f G : K⟦X⟧) (c : K) (p : ℕ) (hp : 4 ≤ p) (r : ℝ)
    (hr0 : 0<r) (hr1 : r≤1) (hnormp : ‖(p:K)‖=r)
    (hf0 : constantCoeff f = 0) (hG0 : coeff 0 G = 1) (hG1 : coeff 1 G = 0)
    (hG : ∀k, ‖coeff k G‖ ≤ 1) (hf : ∀i<p, ‖coeff i f‖ ≤ r)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖=1)
    (hdiff : subst f G*d⁄dX K f = C c*G) :
    Cong r 3 (coeff p f) (c*coeff (p-1) G/(p:K)) := by
  change ‖coeff p f-c*coeff (p-1) G/(p:K)‖ ≤ r^3
  rw [log_tail f G c hf0 hG0 hdiff p (by omega), norm_neg]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0.le _)
  intro k hk
  have hkp : k+2 ≤ p := by have := mem_range.mp hk; omega
  by_cases hk0 : k=0
  · simp only [hk0, zero_add, hG1, zero_div, zero_mul, norm_zero]
    exact pow_nonneg hr0.le _
  by_cases heq : k+2=p
  · have hkpow : f^(k+2) = f^p := by rw [heq]
    have hcast : (k+2:K) = (p:K) := by exact_mod_cast heq
    rw [norm_mul, norm_div, hcast, hnormp, hkpow]
    have hb := coeff_pow_bound f hf0 p r hr0.le hf p p (by omega)
    calc
      _ ≤ (1/r)*r^p := mul_le_mul (div_le_div_of_nonneg_right (hG _) hr0.le) hb
        (norm_nonneg _) (by positivity)
      _ = r^p/r := by ring
      _ ≤ r^3 := by
        apply (div_le_iff₀ hr0).mpr
        rw [← pow_succ]
        exact pow_le_pow_of_le_one hr0.le hr1 (by omega)
  · have hku : ‖(k+2:K)‖=1 := by exact_mod_cast hunit (k+2) (by omega) (by omega)
    rw [norm_mul,norm_div,hku,div_one]
    have hb := coeff_pow_bound f hf0 p r hr0.le hf (k+2) p (by omega)
    calc
      _ ≤ 1*r^(k+2) := mul_le_mul (hG _) hb (norm_nonneg _) zero_le_one
      _ ≤ r^3 := by rw [one_mul]; exact pow_le_pow_of_le_one hr0.le hr1 (by omega)

end AnalyticCoeffWork

end

section

namespace NormalizedCoeffWork
open PowerSeries Finset ApproxWork
open scoped PowerSeries BigOperators
variable {K : Type*} [NormedField K] [CharZero K] [IsUltrametricDist K]

lemma coefficient_equation (f : K⟦X⟧) (N D : Polynomial K) (hD0 : D.coeff 0=1)
    (hrep : f*(D:K⟦X⟧)=N) (n : ℕ) :
    N.coeff n = coeff n f + ∑i∈range n, coeff i f*D.coeff (n-i) := by
  rw [← Polynomial.coeff_coe, ← hrep, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ]
  simp only [Polynomial.coeff_coe, Nat.sub_self, hD0, mul_one]
  ring

lemma low_numerator (f : K⟦X⟧) (N D : Polynomial K) (hD0 : D.coeff 0=1)
    (hrep : f*(D:K⟦X⟧)=N) (p : ℕ) (r : ℝ) (hr : 0≤r)
    (hf : ∀i<p, ‖coeff i f‖ ≤ r) (hD : ∀ i : ℕ, 0 < i → ‖D.coeff i‖ ≤ r)
    (n : ℕ) (hn : n<p) : Cong r 2 (N.coeff n) (coeff n f) := by
  change ‖N.coeff n-coeff n f‖ ≤ _
  rw [coefficient_equation f N D hD0 hrep n, add_sub_cancel_left]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _)
  intro i hi
  have hin : i<n := mem_range.mp hi
  rw [norm_mul, pow_two]
  exact mul_le_mul (hf i (by omega)) (hD (n-i) (by omega)) (norm_nonneg _) hr

lemma top_numerator (f : K⟦X⟧) (N D : Polynomial K) (hD0 : D.coeff 0=1)
    (hrep : f*(D:K⟦X⟧)=N) (p : ℕ) (r : ℝ) (hr : 0≤r) (eps : K) (heps : eps^2=1)
    (hNp : N.coeff p=eps) (hNdeg : N.natDegree=p) (hDrec : D=Polynomial.C eps*N.reverse)
    (hf : ∀i<p, ‖coeff i f‖ ≤ r) (hN : ∀i<p, ‖N.coeff i‖ ≤ r)
    (hD : ∀ i : ℕ, 0 < i → ‖D.coeff i‖ ≤ r) :
    Cong r 3 (coeff p f) (eps*(1-∑i∈range p,(N.coeff i)^2)) := by
  have hrec : ∀i∈range p, D.coeff (p-i)=eps*N.coeff i := by
    intro i hi
    have hip : i≤p := (mem_range.mp hi).le
    rw [hDrec, Polynomial.coeff_C_mul, Polynomial.coeff_reverse, hNdeg,
      Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hip]
  have he := coefficient_equation f N D hD0 hrep p
  rw [hNp] at he
  have hs : ∑i∈range p, coeff i f*D.coeff (p-i) = eps*∑i∈range p, coeff i f*N.coeff i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [hrec i hi]
    ring
  rw [hs] at he
  have hsum : Cong r 3 (∑i∈range p, coeff i f*N.coeff i) (∑i∈range p,(N.coeff i)^2) := by
    apply Cong.sum _ hr
    intro i hi
    have hh := (low_numerator f N D hD0 hrep p r hr hf hD i (mem_range.mp hi)).symm
    simpa only [pow_one, pow_two] using hh.mul_right (m := 1) (by simpa using hN i (mem_range.mp hi))
  have heq : coeff p f = eps-eps*∑i∈range p, coeff i f*N.coeff i := by linear_combination -he
  rw [heq]
  have hh := (Cong.refl hr 3 eps).sub (hsum.mul_left_unit (NormalizationWork.eps_norm heps).le)
  convert hh using 1 <;> ring

lemma low_square (f G : K⟦X⟧) (N D : Polynomial K) (c : K) (p : ℕ) (r : ℝ)
    (hr0 : 0≤r) (hr1 : r≤1) (hc : ‖c‖=r)
    (hf0 : constantCoeff f=0) (hG0 : coeff 0 G=1) (hD0 : D.coeff 0=1)
    (hrep : f*(D:K⟦X⟧)=N) (hdiff : subst f G*d⁄dX K f=C c*G)
    (hG : ∀k, ‖coeff k G‖≤1) (hf : ∀i<p, ‖coeff i f‖≤r)
    (hN : ∀i<p, ‖N.coeff i‖≤r) (hD : ∀ i : ℕ, 0 < i → ‖D.coeff i‖≤r)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖=1) (i : ℕ) (hi : i+1<p) :
    Cong r 3 ((N.coeff (i+1))^2) (c^2*(coeff i G/(i+1:K))^2) := by
  have hh := (low_numerator f N D hD0 hrep p r hr0 hf hD (i+1) hi).trans
    (AnalyticCoeffWork.low_log_approx f G c p r hr0 hr1 hf0 hG0 hG hf hunit hdiff (i+1) (by omega) hi)
  have hn : ‖c*coeff i G/(i+1:K)‖ ≤ r := by
    have hu : ‖(i+1:K)‖=1 := by exact_mod_cast hunit (i+1) (by omega) hi
    rw [norm_div,norm_mul,hc,hu,div_one]
    exact (mul_le_mul_of_nonneg_left (hG i) hr0).trans (by simp)
  have hsq := hh.sq_scaled (m := 1) (by simpa using hN (i+1) hi) (by simpa using hn)
  convert hsq using 1 <;> simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] <;> ring

noncomputable def T (G : K⟦X⟧) (p : ℕ) : K := ∑i∈range (p-1), (coeff i G/(i+1:K))^2

lemma main_coefficient (f G : K⟦X⟧) (N D : Polynomial K) (c eps : K) (p : ℕ) (hp : 4≤p)
    (r : ℝ) (hr0 : 0<r) (hr1 : r≤1) (hc : ‖c‖=r) (hpNorm : ‖(p:K)‖=r)
    (hf0 : constantCoeff f=0) (hG0 : coeff 0 G=1) (hG1 : coeff 1 G=0)
    (hD0 : D.coeff 0=1) (hNp : N.coeff p=eps) (hNdeg : N.natDegree=p)
    (heps : eps^2=1) (hDrec : D=Polynomial.C eps*N.reverse)
    (hrep : f*(D:K⟦X⟧)=N) (hdiff : subst f G*d⁄dX K f=C c*G)
    (hG : ∀k, ‖coeff k G‖≤1) (hf : ∀i<p, ‖coeff i f‖≤r)
    (hN : ∀i<p, ‖N.coeff i‖≤r) (hD : ∀ i : ℕ, 0 < i → ‖D.coeff i‖≤r)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖=1) :
    Cong r 3 ((coeff (p-1) G)^2) (((p:K)/c)^2-2*(p:K)^2*T G p) := by
  have hc0 : c≠0 := by intro hh; rw [hh,norm_zero] at hc; linarith
  have hp0 : (p:K)≠0 := by exact_mod_cast (show p≠0 by omega)
  let bar := (p:K)/c
  have hbar : ‖bar‖=1 := by rw [norm_div,hpNorm,hc,div_self hr0.ne']
  have hN0 : N.coeff 0=0 := by
    have hh := coefficient_equation f N D hD0 hrep 0
    simpa only [sum_range_zero, add_zero, coeff_zero_eq_constantCoeff, hf0] using hh
  have hsum : Cong r 3 (∑i∈range p,(N.coeff i)^2) (c^2*T G p) := by
    have hh := Cong.sum (range (p-1)) hr0.le (fun i hi =>
      low_square f G N D c p r hr0.le hr1 hc hf0 hG0 hD0 hrep hdiff hG hf hN hD hunit i
        (by have := mem_range.mp hi; omega))
    rw [show p=(p-1)+1 by omega, sum_range_succ']
    simp only [Nat.sub_add_cancel (show 1≤p by omega), hN0, zero_pow (by decide : 2≠0), add_zero]
    simpa only [T, mul_sum] using hh
  have htop := top_numerator f N D hD0 hrep p r hr0.le eps heps hNp hNdeg hDrec hf hN hD
  have htop' : Cong r 3 (coeff p f) (eps*(1-c^2*T G p)) := by
    apply htop.trans
    exact ((Cong.refl hr0.le 3 (1:K)).sub hsum).mul_left_unit (NormalizationWork.eps_norm heps).le
  have hlog := AnalyticCoeffWork.top_log_approx f G c p hp r hr0 hr1 hpNorm hf0 hG0 hG1 hG hf hunit hdiff
  have hval : Cong r 3 (coeff (p-1) G) (bar*eps*(1-c^2*T G p)) := by
    have hh := (hlog.symm.trans htop').mul_left_unit hbar.le
    convert hh using 1 <;> dsimp only [bar] <;> field_simp <;> ring
  have hT : ‖T G p‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i hi
    apply unit_pow_bound
    have hu : ‖(i+1:K)‖=1 := by exact_mod_cast hunit (i+1) (by omega) (by have := mem_range.mp hi; omega)
    rw [norm_div,hu,div_one]
    exact hG i
  have hright : ‖bar*eps*(1-c^2*T G p)‖ ≤ 1 := unit_mul_bound
    (unit_mul_bound hbar.le (NormalizationWork.eps_norm heps).le)
    (unit_sub_bound (by simp) (unit_mul_bound (unit_pow_bound (hc.le.trans hr1) 2) hT))
  have hsq := hval.sq (hG _) hright
  apply hsq.trans
  change ‖(bar*eps*(1-c^2*T G p))^2-(bar^2-2*(p:K)^2*T G p)‖ ≤ r^3
  have heq : (bar*eps*(1-c^2*T G p))^2-(bar^2-2*(p:K)^2*T G p) = bar^2*c^4*(T G p)^2 := by
    have hbc : bar*c=(p:K) := div_mul_cancel₀ _ hc0
    linear_combination bar^2*(1-c^2*T G p)^2*heps-2*T G p*(bar*c+(p:K))*hbc
  rw [heq,norm_mul,norm_mul,norm_pow,norm_pow,hbar,hc,one_pow,one_mul]
  exact (mul_le_mul_of_nonneg_left (unit_pow_bound hT 2) (pow_nonneg hr0.le 4)).trans
    (by simpa using pow_le_pow_of_le_one hr0.le hr1 (by decide : 3≤4))

end NormalizedCoeffWork

end

section

namespace PadicCoefficientWork
open PowerSeries AdditionWork ApproxWork
open scoped PowerSeries
variable {p : ℕ} [Fact p.Prime]

lemma small_norm (i : ℕ) (hi : 0 < i) (hip : i < p) : ‖(i:ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hi hip)

lemma half_mem (hp2 : p ≠ 2) : (1/2:ℚ_[p]) ∈ PadicInt.subring p := by
  change ‖(1/2:ℚ_[p])‖ ≤ 1
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  have ht : ‖(2:ℚ_[p])‖ = 1 := by exact_mod_cast small_norm 2 (by omega) hp
  rw [norm_div,norm_one,ht]
  norm_num

lemma parameter_mem (hp2 : p ≠ 2) (w : ℤ_[p]) : -3*((w:ℚ_[p])+2)/8 ∈ PadicInt.subring p := by
  have he : -3*((w:ℚ_[p])+2)/8 = -3*((w:ℚ_[p])+2)*(1/2)^3 := by ring
  rw [he]
  exact (PadicInt.subring p).mul_mem
    ((PadicInt.subring p).mul_mem ((PadicInt.subring p).neg_mem (natCast_mem _ 3))
      ((PadicInt.subring p).add_mem w.2 (natCast_mem _ 2)))
    ((PadicInt.subring p).pow_mem (half_mem hp2) 3)

lemma prime_radius : 0 < ‖(p:ℚ_[p])‖ ∧ ‖(p:ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hp⟩

lemma scalar_norm (w : ℤ_[p]) (hw : w^2-w+2=0) (z : O7Work.O) (hz : z.norm=p)
    (hu : IsUnit ((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w))) :
    ‖(z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p])‖ = ‖(p:ℚ_[p])‖ := by
  have hp : ((z.re:ℤ_[p])+(z.im:ℤ_[p])*w)*((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w)) = p := by
    have hn := congrArg (fun x:ℤ => (x:ℤ_[p])) hz
    rw [O7Work.norm_O] at hn
    push_cast at hn
    linear_combination hn-(z.im:ℤ_[p])^2*hw
  have hh := congrArg norm hp
  rw [norm_mul, PadicInt.isUnit_iff.mp hu, mul_one] at hh
  simpa only [PadicInt.norm_def, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_intCast,
    PadicInt.coe_natCast] using hh

section General
variable {K : Type*} [NormedField K] [CharZero K] [IsUltrametricDist K]

lemma low_coeff (a c : K) (e : EndPair a (PSWork.sqrtQuartic a) c) (p : ℕ)
    (hY : ∀ i, ‖coeff i e.Y‖ ≤ 1) (hG : ∀ i, ‖coeff i (GeneratingWork.Gquartic a)‖ ≤ 1)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖ = 1) :
    ∀ i < p, ‖coeff i e.f‖ ≤ ‖c‖ := by
  have hd : d⁄dX K e.f = C c*(e.Y*GeneratingWork.Gquartic a) := by
    have hh := CMRationalWork.inverse_sqrt (K := K) a
    calc
      d⁄dX K e.f = (d⁄dX K e.f*PSWork.sqrtQuartic a)*GeneratingWork.Gquartic a := by
        linear_combination -(d⁄dX K e.f)*hh
      _ = _ := by rw [e.diff]; ring
  intro i hi
  cases i with
  | zero => simpa [e.f0] using norm_nonneg c
  | succ n =>
    have hh := congrArg (coeff n) hd
    rw [coeff_derivative, coeff_C_mul] at hh
    have hh' := congrArg norm hh
    have hu : ‖(n:K)+1‖ = 1 := by exact_mod_cast hunit (n+1) (by omega) hi
    rw [norm_mul, norm_mul, hu, mul_one] at hh'
    rw [hh']
    suffices hb : ‖coeff n (e.Y*GeneratingWork.Gquartic a)‖ ≤ 1 by
      nlinarith [norm_nonneg c]
    
    rw [coeff_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro ij hij
    exact unit_mul_bound (hY _) (hG _)

lemma positive_denominator (N D : Polynomial K) (eps : K) (heps : eps^2=1)
    (hrec : D=Polynomial.C eps*N.reverse) (hdeg : N.natDegree=p)
    (r : ℝ) (hr : 0≤r) (hN : ∀ i < p, ‖N.coeff i‖ ≤ r) :
    ∀ i : ℕ, 0 < i → ‖D.coeff i‖ ≤ r := by
  intro i hi
  rw [hrec, Polynomial.coeff_C_mul, norm_mul, NormalizationWork.eps_norm heps, one_mul]
  by_cases hip : i≤p
  · rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hip]
    exact hN _ (by omega)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have hh := Polynomial.reverse_natDegree_le N; omega)]
    simpa using hr

lemma coeff_Gquartic_odd (a : K) (n : ℕ) : coeff (2*n+1) (GeneratingWork.Gquartic a) = 0 := by
  simp [GeneratingWork.Gquartic, coeff_expand, show ¬ 2 ∣ 2*n+1 by omega]
end General

lemma ordinary_coefficient (hp4 : 4 ≤ p) (hp2 : p ≠ 2) (w : ℤ_[p])
    (hw : w^2-w+2=0) (z : O7Work.O) (hz : z.norm=p)
    (hu : IsUnit ((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w))) :
    let a : ℚ_[p] := -3*((w:ℚ_[p])+2)/8
    let c : ℚ_[p] := (z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p])
    Cong ‖(p:ℚ_[p])‖ 3 ((coeff (p-1) (GeneratingWork.Gquartic a))^2)
      (((p:ℚ_[p])/c)^2-2*(p:ℚ_[p])^2*NormalizedCoeffWork.T (GeneratingWork.Gquartic a) p) := by
  let a : ℚ_[p] := -3*((w:ℚ_[p])+2)/8
  let c : ℚ_[p] := (z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p])
  let r := ‖(p:ℚ_[p])‖
  have hw' : (w:ℚ_[p])^2-(w:ℚ_[p])+2=0 := by
    have hh := congrArg (PadicInt.Coe.ringHom (p := p)) hw
    simpa only [map_add,map_sub,map_pow,map_ofNat,map_zero] using hh
  have hz0 := PadicSetupWork.norm_prime_im_ne_zero Fact.out z hz
  obtain ⟨hzu,hzv⟩ := PadicSetupWork.norm_prime_parity Fact.out hp2 z hz
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨e,N,D,eps,hrep,hD0,hcop,hNdeg,hDdeg,heps,hNrec,hDrec⟩ :=
    CMRationalWork.exists_rational_prime_map (w:ℚ_[p]) hw' z hz0 hzu hzv p hpodd hz
  have ha := parameter_mem hp2 w
  have hy := IntegralWork.sqrtQuartic_mem (PadicInt.subring p) (half_mem hp2) ha
  have hg := CMRationalWork.Gquartic_integral (PadicInt.subring p) (half_mem hp2) ha
  obtain ⟨hw1,hw2,_,_⟩ := CMRationalWork.cm_parameters (w:ℚ_[p]) hw'
  have hi := IntegralWork.endPair_integral (PadicInt.subring p) a (w:ℚ_[p]) (PSWork.sqrtQuartic a)
    (PSWork.sqrtQuartic_const a) (PSWork.sqrtQuartic_sq a) ha w.2 hy hw1 hw2 z.re z.im e
  have hG : ∀i, ‖coeff i (GeneratingWork.Gquartic a)‖≤1 := hg
  have hc : ‖c‖=r := scalar_norm w hw z hz hu
  have hf : ∀i<p, ‖coeff i e.f‖≤r := by
    rw [← hc]
    exact low_coeff a c e p hi.2 hG small_norm
  obtain ⟨hr0,hr1⟩ := prime_radius (p := p)
  have hN : N≠0 := by intro hh; rw [hh,Polynomial.natDegree_zero] at hNdeg; omega
  obtain ⟨A,B,hAB,hAdeg,hBdeg,hB0,hAp,hA,hB,hArec,hBrec⟩ :=
    NormalizationWork.normalize_reciprocal e.f N D eps p hN hNdeg hDdeg hrep heps hNrec hDrec r hr0.le hr1 hf
  have hAlow : ∀i<p, ‖A.coeff i‖≤r := by
    intro i hi
    rw [← Polynomial.coeff_coe,←hAB]
    exact NormalizationWork.coeff_product_bound e.f B i r hr0.le (fun j hj => hf j (by omega)) hB
  have hBlow := positive_denominator A B eps heps hBrec hAdeg r hr0.le hAlow
  exact NormalizedCoeffWork.main_coefficient e.f (GeneratingWork.Gquartic a) A B c eps p hp4 r hr0 hr1.le
    hc rfl e.f0 (by simp) (coeff_Gquartic_odd a 0) hB0 hAp hAdeg heps hBrec hAB
    (CMRationalWork.endPair_differential e) hG hf hAlow hBlow small_norm

end PadicCoefficientWork

end

section

namespace DeformWork
open Finset
open scoped BigOperators

variable {K : Type*} [Field K]

lemma d_recur_cast (n k : ℕ) :
    (k + 1 : K) ^ 2 * (LegendreWork.d n (k + 1) : K) =
      ((n : K) * (n + 1) - k * (k + 1)) * (LegendreWork.d n k : K) := by
  have h := congrArg (Int.castRingHom K) (LegendreWork.d_recur n k)
  simpa using h

lemma central_recur_cast (k : ℕ) :
    (k + 1 : K) * (Nat.centralBinom (k + 1) : K) =
      2 * (2 * k + 1 : K) * Nat.centralBinom k := by
  have h := congrArg (Nat.castRingHom K) (Nat.succ_mul_centralBinom_succ k)
  simpa using h

lemma d_deform (m k : ℕ) (h2 : (2 : K) ≠ 0)
    (hk : ∀ j < k, (j + 1 : K) ≠ 0)
    (ho : ∀ j < k, (2 * j + 1 : K) ≠ 0) :
    (LegendreWork.d m k : K) = (Nat.centralBinom k : K) ^ 2 * (-1 / 16 : K) ^ k *
      ∏ j ∈ range k, (1 - (2 * m + 1 : K) ^ 2 / (2 * j + 1 : K) ^ 2) := by
  induction k with
  | zero => simp [LegendreWork.d_zero]
  | succ k ih =>
    have hkk : (k + 1 : K) ≠ 0 := hk k (by omega)
    have hok : (2 * k + 1 : K) ≠ 0 := ho k (by omega)
    have h16 : (16 : K) ≠ 0 := by
      have hh := pow_ne_zero 4 h2
      norm_num only [show (2 : K) ^ 4 = 16 by ring] at hh
      exact hh
    have hd : (LegendreWork.d m (k + 1) : K) =
        (((m : K) * (m + 1) - k * (k + 1)) * (LegendreWork.d m k : K)) / (k + 1 : K) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 hkk)).mpr
      simpa only [mul_comm] using d_recur_cast (K := K) m k
    have hc : (Nat.centralBinom (k + 1) : K) =
        (2 * (2 * k + 1 : K) * Nat.centralBinom k) / (k + 1 : K) := by
      apply (eq_div_iff hkk).mpr
      simpa only [mul_comm] using central_recur_cast (K := K) k
    have hi := ih (fun j hj => hk j (by omega)) (fun j hj => ho j (by omega))
    simp only [Nat.succ_eq_add_one, hd, hc, Finset.prod_range_succ, hi]
    rw [pow_succ (-1 / 16 : K) k]
    generalize (∏ j ∈ range k, (1 - (2 * m + 1 : K) ^ 2 / (2 * j + 1 : K) ^ 2)) = T
    generalize ((-1 / 16 : K) ^ k) = t
    field_simp [hkk, hok, h16]
    have hok' : (k : K) * 2 + 1 ≠ 0 := by simpa only [mul_comm] using hok
    field_simp [hok']
    ring

section CharZero
variable [CharZero K]

lemma d_deform_charZero (m k : ℕ) :
    (LegendreWork.d m k : K) = (Nat.centralBinom k : K) ^ 2 * (-1 / 16 : K) ^ k *
      ∏ j ∈ range k, (1 - (2 * m + 1 : K) ^ 2 / (2 * j + 1 : K) ^ 2) := by
  apply d_deform m k (by norm_num)
  · intro j hj
    exact_mod_cast (show j + 1 ≠ 0 by omega)
  · intro j hj
    exact_mod_cast (show 2 * j + 1 ≠ 0 by omega)

lemma P_deform (m : ℕ) (a : K) :
    GeneratingWork.P m a ^ 2 = ∑ k ∈ range (m + 1),
      (Nat.centralBinom k : K) ^ 3 * ((1 - a ^ 2) / 64) ^ k *
        ∏ j ∈ range k, (1 - (2 * m + 1 : K) ^ 2 / (2 * j + 1 : K) ^ 2) := by
  rw [GeneratingWork.P_clausen]
  apply Finset.sum_congr rfl
  intro k hk
  rw [d_deform_charZero]
  have hh : (-1 / 16 : K) * ((a ^ 2 - 1) / 4) = (1 - a ^ 2) / 64 := by ring
  rw [← hh, mul_pow]
  ring

end CharZero
end DeformWork

end

section

namespace CorrectionWork
open Finset Polynomial
open scoped BigOperators

section FiniteField
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

lemma sum_units_inv_sq (hK : 3 < Fintype.card K) :
    ∑ u : Kˣ, ((u : K)⁻¹) ^ 2 = 0 := by
  have hi := Equiv.sum_comp (Equiv.inv Kˣ) (fun u : Kˣ => (u : K) ^ 2)
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val] at hi
  rw [hi, FiniteField.sum_pow_units]
  rw [if_neg]
  intro h
  have := Nat.le_of_dvd (by omega : 0 < 2) h
  omega

lemma sum_units_inv_sq_mul_pow (hK : 3 < Fintype.card K) (k : ℕ)
    (hk : 2 * k < Fintype.card K + 1) :
    ∑ u : Kˣ, (u : K)⁻¹ ^ 2 * ((u : K) ^ 2) ^ k =
      if k = 1 then -1 else 0 := by
  cases k with
  | zero => simpa using sum_units_inv_sq hK
  | succ k =>
    have hh : ∀ u : Kˣ, (u : K)⁻¹ ^ 2 * ((u : K) ^ 2) ^ (k + 1) =
        (u : K) ^ (2 * k) := by
      intro u
      rw [pow_succ ((u : K) ^ 2) k, mul_left_comm, ← mul_pow,
        inv_mul_cancel₀ (Units.ne_zero u), one_pow, mul_one, ← pow_mul]
    simp_rw [hh]
    rw [FiniteField.sum_pow_units]
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hn : ¬Fintype.card K - 1 ∣ 2 * k := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < 2 * k) hd
        omega
      simp [hn, hk0]

lemma sum_units_inv_sq_eval (hK : 3 < Fintype.card K) (Q : K[X])
    (hQ : 2 * Q.natDegree < Fintype.card K + 1) :
    ∑ u : Kˣ, (u : K)⁻¹ ^ 2 * Q.eval ((u : K) ^ 2) = -Q.coeff 1 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hh : ∀ k ∈ Q.support,
      ∑ u : Kˣ, (u : K)⁻¹ ^ 2 * (Q.coeff k * ((u : K) ^ 2) ^ k) =
        Q.coeff k * (if k = 1 then -1 else 0) := by
    intro k hk
    simp_rw [show ∀ u : Kˣ, (u : K)⁻¹ ^ 2 * (Q.coeff k * ((u : K) ^ 2) ^ k) =
        Q.coeff k * ((u : K)⁻¹ ^ 2 * ((u : K) ^ 2) ^ k) by intro u; ring]
    rw [← Finset.mul_sum, sum_units_inv_sq_mul_pow hK k (by
      have := Polynomial.le_natDegree_of_mem_supp k hk
      omega)]
  rw [Finset.sum_congr rfl hh]
  simp only [mul_ite, mul_neg, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Polynomial.mem_support_iff, not_not] at h
    simp [h]

lemma prod_linear_coeff_one {ι : Type*} (s : Finset ι) (c : ι → K) :
    (∏ j ∈ s, (1 - C (c j) * X : K[X])).coeff 1 = -∑ j ∈ s, c j := by
  classical
  have hconst : ∀ t : Finset ι, (∏ j ∈ t, (1 - C (c j) * X : K[X])).coeff 0 = 1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih => simp [Finset.prod_insert ha, mul_coeff_zero, ih]
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, sub_mul, one_mul, coeff_sub,
      mul_assoc, coeff_C_mul, coeff_X_mul, hconst, ih]
    ring

lemma correction_full_field (hK : 3 < Fintype.card K) (c : ℕ → K) (k : ℕ)
    (hk : 2 * k < Fintype.card K + 1) :
    (∑ u : Kˣ, (u : K)⁻¹ ^ 2 * ∏ j ∈ range k, (1 - c j * (u : K) ^ 2)) =
      ∑ j ∈ range k, c j := by
  let Q : K[X] := ∏ j ∈ range k, (1 - C (c j) * X)
  have hdeg : Q.natDegree ≤ k := by
    calc
      Q.natDegree ≤ ∑ j ∈ range k, (1 - C (c j) * X : K[X]).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ j ∈ range k, 1 := by
        apply sum_le_sum
        intro j hj
        exact (natDegree_sub_le_of_le (show (1 : K[X]).natDegree ≤ 1 by simp)
          (show (C (c j) * X).natDegree ≤ 1 from natDegree_mul_le.trans (by simp)))
      _ = k := by simp
  have heval : ∀ u : Kˣ, Q.eval ((u : K) ^ 2) =
      ∏ j ∈ range k, (1 - c j * (u : K) ^ 2) := by intro u; simp [Q, Polynomial.eval_prod]
  simpa only [heval, Q, prod_linear_coeff_one, neg_neg] using
    sum_units_inv_sq_eval hK Q (by omega)

lemma sum_units_eq_sum_field (f : K → K) (h0 : f 0 = 0) :
    ∑ u : Kˣ, f u = ∑ x : K, f x := by
  apply Finset.sum_bij_ne_zero (fun (u : Kˣ) _ _ => (u : K)) (by simp)
  · intro u hu hfu v hv hfv heq
    exact Units.val_injective heq
  · intro x hx hfx
    have hx0 : x ≠ 0 := by intro hh; simp [hh, h0] at hfx
    exact ⟨Units.mk0 x hx0, by simp, hfx, rfl⟩
  · intros; rfl

end FiniteField

lemma sum_range_double {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, sum_range_succ,
      sum_range_succ, sum_range_succ, ih]
    simp only [add_assoc]

lemma P_clausen_field {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (n : ℕ) (a : K) :
    GeneratingWork.P n a ^ 2 = ∑ k ∈ range (n + 1),
      (LegendreWork.d n k : K) * (Nat.centralBinom k : K) * ((a ^ 2 - 1) / 4) ^ k := by
  have h := congrArg (fun Q : Polynomial ℤ => Q.eval₂ (Int.castRingHom K) ((a - 1) / 2))
    (LegendreWork.clausen n)
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  have h4 : (4 : K) ≠ 0 := by simpa only [show (2 : K)^2 = 4 by ring] using pow_ne_zero 2 h2
  have hx : (a - 1) / 2 * (1 + (a - 1) / 2) = (a ^ 2 - 1) / 4 := by
    field_simp
    ring
  rw [hx] at h
  have hi : ∀ (x : K) (z : ℤ), (z : Polynomial ℤ).eval₂ (Int.castRingHom K) x = (z : K) :=
    fun x z => map_intCast (Polynomial.eval₂RingHom (Int.castRingHom K) x) z
  simpa [GeneratingWork.P, LegendreWork.R, Polynomial.eval₂_finset_sum, map_mul, hi] using h

section ZMod
variable {p : ℕ} [Fact p.Prime]

lemma sum_zmod_eq_range (f : ZMod p → ZMod p) :
    ∑ x : ZMod p, f x = ∑ i ∈ range p, f i := by
  symm
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ZMod p)) (by simp)
  · intro i hi j hj heq
    have := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp hi),
      ZMod.val_natCast_of_lt (mem_range.mp hj)] using this
  · intro x hx
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intros; rfl

lemma sum_even_function (m : ℕ) (hp : p = 2 * m + 1) (f : ZMod p → ZMod p)
    (h0 : f 0 = 0) (heven : ∀ x, f (-x) = f x) :
    ∑ u : (ZMod p)ˣ, f u = 2 * ∑ i ∈ range m, f (2 * i + 1) := by
  rw [sum_units_eq_sum_field f h0, sum_zmod_eq_range]
  rw [show range p = range (2 * m + 1) from congrArg range hp, sum_range_succ', Nat.cast_zero, h0, add_zero, sum_range_double, sum_add_distrib]
  have hreflect : ∑ i ∈ range m, f ((2 * i + 1 + 1 : ℕ) : ZMod p) =
      ∑ i ∈ range m, f (2 * i + 1) := by
    rw [← sum_range_reflect (fun i => f (2 * i + 1)) m]
    apply sum_congr rfl
    intro i hi
    have hnat : 2 * (m - 1 - i) + 1 + (2 * i + 1 + 1) = p := by
      have := mem_range.mp hi
      omega
    have heq : (2 * ((m - 1 - i : ℕ) : ZMod p) + 1) = -((2 * i + 1 + 1 : ℕ) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      have hh := congrArg (fun n : ℕ => (n : ZMod p)) hnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ZMod.natCast_self] using hh
    rw [heq, heven]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hreflect ⊢
  rw [hreflect, two_mul]

lemma correction_half_field (m : ℕ) (hp : p = 2 * m + 1) (hp3 : 3 < p)
    (c : ℕ → ZMod p) (k : ℕ) (hk : k ≤ m) :
    2 * (∑ i ∈ range m, (2 * i + 1 : ZMod p)⁻¹ ^ 2 *
      ∏ j ∈ range k, (1 - c j * (2 * i + 1 : ZMod p) ^ 2)) =
      ∑ j ∈ range k, c j := by
  rw [← sum_even_function m hp (fun x => x⁻¹ ^ 2 * ∏ j ∈ range k, (1 - c j * x ^ 2))
    (by simp) (by intro x; simp)]
  apply correction_full_field
  · simpa using hp3
  · rw [ZMod.card]
    omega

lemma natCast_ne_zero_small {n : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hn hnp

lemma P_deform_mod (m : ℕ) (hp : p = 2 * m + 1) (hp3 : 3 < p)
    (i : ℕ) (hi : i ≤ m) (a : ZMod p) :
    GeneratingWork.P i a ^ 2 = ∑ k ∈ range (m + 1),
      (Nat.centralBinom k : ZMod p) ^ 3 * ((1 - a ^ 2) / 64) ^ k *
      ∏ j ∈ range k, (1 - (2 * i + 1 : ZMod p) ^ 2 / (2 * j + 1 : ZMod p) ^ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := natCast_ne_zero_small (n := 2) (by omega) (by omega)
  have h16 : (16 : ZMod p) ≠ 0 := by
    simpa only [show (2 : ZMod p)^4 = 16 by ring] using pow_ne_zero 4 h2
  have h64 : (64 : ZMod p) ≠ 0 := by
    simpa only [show (2 : ZMod p)^6 = 64 by ring] using pow_ne_zero 6 h2
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [show (2 : ZMod p)^2 = 4 by ring] using pow_ne_zero 2 h2
  rw [P_clausen_field h2]
  trans ∑ k ∈ range (m + 1), (LegendreWork.d i k : ZMod p) *
    (Nat.centralBinom k : ZMod p) * ((a ^ 2 - 1) / 4) ^ k
  · apply sum_subset (range_mono (by omega))
    intro k hk hki
    have hik : i < k := by simp only [mem_range] at *; omega
    simp [LegendreWork.d_eq_zero hik]
  · apply sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by simp only [mem_range] at hk; omega
    rw [DeformWork.d_deform i k h2 (fun j hj => by
      exact_mod_cast (natCast_ne_zero_small (p := p) (n := j + 1) (by omega) (by omega)))
      (fun j hj => by
      exact_mod_cast (natCast_ne_zero_small (p := p) (n := 2 * j + 1) (by omega) (by omega)))]
    have hh : (-1 / 16 : ZMod p) * ((a ^ 2 - 1) / 4) = (1 - a ^ 2) / 64 := by
      field_simp
      ring
    rw [← hh, mul_pow]
    ring

lemma correction_identity (m : ℕ) (hp : p = 2 * m + 1) (hp3 : 3 < p) (a : ZMod p) :
    (∑ k ∈ range (m + 1), (Nat.centralBinom k : ZMod p) ^ 3 * ((1 - a ^ 2) / 64) ^ k *
      ∑ j ∈ range k, (2 * j + 1 : ZMod p)⁻¹ ^ 2) =
    2 * ∑ i ∈ range m, GeneratingWork.P i a ^ 2 / (2 * i + 1 : ZMod p) ^ 2 := by
  have hh : ∀ i ∈ range m, GeneratingWork.P i a ^ 2 =
      ∑ k ∈ range (m + 1), (Nat.centralBinom k : ZMod p) ^ 3 * ((1 - a ^ 2) / 64) ^ k *
      ∏ j ∈ range k, (1 - (2 * i + 1 : ZMod p) ^ 2 * (2 * j + 1 : ZMod p)⁻¹ ^ 2) := by
    intro i hi
    simpa only [div_eq_mul_inv, inv_pow] using P_deform_mod m hp hp3 i (by simpa using (mem_range.mp hi).le) a
  simp only [div_eq_mul_inv, ← inv_pow] at hh ⊢
  have hs := sum_congr rfl (fun (i : ℕ) hi => congrArg
    (fun x : ZMod p => x * (2 * i + 1 : ZMod p)⁻¹ ^ 2) (hh i hi))
  rw [hs]
  simp_rw [sum_mul]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hc := correction_half_field m hp hp3 (fun j => (2 * j + 1 : ZMod p)⁻¹ ^ 2) k
    (by have := mem_range.mp hk; omega)
  simp_rw [mul_comm ((2 * _ + 1 : ZMod p)⁻¹ ^ 2) ((2 * _ + 1 : ZMod p) ^ 2)] at hc
  rw [← hc]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

end ZMod
end CorrectionWork

end

section

namespace DeformApproxWork
open Finset PowerSeries ApproxWork
open scoped PowerSeries BigOperators
variable {K : Type*} [NormedField K] [CharZero K] [IsUltrametricDist K]

noncomputable def F (m : ℕ) (a : K) : K :=
  ∑ k ∈ range (m+1), (Nat.centralBinom k:K)^3*((1-a^2)/64)^k
noncomputable def Corr (m : ℕ) (a : K) : K :=
  ∑ k ∈ range (m+1), (Nat.centralBinom k:K)^3*((1-a^2)/64)^k *
    ∑ j ∈ range k, (2*j+1:K)⁻¹^2
noncomputable def T (m : ℕ) (a : K) : K :=
  ∑ i ∈ range m, GeneratingWork.P i a ^2/(2*i+1:K)^2

lemma T_eq (m : ℕ) (a : K) : NormalizedCoeffWork.T (GeneratingWork.Gquartic a) (2*m+1) = T m a := by
  simp only [NormalizedCoeffWork.T, Nat.add_sub_cancel]
  rw [CorrectionWork.sum_range_double]
  simp only [GeneratingWork.coeff_Gquartic_even, PadicCoefficientWork.coeff_Gquartic_odd,
    zero_div, zero_pow (by decide : 2≠0), add_zero, T]
  apply sum_congr rfl
  intro i hi
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_pow]

lemma deformation_approx (p m : ℕ) (hp : p=2*m+1) (a : K) (r : ℝ)
    (hr0 : 0≤r) (hr1 : r≤1) (hpNorm : ‖(p:K)‖=r)
    (hz : ‖(1-a^2)/64‖≤1) (hcb : ∀k, ‖(Nat.centralBinom k:K)‖≤1)
    (hunit : ∀ i : ℕ, 0 < i → i < p → ‖(i:K)‖=1) :
    Cong r 3 (F m a) (GeneratingWork.P m a^2+(p:K)^2*Corr m a) := by
  have hs : Cong r 3 (GeneratingWork.P m a^2) (F m a-(p:K)^2*Corr m a) := by
    rw [DeformWork.P_deform]
    have hpc : (2*m+1:K)=(p:K) := by exact_mod_cast hp.symm
    simp only [hpc]
    have hh : ∀k∈range (m+1), Cong r 3
        (∏j∈range k,(1-(p:K)^2/(2*j+1:K)^2))
        (1-(p:K)^2*∑j∈range k,(2*j+1:K)⁻¹^2) := by
      intro k hk
      have he := prod_first_order (range k) (fun j => -(p:K)^2/(2*j+1:K)^2) hr0 hr1 2 (by
        intro j hj
        have hu : ‖(2*j+1:K)‖=1 := by
          exact_mod_cast hunit (2*j+1) (by omega) (by have := mem_range.mp hk; have := mem_range.mp hj; omega)
        rw [norm_div,norm_neg,norm_pow,norm_pow,hu,hpNorm,one_pow,div_one])
      have he' := he.mono hr0 hr1 (by decide : 3≤2*2)
      convert he' using 1
      · congr 1; ext j; ring
      · simp only [mul_sum, sum_neg_distrib, sub_eq_add_neg, div_eq_mul_inv, inv_pow, neg_mul]
    have hh' := Cong.sum (range (m+1)) hr0 (fun k hk =>
      (hh k hk).mul_left_unit (unit_mul_bound (unit_pow_bound (hcb k) 3) (unit_pow_bound hz k)))
    convert hh' using 1
    simp only [F,Corr,mul_sub,mul_one,sum_sub_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro k hk
    ring
  have hh := hs.add (Cong.refl hr0 3 ((p:K)^2*Corr m a))
  simpa only [sub_add_cancel] using hh.symm

end DeformApproxWork

end

section

namespace ReductionWork
open Finset ApproxWork
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

def Rel (x : ℚ_[p]) (y : ZMod p) : Prop := ∃ z : ℤ_[p], (z:ℚ_[p])=x ∧ PadicInt.toZMod z=y

namespace Rel
variable {x x' : ℚ_[p]} {y y' : ZMod p}
lemma norm (h : Rel x y) : ‖x‖ ≤ 1 := by obtain ⟨z,rfl,_⟩ := h; exact z.2
lemma nat (n : ℕ) : Rel (n:ℚ_[p]) (n:ZMod p) := ⟨n,by simp,by simp⟩
lemma int (n : ℤ) : Rel (n:ℚ_[p]) (n:ZMod p) := ⟨n,by simp,by simp⟩
lemma add (h : Rel x y) (h' : Rel x' y') : Rel (x+x') (y+y') := by
  obtain ⟨z,rfl,rfl⟩ := h; obtain ⟨z',rfl,rfl⟩ := h'
  exact ⟨z+z',by simp,by simp⟩
lemma sub (h : Rel x y) (h' : Rel x' y') : Rel (x-x') (y-y') := by
  obtain ⟨z,rfl,rfl⟩ := h; obtain ⟨z',rfl,rfl⟩ := h'
  exact ⟨z-z',by simp,by simp⟩
lemma mul (h : Rel x y) (h' : Rel x' y') : Rel (x*x') (y*y') := by
  obtain ⟨z,rfl,rfl⟩ := h; obtain ⟨z',rfl,rfl⟩ := h'
  exact ⟨z*z',by simp,by simp⟩
lemma pow (h : Rel x y) (n : ℕ) : Rel (x^n) (y^n) := by
  obtain ⟨z,rfl,rfl⟩ := h
  exact ⟨z^n,by simp,by simp⟩
lemma inv (h : Rel x y) (hx : ‖x‖=1) : Rel x⁻¹ y⁻¹ := by
  obtain ⟨z,rfl,rfl⟩ := h
  have hu : IsUnit z := PadicInt.isUnit_iff.mpr hx
  obtain ⟨u,rfl⟩ := hu
  refine ⟨↑u⁻¹,?_,?_⟩
  · have hh := congrArg (PadicInt.Coe.ringHom (p := p)) (show (↑u⁻¹ : ℤ_[p]) * ↑u = 1 by simp)
    simp only [map_mul,map_one] at hh
    exact eq_inv_of_mul_eq_one_left hh
  · have hh := congrArg (PadicInt.toZMod (p := p)) (show (↑u⁻¹ : ℤ_[p]) * ↑u = 1 by simp)
    simp only [map_mul,map_one] at hh
    exact eq_inv_of_mul_eq_one_left hh
lemma div (h : Rel x y) (h' : Rel x' y') (hx : ‖x'‖=1) : Rel (x/x') (y/y') := by
  simpa only [div_eq_mul_inv] using h.mul (h'.inv hx)
lemma sum {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) (g : ι → ZMod p)
    (h : ∀i∈s,Rel (f i) (g i)) : Rel (∑i∈s,f i) (∑i∈s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nat (p := p) 0
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))
lemma poly (Q : Polynomial ℤ) (h : Rel x y) :
    Rel (Q.eval₂ (Int.castRingHom ℚ_[p]) x) (Q.eval₂ (Int.castRingHom (ZMod p)) y) := by
  rw [Polynomial.eval₂_eq_sum,Polynomial.eval₂_eq_sum]
  exact sum Q.support _ _ (fun i hi => (int _).mul (h.pow i))
lemma cong (h : Rel x y) (h' : Rel x' y) : Cong ‖(p:ℚ_[p])‖ 1 x x' := by
  obtain ⟨z,rfl,hz⟩ := h; obtain ⟨z',rfl,hz'⟩ := h'
  have he : PadicInt.toZMod (z-z')=0 := by rw [map_sub,hz,hz',sub_self]
  have hm : z-z' ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod,RingHom.mem_ker]; exact he
  have hn : ‖z-z'‖ < 1 := by
    rw [← PadicInt.mem_nonunits]
    exact hm
  have hh := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (z-z') 0).mp (by simpa using hn)
  simpa only [Cong,pow_one,Padic.norm_p,PadicInt.norm_def,PadicInt.coe_sub,
    zero_sub,zpow_neg_one] using hh
end Rel

lemma norm_two (hp3 : 3<p) : ‖(2:ℚ_[p])‖=1 := by
  exact_mod_cast PadicCoefficientWork.small_norm (p := p) 2 (by omega) (by omega)
lemma norm_64 (hp3 : 3<p) : ‖(64:ℚ_[p])‖=1 := by
  have hh := congrArg (fun x:ℝ => x^6) (norm_two hp3)
  simpa only [←norm_pow,show (2:ℚ_[p])^6=64 by norm_num,one_pow] using hh
lemma rel_P (hp3 : 3<p) {a : ℚ_[p]} {b : ZMod p} (ha : Rel a b) (n : ℕ) :
    Rel (GeneratingWork.P n a) (GeneratingWork.P n b) := by
  exact Rel.poly _ ((ha.sub (by exact_mod_cast Rel.nat (p := p) 1)).div
    (by exact_mod_cast Rel.nat (p := p) 2) (norm_two hp3))

lemma correction_cong (m : ℕ) (hp : p=2*m+1) (hp3 : 3<p) (a : ℚ_[p]) (ha : ‖a‖≤1) :
    Cong ‖(p:ℚ_[p])‖ 1 (DeformApproxWork.Corr m a) (2*DeformApproxWork.T m a) := by
  let b := PadicInt.toZMod (⟨a,ha⟩:ℤ_[p])
  have hab : Rel a b := ⟨⟨a,ha⟩,rfl,rfl⟩
  have hz : Rel ((1-a^2)/64) ((1-b^2)/64) :=
    (Rel.sub (by exact_mod_cast Rel.nat (p := p) 1) (hab.pow 2)).div
      (by exact_mod_cast Rel.nat (p := p) 64) (norm_64 hp3)
  have ho : ∀ i < m, ‖(2*i+1:ℚ_[p])‖=1 := by
    intro i hi
    exact_mod_cast PadicCoefficientWork.small_norm (p := p) (2*i+1) (by omega) (by omega)
  have hor : ∀ i : ℕ, Rel (2*i+1:ℚ_[p]) (2*i+1:ZMod p) := by intro i; exact_mod_cast Rel.nat (p := p) (2*i+1)
  have hC : Rel (DeformApproxWork.Corr m a)
      (∑k∈range (m+1),(Nat.centralBinom k:ZMod p)^3*((1-b^2)/64)^k *
        ∑j∈range k,(2*j+1:ZMod p)⁻¹^2) := by
    apply Rel.sum
    intro k hk
    exact ((Rel.nat _).pow 3 |>.mul (hz.pow k)).mul (Rel.sum (range k) _ _ (fun j hj =>
      ((hor j).inv (ho j (by have := mem_range.mp hk; have := mem_range.mp hj; omega))).pow 2))
  rw [CorrectionWork.correction_identity m hp hp3 b] at hC
  apply hC.cong
  apply Rel.mul (by exact_mod_cast Rel.nat (p := p) 2)
  apply Rel.sum
  intro i hi
  exact ((rel_P hp3 hab i).pow 2).div ((hor i).pow 2) (by rw [norm_pow,ho i (mem_range.mp hi),one_pow])

end ReductionWork

end

section

namespace OrdinaryWork
open ApproxWork PowerSeries DeformApproxWork
open scoped PowerSeries
variable {p : ℕ} [Fact p.Prime]

lemma hypergeometric (m : ℕ) (hp : p=2*m+1) (hp3 : 3<p) (w : ℤ_[p])
    (hw : w^2-w+2=0) (z : O7Work.O) (hz : z.norm=p)
    (hu : IsUnit ((z.re:ℤ_[p])+(z.im:ℤ_[p])*(1-w))) :
    let a : ℚ_[p] := -3*((w:ℚ_[p])+2)/8
    let c : ℚ_[p] := (z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p])
    Cong ‖(p:ℚ_[p])‖ 3 (F m a) (((p:ℚ_[p])/c)^2) := by
  let a : ℚ_[p] := -3*((w:ℚ_[p])+2)/8
  let c : ℚ_[p] := (z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p])
  let r := ‖(p:ℚ_[p])‖
  have ha : ‖a‖≤1 := PadicCoefficientWork.parameter_mem (by omega) w
  obtain ⟨hr0,hr1⟩ := PadicCoefficientWork.prime_radius (p := p)
  have hzNorm : ‖(1-a^2)/64‖≤1 := by
    rw [norm_div,ReductionWork.norm_64 hp3,div_one]
    exact unit_sub_bound (by simp) (unit_pow_bound ha 2)
  have hd := deformation_approx p m hp a r hr0.le hr1.le rfl hzNorm
    (fun k => Padic.norm_int_le_one _) PadicCoefficientWork.small_norm
  have hc := PadicCoefficientWork.ordinary_coefficient (by omega) (by omega) w hw z hz hu
  change Cong r 3 _ _ at hc
  have he : p-1=2*m := by omega
  have hT : NormalizedCoeffWork.T (GeneratingWork.Gquartic a) p = T m a := by
    simpa only [hp] using T_eq (K := ℚ_[p]) m a
  rw [he,GeneratingWork.coeff_Gquartic_even] at hc
  change Cong r 3 (GeneratingWork.P m a^2) (((p:ℚ_[p])/c)^2-2*(p:ℚ_[p])^2*NormalizedCoeffWork.T (GeneratingWork.Gquartic a) p) at hc
  rw [hT] at hc
  have hcorr := ReductionWork.correction_cong m hp hp3 a ha
  have hcorr' := hcorr.mul_left (m := 2) (a := (p:ℚ_[p])^2) (by simp only [norm_pow]; rfl)
  have hsum := hc.add hcorr'
  have hsum' : Cong r 3 (GeneratingWork.P m a^2+(p:ℚ_[p])^2*Corr m a) (((p:ℚ_[p])/c)^2) := by
    convert hsum using 1 <;> ring
  exact hd.trans hsum'

end OrdinaryWork

end

section

set_option maxHeartbeats 1500000

namespace FieldGeneratingWork
open PowerSeries
open scoped PowerSeries

noncomputable def Lseries : (Polynomial ℤ)⟦X⟧ := mk LegendreWork.L

lemma map_Lseries {K : Type*} [Field K] (h2 : (2:K)≠0) (x : K) :
    PowerSeries.map (Polynomial.eval₂RingHom (Int.castRingHom K) x) Lseries = GeneratingWork.G (1+2*x) := by
  ext n
  simp only [coeff_map,Lseries,coeff_mk,GeneratingWork.G,coeff_mk,GeneratingWork.P,
    Polynomial.coe_eval₂RingHom]
  congr 1
  field_simp
  ring

lemma Lseries_sq : Lseries^2*(1-2*C (1+2*Polynomial.X)*X+X^2)=1 := by
  let φ : Polynomial ℤ →+* RatFunc ℚ := Polynomial.eval₂RingHom (Int.castRingHom _) RatFunc.X
  have hφeq : φ = (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · simp only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply]
      change RatFunc.X = (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.map (Int.castRingHom ℚ) Polynomial.X)
      rw [Polynomial.map_X,RatFunc.algebraMap_X]
  have hφ : Function.Injective φ := by
    rw [hφeq]
    exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)
  apply PowerSeries.map_injective φ hφ
  simp only [map_mul,map_pow,map_add,map_sub,map_one,map_ofNat,PowerSeries.map_C,PowerSeries.map_X]
  dsimp only [φ]
  rw [map_Lseries (K := RatFunc ℚ) (by norm_num)]
  simpa only [φ, Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,map_add,map_one,map_mul,map_ofNat]
    using GeneratingWork.G_sq (1+2*(RatFunc.X:RatFunc ℚ))

lemma G_sq {K : Type*} [Field K] (h2 : (2:K)≠0) (a : K) :
    GeneratingWork.G a ^2*(1-2*C a*X+X^2)=1 := by
  let x := (a-1)/2
  have hx : 1+2*x=a := by dsimp [x]; field_simp; ring
  have hh := congrArg (PowerSeries.map (Polynomial.eval₂RingHom (Int.castRingHom K) x)) Lseries_sq
  simp only [map_mul,map_pow,map_add,map_sub,map_one,map_ofNat,PowerSeries.map_C,PowerSeries.map_X,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_mul,
    Polynomial.eval₂_ofNat,Polynomial.eval₂_X] at hh
  rw [map_Lseries h2,hx] at hh
  simpa only [←map_ofNat C,←map_mul,←map_one C,←map_add,hx] using hh

lemma Gquartic_sq {K : Type*} [Field K] (h2 : (2:K)≠0) (a : K) :
    GeneratingWork.Gquartic a ^2*(1-2*C a*X^2+X^4)=1 := by
  have h := congrArg (expand (R := K) 2 (by decide)) (G_sq h2 a)
  simp only [map_mul,map_sub,map_add,map_pow,map_one,map_ofNat,expand_C,expand_X] at h
  simpa only [GeneratingWork.Gquartic,←pow_mul,show 2*2=4 by rfl] using h

lemma sq_unique {K : Type*} [Field K] (h2 : (2:K)≠0) {f g : K⟦X⟧}
    (hf : constantCoeff f=1) (hg : constantCoeff g=1) (hsq : f^2=g^2) : f=g := by
  have hh : (f-g)*(f+g)=0 := by linear_combination hsq
  rcases mul_eq_zero.mp hh with hh | hh
  · exact sub_eq_zero.mp hh
  · have hh' := congrArg (constantCoeff (R := K)) hh
    simp only [map_add,map_zero,hf,hg] at hh'
    exact (h2 (by simpa only [one_add_one_eq_two] using hh')).elim

end FieldGeneratingWork

end

section

namespace FieldCMWork
open PowerSeries AdditionWork
open scoped PowerSeries
variable {K : Type*} [Field K]

noncomputable def cm (a w : K) (y : K⟦X⟧) (hy0 : constantCoeff y = 1)
    (hy : y ^ 2 = 1 - 2 * C a * X ^ 2 + X ^ 4)
    (hw1 : a * w ^ 2 = a + 3) (hw2 : w ^ 4 = 8 * (a + 1)) : EndPair a y w := by
  let D : K⟦X⟧ := 1 + X^2
  let N : K⟦X⟧ := C w * X
  let M : K⟦X⟧ := (1-X^2)*y
  let F := N * D⁻¹
  let YY := M * (D⁻¹)^2
  have hD0 : constantCoeff D = 1 := by simp [D]
  have hD : D ≠ 0 := by intro hz; simp [hz] at hD0
  have hDD : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel D (by rw [hD0]; exact one_ne_zero)
  have hF : F * D = N := by simp only [F, mul_assoc, hDD, mul_one]
  have hY : YY * D ^ 2 = M := by
    change (M * (D⁻¹)^2) * D^2 = M
    rw [mul_assoc, ← mul_pow, hDD, one_pow, mul_one]
  refine ⟨F, YY, ?_, ?_, ?_, ?_⟩
  · simp [F, N]
  · simp [YY, M, D, hy0]
  · have h1 : C a * (C w)^2 = C a + 3 := by
      simpa only [map_add, map_ofNat, map_mul, map_pow] using congrArg C hw1
    have h2 : (C w)^4 = 8 * (C a + 1) := by
      simpa only [map_add, map_one, map_ofNat, map_mul, map_pow] using congrArg C hw2
    have hcurve := CMWork.quartic_isogeny_identity (C a) (C w) X h1 h2
    apply mul_right_cancel₀ (pow_ne_zero 4 hD)
    calc
      YY ^ 2 * D ^ 4 = (YY * D ^ 2) ^ 2 := by ring
      _ = M ^ 2 := by rw [hY]
      _ = D ^ 4 - 2 * C a * N ^ 2 * D ^ 2 + N ^ 4 := by
        change ((1-X^2)*y)^2 = _
        rw [mul_pow, hy]
        exact hcurve.symm
      _ = (1 - 2 * C a * F ^ 2 + F ^ 4) * D ^ 4 := by rw [← hF]; ring
  · have hfd := congrArg (d⁄dX K) hF
    have hDdiff : d⁄dX K D = 2 * X := by
      simp [D, pow_two, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero]
      ring
    have hNdiff : d⁄dX K N = C w := by simp [N, Derivation.leibniz, smul_eq_mul]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDdiff, hNdiff] at hfd
    apply mul_right_cancel₀ (pow_ne_zero 2 hD)
    calc
      (d⁄dX K F * y) * D^2 = (C w * D - N * (2*X)) * y := by
        rw [← hF]
        linear_combination D * y * hfd
      _ = C w * M := by dsimp [D, N, M]; ring
      _ = (C w * YY) * D^2 := by rw [← hY]; ring

lemma constantCoeff_subst_self {h : K⟦X⟧} (hh : constantCoeff h = 0) (f : K⟦X⟧) :
    constantCoeff (subst h f) = constantCoeff f := by
  change MvPowerSeries.constantCoeff (subst h f) = constantCoeff f
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' hh)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro d hd
    have hh' : MvPowerSeries.constantCoeff h = 0 := hh
    simp [hh', hd]


lemma G0 (a : K) : constantCoeff (GeneratingWork.Gquartic a)=1 := by
  simp [GeneratingWork.Gquartic,GeneratingWork.G,GeneratingWork.P,LegendreWork.L,LegendreWork.d]

lemma differential (h2 : (2:K)≠0) (a w : K)
    (hw1 : a*w^2=a+3) (hw2 : w^4=8*(a+1)) :
    let f : K⟦X⟧ := C w*X*(1+X^2)⁻¹
    subst f (GeneratingWork.Gquartic a)*d⁄dX K f = C w*GeneratingWork.Gquartic a := by
  let G := GeneratingWork.Gquartic a
  let y := G⁻¹
  have hG0 : constantCoeff G=1 := G0 a
  have hy0 : constantCoeff y=1 := by simp [y,hG0]
  have hGy : G*y=1 := PowerSeries.mul_inv_cancel G (by rw [hG0]; exact one_ne_zero)
  have hysq : y^2=1-2*C a*X^2+X^4 := by
    have hh := FieldGeneratingWork.Gquartic_sq h2 a
    change G^2*(1-2*C a*X^2+X^4)=1 at hh
    calc
      y^2 = y^2*(G^2*(1-2*C a*X^2+X^4)) := by rw [hh,mul_one]
      _ = _ := by linear_combination (G*y+1)*(1-2*C a*X^2+X^4)*hGy
  let e := cm a w y hy0 hysq hw1 hw2
  have hY : e.Y=subst e.f y := by
    apply FieldGeneratingWork.sq_unique h2 e.Y0 (constantCoeff_subst_self e.f0 y |>.trans hy0)
    have hh := congrArg (substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' e.f0)) hysq
    simp only [map_pow,map_sub,map_mul,map_add,map_one,map_ofNat,coe_substAlgHom,
      CompositionWork.subst_C (HasSubst.of_constantCoeff_zero' e.f0),subst_X (HasSubst.of_constantCoeff_zero' e.f0)] at hh
    exact e.curve.trans hh.symm
  have hs := congrArg (substAlgHom (R := K) (HasSubst.of_constantCoeff_zero' e.f0)) hGy
  simp only [map_mul,map_one,coe_substAlgHom,←hY] at hs
  change subst e.f G*d⁄dX K e.f=C w*G
  calc
    subst e.f G*d⁄dX K e.f = subst e.f G*(d⁄dX K e.f*y)*G := by
      linear_combination -(subst e.f G*d⁄dX K e.f)*hGy
    _ = C w*G := by rw [e.diff]; linear_combination C w*G*hs

end FieldCMWork

end

section

namespace ObstructionWork
open PowerSeries Finset
open scoped PowerSeries BigOperators
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

lemma small_cast (n : ℕ) (hn : 0<n) (hp : n<p) : (n:K)≠0 := by
  rw [ne_eq,CharP.cast_eq_zero_iff K p]
  exact Nat.not_dvd_of_pos_of_lt hn hp

lemma coeff_differential (f G : K⟦X⟧) (c : K) (hf0 : constantCoeff f=0)
    (hf1 : coeff 1 f=c) (hdiff : subst f G*d⁄dX K f=C c*G) :
    (c^p-c)*coeff (p-1) G=0 := by
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hh := congrArg (coeff (p-1)) hdiff
  rw [CompositionWork.coeff_subst_mul hf0 G (d⁄dX K f) (p-1) p (by omega),coeff_C_mul] at hh
  have hlow : ∀k<p-1, coeff (p-1) (f^k*d⁄dX K f)=0 := by
    intro k hk
    have hd := congrArg (coeff (p-1)) (Derivation.leibniz_pow (d⁄dX K) f (k+1))
    rw [coeff_derivative] at hd
    simp only [show p-1+1=p by omega,Nat.add_sub_cancel,smul_eq_mul] at hd
    rw [map_nsmul,nsmul_eq_mul] at hd
    have hpc : ((p-1:ℕ):K)+1=(p:K) := by
      have he := congrArg (Nat.cast (R := K)) (Nat.sub_add_cancel (by omega : 1≤p))
      simpa only [Nat.cast_add,Nat.cast_one] using he
    rw [hpc,CharP.cast_eq_zero,mul_zero] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (small_cast (k+1) (by omega) (by omega))
  have htop : coeff (p-1) (f^(p-1)*d⁄dX K f)=c^p := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
    simp only [Prod.fst,Prod.snd]
    have hz : ∑i∈range (p-1),coeff i (f^(p-1))*coeff (p-1-i) (d⁄dX K f)=0 := by
      apply sum_eq_zero
      intro i hi
      rw [CompositionWork.coeff_pow_eq_zero hf0 (mem_range.mp hi),zero_mul]
    rw [hz,zero_add,Nat.sub_self,CompositionWork.coeff_pow_self hf0,coeff_derivative]
    simp only [zero_add,Nat.cast_zero,hf1,mul_one]
    rw [←pow_succ, Nat.sub_add_cancel (by omega : 1≤p)]
  have hs : (∑k∈range p, coeff k G*coeff (p-1) (f^k*d⁄dX K f)) = coeff (p-1) G*c^p := by
    rw [show range p=range ((p-1)+1) by congr 1; omega,sum_range_succ]
    have hz : ∑k∈range (p-1),coeff k G*coeff (p-1) (f^k*d⁄dX K f)=0 := by
      apply sum_eq_zero; intro k hk; rw [hlow k (mem_range.mp hk),mul_zero]
    rw [hz,zero_add,htop]
  rw [hs] at hh
  linear_combination hh

lemma cm_vanishing (hp3 : 3<p) (m : ℕ) (hp : p=2*m+1) (w : K)
    (hw : w^2-w+2=0) (hfrob : w^p≠w) :
    GeneratingWork.P m (-3*(w+2)/8)=0 := by
  have h2 : (2:K)≠0 := by exact_mod_cast small_cast (K := K) (p := p) 2 (by omega) (by omega)
  have h8 : (8:K)≠0 := by simpa only [show (2:K)^3=8 by ring] using pow_ne_zero 3 h2
  let a := -3*(w+2)/8
  obtain ⟨hh1,hh2⟩ := CMWork.cm_parameters a w hw (by dsimp [a]; field_simp)
  have hw1 : a*w^2=a+3 := by
    have hh := (mul_eq_zero.mp hh1).resolve_left h8
    linear_combination hh
  have hw2 : w^4=8*(a+1) := sub_eq_zero.mp hh2
  let f : K⟦X⟧ := C w*X*(1+X^2)⁻¹
  have hf0 : constantCoeff f=0 := by simp [f]
  have hf1 : coeff 1 f=w := by
    have he : f*(1+X^2)=C w*X := by
      dsimp [f]
      rw [mul_assoc,PowerSeries.inv_mul_cancel _ (by simp),mul_one]
    have hh := congrArg (coeff 1) he
    rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
    norm_num [sum_range_succ,coeff_C_mul,coeff_zero_eq_constantCoeff,hf0] at hh
    exact hh
  have hh := coeff_differential f (GeneratingWork.Gquartic a) w hf0 hf1 (FieldCMWork.differential h2 a w hw1 hw2)
  have hv := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hfrob)
  have he : p-1=2*m := by omega
  rw [he] at hv
  simpa only [GeneratingWork.Gquartic,coeff_expand_mul,GeneratingWork.G,coeff_mk] using hv

end ObstructionWork

end

section

namespace InertFieldWork
variable {p : ℕ} [Fact p.Prime]

lemma split_of_root (hp2 : p≠2) (hp7 : p≠7) (w : ZMod p) (hw : w^2-w+2=0) :
    p%7 ∈ ({1,2,4}:Set ℕ) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs : IsSquare (-7:ZMod p) := ⟨2*w-1,by linear_combination -4*hw⟩
  have hn : quadraticChar (ZMod p) (-7) ≠ -1 := by
    intro hh
    exact (quadraticChar_neg_one_iff_not_isSquare.mp hh) hs
  have hc : ZMod.χ₄ (7:ZMod 4)=(-1:ℤ) := by decide
  have hs7 : IsSquare (p:ZMod 7) :=
    (FiniteField.isSquare_odd_prime_iff (F := ZMod 7) (by norm_num [ZMod.ringChar_zmod_n]) hp2).mpr
      (by simpa only [ZMod.card,Nat.cast_ofNat,hc,Int.cast_neg,Int.cast_one,neg_one_mul] using hn)
  have hp70 : p%7≠0 := by
    intro hh
    have hd := Nat.dvd_of_mod_eq_zero hh
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) Fact.out).mp hd).symm
  rw [←ZMod.natCast_mod p 7] at hs7
  have hm : p%7<7 := Nat.mod_lt _ (by decide)
  have hh : ∀ n : Fin 7, IsSquare (n.val:ZMod 7) → n.val=0 ∨ n.val=1 ∨ n.val=2 ∨ n.val=4 := by decide
  have hh' := hh ⟨p%7,hm⟩ hs7
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh'.resolve_left hp70

lemma no_root (hp2 : p≠2) (hp7 : p≠7) (hns : p%7 ∉ ({1,2,4}:Set ℕ)) :
    ∀r:ZMod p, r^2≠(-2)+1*r := by
  intro r hr
  exact hns (split_of_root hp2 hp7 r (by linear_combination hr))

abbrev E (p : ℕ) := QuadraticAlgebra (ZMod p) (-2) 1

instance : CharP (E p) p := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p

lemma omega_not_fixed [Fact (∀r:ZMod p, r^2≠(-2)+1*r)] :
    (QuadraticAlgebra.omega : E p)^p ≠ QuadraticAlgebra.omega := by
  intro hh
  have hb := (Subfield.mem_bot_iff_pow_eq_self (E p) p).mpr hh
  obtain ⟨n,hn⟩ := (mem_bot_iff_intCast p (E p)).mp hb
  have hi := congrArg QuadraticAlgebra.im hn
  simpa using hi

lemma omega_vanishing (hp3 : 3<p) (m : ℕ) (hp : p=2*m+1)
    [Fact (∀r:ZMod p, r^2≠(-2)+1*r)] :
    GeneratingWork.P m (-3*((QuadraticAlgebra.omega:E p)+2)/8)=0 := by
  apply ObstructionWork.cm_vanishing hp3 m hp _ _ omega_not_fixed
  have hh := QuadraticAlgebra.omega_mul_omega_eq_add (R := ZMod p) (a := (-2:ZMod p)) (b := 1)
  simp only [Algebra.smul_def,map_neg,map_ofNat,map_one,mul_one,one_mul] at hh
  linear_combination hh

end InertFieldWork

end

section

namespace RingDeformWork
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]

noncomputable def P (n : ℕ) (a h : R) : R := (LegendreWork.L n).eval₂ (Int.castRingHom R) ((a-1)*h)
noncomputable def F (m : ℕ) (a h : R) : R := ∑k∈range (m+1), (Nat.centralBinom k:R)^3*((1-a^2)*h^6)^k

lemma eval_int (x : R) (z : ℤ) : (z:Polynomial ℤ).eval₂ (Int.castRingHom R) x = (z:R) :=
  map_intCast (Polynomial.eval₂RingHom (Int.castRingHom R) x) z

lemma clausen (n : ℕ) (a h : R) (hh : 2*h=1) :
    P n a h ^2 = ∑k∈range (n+1), (LegendreWork.d n k:R)*(Nat.centralBinom k:R)*((a^2-1)*h^2)^k := by
  have he := congrArg (fun Q : Polynomial ℤ => Q.eval₂ (Int.castRingHom R) ((a-1)*h)) (LegendreWork.clausen n)
  simp only [Polynomial.eval₂_pow,Polynomial.eval₂_comp,Polynomial.eval₂_mul,Polynomial.eval₂_add,
    Polynomial.eval₂_X,Polynomial.eval₂_one] at he
  have hx : (a-1)*h*(1+(a-1)*h)=(a^2-1)*h^2 := by linear_combination -(a-1)*h*hh
  rw [hx] at he
  simpa [P,LegendreWork.R,Polynomial.eval₂_finset_sum,map_mul,eval_int] using he

lemma d_recur (n k : ℕ) : (k+1:R)^2*(LegendreWork.d n (k+1):R) =
    ((n:R)*(n+1)-k*(k+1))*(LegendreWork.d n k:R) := by
  have hh := congrArg (Int.castRingHom R) (LegendreWork.d_recur n k)
  simpa using hh
lemma central_recur (k : ℕ) : (k+1:R)*(Nat.centralBinom (k+1):R)=2*(2*k+1:R)*Nat.centralBinom k := by
  have hh := congrArg (Nat.castRingHom R) (Nat.succ_mul_centralBinom_succ k)
  simpa using hh

lemma d_mod_square (m k : ℕ) (h : R) (hh : 2*h=1) (hp : (2*m+1:R)^2=0)
    (hunit : ∀ j < k, IsUnit (j+1:R)) :
    (LegendreWork.d m k:R)=(Nat.centralBinom k:R)^2*(-h^4)^k := by
  have hm : (m:R)*(m+1)=-h^2 := by
    have hh2 : 4*h^2=1 := by linear_combination (2*h+1)*hh
    linear_combination h^2*hp-((m:R)*(m+1))*hh2
  induction k with
  | zero => simp [LegendreWork.d_zero]
  | succ k ih =>
    have hi := ih (fun j hj => hunit j (by omega))
    have hd := d_recur (R := R) m k
    have hc := central_recur (R := R) k
    have hh4 : 4*h^2=1 := by linear_combination (2*h+1)*hh
    apply (hunit k (by omega) |>.pow 2).mul_left_cancel
    simp only [Nat.cast_add,Nat.cast_one] at hd ⊢
    rw [hd,hm,hi,pow_succ (-h^4) k]
    have hc2 : (k+1:R)^2*(Nat.centralBinom (k+1):R)^2=4*(2*k+1:R)^2*(Nat.centralBinom k:R)^2 := by
      linear_combination ((k+1:R)*(Nat.centralBinom (k+1):R)+2*(2*k+1:R)*(Nat.centralBinom k:R))*hc
    have hmul : ((k: R)+1)^2 * ((Nat.centralBinom (k+1):R)^2*((-h^4)^k * -h^4)) =
        -4*(2*k+1:R)^2*(Nat.centralBinom k:R)^2*(-h^4)^k*h^4 := by
      linear_combination -(-h^4)^k*h^4*hc2
    push_cast
    rw [hmul]
    linear_combination (Nat.centralBinom k:R)^2*(-h^4)^k*(h^2*(2*k+1:R)^2+k*(k+1))*hh4

lemma hypergeometric_square (m : ℕ) (a h : R) (hh : 2*h=1) (hp : (2*m+1:R)^2=0)
    (hunit : ∀ j < m, IsUnit (j+1:R)) : F m a h=P m a h^2 := by
  rw [clausen m a h hh]
  apply sum_congr rfl
  intro k hk
  rw [d_mod_square m k h hh hp (fun j hj => hunit j (by have := mem_range.mp hk; omega))]
  have he : (-h^4)*((a^2-1)*h^2)=(1-a^2)*h^6 := by ring
  rw [←he,mul_pow]
  ring

end RingDeformWork

end

section

namespace QuadraticModWork
open QuadraticAlgebra Finset
open scoped BigOperators

abbrev Q (n : ℕ) := QuadraticAlgebra (ZMod n) (-2) 1

noncomputable def mapQ {m n : ℕ} (h : n ∣ m) : Q m →+* Q n where
  toFun x := ⟨ZMod.castHom h (ZMod n) x.re, ZMod.castHom h (ZMod n) x.im⟩
  map_zero' := by ext <;> simp [-ZMod.castHom_apply]
  map_one' := by ext <;> simp [-ZMod.castHom_apply]
  map_add' x y := by ext <;> simp [-ZMod.castHom_apply]
  map_mul' x y := by ext <;> simp [-ZMod.castHom_apply, map_mul,map_add,map_sub,map_ofNat]

@[simp] lemma mapQ_re {m n : ℕ} (h : n∣m) (x : Q m) : (mapQ h x).re=ZMod.castHom h (ZMod n) x.re := rfl
@[simp] lemma mapQ_im {m n : ℕ} (h : n∣m) (x : Q m) : (mapQ h x).im=ZMod.castHom h (ZMod n) x.im := rfl
@[simp] lemma mapQ_omega {m n : ℕ} (h : n∣m) : mapQ h omega=omega := by ext <;> simp [mapQ,-ZMod.castHom_apply]

noncomputable def half (n : ℕ) : Q n := algebraMap (ZMod n) (Q n) ((2:ZMod n)⁻¹)
lemma half_spec {n : ℕ} (hn : n.Coprime 2) : 2*half n=1 := by
  have hh := ZMod.mul_inv_of_unit (2:ZMod n) (by exact_mod_cast (ZMod.isUnit_iff_coprime 2 n).mpr hn.symm)
  have he := congrArg (algebraMap (ZMod n) (Q n)) hh
  simpa only [map_mul,map_ofNat,map_one] using he

lemma unit_small {p : ℕ} (hp : p.Prime) (n i : ℕ) (hi : 0 < i) (hip : i < p) : IsUnit (i:Q (p^n)) := by
  have hh : IsUnit (i:ZMod (p^n)) := (ZMod.isUnit_iff_coprime i (p^n)).mpr
    (hp.coprime_pow_of_not_dvd (Nat.not_dvd_of_pos_of_lt hi hip))
  simpa only [map_natCast] using hh.map (algebraMap (ZMod (p^n)) (Q (p^n)))

lemma omega_equation (n : ℕ) : (omega:Q n)^2-omega+2=0 := by
  have hh := omega_mul_omega_eq_add (R := ZMod n) (a := (-2:ZMod n)) (b := 1)
  simp only [Algebra.smul_def,map_neg,map_ofNat,map_one,mul_one,one_mul] at hh
  linear_combination hh

lemma square_prime (p : ℕ) : (p:Q (p^2))^2=0 := by
  have hh := congrArg (algebraMap (ZMod (p^2)) (Q (p^2))) (ZMod.natCast_self (p^2))
  simpa only [map_natCast,map_zero,Nat.cast_pow,map_pow] using hh

lemma kernel_cast_dvd {p : ℕ} [Fact p.Prime] (x : ZMod (p^2))
    (hx : ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) (ZMod p) x=0) : (p:ZMod (p^2))∣x := by
  rw [ZMod.castHom_apply,ZMod.cast_eq_val,ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨k,hk⟩ := hx
  refine ⟨k,?_⟩
  rw [←ZMod.natCast_zmod_val x,hk,Nat.cast_mul]

lemma kernel_square {p : ℕ} [Fact p.Prime] (x : Q (p^2))
    (hx : mapQ (dvd_pow_self p (by decide : 2≠0)) x=0) : x^2=0 := by
  have hr := congrArg QuadraticAlgebra.re hx
  have hi := congrArg QuadraticAlgebra.im hx
  obtain ⟨u,hu⟩ := kernel_cast_dvd x.re (by simpa using hr)
  obtain ⟨v,hv⟩ := kernel_cast_dvd x.im (by simpa using hi)
  have he : x=(p:Q (p^2))*⟨u,v⟩ := by ext <;> simp [hu,hv]
  rw [he,mul_pow,square_prime,zero_mul]

lemma map_P {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (a h : R) :
    φ (RingDeformWork.P n a h)=RingDeformWork.P n (φ a) (φ h) := by
  simp only [RingDeformWork.P,Polynomial.hom_eval₂,map_mul,map_sub,map_one,
    RingHom.ext_int (φ.comp (Int.castRingHom R)) (Int.castRingHom S)]

lemma half_mod {p : ℕ} [Fact p.Prime] (hp2 : p≠2)
    [Fact (∀r:ZMod p, r^2≠(-2)+1*r)] :
    mapQ (dvd_pow_self p (by decide : 2≠0)) (half (p^2)) = (1/2:Q p) := by
  have hcop : (p^2).Coprime 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (by intro hh; have := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hh; rcases this with h|h <;> [exact (Fact.out : p.Prime).ne_one h; exact hp2 h]) |>.pow_left _
  have hh := congrArg (mapQ (dvd_pow_self p (by decide : 2≠0))) (half_spec hcop)
  simp only [map_mul,map_ofNat,map_one] at hh
  have ht : (2:Q p)≠0 := by intro hz; rw [hz,zero_mul] at hh; exact zero_ne_one hh
  apply (eq_div_iff ht).mpr
  simpa only [mul_comm] using hh

lemma inert_hypergeometric {p : ℕ} [Fact p.Prime] (hp3 : 3<p) (m : ℕ) (hp : p=2*m+1)
    [Fact (∀r:ZMod p, r^2≠(-2)+1*r)] :
    let h := half (p^2)
    let a := -3*((omega:Q (p^2))+2)*h^3
    RingDeformWork.F m a h=0 := by
  let h := half (p^2)
  let a := -3*((omega:Q (p^2))+2)*h^3
  have hcop : (p^2).Coprime 2 := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) |>.pow_left _
  have hh : 2*h=1 := half_spec hcop
  have hpz : (2*m+1:Q (p^2))^2=0 := by
    have hc : (2*m+1:Q (p^2))=(p:Q (p^2)) := by
      have he := congrArg (fun n : ℕ => (n:Q (p^2))) hp.symm
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using he
    rw [hc,square_prime]
  change RingDeformWork.F m a h=0
  rw [RingDeformWork.hypergeometric_square m a h hh hpz (fun j hj => by
    simpa only [Nat.cast_add,Nat.cast_one] using unit_small Fact.out 2 (j+1) (by omega) (by omega))]
  apply kernel_square
  rw [map_P]
  have hhmap : mapQ (dvd_pow_self p (by decide : 2≠0)) h=(1/2:Q p) := half_mod (by omega)
  have hamap : mapQ (dvd_pow_self p (by decide : 2≠0)) a=-3*((omega:Q p)+2)/8 := by
    simp only [a,map_mul,map_neg,map_ofNat,map_add,map_pow,mapQ_omega,hhmap]
    rw [show (8:Q p)=2^3 by ring]
    simp only [div_eq_mul_inv,one_mul,inv_pow]
  rw [hhmap,hamap]
  simpa only [RingDeformWork.P,GeneratingWork.P,div_eq_mul_inv,one_mul] using InertFieldWork.omega_vanishing hp3 m hp

end QuadraticModWork

end

section

def aWork : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * aWork (n + 1) - 8 * aWork n

open Finset Nat
open scoped BigOperators

lemma aWork_step (n : ℕ) : aWork (n + 2) = 5 * aWork (n + 1) - 8 * aWork n := rfl

lemma aWork_step_eight (n : ℕ) :
    aWork (n + 8) = -47 * aWork (n + 4) - 4096 * aWork n := by
  have h0 := aWork_step n
  have h1 := aWork_step (n + 1)
  have h2 := aWork_step (n + 2)
  have h3 := aWork_step (n + 3)
  have h4 := aWork_step (n + 4)
  have h5 := aWork_step (n + 5)
  have h6 := aWork_step (n + 6)
  norm_num [Nat.add_assoc] at h0 h1 h2 h3 h4 h5 h6
  linarith

lemma aWork_four_step (k : ℕ) :
    aWork (4 * (k + 2)) = -47 * aWork (4 * (k + 1)) - 4096 * aWork (4 * k) := by
  simpa [Nat.mul_add] using aWork_step_eight (4 * k)

lemma central_choose_dvd_work {p k : ℕ} (hp : p.Prime)
    (hk : k < p) (hpk : p ≤ 2 * k) : p ∣ choose (2 * k) k := by
  have h := hp.dvd_choose_add hk hk (show p ≤ k + k by omega)
  simpa [two_mul] using h

lemma central_choose_cube_zero_work {p k n : ℕ} (hp : p.Prime)
    (hk : k < p) (hpk : p ≤ 2 * k) (hn : n ≤ 3) :
    ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact dvd_trans (pow_dvd_pow p hn)
    (pow_dvd_pow_of_dvd (central_choose_dvd_work hp hk hpk) 3)

lemma sum_truncate_work {p n : ℕ} (hp : p.Prime) (hn : n ≤ 3) :
    (range p).sum (fun k =>
      (aWork (4 * k) : ZMod (p ^ n)) * (choose (2 * k) k : ZMod (p ^ n)) ^ 3 *
        (((-4096 : ℤ) : ZMod (p ^ n)) ^ k)⁻¹) =
    (range (p / 2 + 1)).sum (fun k =>
      (aWork (4 * k) : ZMod (p ^ n)) * (choose (2 * k) k : ZMod (p ^ n)) ^ 3 *
        (((-4096 : ℤ) : ZMod (p ^ n)) ^ k)⁻¹) := by
  symm
  apply Finset.sum_subset
  · apply Finset.range_mono
    have := hp.two_le
    omega
  · intro k hkp hkr
    have hk : k < p := Finset.mem_range.mp hkp
    have hpk : p ≤ 2 * k := by
      simp only [Finset.mem_range] at hkr
      omega
    rw [central_choose_cube_zero_work hp hk hpk hn, mul_zero, zero_mul]

example : (range 3).sum (fun k =>
      (aWork (4 * k) : ZMod (3 ^ 2)) * (choose (2 * k) k : ZMod (3 ^ 2)) ^ 3 *
        (((-4096 : ℤ) : ZMod (3 ^ 2)) ^ k)⁻¹) = 0 := by
  decide

def sumWork (p n : ℕ) : ZMod (p ^ n) :=
  (range p).sum fun k =>
      (aWork (4 * k) : ZMod (p ^ n)) * (choose (2 * k) k : ZMod (p ^ n)) ^ 3 *
        (((-4096 : ℤ) : ZMod (p ^ n)) ^ k)⁻¹

example : sumWork 5 2 = 0 := by
  unfold sumWork
  rw [sum_truncate_work (by decide) (by omega)]
  decide

example : sumWork 7 2 = 0 := by
  unfold sumWork
  rw [sum_truncate_work (by decide) (by omega)]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
example : sumWork 11 3 = 0 := by
  unfold sumWork
  rw [sum_truncate_work (by decide) (by omega)]
  decide

end

section

namespace SequenceWork
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]

noncomputable def A (m : ℕ) (h : R) : R :=
  ∑k∈range (m+1), (aWork (4*k):R)*(Nat.centralBinom k:R)^3*(-h^12)^k

lemma half_pow (h : R) (hh : 2*h=1) (n : ℕ) : (2:R)^n*h^n=1 := by rw [←mul_pow,hh,one_pow]
lemma half_4096 (h : R) (hh : 2*h=1) : 4096*h^12=1 := by
  simpa only [show (2:R)^12=4096 by ring] using half_pow h hh 12

lemma parameter_z (w h : R) (hw : w^2-w+2=0) (hh : 2*h=1) :
    (1-(-3*(w+2)*h^3)^2)*h^6=(46-45*w)*h^12 := by
  have h6 : 64*h^6=1 := by simpa only [show (2:R)^6=64 by ring] using half_pow h hh 6
  linear_combination -9*h^12*hw-h^6*h6

lemma powers_difference (w h : R) (hw : w^2-w+2=0) (hh : 2*h=1) (k : ℕ) :
    ((46-45*w)*h^12)^k-((1+45*w)*h^12)^k=(2*w-1)*(aWork (4*k):R)*(-h^12)^k := by
  let z := (46-45*w)*h^12
  let z' := (1+45*w)*h^12
  have hs : z+z'=47*h^12 := by dsimp [z,z']; ring
  have hm : z*z'=h^12 := by
    have h12 := half_4096 h hh
    dsimp [z,z']
    linear_combination -2025*h^24*hw+h^12*h12
  have hpow : ∀j, z^(j+2)-z'^(j+2) = (47*h^12)*(z^(j+1)-z'^(j+1))-h^12*(z^j-z'^j) := by
    intro j
    rw [←hs,←hm,pow_add,pow_add,pow_succ,pow_succ]
    ring
  change z^k-z'^k=_
  induction k using Nat.twoStepInduction with
  | zero => simp [aWork]
  | one => norm_num [aWork,z,z']; ring
  | more k ih0 ih1 =>
    rw [hpow,ih0,ih1,aWork_four_step]
    push_cast
    rw [pow_add,pow_succ]
    have h12 := half_4096 h hh
    linear_combination (2*w-1)*(aWork (4*k):R)*(-h^12)^k*h^12*h12

lemma sum_difference (w h : R) (hw : w^2-w+2=0) (hh : 2*h=1) (m : ℕ) :
    RingDeformWork.F m (-3*(w+2)*h^3) h - RingDeformWork.F m (-3*((1-w)+2)*h^3) h = (2*w-1)*A m h := by
  have hw' : (1-w)^2-(1-w)+2=0 := by linear_combination hw
  simp only [RingDeformWork.F,parameter_z w h hw hh,parameter_z (1-w) h hw' hh]
  have he : (46-45*(1-w))*h^12=(1+45*w)*h^12 := by ring
  simp only [he,←sum_sub_distrib,A,mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [←mul_sub,powers_difference w h hw hh]
  ring

lemma map_A {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ) (h : R) : φ (A m h)=A m (φ h) := by
  simp only [A,map_sum,map_mul,map_intCast,map_natCast,map_pow,map_neg]

lemma map_F {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ) (a h : R) :
    φ (RingDeformWork.F m a h)=RingDeformWork.F m (φ a) (φ h) := by
  simp only [RingDeformWork.F,map_sum,map_mul,map_natCast,map_pow,map_sub,map_one]

end SequenceWork

end

section

namespace InertSumWork
open QuadraticAlgebra QuadraticModWork SequenceWork Finset
open scoped BigOperators

lemma star_half (n : ℕ) : star (half n)=half n := by
  ext <;> simp [half]
lemma star_omega (n : ℕ) : star (omega:Q n)=1-omega := by ext <;> simp

lemma mod_A_eq (p n m : ℕ) (h : ZMod (p^n)) (hh : 2*h=1) :
    A m h = ∑k∈range (m+1), (aWork (4*k):ZMod (p^n))*(Nat.choose (2*k) k:ZMod (p^n))^3*
      (((-4096:ℤ):ZMod (p^n))^k)⁻¹ := by
  apply sum_congr rfl
  intro k hk
  have hi : (((-4096:ℤ):ZMod (p^n))^k)⁻¹=(-h^12)^k := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [←mul_pow]
    have he : ((-4096:ℤ):ZMod (p^n))*(-h^12)=1 := by
      push_cast
      simpa only [neg_mul_neg] using half_4096 h hh
    rw [he,one_pow]
  rw [hi,Nat.centralBinom]

lemma mod_A_eq_sum (p n : ℕ) (hp : p.Prime) (hn : n≤3) (h : ZMod (p^n)) (hh : 2*h=1) :
    A (p/2) h=sumWork p n := by
  rw [mod_A_eq p n (p/2) h hh]
  exact (sum_truncate_work hp hn).symm

lemma inert_sum (p : ℕ) (hp : p.Prime) (hp3 : 3<p) (hp7 : p≠7)
    (hns : p%7 ∉ ({1,2,4}:Set ℕ)) : sumWork p 2=0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (∀r:ZMod p, r^2≠(-2)+1*r) := ⟨InertFieldWork.no_root (by omega) hp7 hns⟩
  let m := p/2
  have hpm : p=2*m+1 := by
    have hpodd := hp.mod_two_eq_one_iff_ne_two.mpr (by omega : p≠2)
    dsimp [m]
    omega
  have hcop : (p^2).Coprime 2 := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).pow_left _
  have hh := half_spec hcop
  have hF := inert_hypergeometric hp3 m hpm
  dsimp only at hF
  have hstar := congrArg (starRingEnd (Q (p^2))) hF
  rw [map_F] at hstar
  simp only [map_mul,map_neg,map_ofNat,map_add,map_pow,starRingEnd_apply,star_half,star_omega,map_zero] at hstar
  have hd := sum_difference (omega:Q (p^2)) (half (p^2)) (omega_equation (p^2)) hh m
  rw [hF,hstar,sub_self] at hd
  have h7 : IsUnit (7:Q (p^2)) := by
    have hh : IsUnit (7:ZMod (p^2)) := by
      apply (ZMod.isUnit_iff_coprime 7 (p^2)).mpr
      apply hp.coprime_pow_of_not_dvd
      intro hd
      exact hp7 ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd |>.resolve_left hp.ne_one)
    simpa only [map_ofNat] using hh.map (algebraMap (ZMod (p^2)) (Q (p^2)))
  have hdisc : (2*(omega:Q (p^2))-1)^2 = -7 := by linear_combination 4*(omega_equation (p^2))
  have hu : IsUnit (2*(omega:Q (p^2))-1) := (isUnit_pow_iff (by decide : 2≠0)).mp (hdisc ▸ h7.neg)
  have hA : A m (half (p^2))=0 := hu.mul_left_cancel (by simpa only [mul_zero] using hd.symm)
  let h : ZMod (p^2) := (2:ZMod (p^2))⁻¹
  have hhs : 2*h=1 := ZMod.mul_inv_of_unit 2 (by exact_mod_cast (ZMod.isUnit_iff_coprime 2 (p^2)).mpr hcop.symm)
  have hA' : A m h=0 := by
    apply QuadraticAlgebra.algebraMap_injective (a := (-2:ZMod (p^2))) (b := 1)
    rw [map_zero,map_A]
    exact hA
  rw [←mod_A_eq_sum p 2 hp (by omega) h hhs]
  exact hA'

end InertSumWork

end

section

namespace OrdinarySumWork
open ApproxWork SequenceWork
variable {p : ℕ} [Fact p.Prime]

lemma padic_transfer (hp2 : p≠2) (n : ℕ) (hn : n≤3)
    (hb : Cong ‖(p:ℚ_[p])‖ n (A (p/2) (1/2:ℚ_[p])) 0) : sumWork p n=0 := by
  let h : ℤ_[p] := ⟨1/2,PadicCoefficientWork.half_mem hp2⟩
  have hh : 2*h=1 := by apply Subtype.ext; change (2:ℚ_[p])*(1/2)=1; norm_num
  have hA : PadicInt.Coe.ringHom (A (p/2) h)=A (p/2) (1/2:ℚ_[p]) := map_A _ _ _
  have hnorm : ‖A (p/2) h‖ ≤ (p:ℝ)^(-(n:ℤ)) := by
    have he : (p:ℝ)^(-(n:ℤ))=‖(p:ℚ_[p])‖^n := by simp [Padic.norm_p,zpow_neg,zpow_natCast,inv_pow]
    rw [he,PadicInt.norm_def]
    change ‖PadicInt.Coe.ringHom (A (p/2) h)‖≤_
    rw [hA]
    simpa only [Cong,sub_zero] using hb
  have hk := (PadicInt.norm_le_pow_iff_mem_span_pow (A (p/2) h) n).mp hnorm
  rw [←PadicInt.ker_toZModPow,RingHom.mem_ker] at hk
  rw [map_A] at hk
  have hh' : 2*PadicInt.toZModPow n h=1 := by
    simpa only [map_mul,map_ofNat,map_one] using congrArg (PadicInt.toZModPow n) hh
  rw [InertSumWork.mod_A_eq_sum p n Fact.out hn _ hh'] at hk
  exact hk

lemma field_F (m : ℕ) (a : ℚ_[p]) : RingDeformWork.F m a (1/2)=DeformApproxWork.F m a := by
  unfold RingDeformWork.F DeformApproxWork.F
  congr 1
  ext k
  congr 1
  ring

lemma conjugate_norm (z : O7Work.O) : (star z).norm=z.norm := by
  simp only [O7Work.norm_O,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  ring

lemma ordinary_bound (hp3 : 3<p) (hp7 : p≠7) (hmod : p%7 ∈ ({1,2,4}:Set ℕ)) :
    Cong ‖(p:ℚ_[p])‖ 3 (A (p/2) (1/2:ℚ_[p])) 0 := by
  obtain ⟨w,z,hw,hz,hzu,hzv,hzi,hu,hnu⟩ := PadicSetupWork.split_scalar (by omega) hp7 hmod
  let m := p/2
  have hpm : p=2*m+1 := by
    have ho := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p≠2)
    dsimp [m]; omega
  have hw' : (1-w)^2-(1-w)+2=0 := by linear_combination hw
  have hz' : (star z).norm=p := (conjugate_norm z).trans hz
  have hu' : IsUnit (((star z).re:ℤ_[p])+((star z).im:ℤ_[p])*(1-(1-w))) := by
    convert hu using 1
    simp only [QuadraticAlgebra.re_star,QuadraticAlgebra.im_star,Int.cast_add,Int.cast_mul,Int.cast_neg,
      Int.cast_one,one_mul]
    ring
  have h1 := OrdinaryWork.hypergeometric m hpm hp3 w hw z hz hu
  have h2 := OrdinaryWork.hypergeometric m hpm hp3 (1-w) hw' (star z) hz' hu'
  dsimp only at h1 h2
  have hc : (((star z).re:ℚ_[p])+((star z).im:ℚ_[p])*((1-w:ℤ_[p]):ℚ_[p])) =
      (z.re:ℚ_[p])+(z.im:ℚ_[p])*(w:ℚ_[p]) := by
    simp only [QuadraticAlgebra.re_star,QuadraticAlgebra.im_star,Int.cast_add,Int.cast_mul,Int.cast_neg,
      Int.cast_one,one_mul,PadicInt.coe_sub,PadicInt.coe_one]
    ring
  rw [hc] at h2
  have hs := h1.sub h2
  simp only [sub_self] at hs
  have he1 : -3*((w:ℚ_[p])+2)*(1/2)^3=-3*((w:ℚ_[p])+2)/8 := by ring
  have hwQ : (w:ℚ_[p])^2-(w:ℚ_[p])+2=0 := by
    have hh := congrArg (PadicInt.Coe.ringHom (p := p)) hw
    simpa only [map_add,map_sub,map_pow,map_ofNat,map_zero] using hh
  have hdiff := sum_difference (w:ℚ_[p]) (1/2:ℚ_[p]) hwQ (by norm_num) m
  simp only [he1,field_F] at hdiff
  have hdiff' : DeformApproxWork.F m (-3*((w:ℚ_[p])+2)/8)-
      DeformApproxWork.F m (-3*(((1-w:ℤ_[p]):ℚ_[p])+2)/8) = (2*(w:ℚ_[p])-1)*A m (1/2:ℚ_[p]) := by
    convert hdiff using 2 <;> simp only [PadicInt.coe_sub,PadicInt.coe_one] <;> ring
  rw [hdiff'] at hs
  have h7 : ‖(7:ℚ_[p])‖=1 := by
    have hh : ‖((7:ℕ):ℚ_[p])‖=1 := Padic.norm_natCast_eq_one_iff.mpr
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
        intro hd
        exact hp7 ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)))
    exact hh
  have hd : ‖2*(w:ℚ_[p])-1‖=1 := by
    have he : (2*(w:ℚ_[p])-1)^2 = -7 := by linear_combination 4*hwQ
    have hh := congrArg norm he
    rw [norm_pow,norm_neg,h7] at hh
    nlinarith [norm_nonneg (2*(w:ℚ_[p])-1)]
  change ‖_ - 0‖≤_ at hs ⊢
  simpa only [sub_zero,norm_mul,hd,one_mul] using hs

lemma ordinary_sum (hp3 : 3<p) (hp7 : p≠7) (hmod : p%7 ∈ ({1,2,4}:Set ℕ)) :
    sumWork p 2=0 ∧ sumWork p 3=0 := by
  have hh := ordinary_bound hp3 hp7 hmod
  obtain ⟨hr0,hr1⟩ := PadicCoefficientWork.prime_radius (p := p)
  exact ⟨padic_transfer (by omega) 2 (by omega) (hh.mono hr0.le hr1.le (by omega)),
    padic_transfer (by omega) 3 (by omega) hh⟩

end OrdinarySumWork

end

section

open Finset Nat

lemma conjecture_work (p : ℕ) (hp : p.Prime) (hp2 : p≠2) :
    sumWork p 2=0 ∧ (p%7 ∈ ({1,2,4}:Set ℕ) → sumWork p 3=0) := by
  by_cases hp3 : p=3
  · subst p
    constructor
    · decide
    · intro hh; norm_num at hh
  by_cases hp5 : p=5
  · subst p
    constructor
    · unfold sumWork
      rw [sum_truncate_work (by decide) (by omega)]
      decide
    · intro hh; norm_num at hh
  by_cases hp7 : p=7
  · subst p
    constructor
    · unfold sumWork
      rw [sum_truncate_work (by decide) (by omega)]
      decide
    · intro hh; norm_num at hh
  have hpgt : 3<p := by have := hp.two_le; omega
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hs : p%7 ∈ ({1,2,4}:Set ℕ)
  · obtain ⟨h2,h3⟩ := OrdinarySumWork.ordinary_sum hpgt hp7 hs
    exact ⟨h2,fun _ => h3⟩
  · exact ⟨InertSumWork.inert_sum p hp hpgt hp7 hs,fun hh => (hs hh).elim⟩

lemma aWork_eq (n : ℕ) : aWork n=a n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 => simpa only [aWork,a,ih0,ih1]

end

open Finset Nat
open scoped BigOperators

/--
Conjecture of Zhi-Wei Sun on the sum $S(p)$ for the sequence A190969.
Let $S(p) := \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$.
Sun conjectured that $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$,
and also $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1,2,4 \pmod{7}$.

The sum is formalized here by interpreting the division as multiplication by the modular inverse
in the ring $\mathbb{Z}/p^n\mathbb{Z}$. Since $p$ is an odd prime, $4096$ is invertible modulo $p^n$.
-/
theorem oeis_a190969_conjecture_0 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    let K (n : ℕ) := ZMod (p ^ n)
    let S (n : ℕ) : K n :=
        (range p).sum fun k =>
            let num : K n := (a (4 * k) : K n) * ((choose (2 * k) k : ℕ) : K n) ^ 3
            let den : K n := ((-4096 : ℤ) : K n) ^ k
            -- The inverse den⁻¹ exists because p is an odd prime and thus coprime to 4096.
            num * den⁻¹
    S 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → S 3 = 0) := by
  simpa only [sumWork, aWork_eq] using conjecture_work p hp hp_odd

theorem oeis_a190969_conjecture_0.disproof : ¬ (type_of% @oeis_a190969_conjecture_0) := sorry
