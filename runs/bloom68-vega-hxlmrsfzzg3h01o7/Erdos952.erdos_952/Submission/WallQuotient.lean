import FormalConjecturesUtil
import Submission.WallDataChecker
import Submission.WallObstruction

/-!
# The arithmetic quotient for the supplied black wall

The quotient has periods `p = 96135 * (6 + i)` and `i * p`. Its two
coordinates are the residues of `re - 6 * im` modulo `3556995` and of `im`
modulo `96135`. All calculations use symbolic integer casts; no enumeration
of the finite quotient or import of the large wall certificate is needed.

Blackness is exactly `WallData.Black`. Each of its ten labels is invariant
under equal quotient residues and under the affine rotation `R`.
-/

namespace Erdos952.WallQuotient

/-- The common coordinate factor of the period vector. -/
def A : ℤ := 96135

/-- The modulus of the sheared real coordinate. -/
def M : ℤ := 3556995

theorem M_eq_37_mul_A : M = 37 * A := by norm_num [M, A]

/-- The finite additive quotient; its instances do not require enumeration. -/
abbrev α := ZMod 3556995 × ZMod 96135

/-- The displacement of the supplied wall. -/
def p : GaussianInt := ⟨576810, 96135⟩

@[simp] theorem p_re : p.re = 576810 := rfl
@[simp] theorem p_im : p.im = 96135 := rfl

theorem p_eq_A_mul : p = (A : GaussianInt) * (6 + WallObstruction.I) := by
  ext <;> norm_num [p, A, WallObstruction.I]

theorem p_ne_zero : p ≠ 0 := by
  intro h
  have hi := congrArg Zsqrtd.im h
  norm_num [p] at hi

/-- The residue map, including its additive-homomorphism structure. -/
def r : GaussianInt →+ α where
  toFun w := (((w.re - 6 * w.im : ℤ) : ZMod 3556995), (w.im : ZMod 96135))
  map_zero' := by simp
  map_add' u v := by
    apply Prod.ext <;> simp
    ring

@[simp] theorem r_apply (w : GaussianInt) :
    r w = (((w.re - 6 * w.im : ℤ) : ZMod 3556995), (w.im : ZMod 96135)) := rfl

/-- Lift the second residue first, then undo the shear in the first. -/
theorem r_surjective : Function.Surjective r := by
  rintro ⟨u, v⟩
  refine ⟨⟨(u.val : ℤ) + 6 * (v.val : ℤ), (v.val : ℤ)⟩, ?_⟩
  apply Prod.ext <;> simp [r]

/-- Kernel membership is precisely two integer divisibility conditions. -/
theorem r_eq_zero_iff (w : GaussianInt) :
    r w = 0 ↔ M ∣ w.re - 6 * w.im ∧ A ∣ w.im := by
  change (((w.re - 6 * w.im : ℤ) : ZMod 3556995), (w.im : ZMod 96135)) =
    (0, 0) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

@[simp] theorem r_p : r p = 0 := by
  rw [r_eq_zero_iff]
  norm_num [M, A, p]

@[simp] theorem r_I_mul_p : r (WallObstruction.I * p) = 0 := by
  rw [r_eq_zero_iff]
  norm_num [M, A, p, WallObstruction.I]

/-- If the residue differences are `A * k` and `M * l`, the two period
coefficients are `k + 6 * l` and `-l`. -/
theorem kernel_representation (u v : GaussianInt) (h : r u = r v) :
    ∃ m n : ℤ, v - u = m • p + n • (WallObstruction.I * p) := by
  have hx : ((u.re - 6 * u.im : ℤ) : ZMod 3556995) =
      ((v.re - 6 * v.im : ℤ) : ZMod 3556995) := congrArg Prod.fst h
  have hy : (u.im : ZMod 96135) = (v.im : ZMod 96135) := congrArg Prod.snd h
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hy
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hx
  refine ⟨k + 6 * l, -l, ?_⟩
  apply Zsqrtd.ext <;>
    simp [zsmul_eq_mul, p, WallObstruction.I] <;> omega

/-- The period displacement alone suffices to identify endpoint residues.
This interface deliberately does not depend on the wall-data certificate. -/
theorem residue_eq_of_sub_eq_p {u v : GaussianInt} (h : v - u = p) : r u = r v := by
  have he : r v - r u = 0 := by rw [← map_sub, h, r_p]
  exact (sub_eq_zero.mp he).symm

/-- Exactly the ten modular tests from the wall checker. -/
abbrev B : GaussianInt → Prop := WallData.Black

/-- The catch-all false case rules out every label at least ten. -/
theorem labelBlack_lt_ten {x y : ℤ} {label : ℕ}
    (h : WallData.LabelBlack x y label) : label < 10 := by
  unfold WallData.LabelBlack at h
  split at h <;> simp_all

/-- Every individual black label is constant on residue classes. -/
theorem labelBlack_residue_invariant (u v : GaussianInt) (h : r u = r v)
    (label : ℕ) (hb : WallData.LabelBlack u.re u.im label) :
    WallData.LabelBlack v.re v.im label := by
  obtain ⟨m, n, hmn⟩ := kernel_representation u v h
  have hx := congrArg Zsqrtd.re hmn
  have hy := congrArg Zsqrtd.im hmn
  simp [zsmul_eq_mul, p, WallObstruction.I] at hx hy
  have hl := labelBlack_lt_ten hb
  interval_cases label <;> simp only [WallData.LabelBlack] at hb ⊢ <;> omega

/-- The residue-invariance hypothesis needed to construct a quotient current. -/
theorem B_residue_invariant (u v : GaussianInt) (h : r u = r v) (hb : B u) : B v := by
  obtain ⟨label, hl⟩ := hb
  exact ⟨label, labelBlack_residue_invariant u v h label hl⟩

/-- The affine quarter turn preserves each of the ten labels separately. -/
theorem labelBlack_R (u : GaussianInt) (label : ℕ)
    (h : WallData.LabelBlack u.re u.im label) :
    WallData.LabelBlack (WallObstruction.R u).re (WallObstruction.R u).im label := by
  have hl := labelBlack_lt_ten h
  interval_cases label <;>
    simp only [WallData.LabelBlack, WallObstruction.R] at h ⊢ <;> omega

/-- Black preservation in the form required by the finite-wall obstruction. -/
theorem B_R (u : GaussianInt) (h : B u) : B (WallObstruction.R u) := by
  obtain ⟨label, hl⟩ := h
  exact ⟨label, labelBlack_R u label hl⟩

/-- Equivalently, the inverse affine rotation preserves white vertices. -/
theorem white_Rinv (u : GaussianInt) (h : ¬ B u) : ¬ B (WallObstruction.Rinv u) :=
  WallObstruction.white_Rinv_of_black_R B_R h

end Erdos952.WallQuotient
