import Submission.Investigation

/-! Bounded representatives for a principal Gaussian ideal and its exact
additive index. These are lattice-counting tools, not a Gaussian moat proof. -/
namespace Erdos952Investigation.GaussianIdealRepresentatives
set_option maxHeartbeats 0

def coordinates : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re,z.im]
  invFun f := ⟨f 0,f 1⟩
  left_inv z := by cases z; rfl
  right_inv f := by funext i; fin_cases i <;> rfl
  map_add' z w := by funext i; fin_cases i <;> rfl
  map_smul' n z := by
    funext i
    fin_cases i <;> simp [zsmul_eq_mul]

noncomputable def gaussianBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map coordinates.symm

local instance : Module.Free ℤ GaussianInt := Module.Free.of_basis gaussianBasis
local instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis gaussianBasis

lemma basis_repr (z : GaussianInt) (i : Fin 2) : gaussianBasis.repr z i = coordinates z i := by
  simp [gaussianBasis]

lemma basis_zero : gaussianBasis 0 = (⟨1,0⟩ : GaussianInt) := by
  simp [gaussianBasis,coordinates]

lemma basis_one : gaussianBasis 1 = (⟨0,1⟩ : GaussianInt) := by
  simp [gaussianBasis,coordinates]

def multiplication (g : GaussianInt) : GaussianInt →ₗ[ℤ] GaussianInt :=
  LinearMap.mulLeft ℤ g

def multiples (g : GaussianInt) : Submodule ℤ GaussianInt := (multiplication g).range

lemma multiplication_det (g : GaussianInt) : (multiplication g).det = g.norm := by
  rw [← LinearMap.det_toMatrix gaussianBasis]
  have hm : LinearMap.toMatrix gaussianBasis gaussianBasis (multiplication g) =
      !![g.re,-g.im;g.im,g.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply,basis_repr,basis_zero,basis_one,
        multiplication,coordinates]
  rw [hm,Matrix.det_fin_two,gaussian_norm_sq]
  norm_num
  ring

/-- The additive index of g Z[i] is exactly the Gaussian norm of g. -/
theorem quotient_card (g : GaussianInt) (hg : g ≠ 0) :
    Nat.card (GaussianInt ⧸ multiples g) = g.norm.natAbs := by
  let e := LinearEquiv.ofInjective (multiplication g) (mul_right_injective₀ hg)
  have hh := Submodule.natAbs_det_equiv (multiples g) e
  change (multiplication g).det.natAbs = Nat.card (GaussianInt ⧸ multiples g) at hh
  rw [multiplication_det] at hh
  exact hh.symm

lemma exists_small_representative (g : GaussianInt) (hg : g ≠ 0)
    (q : GaussianInt ⧸ multiples g) :
    ∃ r : GaussianInt, Submodule.Quotient.mk r = q ∧ r.norm < g.norm := by
  induction q using Quotient.inductionOn' with
  | h x =>
    refine ⟨x%g,?_,GaussianInt.norm_mod_lt x hg⟩
    apply (Submodule.Quotient.eq (multiples g)).mpr
    refine ⟨-(x/g),?_⟩
    change g*(-(x/g)) = x%g-x
    rw [GaussianInt.mod_def]
    ring

noncomputable def representative (g : GaussianInt) (hg : g ≠ 0)
    (q : GaussianInt ⧸ multiples g) : GaussianInt :=
  Classical.choose (exists_small_representative g hg q)

lemma representative_class (g : GaussianInt) (hg : g ≠ 0)
    (q : GaussianInt ⧸ multiples g) :
    Submodule.Quotient.mk (representative g hg q) = q :=
  (Classical.choose_spec (exists_small_representative g hg q)).1

lemma representative_norm (g : GaussianInt) (hg : g ≠ 0)
    (q : GaussianInt ⧸ multiples g) : (representative g hg q).norm < g.norm :=
  (Classical.choose_spec (exists_small_representative g hg q)).2

lemma representative_injective (g : GaussianInt) (hg : g ≠ 0) :
    Function.Injective (representative g hg) := by
  intro q r he
  have hh := congrArg (Submodule.Quotient.mk (p := multiples g)) he
  simpa only [representative_class] using hh

theorem quotient_finite (g : GaussianInt) (hg : g ≠ 0) :
    Finite (GaussianInt ⧸ multiples g) := by
  apply Nat.finite_of_card_ne_zero
  rw [quotient_card g hg]
  exact Int.natAbs_ne_zero.mpr (GaussianInt.norm_eq_zero.not.mpr hg)

/-- Each quotient class has a representative in one fixed square of radius
floor(sqrt(norm g)). The square bound is intentionally conservative. -/
theorem representative_coordinates (g : GaussianInt) (hg : g ≠ 0)
    (q : GaussianInt ⧸ multiples g) :
    |(representative g hg q).re| ≤ (Nat.sqrt g.norm.natAbs : ℤ) ∧
      |(representative g hg q).im| ≤ (Nat.sqrt g.norm.natAbs : ℤ) := by
  let r := representative g hg q
  have hn : r.norm < g.norm := representative_norm g hg q
  have hre : r.re.natAbs^2 ≤ g.norm.natAbs := by
    have hr : r.re^2 ≤ g.norm := by
      rw [gaussian_norm_sq] at hn
      nlinarith [sq_nonneg r.im]
    have hh : (r.re.natAbs : ℤ)^2 ≤ (g.norm.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs,sq_abs,abs_of_nonneg (GaussianInt.norm_nonneg g)] using hr
    exact_mod_cast hh
  have him : r.im.natAbs^2 ≤ g.norm.natAbs := by
    have hi : r.im^2 ≤ g.norm := by
      rw [gaussian_norm_sq] at hn
      nlinarith [sq_nonneg r.re]
    have hh : (r.im.natAbs : ℤ)^2 ≤ (g.norm.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs,sq_abs,abs_of_nonneg (GaussianInt.norm_nonneg g)] using hi
    exact_mod_cast hh
  have hr := Nat.le_sqrt.mpr (by simpa only [pow_two] using hre)
  have hi := Nat.le_sqrt.mpr (by simpa only [pow_two] using him)
  constructor
  · have hh : (r.re.natAbs : ℤ) ≤ Nat.sqrt g.norm.natAbs := by exact_mod_cast hr
    simpa only [Int.natCast_natAbs] using hh
  · have hh : (r.im.natAbs : ℤ) ≤ Nat.sqrt g.norm.natAbs := by exact_mod_cast hi
    simpa only [Int.natCast_natAbs] using hh

lemma quotient_eq_iff_dvd (g x y : GaussianInt) :
    (Submodule.Quotient.mk x : GaussianInt ⧸ multiples g) = Submodule.Quotient.mk y ↔
      g ∣ x-y := by
  rw [Submodule.Quotient.eq]
  change (∃ w, g*w = x-y) ↔ g ∣ x-y
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

#print axioms quotient_eq_iff_dvd


#print axioms multiplication_det
#print axioms quotient_card
#print axioms quotient_finite
#print axioms representative_coordinates
end Erdos952Investigation.GaussianIdealRepresentatives
