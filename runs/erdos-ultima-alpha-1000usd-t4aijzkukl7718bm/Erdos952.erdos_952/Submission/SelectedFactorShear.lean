import Submission.Sieve729Application

/-!
Coordinates for adding the Gaussian factor `6+i` to the six-prime sieve,
without multiplying its column period by 37. This file verifies the arithmetic
coordinate reduction, not the existence of a barrier in the resulting graph.
-/
namespace Erdos952Investigation.SelectedFactorShear
set_option maxHeartbeats 0

def shear37 (t s : ℤ) : GaussianInt := ⟨1+t+5*s,t+7*s⟩

lemma shear37_coordU (t s : ℤ) : coordU (shear37 t s) = t+6*s := by
  simp only [coordU,shear37]
  omega

lemma shear37_coordV (t s : ℤ) : coordV (shear37 t s) = -s := by
  simp only [coordV,shear37]
  omega

lemma shear37_injective : Function.Injective (fun z : ℤ × ℤ => shear37 z.1 z.2) := by
  intro z w h
  have hu := congrArg coordU h
  have hv := congrArg coordV h
  simp only [shear37_coordU,shear37_coordV] at hu hv
  apply Prod.ext <;> omega

lemma shear37_reconstruct {z : GaussianInt} (hz : (z.re+z.im)%2 = 1) :
    shear37 (coordU z+6*coordV z) (-coordV z) = z := by
  apply Zsqrtd.ext
  · simp only [shear37]
    rw [coordinates_re hz]
    ring
  · simp only [shear37]
    rw [coordinates_im hz]
    ring

/-- The old checkerboard metric expressed in sheared coordinates. -/
lemma shear37_step_norm (t s u v : ℤ) :
    (shear37 u v-shear37 t s).norm =
      2*((u-t+6*(v-s))^2+(v-s)^2) := by
  simp only [gaussian_norm_sq,shear37,Zsqrtd.re_sub,Zsqrtd.im_sub]
  ring

/-- A column translation is a multiple of `6+i`, so that factor does not
require an additional factor of 37 in the column period. -/
lemma shear37_column_difference (t s M : ℤ) :
    shear37 t (s+M)-shear37 t s =
      (M : GaussianInt)*(⟨1,1⟩ : GaussianInt)*(⟨6,1⟩ : GaussianInt) := by
  apply Zsqrtd.ext <;>
    simp [shear37,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

/-- The excluded row is exactly divisibility by the selected factor, not
an additional heuristic exclusion. -/
lemma selected_factor_divides_iff (t s : ℤ) :
    (⟨6,1⟩ : GaussianInt) ∣ shear37 t s ↔ t%37 = 15 := by
  constructor
  · rintro ⟨w,hw⟩
    have hr := congrArg Zsqrtd.re hw
    have hi := congrArg Zsqrtd.im hw
    norm_num [shear37,Zsqrtd.re_mul,Zsqrtd.im_mul] at hr hi
    omega
  · intro ht
    have he : t = 15+37*(t/37) := by omega
    refine ⟨⟨s+3+7*(t/37),s+2+5*(t/37)⟩,?_⟩
    apply Zsqrtd.ext <;>
      simp only [shear37,Zsqrtd.re_mul,Zsqrtd.im_mul]
    · linear_combination he
    · linear_combination he

lemma norm_divisible_on_forbidden_row (t s : ℤ) (ht : t%37 = 15) :
    (37 : ℤ) ∣ (shear37 t s).norm := by
  have he : t = 15+37*(t/37) := by omega
  refine ⟨13+62*(t/37)+74*(t/37)^2+10*s+24*(t/37)*s+2*s^2,?_⟩
  simp only [gaussian_norm_sq,shear37]
  conv_lhs => rw [he]
  ring

def Allowed37 (z : ℤ × ℤ) : Prop :=
  Sieve729.Allowed (z.1+6*z.2,-z.2) ∧ z.1%37 ≠ 15

lemma allowed37_column_period (t s : ℤ) (h : Allowed37 (t,s)) :
    Allowed37 (t,s+Sieve729.period) := by
  refine ⟨?_,h.2⟩
  have h1 := Sieve729.allowed_period (-6) (t+6*s,-s) h.1
  have h2 := Sieve729.allowed_swap _ h1
  have h3 := Sieve729.allowed_period 1 _ h2
  have h4 := Sieve729.allowed_swap _ h3
  convert h4 using 1 <;> congr 1 <;> ring

lemma shear37_rotate (t s : ℤ) :
    shear37 (-6*t-37*s-6) (t+6*s+1) =
      (⟨-(shear37 t s).im,(shear37 t s).re⟩ : GaussianInt) := by
  apply Zsqrtd.ext <;> simp only [shear37] <;> ring

/-- Keeping only one conjugate factor loses reflection symmetry, but retains
the quarter-turn symmetry needed for a two-dimensional barrier argument. -/
lemma allowed37_rotate (t s : ℤ) (h : Allowed37 (t,s)) :
    Allowed37 (-6*t-37*s-6,t+6*s+1) := by
  constructor
  · have h1 := Sieve729.allowed_reflect (t+6*s,-s) h.1
    have h2 := Sieve729.allowed_swap _ h1
    convert h2 using 1 <;> congr 1 <;> ring
  · change (-6*t-37*s-6)%37 ≠ 15
    intro hh
    apply h.2
    omega

/-- Every sufficiently large actual prime lies in this selected-factor sieve. -/
lemma prime_shear37_allowed (t s : ℤ) (hp : Prime (shear37 t s))
    (hlarge : 1369 < (shear37 t s).norm) : Allowed37 (t,s) := by
  constructor
  · simpa only [shear37_coordU,shear37_coordV] using
      Sieve729.prime_allowed hp (by omega)
  · intro ht
    have hh := prime_norm_divisor_bound hp (by decide : Nat.Prime 37)
      (norm_divisible_on_forbidden_row t s ht)
    norm_num at hh
    omega

#print axioms allowed37_rotate
#print axioms selected_factor_divides_iff
#print axioms allowed37_column_period
#print axioms prime_shear37_allowed
#print axioms shear37_step_norm
#print axioms shear37_column_difference
end Erdos952Investigation.SelectedFactorShear
