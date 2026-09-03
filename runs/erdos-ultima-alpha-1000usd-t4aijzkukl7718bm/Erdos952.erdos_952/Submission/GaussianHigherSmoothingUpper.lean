import Submission.GaussianSmoothingBuckets

/-! The same higher-order kernel used in the polynomial-loss ray lower
bound has geometrically improving ideal-coset error. The tuple rearrangement
and normalization are explicit, so upper and lower bounds concern the same
finite weighted count. No growing-prime-pattern main-term bound is asserted. -/
namespace Erdos952Investigation.GaussianHigherSmoothingUpper
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianIteratedSmoothing
open FiniteConvolutionSmoothing FiniteSampleSmoothing GaussianHigherSmoothingLower
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

def boxShift (a : GaussianInt) (R : ℕ) : Box a R ≃ Box 0 R where
  toFun z := ⟨z.val-a,by have h := z.property; dsimp [InBox] at h ⊢; omega⟩
  invFun z := ⟨a+z.val,by have h := z.property; dsimp [InBox] at h ⊢; omega⟩
  left_inv z := by apply Subtype.ext; dsimp; abel
  right_inv z := by apply Subtype.ext; dsimp; abel

def kernelEquiv (a : GaussianInt) (R n : ℕ) :
    KernelSample (Sample (Box 0 R) n) a R ≃
      Sample (Box 0 R) (n+1) × Sample (Box 0 R) (n+1) where
  toFun s := ((s.2.1,s.1.2),(s.2.2,boxShift a R s.1.1))
  invFun s := (((boxShift a R).symm s.2.2,s.1.2),(s.1.1,s.2.1))
  left_inv s := by simp
  right_inv s := by simp

lemma kernelEquiv_value (a : GaussianInt) (R n : ℕ)
    (s : KernelSample (Sample (Box 0 R) n) a R) :
    kernelValue (tupleValue 0 R n) a R s =
      a+tupleValue 0 R (n+1) (kernelEquiv a R n s).1-
        tupleValue 0 R (n+1) (kernelEquiv a R n s).2 := by
  dsimp [kernelValue,kernelEquiv,tupleValue,value,boxShift]
  abel

lemma kernel_coset_eq_density {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → GaussianInt) (g a : GaussianInt) (R : ℕ) (hR : 0 < R)
    (c : GaussianInt ⧸ multiples g) :
    kernelCount f (fun z => (Submodule.Quotient.mk z : GaussianInt ⧸ multiples g) = c) a R =
      (R : ℝ)^2*density (fun s : KernelSample Ω a R =>
        (Submodule.Quotient.mk (kernelValue f a R s) : GaussianInt ⧸ multiples g)) c := by
  have hA : Fintype.card (Box a R) = R^2 := by rw [← Nat.card_eq_fintype_card]; exact box_card a R
  have hB : Fintype.card (Box 0 R) = R^2 := by rw [← Nat.card_eq_fintype_card]; exact box_card 0 R
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  simp only [kernelCount,density,Fintype.card_prod,hA,hB,Nat.cast_mul,Nat.cast_pow]
  field_simp

def higherCosetWeight (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a : GaussianInt) (R n : ℕ) : ℝ :=
  kernelCount (tupleValue 0 R n)
    (fun z => (Submodule.Quotient.mk z : GaussianInt ⧸ multiples g) = c) a R

lemma higher_coset_eq_corr (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R n : ℕ) (hR : 0 < R) :
    letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
    letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
    let F : Sample (Box 0 R) (n+1) → GaussianInt ⧸ multiples g :=
      fun s => Submodule.Quotient.mk (tupleValue 0 R (n+1) s)
    higherCosetWeight g c a R n = (R : ℝ)^2*corr (density F) (density F)
      (c-Submodule.Quotient.mk a) := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  letI : Nonempty (Box 0 R) := box_nonempty 0 R hR
  dsimp only
  rw [higherCosetWeight,kernel_coset_eq_density _ g a R hR]
  let F : Sample (Box 0 R) (n+1) → GaussianInt ⧸ multiples g :=
    fun s => Submodule.Quotient.mk (tupleValue 0 R (n+1) s)
  have he := density_equiv (kernelEquiv a R n)
    (fun s => (Submodule.Quotient.mk (kernelValue (tupleValue 0 R n) a R s) : GaussianInt ⧸ multiples g))
    (fun s => Submodule.Quotient.mk a+(F s.1-F s.2)) (fun s => by
      change Submodule.Quotient.mk (kernelValue (tupleValue 0 R n) a R s) =
        Submodule.Quotient.mk a+(F (kernelEquiv a R n s).1-F (kernelEquiv a R n s).2)
      rw [kernelEquiv_value,Submodule.Quotient.mk_sub,Submodule.Quotient.mk_add]
      dsimp [F]
      abel) c
  rw [he,density_add_const,density_difference]

/-- This is the upper estimate for precisely the kernel appearing in
GaussianSmoothingBuckets.ray_forces_higher_smoothed_count. -/
theorem higher_coset_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R n : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |higherCosetWeight g c a R n-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      ((R : ℝ)^2/(g.norm.natAbs : ℝ))*(8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))^(2*(n+2)) := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  letI : Nonempty (Box 0 R) := box_nonempty 0 R hR
  let m : ℝ := g.norm.natAbs
  let κ : ℝ := 8*Real.sqrt m/(R : ℝ)
  let f : Box 0 R → GaussianInt ⧸ multiples g := fun s => Submodule.Quotient.mk s.val
  let F : Sample (Box 0 R) (n+1) → GaussianInt ⧸ multiples g :=
    fun s => Submodule.Quotient.mk (tupleValue 0 R (n+1) s)
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hc : (Fintype.card (GaussianInt ⧸ multiples g) : ℝ) = m := by
    dsimp [m]
    exact_mod_cast (Nat.card_eq_fintype_card.symm.trans (quotient_card g hg))
  have hf (q) : |density f q-1/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ)| ≤
      κ/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ) := by
    rw [hc]
    change |density (fun z : Box 0 R => (Submodule.Quotient.mk z.val : GaussianInt ⧸ multiples g)) q-1/m| ≤ κ/m
    rw [← boxDensity_eq_density]
    exact box_density_error g hg 0 R hR hmR q
  have hF (q) : |density F q-1/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ)| ≤
      κ^(n+2)/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ) := by
    have hEq : F = value f (n+1) := funext (quotient_tupleValue g 0 R (n+1))
    rw [hEq]
    exact sample_error_ratio f κ (by positivity) hf (n+1) q
  have hh := corr_error (density F) (density F) (density_mass F) (density_mass F)
    (κ^(n+2)/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ))
    (κ^(n+2)/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ))
    (by positivity) (by positivity) hF hF (c-Submodule.Quotient.mk a)
  rw [hc] at hh
  have hpow : m*(κ^(n+2)/m)*(κ^(n+2)/m) = κ^(2*(n+2))/m := by
    rw [show 2*(n+2) = (n+2)*2 by omega,pow_mul,pow_two]
    field_simp
  rw [hpow] at hh
  rw [higher_coset_eq_corr g hg c a R n hR]
  change |(R : ℝ)^2*corr (density F) (density F) (c-Submodule.Quotient.mk a)-(R : ℝ)^2/m| ≤
    ((R : ℝ)^2/m)*κ^(2*(n+2))
  have he : (R : ℝ)^2*corr (density F) (density F) (c-Submodule.Quotient.mk a)-(R : ℝ)^2/m =
      (R : ℝ)^2*(corr (density F) (density F) (c-Submodule.Quotient.mk a)-1/m) := by ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg (R : ℝ))]
  apply (mul_le_mul_of_nonneg_left hh (sq_nonneg (R : ℝ))).trans_eq
  ring

#print axioms kernelEquiv_value
#print axioms higher_coset_eq_corr
#print axioms higher_coset_error
end
end Erdos952Investigation.GaussianHigherSmoothingUpper
