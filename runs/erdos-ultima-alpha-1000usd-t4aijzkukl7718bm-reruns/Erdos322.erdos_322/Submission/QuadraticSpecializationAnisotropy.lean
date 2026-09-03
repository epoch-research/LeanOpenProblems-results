import Submission.QuarticFormalSpecialization

/-! Quadratic algebras inherit fourth-power anisotropy from a separating
family of specializations with two distinct roots. -/
namespace Erdos322Research.QuadraticSpecializationAnisotropy

noncomputable section
open QuarticFormalSpecialization
set_option Elab.async false
set_option maxHeartbeats 0

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation at a root, without imposing an algebra structure on the target. -/
def quadraticEval (a : R) (f : R →+* S) (r : S) (hr : r^2 = f a) :
    QuadraticAlgebra R a 0 →+* S where
  toFun z := f z.re + f z.im * r
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by simp [add_mul]; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,map_add,map_mul,
      zero_mul,add_zero]
    linear_combination -(f z.im*f w.im)*hr

@[simp] lemma quadraticEval_apply (a : R) (f : R →+* S) (r : S) (hr : r^2=f a)
    (z : QuadraticAlgebra R a 0) : quadraticEval a f r hr z = f z.re+f z.im*r := rfl

lemma quadraticEval_pair_zero [IsDomain S] [CharZero S]
    (a : R) (f : R →+* S) (r : S) (hr : r^2=f a) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra R a 0)
    (hp : quadraticEval a f r hr z = 0)
    (hm : quadraticEval a f (-r) (by simpa using hr) z = 0) :
    f z.re = 0 ∧ f z.im = 0 := by
  simp only [quadraticEval_apply] at hp hm
  have hre : (2 : S)*f z.re = 0 := by linear_combination hp+hm
  have him : (2*r)*f z.im = 0 := by linear_combination hp-hm
  exact ⟨(mul_eq_zero.mp hre).resolve_left (by norm_num),
    (mul_eq_zero.mp him).resolve_left (mul_ne_zero (by norm_num) hr0)⟩

/-- Separation is required jointly, not for each individual specialization.
This allows repeated quadratic adjunctions without irreducibility assumptions. -/
theorem quadratic_family_separates {ι : Type*} [IsDomain S] [CharZero S]
    (a : R) (f : ι → R →+* S)
    (hsep : ∀ z : R, (∀ j, f j z = 0) → z = 0)
    (r : ι → S) (hr : ∀ j, r j^2 = f j a) (hr0 : ∀ j, r j ≠ 0)
    (z : QuadraticAlgebra R a 0)
    (hp : ∀ j, quadraticEval a (f j) (r j) (hr j) z = 0)
    (hm : ∀ j, quadraticEval a (f j) (-r j) (by simpa using hr j) z = 0) : z = 0 := by
  have hh (j : ι) := quadraticEval_pair_zero a (f j) (r j) (hr j) (hr0 j) z (hp j) (hm j)
  apply QuadraticAlgebra.ext
  · exact hsep z.re (fun j ↦ (hh j).1)
  · exact hsep z.im (fun j ↦ (hh j).2)

/-- Fourth-power anisotropy after a quadratic adjunction, using a jointly
separating family of maps into one anisotropic domain. -/
theorem quadratic_anisotropic_of_family {ι : Type*} [IsDomain S] [CharZero S]
    (a : R) (f : ι → R →+* S)
    (hsep : ∀ z : R, (∀ j, f j z = 0) → z = 0)
    (r : ι → S) (hr : ∀ j, r j^2 = f j a) (hr0 : ∀ j, r j ≠ 0)
    (hS : FourthAnisotropic S) : FourthAnisotropic (QuadraticAlgebra R a 0) := by
  intro P hP i
  apply quadratic_family_separates a f hsep r hr hr0
  · intro j
    apply hS (fun i ↦ quadraticEval a (f j) (r j) (hr j) (P i)) _ i
    have hh := congrArg (quadraticEval a (f j) (r j) (hr j)) hP
    simpa only [map_sum,map_pow,map_zero] using hh
  · intro j
    apply hS (fun i ↦ quadraticEval a (f j) (-r j) (by simpa using hr j) (P i)) _ i
    have hh := congrArg (quadraticEval a (f j) (-r j) (by simpa using hr j)) hP
    simpa only [map_sum,map_pow,map_zero] using hh

/-- The single injective coefficient-map case. -/
theorem quadratic_anisotropic [IsDomain S] [CharZero S]
    (a : R) (f : R →+* S) (hf : Function.Injective f)
    (r : S) (hr : r^2=f a) (hr0 : r ≠ 0) (hS : FourthAnisotropic S) :
    FourthAnisotropic (QuadraticAlgebra R a 0) := by
  apply quadratic_anisotropic_of_family a (fun _ : Unit ↦ f)
    (fun z hz ↦ hf (by simpa using hz ())) (fun _ ↦ r) (fun _ ↦ hr) (fun _ ↦ hr0) hS

/-- Two independent quadratic relations. Both sign choices for each root
are retained, so no irreducibility or field-extension hypothesis is needed. -/
theorem double_quadratic_anisotropic [IsDomain S] [CharZero S]
    (a b : R) (f : R →+* S) (hf : Function.Injective f)
    (r s : S) (hr : r^2=f a) (hs : s^2=f b) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hS : FourthAnisotropic S) :
    FourthAnisotropic (QuadraticAlgebra (QuadraticAlgebra R b 0)
      (algebraMap R (QuadraticAlgebra R b 0) a) 0) := by
  let F : Bool → QuadraticAlgebra R b 0 →+* S := fun j ↦
    if j then quadraticEval b f s hs else quadraticEval b f (-s) (by simpa using hs)
  have hsep : ∀ z : QuadraticAlgebra R b 0, (∀ j, F j z = 0) → z = 0 := by
    intro z hz
    have hh := quadraticEval_pair_zero b f s hs hs0 z (hz true) (hz false)
    apply QuadraticAlgebra.ext
    · exact hf (by simpa using hh.1)
    · exact hf (by simpa using hh.2)
  apply quadratic_anisotropic_of_family _ F hsep (fun _ ↦ r) _ (fun _ ↦ hr0) hS
  intro j
  cases j <;> simpa [F,quadraticEval_apply] using hr

end
end Erdos322Research.QuadraticSpecializationAnisotropy
