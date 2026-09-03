import Submission.QuarticFiveInputDegreeFourLinear6
import Submission.QuarticAutomaticHomogeneity

/-! A kernel-checked interpolation classification for homogeneous quartic
five-input to four-output norm transfers. This is not a full count bound. -/
namespace Erdos322Research.QuarticFiveInputDegreeFour
noncomputable section
open GaussianQuartic
open Matrix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A general homogeneous quartic form, encoded by its seventy coefficients. -/
def form {R : Type*} [CommRing R] (a : Fin 70 → R) : MvPolynomial (Fin 5) R :=
  ∑ m, MvPolynomial.C (a m)*∏ j, MvPolynomial.X j^exponents m j

private def projection (r : Fin 69) : GaussianInt →+ ℤ :=
  if imaginaryPart r then
    { toFun := Zsqrtd.im, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  else
    { toFun := Zsqrtd.re, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }

private lemma projection_int_mul (r : Fin 69) (a : ℤ) (z : GaussianInt) :
    projection r ((a : GaussianInt)*z)=a*projection r z := by
  dsimp only [projection]
  split_ifs <;> simp

private lemma projection_monomial (r : Fin 69) (m : Fin 70) :
    projection r (∏ j, testPoint r j^exponents m j)=evaluationMatrix r m := by
  rw [evaluationMatrix_correct]
  dsimp only [projection]
  split_ifs <;> rfl

private lemma evaluation_eq_mulVec (a : Fin 70 → ℤ) (r : Fin 69) :
    projection r (MvPolynomial.eval₂Hom (Int.castRingHom GaussianInt) (testPoint r) (form a))=
      (evaluationMatrix *ᵥ a) r := by
  simp only [form,map_sum,map_mul,map_prod,map_pow,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',Int.coe_castRingHom,projection_int_mul,projection_monomial]
  simp only [Matrix.mulVec,dotProduct,mul_comm]

private lemma radial_of_evaluation_zero (a : Fin 70 → ℤ)
    (h : evaluationMatrix *ᵥ a=0) : ∀ m, a m=radialMask m*a 0 := by
  intro m
  fin_cases m
  · change a 0=1*a 0
    ring
  · exact coefficient1 a h
  · exact coefficient2 a h
  · exact coefficient3 a h
  · exact coefficient4 a h
  · exact coefficient5 a h
  · exact coefficient6 a h
  · exact coefficient7 a h
  · exact coefficient8 a h
  · exact coefficient9 a h
  · exact coefficient10 a h
  · exact coefficient11 a h
  · exact coefficient12 a h
  · exact coefficient13 a h
  · exact coefficient14 a h
  · exact coefficient15 a h
  · exact coefficient16 a h
  · exact coefficient17 a h
  · exact coefficient18 a h
  · exact coefficient19 a h
  · exact coefficient20 a h
  · exact coefficient21 a h
  · exact coefficient22 a h
  · exact coefficient23 a h
  · exact coefficient24 a h
  · exact coefficient25 a h
  · exact coefficient26 a h
  · exact coefficient27 a h
  · exact coefficient28 a h
  · exact coefficient29 a h
  · exact coefficient30 a h
  · exact coefficient31 a h
  · exact coefficient32 a h
  · exact coefficient33 a h
  · exact coefficient34 a h
  · exact coefficient35 a h
  · exact coefficient36 a h
  · exact coefficient37 a h
  · exact coefficient38 a h
  · exact coefficient39 a h
  · exact coefficient40 a h
  · exact coefficient41 a h
  · exact coefficient42 a h
  · exact coefficient43 a h
  · exact coefficient44 a h
  · exact coefficient45 a h
  · exact coefficient46 a h
  · exact coefficient47 a h
  · exact coefficient48 a h
  · exact coefficient49 a h
  · exact coefficient50 a h
  · exact coefficient51 a h
  · exact coefficient52 a h
  · exact coefficient53 a h
  · exact coefficient54 a h
  · exact coefficient55 a h
  · exact coefficient56 a h
  · exact coefficient57 a h
  · exact coefficient58 a h
  · exact coefficient59 a h
  · exact coefficient60 a h
  · exact coefficient61 a h
  · exact coefficient62 a h
  · exact coefficient63 a h
  · exact coefficient64 a h
  · exact coefficient65 a h
  · exact coefficient66 a h
  · exact coefficient67 a h
  · exact coefficient68 a h
  · exact coefficient69 a h

private lemma mask_form : form radialMask=∑ j : Fin 5, MvPolynomial.X j^4 := by
  norm_num [form,radialMask,exponents,Fin.sum_univ_succ,Fin.prod_univ_succ]
  ring_nf!

private lemma form_radial (a : Fin 70 → ℤ) (h : ∀ m, a m=radialMask m*a 0) :
    form a=MvPolynomial.C (a 0)*(∑ j : Fin 5, MvPolynomial.X j^4) := by
  conv_lhs => unfold form; arg 2; ext m; rw [h m]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_left_comm (MvPolynomial.C (radialMask _)) (MvPolynomial.C (a 0))]
  rw [← Finset.mul_sum]
  change MvPolynomial.C (a 0)*form radialMask=_
  rw [mask_form]

/-- Every homogeneous degree-four integer-coefficient transfer of the
five-coordinate quartic norm to four coordinates is radial: each output is a
constant multiple of the original norm. The multiplier need not be positive. -/
theorem transfer_is_radial (A : Fin 4 → Fin 70 → ℤ) (C : ℤ)
    (h : ∑ i, (form (A i))^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4) :
    ∀ i, form (A i)=MvPolynomial.C (A i 0)*(∑ j : Fin 5, MvPolynomial.X j^4) := by
  have hz (r : Fin 69) (i : Fin 4) :
      MvPolynomial.eval₂Hom (Int.castRingHom GaussianInt) (testPoint r) (form (A i))=0 := by
    apply gaussian_fourth_sum_zero (fun j ↦ MvPolynomial.eval₂Hom (Int.castRingHom GaussianInt) (testPoint r) (form (A j))) _ i
    have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom GaussianInt) (testPoint r)) h
    simpa only [map_sum,map_pow,map_mul,MvPolynomial.eval₂Hom_X',
      testPoint_norm,zero_pow (by decide : 4 ≠ 0),mul_zero] using he
  intro i
  apply form_radial
  apply radial_of_evaluation_zero
  funext r
  rw [← evaluation_eq_mulVec,hz,map_zero]
  rfl

/-- Consequently all evaluations on one input norm level coincide. Such a
transfer cannot carry multiplicity from the five-input problem. -/
theorem transfer_constant_on_levels (A : Fin 4 → Fin 70 → ℤ) (C : ℤ)
    (h : ∑ i, (form (A i))^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j^4=∑ j, y j^4) (i : Fin 4) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) x (form (A i))=
      MvPolynomial.eval₂Hom (Int.castRingHom ℚ) y (form (A i)) := by
  rw [transfer_is_radial A C h i]
  simp only [map_mul,map_sum,map_pow,MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',hxy]

private lemma map_form {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 70 → R) :
    MvPolynomial.map f (form a)=form (fun m ↦ f (a m)) := by
  simp [form]

private lemma form_scalar {R : Type*} [CommRing R] (a : Fin 70 → R) (c : R) :
    form (fun m ↦ c*a m)=MvPolynomial.C c*form a := by
  simp [form,Finset.mul_sum,mul_assoc]

private lemma form_at_axis {R : Type*} [CommRing R] (a : Fin 70 → R) :
    MvPolynomial.eval ![1,0,0,0,0] (form a)=a 0 := by
  simp [form,exponents,Fin.sum_univ_succ,Fin.prod_univ_succ]

private theorem common_denominator {ι : Type*} [Fintype ι] (a : ι → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ b : ι → ℤ, ∀ i, (b i : ℚ)=(d : ℚ)*a i := by
  classical
  let d := ∏ i, (a i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  refine ⟨d,hd,fun i ↦ (a i).num*(d/(a i).den),?_⟩
  intro i
  have hdiv : (a i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hm : ((a i).den : ℚ)*(d/(a i).den : ℕ)=d := by
    exact_mod_cast Nat.mul_div_cancel' hdiv
  push_cast
  calc
    ((a i).num : ℚ)*(d/(a i).den : ℕ) =
        (a i*(a i).den)*(d/(a i).den : ℕ) := by rw [Rat.mul_den_eq_num]
    _ = (d : ℚ)*a i := by rw [mul_assoc,hm,mul_comm]

/-- The same classification for rational coefficients and an arbitrary
rational target multiplier. Clearing coefficients creates no extra formulas. -/
theorem rational_transfer_is_radial (A : Fin 4 → Fin 70 → ℚ) (C : ℚ)
    (h : ∑ i, (form (A i))^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4) :
    ∀ i, form (A i)=MvPolynomial.C (A i 0)*(∑ j : Fin 5, MvPolynomial.X j^4) := by
  obtain ⟨d,hd,b,hb⟩ := common_denominator (fun im : Fin 4 × Fin 70 ↦ A im.1 im.2)
  let B : Fin 4 → Fin 70 → ℤ := fun i m ↦ b (i,m)
  have hB (i : Fin 4) (m : Fin 70) : (B i m : ℚ)=(d : ℚ)*A i m := hb (i,m)
  have hmap (i : Fin 4) : MvPolynomial.map (Int.castRingHom ℚ) (form (B i))=
      MvPolynomial.C (d : ℚ)*form (A i) := by
    rw [map_form]
    simp only [Int.coe_castRingHom,hB]
    exact form_scalar _ _
  have hC : ∑ i, A i 0^4=C := by
    have he := congrArg (MvPolynomial.eval (![1,0,0,0,0] : Fin 5 → ℚ)) h
    simpa only [map_sum,map_add,map_pow,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
      form_at_axis,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.cons_val_fin_one,Fin.sum_univ_zero,zero_pow (by decide : 4 ≠ 0),
      one_pow,add_zero,mul_one] using he
  let K : ℤ := ∑ i, B i 0^4
  have hK : (K : ℚ)=(d : ℚ)^4*C := by
    dsimp only [K]
    push_cast
    simp_rw [hB,mul_pow]
    rw [← Finset.mul_sum,hC]
  have hIdentity : ∑ i, (form (B i))^4=
      MvPolynomial.C K*(∑ j : Fin 5, MvPolynomial.X j^4)^4 := by
    apply MvPolynomial.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
    simp only [map_sum,map_pow,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,hmap,
      Int.coe_castRingHom,hK]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum,h]
    ring
  have hd0 : MvPolynomial.C (d : ℚ) ≠ (0 : MvPolynomial (Fin 5) ℚ) := by
    simpa only [ne_eq,MvPolynomial.C_eq_zero] using (show (d : ℚ) ≠ 0 by exact_mod_cast hd.ne')
  intro i
  have he := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) (transfer_is_radial B K hIdentity i)
  rw [hmap] at he
  simp only [map_mul,map_sum,map_pow,MvPolynomial.map_C,MvPolynomial.map_X,
    Int.coe_castRingHom,hB] at he
  rw [mul_assoc] at he
  exact mul_left_cancel₀ hd0 he

/-- All rational evaluations on equal input norm levels coincide. -/
theorem rational_transfer_constant_on_levels (A : Fin 4 → Fin 70 → ℚ) (C : ℚ)
    (h : ∑ i, (form (A i))^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j^4=∑ j, y j^4) (i : Fin 4) :
    MvPolynomial.eval x (form (A i))=MvPolynomial.eval y (form (A i)) := by
  rw [rational_transfer_is_radial A C h i]
  simp only [map_mul,map_sum,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,hxy]

private theorem exponents_injective : Function.Injective exponents := by decide +kernel

private theorem exponents_exhaustive : ∀ a b c d e : Fin 5,
    a.val+b.val+c.val+d.val+e.val=4 →
      ∃ m : Fin 70, exponents m=![a.val,b.val,c.val,d.val,e.val] := by decide +kernel

private noncomputable def multiIndex (m : Fin 70) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (exponents m)

private lemma multiIndex_injective : Function.Injective multiIndex := by
  intro m n h
  apply exponents_injective
  exact congrArg (fun f : Fin 5 →₀ ℕ ↦ (f : Fin 5 → ℕ)) h

private lemma form_as_monomials {R : Type*} [CommRing R] (a : Fin 70 → R) :
    form a=∑ m, MvPolynomial.monomial (multiIndex m) (a m) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  rfl

private lemma homogeneous_index {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin 5) R) (hP : P.IsHomogeneous 4)
    (e : Fin 5 →₀ ℕ) (he : P.coeff e ≠ 0) : ∃ m : Fin 70, multiIndex m=e := by
  have hs : ∑ j : Fin 5, e j=4 := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hP he
  have hb (j : Fin 5) : e j<5 := by
    have hh := Finset.single_le_sum (f := fun j : Fin 5 ↦ e j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    rw [hs] at hh
    change e j ≤ 4 at hh
    omega
  obtain ⟨m,hm⟩ := exponents_exhaustive ⟨e 0,hb 0⟩ ⟨e 1,hb 1⟩
    ⟨e 2,hb 2⟩ ⟨e 3,hb 3⟩ ⟨e 4,hb 4⟩ (by simpa [Fin.sum_univ_succ,← add_assoc] using hs)
  refine ⟨m,?_⟩
  ext j
  change exponents m j=e j
  rw [hm]
  fin_cases j <;> rfl

/-- The coefficient encoding is complete, not a restriction to a proper
subspace of homogeneous quartic polynomials. -/
theorem homogeneous_form_expansion {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin 5) R) (hP : P.IsHomogeneous 4) :
    ∃ a : Fin 70 → R, form a=P := by
  classical
  refine ⟨fun m ↦ P.coeff (multiIndex m),?_⟩
  rw [form_as_monomials]
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  by_cases hex : ∃ m : Fin 70, multiIndex m=e
  · obtain ⟨m,rfl⟩ := hex
    simp only [multiIndex_injective.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · have hz : P.coeff e=0 := by
      by_contra hn
      exact hex (homogeneous_index P hP e hn)
    have hh (m : Fin 70) : multiIndex m ≠ e := fun he ↦ hex ⟨m,he⟩
    simp only [hh,if_false,Finset.sum_const_zero,hz]

/-- Direct polynomial version: every homogeneous degree-four rational
five-input to four-output norm-power formula is constant on each input level. -/
theorem homogeneous_transfer_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (hP : ∀ i, (P i).IsHomogeneous 4) (C : ℚ)
    (h : ∑ i, P i^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j^4=∑ j, y j^4) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) := by
  choose A hA using fun i ↦ homogeneous_form_expansion (P i) (hP i)
  have hh : ∑ i, (form (A i))^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4 := by
    simpa only [hA] using h
  simpa only [hA] using rational_transfer_constant_on_levels A C hh x y hxy i

/-- The only polynomial identities with this target are the trivial radial
ones. No degree, positivity, or homogeneity assumption is imposed. -/
theorem polynomial_transfer_iff
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (C : ℚ) :
    (∑ i, P i^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4) ↔
      ∃ b : Fin 4 → ℚ,
        (∀ i, P i=MvPolynomial.C (b i)*(∑ j : Fin 5, MvPolynomial.X j^4)) ∧
        ∑ i, b i^4=C := by
  constructor
  · intro h
    have hP := QuarticAutomaticHomogeneity.transfer_is_homogeneous P C 4 h
    choose A hA using fun i ↦ homogeneous_form_expansion (P i) (hP i)
    have hh : ∑ i, (form (A i))^4=
        MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4 := by
      simpa only [hA] using h
    refine ⟨fun i ↦ A i 0,?_,?_⟩
    · intro i
      rw [← hA i]
      exact rational_transfer_is_radial A C hh i
    · have he := congrArg (MvPolynomial.eval (![1,0,0,0,0] : Fin 5 → ℚ)) hh
      simpa only [map_sum,map_add,map_pow,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
        form_at_axis,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_fin_one,Fin.sum_univ_zero,zero_pow (by decide : 4 ≠ 0),
        one_pow,add_zero,mul_one] using he
  · rintro ⟨b,hP,hb⟩
    simp_rw [hP,mul_pow,← map_pow]
    rw [← Finset.sum_mul,← map_sum,hb]

/-- No degree assumption is necessary: every polynomial transfer to the fourth
power of the five-coordinate norm is constant on each input norm level. -/
theorem polynomial_transfer_constant_on_levels
    (P : Fin 4 → MvPolynomial (Fin 5) ℚ) (C : ℚ)
    (h : ∑ i, P i^4=MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^4)
    (x y : Fin 5 → ℚ) (hxy : ∑ j, x j^4=∑ j, y j^4) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) :=
  homogeneous_transfer_constant_on_levels P
    (QuarticAutomaticHomogeneity.transfer_is_homogeneous P C 4 h) C h x y hxy i

end
end Erdos322Research.QuarticFiveInputDegreeFour
