import Submission.QuarticBilinearObstruction

/-! Polynomial maps cannot provide a dimension-saving product of quartic norms. -/
namespace Erdos322Research.QuarticPolynomial

open Polynomial

private theorem degree_bound_of_fourth_power_sum
    {ι : Type*} [Fintype ι] (p : ι → Polynomial ℝ) (d : ℕ)
    (h : (∑ i, p i^4).natDegree ≤ 4*d) :
    ∀ i, (p i).natDegree ≤ d := by
  classical
  intro i
  by_contra hn
  let D := Finset.univ.sup (fun j ↦ (p j).natDegree)
  have hDi : (p i).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (p j).natDegree) (Finset.mem_univ i)
  have hDd : d < D := by omega
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨i⟩) (fun j ↦ (p j).natDegree)
  change D=(p j).natDegree at hj
  have hD (a : ι) : (p a).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (p j).natDegree) (Finset.mem_univ a)
  have hz : (∑ a, p a^4).coeff (4*D)=0 :=
    coeff_eq_zero_of_natDegree_lt (h.trans_lt (by omega))
  have he : (∑ a, p a^4).coeff (4*D)=∑ a, (p a).coeff D^4 := by
    simp only [finset_sum_coeff]
    exact Finset.sum_congr rfl (fun a _ ↦ coeff_pow_of_natDegree_le (hD a))
  have hpn : p j ≠ 0 := by
    intro hp
    simp [hp] at hj
    omega
  have hcoeff : (p j).coeff D ≠ 0 := by
    rw [hj, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hpn
  have hp : 0 < (p j).coeff D^4 := by positivity
  have hh := Finset.single_le_sum (f := fun a ↦ (p a).coeff D^4)
    (fun a _ ↦ by positivity) (Finset.mem_univ j)
  rw [he] at hz
  linarith

/-- Each coordinate is a polynomial on every affine line. All multivariate
polynomial maps have this property. -/
def PolynomialOnLines {κ ι : Type*} (F : (κ → ℝ) → (ι → ℝ)) : Prop :=
  ∀ x v i, ∃ p : Polynomial ℝ, ∀ t : ℝ,
    F (x+t • v) i=p.eval t

/-- A polynomial map preserving a positive even quartic norm up to a scalar
must be linear; the scalar need not be assumed positive. -/
theorem norm_polynomial_is_linear
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (F : (κ → ℝ) → (ι → ℝ)) (C : ℝ)
    (hpoly : PolynomialOnLines F)
    (h : ∀ x, ∑ i, F x i^4=C*∑ j, x j^4) :
    ∃ L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ), ∀ x, F x=L x := by
  classical
  have hzero : F 0=0 := by
    funext i
    have hs : ∑ j, F 0 j^4=0 := by simpa using h 0
    have hi := Finset.single_le_sum (f := fun j ↦ F 0 j^4)
      (fun _ _ ↦ by positivity) (Finset.mem_univ i)
    rw [hs] at hi
    have hz : F 0 i^4=0 := le_antisymm hi (by positivity)
    exact eq_zero_of_pow_eq_zero hz
  have haff (x v : κ → ℝ) (i : ι) (t : ℝ) :
      F (x+t • v) i=F x i+t*(F (x+v) i-F x i) := by
    choose p hp using hpoly x v
    let q : Polynomial ℝ := Polynomial.C C *
      ∑ j, (Polynomial.C (x j)+Polynomial.C (v j)*Polynomial.X)^4
    have heq : ∑ i, p i^4=q := by
      apply Polynomial.funext
      intro s
      simp only [eval_finset_sum,eval_pow]
      simp_rw [←hp]
      rw [h]
      simp only [q,eval_mul,eval_C,eval_finset_sum,eval_pow,eval_add,eval_X,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hd : q.natDegree ≤ 4*1 := by
      apply (natDegree_C_mul_le _ _).trans
      apply natDegree_sum_le_of_forall_le
      intro j _
      apply natDegree_pow_le.trans
      have hb : (Polynomial.C (x j)+Polynomial.C (v j)*Polynomial.X).natDegree ≤ 1 := by
        apply natDegree_add_le_of_degree_le
        · simp
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      omega
    have hl := degree_bound_of_fourth_power_sum p 1 (heq ▸ hd) i
    have he := eq_X_add_C_of_natDegree_le_one hl
    have h0 := hp i 0
    have h1 := hp i 1
    have ht := hp i t
    rw [he] at h0 h1 ht
    simp only [zero_smul,add_zero,one_smul,eval_add,eval_mul,eval_C,eval_X,
      mul_zero,zero_add,mul_one] at h0 h1 ht
    rw [h0,h1,ht]
    ring
  have hsmul (t : ℝ) (x : κ → ℝ) : F (t • x)=t • F x := by
    funext i
    have hh := haff 0 x i t
    simpa [hzero] using hh
  have hadd (x y : κ → ℝ) : F (x+y)=F x+F y := by
    funext i
    have ha := haff x (y-x) i (1/2)
    have hb := congrFun (hsmul (1/2) (x+y)) i
    have hm : x+(1/2 : ℝ) • (y-x)=(1/2 : ℝ) • (x+y) := by
      funext j
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hm,show x+(y-x)=y by abel] at ha
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hb ⊢
    linarith
  exact ⟨{ toFun := F, map_add' := hadd, map_smul' := hsmul },fun _ ↦ rfl⟩


/-- Allowing arbitrary polynomial coordinate formulas does not lower the
number of outputs needed for a quartic-norm multiplication formula. -/
theorem output_dimension_ge_product
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq κ] [DecidableEq ν]
    (F : (κ → ℝ) → (ν → ℝ) → (ι → ℝ)) (C : ℝ) (hC : 0 < C)
    (hx : ∀ y, PolynomialOnLines (fun x ↦ F x y))
    (hy : ∀ x, PolynomialOnLines (F x))
    (h : ∀ x y, ∑ i, F x y i^4=C*(∑ j, x j^4)*(∑ l, y l^4)) :
    Fintype.card κ * Fintype.card ν ≤ Fintype.card ι := by
  classical
  have hxl (y : ν → ℝ) : ∃ L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ),
      ∀ x, F x y=L x := by
    apply norm_polynomial_is_linear _ (C*∑ l, y l^4) (hx y)
    intro x
    simpa only [mul_comm,mul_left_comm,mul_assoc] using h x y
  have hyl (x : κ → ℝ) : ∃ L : (ν → ℝ) →ₗ[ℝ] (ι → ℝ),
      ∀ y, F x y=L y := norm_polynomial_is_linear _ _ (hy x) (h x)
  choose L hL using hxl
  choose R hR using hyl
  let eK (j : κ) : κ → ℝ := Pi.single j 1
  let eN (l : ν) : ν → ℝ := Pi.single l 1
  have hxsum (x : κ → ℝ) : ∑ j, x j • eK j=x := by
    funext j
    simp [eK,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  have hysum (y : ν → ℝ) : ∑ l, y l • eN l=y := by
    funext l
    simp [eN,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  have hrepX (x : κ → ℝ) (y : ν → ℝ) (i : ι) :
      F x y i=∑ j, x j*F (eK j) y i := by
    have hh : F x y=∑ j, x j • F (eK j) y := by
      calc
        F x y = L y x := hL y x
        _ = L y (∑ j, x j • eK j) := congrArg (L y) (hxsum x).symm
        _ = ∑ j, x j • L y (eK j) := by simp only [map_sum,map_smul]
        _ = _ := by simp_rw [←hL]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun hh i
  have hrepY (x : κ → ℝ) (y : ν → ℝ) (i : ι) :
      F x y i=∑ l, y l*F x (eN l) i := by
    have hh : F x y=∑ l, y l • F x (eN l) := by
      calc
        F x y = R x y := hR x y
        _ = R x (∑ l, y l • eN l) := congrArg (R x) (hysum y).symm
        _ = ∑ l, y l • R x (eN l) := by simp only [map_sum,map_smul]
        _ = _ := by simp_rw [←hR]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun hh i
  have hrep (x : κ → ℝ) (y : ν → ℝ) (i : ι) :
      F x y i=∑ j, ∑ l, F (eK j) (eN l) i*x j*y l := by
    rw [hrepX]
    apply Finset.sum_congr rfl
    intro j _
    rw [hrepY (eK j) y i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  apply QuarticBilinear.output_dimension_ge_product
    (fun i j l ↦ F (eK j) (eN l) i) C hC
  intro x y
  simp_rw [←hrep]
  exact h x y


private theorem eval_line_polynomial {σ : Type*}
    (P : MvPolynomial σ ℝ) (a b : σ → ℝ) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      MvPolynomial.eval (fun j ↦ a j+t*b j) P=p.eval t := by
  refine ⟨MvPolynomial.eval₂ Polynomial.C
    (fun j ↦ Polynomial.C (a j)+Polynomial.C (b j)*Polynomial.X) P,fun t ↦ ?_⟩
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C=RingHom.id ℝ := by
    ext r
    simp
  rw [hc,MvPolynomial.eval₂_id]
  apply congrArg (fun g : σ → ℝ ↦ MvPolynomial.eval g P)
  funext j
  simp only [eval_add,eval_mul,eval_C,eval_X]
  ring

/-- This formulation applies directly to arbitrary multivariate polynomial
coordinate formulas, with no degree restriction. -/
theorem mvPolynomial_output_dimension_ge_product
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq κ] [DecidableEq ν]
    (P : ι → MvPolynomial (κ ⊕ ν) ℝ) (C : ℝ) (hC : 0 < C)
    (h : ∀ (x : κ → ℝ) (y : ν → ℝ),
      ∑ i, (MvPolynomial.eval (Sum.elim x y) (P i))^4 =
        C*(∑ j, x j^4)*(∑ l, y l^4)) :
    Fintype.card κ * Fintype.card ν ≤ Fintype.card ι := by
  apply output_dimension_ge_product
    (fun x y i ↦ MvPolynomial.eval (Sum.elim x y) (P i)) C hC ?_ ?_ h
  · intro y x v i
    obtain ⟨p,hp⟩ := eval_line_polynomial (P i) (Sum.elim x y) (Sum.elim v 0)
    refine ⟨p,fun t ↦ ?_⟩
    refine (congrArg (fun g : (κ ⊕ ν) → ℝ ↦ MvPolynomial.eval g (P i)) ?_).trans (hp t)
    funext j
    cases j <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · intro x y v i
    obtain ⟨p,hp⟩ := eval_line_polynomial (P i) (Sum.elim x y) (Sum.elim 0 v)
    refine ⟨p,fun t ↦ ?_⟩
    refine (congrArg (fun g : (κ ⊕ ν) → ℝ ↦ MvPolynomial.eval g (P i)) ?_).trans (hp t)
    funext j
    cases j <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]

/-- There is no four-coordinate polynomial multiplication formula for quartic
norms, even if arbitrarily high polynomial degrees are allowed. -/
theorem no_four_coordinate_polynomial_product
    (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℝ) :
    ¬ (∀ (x y : Fin 4 → ℝ),
      ∑ i, (MvPolynomial.eval (Sum.elim x y) (P i))^4 =
        (∑ j, x j^4)*(∑ l, y l^4)) := by
  intro h
  have hc := mvPolynomial_output_dimension_ge_product P 1 (by norm_num) (by simpa using h)
  norm_num at hc

end Erdos322Research.QuarticPolynomial
