import Submission.QuarticAdditiveThinning

/-!
The quartic additive-norm thinning obstruction extends to characteristic two.
Together with the odd-characteristic coordinate argument, this covers every
finite quartic extension. It does not concern multiplicative norm weights.
-/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714QuarticAdditiveAll
open Erdos714QuarticAdditive
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The characteristic polynomial of multiplication by -x. -/
def normPolynomial (x : E) : F[X] :=
  (Algebra.leftMulMatrix (Module.finBasis F E) (-x)).charpoly

omit [Fintype F] in
lemma normPolynomial_eval (x : E) (t : F) :
    (normPolynomial (F := F) x).eval t = Algebra.norm F (x+algebraMap F E t) := by
  rw [normPolynomial,Matrix.eval_charpoly,Algebra.norm_eq_matrix_det (Module.finBasis F E)]
  congr 1
  rw [map_add,map_neg,AlgHom.commutes]
  simp only [sub_neg_eq_add,add_comm]
  rfl

omit [Fintype F] in
lemma normPolynomial_degree (hd : Module.finrank F E=4) (x : E) :
    (normPolynomial (F := F) x).natDegree=4 := by
  rw [normPolynomial,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin,hd]

omit [Fintype F] in
lemma normPolynomial_cubic (hd : Module.finrank F E=4) (x : Point (F := F) (E := E)) :
    (normPolynomial (F := F) x.val).coeff 3=0 := by
  have ht := Matrix.trace_eq_neg_charpoly_nextCoeff
    (Algebra.leftMulMatrix (Module.finBasis F E) (-x.val))
  rw [←Algebra.trace_eq_matrix_trace,map_neg,x.property,neg_zero] at ht
  change 0 = -(normPolynomial (F := F) x.val).nextCoeff at ht
  rw [Polynomial.nextCoeff,normPolynomial_degree hd] at ht
  norm_num at ht
  exact ht

omit [Fintype F] in
/-- The scalar shift of a trace-zero quartic norm has just three free coefficients. -/
lemma norm_shift (hd : Module.finrank F E=4) (x : Point (F := F) (E := E)) (t : F) :
    Algebra.norm F (x.val+algebraMap F E t) = t^4+
      (normPolynomial (F := F) x.val).coeff 2*t^2+
      (normPolynomial (F := F) x.val).coeff 1*t+Algebra.norm F x.val := by
  have hm : (normPolynomial (F := F) x.val).Monic := Matrix.charpoly_monic _
  have h4 : (normPolynomial (F := F) x.val).coeff 4=1 := by
    rw [←normPolynomial_degree hd x.val]
    exact hm.coeff_natDegree
  have h0 : (normPolynomial (F := F) x.val).coeff 0=Algebra.norm F x.val := by
    rw [Polynomial.coeff_zero_eq_eval_zero,normPolynomial_eval,map_zero,add_zero]
  rw [←normPolynomial_eval,Polynomial.eval_eq_sum_range,normPolynomial_degree hd]
  simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add,mul_one,
    normPolynomial_cubic hd,h4,h0,zero_mul,add_zero,one_mul]
  ring

section Splitting
variable {W : Type*} [AddCommGroup W] [Module F W]

def splitEquiv (w : W) (ℓ : W →ₗ[F] F) (hℓ : ℓ w=1) : (ℓ.ker × F) ≃ W := by
  let f : ℓ.ker × F → W := fun p => p.1.val+p.2 • w
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨v,t⟩ ⟨v',t'⟩ he
    have ht : t=t' := by
      have h := congrArg ℓ he
      change ℓ (v.val+t • w)=ℓ (v'.val+t' • w) at h
      simpa only [map_add,map_smul,LinearMap.mem_ker.mp v.property,
        LinearMap.mem_ker.mp v'.property,hℓ,smul_eq_mul,mul_one,zero_add] using h
    subst t'
    have hv : v=v' := Subtype.ext (add_right_cancel he)
    subst v'
    rfl
  · intro x
    refine ⟨(⟨x-ℓ x • w,?_⟩,ℓ x),?_⟩
    · rw [LinearMap.mem_ker,map_sub,map_smul,hℓ,smul_eq_mul,mul_one,sub_self]
    · dsimp [f]
      module
end Splitting

section Binary
variable [CharP F 2]

def onePoint (hd : Module.finrank F E=4) : Point (F := F) (E := E) :=
  ⟨1,by
    change Algebra.trace F E 1=0
    rw [←map_one (algebraMap F E),Algebra.trace_algebraMap,hd]
    norm_num [nsmul_eq_mul]
    reduce_mod_char!⟩

omit [Fintype F] in
lemma onePoint_ne_zero (hd : Module.finrank F E=4) : onePoint (F := F) hd ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

lemma split_card (hd : Module.finrank F E=4)
    (ℓ : Point (F := F) (E := E) →ₗ[F] F) (hℓ : ℓ (onePoint hd)=1) :
    Fintype.card ℓ.ker=Fintype.card F^2 := by
  have h := Fintype.card_congr (splitEquiv (onePoint hd) ℓ hℓ)
  rw [Fintype.card_prod,point_card hd] at h
  have hh : Fintype.card ℓ.ker*Fintype.card F=Fintype.card F^2*Fintype.card F := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos hh

/-- Characteristic two uses the scalar line contained in the trace kernel. -/
theorem binary_fourth_power (hd : Module.finrank F E=4)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one F (onePoint_ne_zero (F := F) (E := E) hd)
  let C := Point (F := F) (E := E) × F
  let V := ℓ.ker
  let ec : (V × F) ≃ Point (F := F) (E := E) := splitEquiv (onePoint hd) ℓ hℓ
  let e : (C ⊕ ((V × F) × F)) ≃ (C ⊕ C) :=
    (Equiv.refl C).sumCongr (ec.prodCongr (Equiv.refl F))
  let J := H.comap e
  let g (v : V) (c : C) : F × F × F :=
    ((normPolynomial (F := F) (v.val+c.1).val).coeff 2,
      (normPolynomial (F := F) (v.val+c.1).val).coeff 1,
      Algebra.norm F (v.val+c.1).val-c.2)
  let ev (_v : V) (p : F × F × F) (t : F) : F := t^4+p.1*t^2+p.2.1*t+p.2.2
  have hJ : J ≤ Erdos714Coding.graph (Erdos714ProfileThinning.code g ev) := by
    have hc (c : C) (v : V) (t a : F) (ha : H.Adj (.inl c) (.inr (ec (v,t),a))) :
        ev v (g v c) t=a := by
      have h := hH ha
      change Algebra.norm F (c.1.val+(ec (v,t)).val)=c.2+a at h
      have hec : (ec (v,t)).val=v.val.val+algebraMap F E t := by
        change (v.val+t • onePoint hd).val=_
        simp only [Submodule.coe_add,Submodule.coe_smul,Algebra.smul_def,onePoint,mul_one]
      rw [hec,show c.1.val+(v.val.val+algebraMap F E t)=
        (v.val+c.1).val+algebraMap F E t by simp only [Submodule.coe_add]; ring,
        norm_shift hd] at h
      dsimp [ev,g]
      linear_combination h
    intro a b hab
    cases a with
    | inl c =>
      cases b with
      | inl d => exact False.elim (hH hab)
      | inr y =>
        change (y.1,y.2) ∈ Erdos714Coding.symbols (Erdos714ProfileThinning.code g ev) c
        rw [Erdos714Coding.mem_symbols]
        exact hc c y.1.1 y.1.2 y.2 hab
    | inr y =>
      cases b with
      | inr z => exact False.elim (hH hab)
      | inl c =>
        change (y.1,y.2) ∈ Erdos714Coding.symbols (Erdos714ProfileThinning.code g ev) c
        rw [Erdos714Coding.mem_symbols]
        exact hc c y.1.1 y.1.2 y.2 hab.symm
  have hfJ : (completeBipartiteGraph (Fin 4) (Fin 4)).Free J :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hf
  have hC : Fintype.card C ≤ Fintype.card F^4 := by
    simp only [C,Fintype.card_prod,point_card hd]; nlinarith
  have hP : Fintype.card (F × F × F) ≤ Fintype.card F^3 := by
    simp only [Fintype.card_prod]; nlinarith
  have hb := Erdos714ProfileThinning.critical_scale_bound g ev J hJ hfJ
    (Fintype.card F) Fintype.card_pos le_rfl (split_card hd ℓ hℓ).le hC hP
  have he : J.edgeFinset.card=H.edgeFinset.card := (SimpleGraph.Iso.comap e H).card_edgeFinset_eq
  rwa [he] at hb
end Binary

/-- Uniform in every characteristic and every actual quartic extension. -/
theorem all_fourth_power (hd : Module.finrank F E=4)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  by_cases hc : ringChar F=2
  · letI : CharP F 2 := ringChar.eq_iff.mp hc
    exact binary_fourth_power hd H hH hf
  · exact Erdos714QuarticAdditive.fourth_power hd (Ring.two_ne_zero hc) H hH hf

/-- Exact host counts require no assumption on the characteristic. -/
theorem all_host_size (hd : Module.finrank F E=4) :
    Fintype.card ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)) =
      2*Fintype.card F^4 ∧
    (graph (F := F) (E := E)).edgeFinset.card=Fintype.card F^7 := by
  constructor
  · simp only [Fintype.card_sum,Fintype.card_prod,point_card hd]; ring
  · let f (c : Point (F := F) (E := E) × F) (p : Point (F := F) (E := E)) : F :=
      Algebra.norm F (c.1.val+p.val)-c.2
    have hg : graph (F := F) (E := E)=Erdos714Coding.graph f := by
      ext a b
      cases a with
      | inl c =>
        cases b with
        | inl d => rfl
        | inr d =>
          change Algebra.norm F (c.1.val+d.1.val)=c.2+d.2 ↔
            (d.1,d.2) ∈ Erdos714Coding.symbols f c
          rw [Erdos714Coding.mem_symbols]
          dsimp [f]
          rw [sub_eq_iff_eq_add,add_comm d.2 c.2]
      | inr d =>
        cases b with
        | inr e => rfl
        | inl c =>
          change Algebra.norm F (c.1.val+d.1.val)=c.2+d.2 ↔
            (d.1,d.2) ∈ Erdos714Coding.symbols f c
          rw [Erdos714Coding.mem_symbols]
          dsimp [f]
          rw [sub_eq_iff_eq_add,add_comm d.2 c.2]
    rw [hg,Erdos714Coding.edge_count,Fintype.card_prod,point_card hd]
    ring

theorem all_relative_bound (hd : Module.finrank F E=4)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card F*H.edgeFinset.card^4 ≤ 165888*(graph (F := F) (E := E)).edgeFinset.card^4 := by
  have h := Nat.mul_le_mul_left (Fintype.card F) (all_fourth_power hd H hH hf)
  rw [(all_host_size hd).2]
  convert h using 1; ring

theorem all_size_budget (hd : Module.finrank F E=4)
    (H : SimpleGraph ((Point (F := F) (E := E) × F) ⊕ (Point (F := F) (E := E) × F)))
    (hH : H ≤ graph (F := F) (E := E))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (he : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have hb := all_fourth_power hd H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms all_host_size
#print axioms all_relative_bound
#print axioms all_size_budget
#print axioms normPolynomial_eval
#print axioms normPolynomial_cubic
#print axioms norm_shift
#print axioms splitEquiv
#print axioms split_card
#print axioms binary_fourth_power
#print axioms all_fourth_power
end Erdos714QuarticAdditiveAll
