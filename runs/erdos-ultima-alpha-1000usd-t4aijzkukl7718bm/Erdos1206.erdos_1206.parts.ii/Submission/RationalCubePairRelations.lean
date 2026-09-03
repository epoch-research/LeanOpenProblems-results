import Submission.FermatConicDegeneracy
import Submission.QuadraticResidualBridge

/-!
Normalization and sign conditions for pair relations in nontrivial rational
quadratic cube-sum identities. No density statement is asserted.
-/
namespace Erdos1206.RationalCubePairRelations
open Polynomial FermatCubicConics FermatConicDegeneracy QuadraticResidualBridge

lemma cube_injective : Function.Injective (fun p : ℚ[X] => p^3) := by
  intro p q h
  apply Polynomial.funext
  intro t
  apply (by decide : Odd (3 : ℕ)).pow_injective
  simpa only [eval_pow] using congrArg (fun p : ℚ[X] => p.eval t) h

lemma sum_ne_zero {A B : ℚ[X]} (h : A^3+B^3 ≠ 0) : A+B ≠ 0 := by
  intro hz
  apply h
  calc
    _ = (A+B)*(A^2-A*B+B^2) := by ring
    _ = 0 := by rw [hz,zero_mul]

lemma same_sum_repeated {A B C D : ℚ[X]}
    (hc : A^3+B^3=C^3+D^3) (hn : A^3+B^3 ≠ 0) (hs : A+B=C+D) :
    A=C ∨ A=D := by
  have hD : D=A+B-C := by linear_combination -hs
  have hp : 3*((A+B)*((A-C)*(A-D)))=0 := by
    rw [hD] at hc ⊢
    linear_combination hc
  have hp' : (A+B)*((A-C)*(A-D))=0 :=
    (mul_eq_zero.mp hp).resolve_left (by norm_num)
  have hp'' := (mul_eq_zero.mp hp').resolve_left (sum_ne_zero hn)
  simpa only [sub_eq_zero] using mul_eq_zero.mp hp''

lemma other_differences {A B C D : ℚ[X]}
    (hc : A^3+B^3=C^3+D^3) (hAC : A ≠ C) (hAD : A ≠ D) :
    B ≠ D ∧ B ≠ C := by
  constructor
  · intro he
    have hh : A^3=C^3 := by rw [he] at hc; linear_combination hc
    exact hAC (cube_injective hh)
  · intro he
    have hh : A^3=D^3 := by rw [he] at hc; linear_combination hc
    exact hAD (cube_injective hh)

lemma dependent_ratio {p q : ℚ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hd : PolynomialPairDependent p q) : ∃ r : ℚ, r ≠ 0 ∧ p=Polynomial.C r*q := by
  obtain ⟨a,b,hab,he⟩ := hd
  have ha : a ≠ 0 := by
    intro hz
    have hb := hab.resolve_left (by simpa [hz])
    rw [hz,map_zero,zero_mul,zero_add] at he
    exact mul_ne_zero (C_ne_zero.mpr hb) hq he
  have hb : b ≠ 0 := by
    intro hz
    rw [hz,map_zero,zero_mul,add_zero] at he
    exact mul_ne_zero (C_ne_zero.mpr ha) hp he
  refine ⟨-b/a,div_ne_zero (neg_ne_zero.mpr hb) ha,?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr ha)
  have hab' : a*(-b/a) = -b := by field_simp
  rw [← mul_assoc,← map_mul,hab',map_neg]
  linear_combination he

private lemma plus_norm_pos {a b : ℚ} (h : a ≠ b) : 0 < a^2+a*b+b^2 := by
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h),sq_nonneg (a+b)]

private lemma minus_norm_pos {a b : ℚ} (h : a+b ≠ 0) : 0 < a^2-a*b+b^2 := by
  nlinarith [sq_pos_of_ne_zero h,sq_nonneg (a-b)]

lemma difference_ratio_negative {A B C D : ℚ[X]} {r : ℚ}
    (hc : A^3+B^3=C^3+D^3) (hBD : B ≠ D) (hr : r ≠ 0)
    (hd : A-C=Polynomial.C r*(B-D)) : r < 0 := by
  have hex : ∃ t : ℚ, B.eval t ≠ D.eval t := by
    by_contra! hh
    exact hBD (Polynomial.funext hh)
  obtain ⟨t,ht⟩ := hex
  have hd' := congrArg (fun p : ℚ[X] => p.eval t) hd
  have hc' := congrArg (fun p : ℚ[X] => p.eval t) hc
  simp only [eval_sub,eval_mul,eval_C] at hd'
  simp only [eval_add,eval_pow] at hc'
  have hAC : A.eval t ≠ C.eval t := by
    intro hz
    rw [hz,sub_self] at hd'
    exact mul_ne_zero hr (sub_ne_zero.mpr ht) hd'.symm
  have h₁ := plus_norm_pos hAC
  have h₂ := plus_norm_pos ht
  have hp : (B.eval t-D.eval t)*
      (r*((A.eval t)^2+A.eval t*C.eval t+(C.eval t)^2)+
        ((B.eval t)^2+B.eval t*D.eval t+(D.eval t)^2))=0 := by
    linear_combination hc' - ((A.eval t)^2+A.eval t*C.eval t+(C.eval t)^2)*hd'
  have hz := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr ht)
  by_contra! hn
  have hnonneg := mul_nonneg hn h₁.le
  linarith

lemma difference_ratio_ne_neg_one {A B C D : ℚ[X]} {r : ℚ}
    (hc : A^3+B^3=C^3+D^3) (hn : A^3+B^3 ≠ 0)
    (hAC : A ≠ C) (hAD : A ≠ D) (hd : A-C=Polynomial.C r*(B-D)) : r ≠ -1 := by
  intro hr
  rw [hr,map_neg,map_one,neg_mul,one_mul] at hd
  have hs : A+B=C+D := by linear_combination hd
  exact (same_sum_repeated hc hn hs).elim hAC hAD

lemma sum_ratio_positive {A B C D : ℚ[X]} {r : ℚ}
    (hc : A^3+B^3=C^3+D^3) (hn : A^3+B^3 ≠ 0) (hr : r ≠ 0)
    (hs : A+B=Polynomial.C r*(C+D)) : 0 < r := by
  have hCD : C+D ≠ 0 := sum_ne_zero (by rw [← hc]; exact hn)
  have hex : ∃ t : ℚ, (C+D).eval t ≠ 0 := by
    by_contra! hh
    apply hCD
    apply Polynomial.funext
    simpa using hh
  obtain ⟨t,ht⟩ := hex
  simp only [eval_add] at ht
  have hs' := congrArg (fun p : ℚ[X] => p.eval t) hs
  have hc' := congrArg (fun p : ℚ[X] => p.eval t) hc
  simp only [eval_add,eval_mul,eval_C] at hs'
  simp only [eval_add,eval_pow] at hc'
  have hAB : A.eval t+B.eval t ≠ 0 := by rw [hs']; exact mul_ne_zero hr ht
  have h₁ := minus_norm_pos hAB
  have h₂ := minus_norm_pos ht
  have hp : (C.eval t+D.eval t)*
      (r*((A.eval t)^2-A.eval t*B.eval t+(B.eval t)^2)-
        ((C.eval t)^2-C.eval t*D.eval t+(D.eval t)^2))=0 := by
    linear_combination hc' - ((A.eval t)^2-A.eval t*B.eval t+(B.eval t)^2)*hs'
  have hz := (mul_eq_zero.mp hp).resolve_left ht
  by_contra! hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hn h₁.le
  linarith

lemma sum_ratio_ne_one {A B C D : ℚ[X]} {r : ℚ}
    (hc : A^3+B^3=C^3+D^3) (hn : A^3+B^3 ≠ 0)
    (hAC : A ≠ C) (hAD : A ≠ D) (hs : A+B=Polynomial.C r*(C+D)) : r ≠ 1 := by
  intro hr
  rw [hr,map_one,one_mul] at hs
  exact (same_sum_repeated hc hn hs).elim hAC hAD


/-- The three-dimensional linearization of the coefficients of a polynomial.
Only its coefficients of degrees zero, one, and two are used. -/
noncomputable def linearize (p : ℚ[X]) (x : Vec) : ℚ :=
  p.coeff 2*x 0+p.coeff 1*x 1+p.coeff 0*x 2

lemma linearize_quad (a x : Vec) : linearize (quad a) x=linear a x := by
  norm_num [linearize,quad,linear]

lemma linearize_add (p q : ℚ[X]) (x : Vec) :
    linearize (p+q) x=linearize p x+linearize q x := by
  simp only [linearize,coeff_add]
  ring

lemma linearize_sub (p q : ℚ[X]) (x : Vec) :
    linearize (p-q) x=linearize p x-linearize q x := by
  simp only [linearize,coeff_sub]
  ring

lemma linearize_Cmul (r : ℚ) (p : ℚ[X]) (x : Vec) :
    linearize (C r*p) x=r*linearize p x := by
  simp only [linearize,coeff_C_mul]
  ring

lemma difference_relation_linear {a b c d : Vec} {r : ℚ}
    (he : quad a-quad c=C r*(quad b-quad d)) :
    ∀ x, linear a x-linear c x=r*(linear b x-linear d x) := by
  intro x
  have hh := congrArg (fun p => linearize p x) he
  simpa only [linearize_sub,linearize_Cmul,linearize_quad] using hh

lemma sum_relation_linear {a b c d : Vec} {r : ℚ}
    (he : quad a+quad b=C r*(quad c+quad d)) :
    ∀ x, linear a x+linear b x=r*(linear c x+linear d x) := by
  intro x
  have hh := congrArg (fun p => linearize p x) he
  simpa only [linearize_add,linearize_Cmul,linearize_quad] using hh

lemma quad_neg (a : Vec) : quad (-a) = -quad a := by
  simp only [quad,Pi.neg_apply,map_neg]
  ring

private lemma dependent_neg_right {p q : ℚ[X]}
    (h : PolynomialPairDependent p (-q)) : PolynomialPairDependent p q := by
  obtain ⟨r,s,hrs,he⟩ := h
  refine ⟨r,-s,hrs.imp_right (neg_ne_zero.mpr),?_⟩
  rw [map_neg]
  linear_combination he

/-- A normalized proportional-pair-sum relation. -/
def SumRelation (a b c d : Vec) : Prop :=
  ∃ k : ℚ, 0 < k ∧ k ≠ 1 ∧ ∀ x, linear a x+linear b x=k*(linear c x+linear d x)

/-- A normalized, nontrivial rational direction relation. -/
def DifferenceRelation (a b c d : Vec) : Prop :=
  ∃ r : ℚ, r < 0 ∧ r ≠ -1 ∧ ∀ x, linear a x-linear c x=r*(linear b x-linear d x)

/-- No sign or normalization assumptions are required in the input: they
follow from the nonzero common sum and distinct unordered polynomial pairs. -/
theorem normalized_pair_relation {a b c d : Vec}
    (hc : quad a^3+quad b^3=quad c^3+quad d^3) (hn : quad a^3+quad b^3 ≠ 0)
    (hac : quad a ≠ quad c) (had : quad a ≠ quad d) :
    SumRelation a b c d ∨ DifferenceRelation a b c d ∨ DifferenceRelation a b d c := by
  have he : quad a^3+quad b^3+quad (-c)^3+quad (-d)^3=0 := by
    rw [quad_neg,quad_neg]
    linear_combination hc
  have hp := quadratic_pair_relation_all he
  simp only [quad_neg,← sub_eq_add_neg] at hp
  have hn' : quad c^3+quad d^3 ≠ 0 := by rw [← hc]; exact hn
  obtain ⟨hbd,hbc⟩ := other_differences hc hac had
  rcases hp with hs | hd | hd
  · obtain ⟨r,hr,hs⟩ := dependent_ratio (sum_ne_zero hn) (sum_ne_zero hn')
      (dependent_neg_right (by convert hs using 1 <;> ring))
    exact Or.inl ⟨r,sum_ratio_positive hc hn hr hs,
      sum_ratio_ne_one hc hn hac had hs,sum_relation_linear hs⟩
  · obtain ⟨r,hr,hd⟩ := dependent_ratio (sub_ne_zero.mpr hac) (sub_ne_zero.mpr hbd) hd
    exact Or.inr (Or.inl ⟨r,difference_ratio_negative hc hbd hr hd,
      difference_ratio_ne_neg_one hc hn hac had hd,difference_relation_linear hd⟩)
  · obtain ⟨r,hr,hd⟩ := dependent_ratio (sub_ne_zero.mpr had) (sub_ne_zero.mpr hbc) hd
    have hc' : quad a^3+quad b^3=quad d^3+quad c^3 := by rw [add_comm (quad d^3)]; exact hc
    exact Or.inr (Or.inr ⟨r,difference_ratio_negative hc' hbc hr hd,
      difference_ratio_ne_neg_one hc' hn had hac hd,difference_relation_linear hd⟩)


lemma SumRelation.swap_left {a b c d : Vec} (h : SumRelation a b c d) : SumRelation b a c d := by
  obtain ⟨r,hr,hr₁,he⟩ := h
  exact ⟨r,hr,hr₁,fun x => by rw [add_comm]; exact he x⟩

lemma SumRelation.swap_right {a b c d : Vec} (h : SumRelation a b c d) : SumRelation a b d c := by
  obtain ⟨r,hr,hr₁,he⟩ := h
  exact ⟨r,hr,hr₁,fun x => by rw [add_comm (linear d x)]; exact he x⟩

lemma SumRelation.symm {a b c d : Vec} (h : SumRelation a b c d) : SumRelation c d a b := by
  obtain ⟨r,hr,hr₁,he⟩ := h
  refine ⟨r⁻¹,inv_pos.mpr hr,?_,fun x => ?_⟩
  · intro hh
    have hh' := congrArg (fun r : ℚ => r⁻¹) hh
    simpa using hr₁ (by simpa using hh')
  · rw [he,inv_mul_cancel_left₀ (ne_of_gt hr)]

lemma DifferenceRelation.symm {a b c d : Vec} (h : DifferenceRelation a b c d) :
    DifferenceRelation c d a b := by
  obtain ⟨r,hr,hr₁,he⟩ := h
  exact ⟨r,hr,hr₁,fun x => by linear_combination -(he x)⟩

lemma DifferenceRelation.swap_both {a b c d : Vec} (h : DifferenceRelation a b c d) :
    DifferenceRelation b a d c := by
  obtain ⟨r,hr,hr₁,he⟩ := h
  have hr0 : r ≠ 0 := ne_of_lt hr
  refine ⟨r⁻¹,inv_lt_zero.mpr hr,?_,fun x => ?_⟩
  · intro hh
    have hh' := congrArg (fun r : ℚ => r⁻¹) hh
    exact hr₁ (by simpa using hh')
  · rw [he,inv_mul_cancel_left₀ hr0]

lemma sum_relation_polynomial {a b c d : Vec} {r : ℚ}
    (he : ∀ x, linear a x+linear b x=r*(linear c x+linear d x)) :
    quad a+quad b=C r*(quad c+quad d) := by
  apply Polynomial.funext
  intro t
  simpa only [eval_add,eval_mul,eval_C,quad_eval] using he ![t^2,t,1]

#print axioms normalized_pair_relation
end Erdos1206.RationalCubePairRelations
