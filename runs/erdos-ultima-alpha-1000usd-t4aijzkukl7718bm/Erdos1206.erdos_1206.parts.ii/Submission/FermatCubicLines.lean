import FormalConjecturesUtil

/-!
Classification of rational linear polynomial families on the Fermat cubic
surface. Auxiliary to a conic classification; no density conclusion is claimed.
-/

namespace Erdos1206.FermatCubicLines
open Polynomial

/-- The four coordinate polynomials span at most one dimension. -/
def CommonFactor (a b c d : ℚ[X]) : Prop :=
  ∃ q : ℚ[X], ∃ u v w z : ℚ,
    a=C u*q ∧ b=C v*q ∧ c=C w*q ∧ d=C z*q

/-- The three rational lines, in signed coordinates with sum of cubes zero. -/
def OppositePairs (a b c d : ℚ[X]) : Prop :=
  (a+b=0 ∧ c+d=0) ∨ (a+c=0 ∧ b+d=0) ∨ (a+d=0 ∧ b+c=0)

private lemma cube_injective {a b : ℚ[X]} (h : a^3=b^3) : a=b := by
  apply Polynomial.funext
  intro t
  have ht := congrArg (fun p : ℚ[X] => p.eval t) h
  simp only [eval_pow] at ht
  exact (Odd.pow_inj (by decide : Odd 3)).mp ht

private lemma cubic_zero_pair {a b : ℚ[X]} (h : a^3+b^3=0) : a+b=0 := by
  have he : a^3=(-b)^3 := by linear_combination h
  have hh := cube_injective he
  rw [hh]
  simp

private lemma linear_at (p : ℚ[X]) (hp : p.natDegree ≤ 1) (t : ℚ) :
    p=C (p.coeff 1)*(X-C t)+C (p.eval t) := by
  have he : p.eval t=p.coeff 1*t+p.coeff 0 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
    simp
  rw [he]
  calc
    p = C (p.coeff 1)*X+C (p.coeff 0) := eq_X_add_C_of_natDegree_le_one hp
    _ = _ := by simp only [map_add,map_mul]; ring

private lemma linear_derivative (p : ℚ[X]) (hp : p.natDegree ≤ 1) :
    derivative p=C (p.coeff 1) := by
  calc
    derivative p = derivative (C (p.coeff 1)*X+C (p.coeff 0)) :=
      congrArg derivative (eq_X_add_C_of_natDegree_le_one hp)
    _ = _ := by simp

private lemma common_of_zero_values {a b c d : ℚ[X]} {t : ℚ}
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (ha0 : a.eval t=0) (hb0 : b.eval t=0) (hc0 : c.eval t=0) (hd0 : d.eval t=0) :
    CommonFactor a b c d := by
  refine ⟨X-C t,a.coeff 1,b.coeff 1,c.coeff 1,d.coeff 1,?_,?_,?_,?_⟩
  · simpa only [ha0,map_zero,add_zero] using linear_at a ha t
  · simpa only [hb0,map_zero,add_zero] using linear_at b hb t
  · simpa only [hc0,map_zero,add_zero] using linear_at c hc t
  · simpa only [hd0,map_zero,add_zero] using linear_at d hd t

private lemma two_zero_values {a b c d : ℚ[X]} {t : ℚ}
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : a^3+b^3+c^3+d^3=0) (ha0 : a.eval t=0) (hb0 : b.eval t=0) :
    (a+b=0 ∧ c+d=0) ∨ CommonFactor a b c d := by
  have hv := congrArg (fun p : ℚ[X] => p.eval t) he
  simp only [eval_add,eval_pow,eval_zero,ha0,hb0,zero_pow (by decide : 3 ≠ 0),
    zero_add] at hv
  have hdc : d.eval t= -c.eval t := by
    apply (Odd.pow_inj (by decide : Odd 3)).mp
    nlinarith only [hv]
  by_cases hc0 : c.eval t=0
  · right
    apply common_of_zero_values ha hb hc hd ha0 hb0 hc0
    simpa [hc0] using hdc
  · left
    have hder := congrArg (fun p : ℚ[X] => (derivative p).eval t) he
    simp only [derivative_add,derivative_pow,derivative_zero,eval_add,eval_mul,
      eval_pow,eval_zero,linear_derivative a ha,linear_derivative b hb,
      linear_derivative c hc,linear_derivative d hd,eval_C,
      ha0,hb0,hdc] at hder
    norm_num only at hder
    have hz : 3*(c.eval t)^2*(c.coeff 1+d.coeff 1)=0 := by
      nlinarith only [hder]
    have hs : c.coeff 1+d.coeff 1=0 :=
      (mul_eq_zero.mp hz).resolve_left
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc0))
    have hcd : c+d=0 := by
      calc
        c+d = C (c.coeff 1)*(X-C t)+C (c.eval t)+
            (C (d.coeff 1)*(X-C t)+C (d.eval t)) :=
          congrArg₂ (·+·) (linear_at c hc t) (linear_at d hd t)
        _ = C (c.coeff 1+d.coeff 1)*(X-C t)+C (c.eval t+d.eval t) := by
          simp only [map_add]; ring
        _ = 0 := by simp [hs,hdc]
    refine ⟨cubic_zero_pair ?_,hcd⟩
    have hd' : d= -c := by linear_combination hcd
    rw [hd'] at he
    linear_combination he

private lemma first_degree_one {a b c d : ℚ[X]}
    (ha : a.natDegree=1) (hb : b.natDegree ≤ 1)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : a^3+b^3+c^3+d^3=0) : OppositePairs a b c d ∨ CommonFactor a b c d := by
  have han : a ≠ 0 := by intro h; simp [h] at ha
  obtain ⟨t,ht⟩ := exists_root_of_degree_eq_one
    (show a.degree=1 by rw [degree_eq_natDegree han,ha]; rfl)
  change a.eval t=0 at ht
  have hv := congrArg (fun p : ℚ[X] => p.eval t) he
  simp only [eval_add,eval_pow,eval_zero,ht,zero_pow (by decide : 3 ≠ 0),zero_add] at hv
  have hor : b.eval t=0 ∨ c.eval t=0 ∨ d.eval t=0 := by
    by_contra! hn
    apply (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
      (b.eval t) (c.eval t) (-d.eval t) hn.1 hn.2.1 (neg_ne_zero.mpr hn.2.2)
    nlinarith only [hv]
  rcases hor with hb0 | hc0 | hd0
  · rcases two_zero_values ha.le hb hc hd he ht hb0 with hp | hp
    · exact Or.inl (Or.inl hp)
    · exact Or.inr hp
  · have he' : a^3+c^3+b^3+d^3=0 := by linear_combination he
    rcases two_zero_values ha.le hc hb hd he' ht hc0 with hp | hp
    · exact Or.inl (Or.inr (Or.inl hp))
    · obtain ⟨q,u,w,v,z,hu,hw,hv,hz⟩ := hp
      exact Or.inr ⟨q,u,v,w,z,hu,hv,hw,hz⟩
  · have he' : a^3+d^3+b^3+c^3=0 := by linear_combination he
    rcases two_zero_values ha.le hd hb hc he' ht hd0 with hp | hp
    · exact Or.inl (Or.inr (Or.inr hp))
    · obtain ⟨q,u,z,v,w,hu,hz,hv,hw⟩ := hp
      exact Or.inr ⟨q,u,v,w,z,hu,hv,hw,hz⟩

/-- Every rational linear family on the signed Fermat cubic is either on
one of its three rational lines or is projectively constant. -/
theorem rational_linear_family {a b c d : ℚ[X]}
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : a^3+b^3+c^3+d^3=0) : OppositePairs a b c d ∨ CommonFactor a b c d := by
  by_cases ha1 : a.natDegree=1
  · exact first_degree_one ha1 hb hc hd he
  by_cases hb1 : b.natDegree=1
  · have he' : b^3+a^3+c^3+d^3=0 := by linear_combination he
    rcases first_degree_one hb1 ha hc hd he' with hp | hp
    · left
      rcases hp with ⟨hba,hcd⟩ | ⟨hbc,had⟩ | ⟨hbd,hac⟩
      · exact Or.inl ⟨by simpa [add_comm] using hba,hcd⟩
      · exact Or.inr (Or.inr ⟨had,hbc⟩)
      · exact Or.inr (Or.inl ⟨hac,hbd⟩)
    · obtain ⟨q,v,u,w,z,hv,hu,hw,hz⟩ := hp
      exact Or.inr ⟨q,u,v,w,z,hu,hv,hw,hz⟩
  by_cases hc1 : c.natDegree=1
  · have he' : c^3+b^3+a^3+d^3=0 := by linear_combination he
    rcases first_degree_one hc1 hb ha hd he' with hp | hp
    · left
      rcases hp with ⟨hcb,had⟩ | ⟨hca,hbd⟩ | ⟨hcd,hba⟩
      · exact Or.inr (Or.inr ⟨had,by simpa [add_comm] using hcb⟩)
      · exact Or.inr (Or.inl ⟨by simpa [add_comm] using hca,hbd⟩)
      · exact Or.inl ⟨by simpa [add_comm] using hba,hcd⟩
    · obtain ⟨q,w,v,u,z,hw,hv,hu,hz⟩ := hp
      exact Or.inr ⟨q,u,v,w,z,hu,hv,hw,hz⟩
  by_cases hd1 : d.natDegree=1
  · have he' : d^3+b^3+c^3+a^3=0 := by linear_combination he
    rcases first_degree_one hd1 hb hc ha he' with hp | hp
    · left
      rcases hp with ⟨hdb,hca⟩ | ⟨hdc,hba⟩ | ⟨hda,hbc⟩
      · exact Or.inr (Or.inl ⟨by simpa [add_comm] using hca,by simpa [add_comm] using hdb⟩)
      · exact Or.inl ⟨by simpa [add_comm] using hba,by simpa [add_comm] using hdc⟩
      · exact Or.inr (Or.inr ⟨by simpa [add_comm] using hda,hbc⟩)
    · obtain ⟨q,z,v,w,u,hz,hv,hw,hu⟩ := hp
      exact Or.inr ⟨q,u,v,w,z,hu,hv,hw,hz⟩
  right
  refine ⟨1,a.coeff 0,b.coeff 0,c.coeff 0,d.coeff 0,?_,?_,?_,?_⟩
  all_goals rw [mul_one]
  · exact eq_C_of_natDegree_eq_zero (by omega)
  · exact eq_C_of_natDegree_eq_zero (by omega)
  · exact eq_C_of_natDegree_eq_zero (by omega)
  · exact eq_C_of_natDegree_eq_zero (by omega)

#print axioms rational_linear_family
end Erdos1206.FermatCubicLines
