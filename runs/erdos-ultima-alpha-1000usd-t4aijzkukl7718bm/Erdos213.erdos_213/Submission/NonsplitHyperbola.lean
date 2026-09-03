import Submission.OffsetCircle
import Mathlib.NumberTheory.FLT.Four

/-! A restriction on antipodal extensions on x^2-D*y^2=1/2.
This does not classify all rational-distance configurations on that hyperbola,
and does not bound arbitrary planar configurations. -/
namespace Erdos213.NonsplitHyperbola
open OffsetCircle

def lorentz (D : ℚ) (p : ℚ × ℚ) : ℚ := p.1^2-D*p.2^2

lemma norm_product_identity (D : ℚ) (p q : ℚ × ℚ) :
    distSq D p q*distSq D p (-q)=D*(2*(p.1*p.2-q.1*q.2))^2+
      (lorentz D p-lorentz D q)^2 := by
  dsimp [distSq,normSq,lorentz]
  ring

lemma same_hyperbola_product (D k : ℚ) (p q : ℚ × ℚ)
    (hp : lorentz D p=k) (hq : lorentz D q=k) :
    distSq D p q*distSq D p (-q)=D*(2*(p.1*p.2-q.1*q.2))^2 := by
  rw [norm_product_identity,hp,hq,sub_self,zero_pow (by decide),add_zero]

lemma distance_pos (D : ℚ) (hD : 0<D) (p q : ℚ × ℚ) (hpq : p ≠ q) :
    0<distSq D p q := by
  dsimp [distSq,normSq]
  by_cases hx : p.1=q.1
  · have hy : p.2 ≠ q.2 := fun h => hpq (Prod.ext hx h)
    have hs : 0<(p.2-q.2)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
    rw [hx,sub_self,zero_pow (by decide),zero_add]
    exact mul_pos hD hs
  · have hs : 0<(p.1-q.1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    positivity

lemma two_opposite_edges_force_square (D k : ℚ) (hD : 0<D) (p q : ℚ × ℚ)
    (hp : lorentz D p=k) (hq : lorentz D q=k) (hne : p ≠ q) (hne' : p ≠ -q)
    (hm : IsSquare (distSq D p q)) (ha : IsSquare (distSq D p (-q))) : IsSquare D := by
  have he := same_hyperbola_product D k p q hp hq
  have hpos := mul_pos (distance_pos D hD p q hne) (distance_pos D hD p (-q) hne')
  have hz : 2*(p.1*p.2-q.1*q.2) ≠ 0 := by
    intro hz
    rw [he,hz] at hpos
    norm_num at hpos
  have hs := (hm.mul ha).div (IsSquare.sq (2*(p.1*p.2-q.1*q.2)))
  convert hs using 1
  rw [he,mul_div_cancel_right₀ _ (pow_ne_zero 2 hz)]

/-- The square-class conclusion is unchanged if both distances are required
only to lie in one common square class. This does not make D=1 impossible. -/
lemma common_class_opposite_edges_force_square (D k δ : ℚ) (hD : 0<D) (hδ : δ ≠ 0)
    (p q : ℚ × ℚ) (hp : lorentz D p=k) (hq : lorentz D q=k)
    (hne : p ≠ q) (hne' : p ≠ -q)
    (hm : IsSquare (distSq D p q/δ)) (ha : IsSquare (distSq D p (-q)/δ)) : IsSquare D := by
  have he := same_hyperbola_product D k p q hp hq
  have hpos := mul_pos (distance_pos D hD p q hne) (distance_pos D hD p (-q) hne')
  have hz : 2*(p.1*p.2-q.1*q.2) ≠ 0 := by
    intro hz
    rw [he,hz] at hpos
    norm_num at hpos
  have hs : IsSquare (distSq D p q*distSq D p (-q)) := by
    convert (hm.mul ha).mul (IsSquare.sq δ) using 1
    field_simp
  have hs' := hs.div (IsSquare.sq (2*(p.1*p.2-q.1*q.2)))
  convert hs' using 1
  rw [he,mul_div_cancel_right₀ _ (pow_ne_zero 2 hz)]

lemma rational_one_add_fourth_not_square {t : ℚ} (ht : t ≠ 0) (u : ℚ) :
    1+t^4 ≠ u^2 := by
  intro h
  have ht0 : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  have hu0 : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  have hn0 : (t.den : ℤ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  have hq0 : (u.den : ℤ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  apply not_fermat_42 (mul_ne_zero hn0 hq0)
    (mul_ne_zero (Rat.num_ne_zero.mpr ht) hq0)
    (c := u.num*(t.den : ℤ)^2*u.den)
  have he : ((t.den : ℚ)*u.den)^4+((t.num : ℚ)*u.den)^4=
      ((u.num : ℚ)*(t.den : ℚ)^2*u.den)^2 := by
    rw [← Rat.num_div_den t,← Rat.num_div_den u] at h
    field_simp at h
    linear_combination (u.den : ℚ)^2*h
  exact_mod_cast he

lemma rational_fourth_sum_not_square (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a^4+b^4 ≠ c^2 := by
  intro h
  apply rational_one_add_fourth_not_square (div_ne_zero ha hb) (c/b^2)
  field_simp
  linear_combination h

lemma half_hyperbola_norm_not_square (x y : ℚ) (hc : x^2-y^2=1/2) :
    ¬ IsSquare (x^2+y^2) := by
  rintro ⟨r,hr⟩
  have hn : x^2+y^2=r^2 := by simpa only [pow_two] using hr
  have hx : x ≠ 0 := by intro hz; rw [hz] at hc; nlinarith only [hc,sq_nonneg y]
  have hy : y ≠ 0 := by
    intro hz
    have hh : ¬ IsSquare (1/2 : ℚ) := by decide +kernel
    apply hh
    refine ⟨x,?_⟩
    rw [hz] at hc
    nlinarith only [hc]
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hn
    nlinarith only [hn,sq_pos_of_ne_zero hx,sq_nonneg y]
  have he : (2*x*y)^2=r^4-1/4 := by
    linear_combination (x^2+y^2+r^2)*hn-(x^2-y^2+1/2)*hc
  have hf : (2*x*y)^4+r^4=(r^4+1/4)^2 := by
    linear_combination ((2*x*y)^2+r^4-1/4)*he
  exact rational_fourth_sum_not_square (2*x*y) r (r^4+1/4)
    (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy) hr0 hf

lemma antipodal_distance_implies_norm_square (D : ℚ) (q : ℚ × ℚ)
    (h : IsSquare (distSq D q (-q))) : IsSquare (normSq D q) := by
  obtain ⟨r,hr⟩ := h
  refine ⟨r/2,?_⟩
  dsimp [distSq,normSq] at *
  linear_combination hr/4

/-- No three distinct rational points on this hyperbola form a rational-distance
triangle containing an antipodal pair. The twist D is arbitrary positive rational. -/
lemma no_antipodal_triple (D : ℚ) (hD : 0<D) (p q : ℚ × ℚ)
    (hp : lorentz D p=1/2) (hq : lorentz D q=1/2) (hne : p ≠ q) (hne' : p ≠ -q)
    (hm : IsSquare (distSq D p q)) (ha : IsSquare (distSq D p (-q)))
    (hanti : IsSquare (distSq D q (-q))) : False := by
  obtain ⟨d,hd⟩ := two_opposite_edges_force_square D (1/2) hD p q hp hq hne hne' hm ha
  have hs := antipodal_distance_implies_norm_square D q hanti
  have he : q.1^2-(d*q.2)^2=1/2 := by
    dsimp [lorentz] at hq
    rw [hd] at hq
    nlinarith only [hq]
  apply half_hyperbola_norm_not_square q.1 (d*q.2) he
  convert hs using 1
  dsimp [normSq]
  rw [hd]
  ring

/-- Positive control: an antipodal pair itself is possible at characteristic 7. -/
lemma antipodal_pair_control :
    lorentz 7 (3/2,1/2)=1/2 ∧ lorentz 7 (-3/2,-1/2)=1/2 ∧
      distSq 7 (3/2,1/2) (-3/2,-1/2)=4^2 := by decide +kernel

#print axioms common_class_opposite_edges_force_square
#print axioms norm_product_identity
#print axioms two_opposite_edges_force_square
#print axioms half_hyperbola_norm_not_square
#print axioms no_antipodal_triple
#print axioms antipodal_pair_control
end Erdos213.NonsplitHyperbola
