import Submission.ConicHeightProduct

/-!
The exact gcd identity for the three rational conic parameters of a primitive
cubic collision. This arithmetic identity does not settle the density conjecture.
-/
namespace Erdos1206.ConicHeightProduct

lemma integral_product_identity {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    (b-a)*(c-a)*(b+c) = defect a b c d *
      (d^2+defect a b c d*(d+defect a b c d/3)) := by
  obtain ⟨j,hj⟩ := three_dvd_defect hab hbc hcd he
  have hh := product_identity hab hbc hcd he
  rw [hj] at hh ⊢
  rw [Nat.mul_div_cancel_left j (by decide : 0<3)]
  nlinarith only [hh]

private lemma no_two_dvd {a b c d p : ℕ} (hp : p.Prime)
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3)
    (hprim : Nat.gcd (Nat.gcd a b) (Nat.gcd c d)=1)
    (hpk : p ∣ defect a b c d) (hpd : p ∣ d) :
    ¬ (p ∣ b-a ∧ p ∣ c-a) ∧ ¬ (p ∣ b-a ∧ p ∣ b+c) ∧
      ¬ (p ∣ c-a ∧ p ∣ b+c) := by
  have hs := root_sum_lt hab hbc hcd he
  have hD : p ∣ d+defect a b c d := Nat.dvd_add hpd hpk
  have hX : d+defect a b c d=(b-a)+c := by dsimp [defect]; omega
  have hY : d+defect a b c d=(c-a)+b := by dsimp [defect]; omega
  have hZ : a+(d+defect a b c d)=b+c := by dsimp [defect]; omega
  have hx (h : p ∣ b-a) : p ∣ c :=
    (Nat.dvd_add_iff_right h).mpr (hX ▸ hD)
  have hy (h : p ∣ c-a) : p ∣ b :=
    (Nat.dvd_add_iff_right h).mpr (hY ▸ hD)
  have hz (h : p ∣ b+c) : p ∣ a :=
    (Nat.dvd_add_iff_left hD).mpr (hZ ▸ h)
  have hzero (ha : p ∣ a) (hb : p ∣ b) (hc : p ∣ c) : False := by
    have hd := Nat.dvd_gcd (Nat.dvd_gcd ha hb) (Nat.dvd_gcd hc hpd)
    rw [hprim] at hd
    exact hp.not_dvd_one hd
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hpx,hpy⟩
    have hb := hy hpy
    have hc := hx hpx
    exact hzero (hz (Nat.dvd_add hb hc)) hb hc
  · rintro ⟨hpx,hpz⟩
    have ha := hz hpz
    have hc := hx hpx
    have hb : p ∣ b := (Nat.dvd_add_iff_left hc).mpr hpz
    exact hzero ha hb hc
  · rintro ⟨hpy,hpz⟩
    have ha := hz hpz
    have hb := hy hpy
    have hc : p ∣ c := (Nat.dvd_add_iff_right hb).mpr hpz
    exact hzero ha hb hc

private lemma factorization_gcd_product {k x y z : ℕ}
    (hk : 0<k) (hx : 0<x) (hy : 0<y) (hz : 0<z) (p : ℕ) :
    (Nat.gcd k x * Nat.gcd k y * Nat.gcd k z).factorization p =
      min (k.factorization p) (x.factorization p) +
      min (k.factorization p) (y.factorization p) +
      min (k.factorization p) (z.factorization p) := by
  have hxg := Nat.gcd_pos_of_pos_left x hk
  have hyg := Nat.gcd_pos_of_pos_left y hk
  have hzg := Nat.gcd_pos_of_pos_left z hk
  rw [Nat.factorization_mul (Nat.mul_pos hxg hyg).ne' hzg.ne',
    Nat.factorization_mul hxg.ne' hyg.ne',
    Nat.factorization_gcd hk.ne' hx.ne',Nat.factorization_gcd hk.ne' hy.ne',
    Nat.factorization_gcd hk.ne' hz.ne']
  rfl

/-- For primitive roots the product of the three conic gcds is exactly the
positive difference between the inner and outer sums of roots. -/
theorem primitive_denominatorProduct {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3)
    (hprim : Nat.gcd (Nat.gcd a b) (Nat.gcd c d)=1) :
    denominatorProduct a b c d = defect a b c d := by
  let k := defect a b c d
  let Q := d^2+k*(d+k/3)
  have hk : 0<k := defect_pos hab hbc hcd he
  have hx : 0<b-a := by omega
  have hy : 0<c-a := by omega
  have hz : 0<b+c := by omega
  have hd : 0<d := by omega
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hP : (b-a)*(c-a)*(b+c)=k*Q := integral_product_identity hab hbc hcd he
  have hG : 0<denominatorProduct a b c d := denominatorProduct_pos hab hbc hcd
  obtain ⟨hg₀,hg₁,hg₂⟩ := gcd_defect hab hbc hcd he
  apply Nat.eq_of_factorization_eq hG.ne' hk.ne'
  intro p
  by_cases hp : p.Prime
  swap
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hfG : (denominatorProduct a b c d).factorization p =
      min (k.factorization p) ((b+c).factorization p) +
      min (k.factorization p) ((b-a).factorization p) +
      min (k.factorization p) ((c-a).factorization p) := by
    rw [denominatorProduct,←hg₀,←hg₁,←hg₂]
    exact factorization_gcd_product hk hz hx hy p
  have hfP : (b-a).factorization p+(c-a).factorization p+(b+c).factorization p =
      k.factorization p+Q.factorization p := by
    have hh := congrArg (fun n : ℕ => n.factorization p) hP
    simpa only [Nat.factorization_mul (Nat.mul_pos hx hy).ne' hz.ne',
      Nat.factorization_mul hx.ne' hy.ne',Nat.factorization_mul hk.ne' hQ.ne',
      Finsupp.add_apply] using hh
  by_cases hpk : p ∣ k
  swap
  · have hf := Nat.factorization_eq_zero_of_not_dvd hpk
    simp only [hfG,hf,Nat.zero_min,zero_add]
  by_cases hpd : p ∣ d
  · obtain ⟨hxy,hxz,hyz⟩ := no_two_dvd hp hab hbc hcd he hprim hpk hpd
    by_cases hpx : p ∣ b-a
    · have hfy := Nat.factorization_eq_zero_of_not_dvd (fun h => hxy ⟨hpx,h⟩)
      have hfz := Nat.factorization_eq_zero_of_not_dvd (fun h => hxz ⟨hpx,h⟩)
      rw [hfG,hfy,hfz]
      simp only [Nat.min_zero,zero_add,add_zero]
      exact Nat.min_eq_left (by omega)
    · have hfx := Nat.factorization_eq_zero_of_not_dvd hpx
      by_cases hpy : p ∣ c-a
      · have hfz := Nat.factorization_eq_zero_of_not_dvd (fun h => hyz ⟨hpy,h⟩)
        rw [hfG,hfx,hfz]
        simp only [Nat.min_zero,zero_add,add_zero]
        exact Nat.min_eq_left (by omega)
      · have hfy := Nat.factorization_eq_zero_of_not_dvd hpy
        rw [hfG,hfx,hfy]
        simp only [Nat.min_zero,add_zero]
        exact Nat.min_eq_left (by omega)
  · have hpQ : ¬p ∣ Q := by
      intro hh
      have hterm : p ∣ k*(d+k/3) := dvd_mul_of_dvd_left hpk _
      have hdsq : p ∣ d^2 := (Nat.dvd_add_iff_left hterm).mpr hh
      exact hpd (hp.dvd_of_dvd_pow hdsq)
    have hfQ := Nat.factorization_eq_zero_of_not_dvd hpQ
    rw [hfQ,add_zero] at hfP
    rw [hfG,Nat.min_eq_right (by omega : (b+c).factorization p ≤ k.factorization p),
      Nat.min_eq_right (by omega : (b-a).factorization p ≤ k.factorization p),
      Nat.min_eq_right (by omega : (c-a).factorization p ≤ k.factorization p)]
    omega

#print axioms integral_product_identity
#print axioms primitive_denominatorProduct


/-- The common gcd of the four roots. -/
def rootGcd (a b c d : ℕ) : ℕ := Nat.gcd (Nat.gcd a b) (Nat.gcd c d)

lemma defect_mul (t a b c d : ℕ) :
    defect (t*a) (t*b) (t*c) (t*d) = t*defect a b c d := by
  simp only [defect,←Nat.mul_add,←Nat.mul_sub_left_distrib]

lemma denominatorProduct_mul (t a b c d : ℕ) :
    denominatorProduct (t*a) (t*b) (t*c) (t*d) = t^3*denominatorProduct a b c d := by
  simp only [denominatorProduct,←Nat.mul_add,←Nat.mul_sub_left_distrib,Nat.gcd_mul_left]
  ring

/-- The exact identity without a primitivity hypothesis. -/
theorem denominatorProduct_eq {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    denominatorProduct a b c d = defect a b c d * (rootGcd a b c d)^2 := by
  let g := rootGcd a b c d
  have hd : 0<d := by omega
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right c hd)
  have hga : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)
  have hgb : g ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)
  have hgc : g ∣ c := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left c d)
  have hgd : g ∣ d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right c d)
  have ha' : g*(a/g)=a := Nat.mul_div_cancel' hga
  have hb' : g*(b/g)=b := Nat.mul_div_cancel' hgb
  have hc' : g*(c/g)=c := Nat.mul_div_cancel' hgc
  have hd' : g*(d/g)=d := Nat.mul_div_cancel' hgd
  have hab' : a/g < b/g := Nat.div_lt_div_of_lt_of_dvd hgb hab
  have hbc' : b/g < c/g := Nat.div_lt_div_of_lt_of_dvd hgc hbc
  have hcd' : c/g < d/g := Nat.div_lt_div_of_lt_of_dvd hgd hcd
  have hprim : Nat.gcd (Nat.gcd (a/g) (b/g)) (Nat.gcd (c/g) (d/g))=1 := by
    rw [Nat.gcd_div hga hgb,Nat.gcd_div hgc hgd,
      Nat.gcd_div (show g ∣ Nat.gcd a b from Nat.gcd_dvd_left _ _)
        (show g ∣ Nat.gcd c d from Nat.gcd_dvd_right _ _)]
    exact Nat.div_self hg
  have he' : (a/g)^3+(d/g)^3=(b/g)^3+(c/g)^3 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hg 3)
    simpa only [Nat.mul_add,←mul_pow,ha',hb',hc',hd'] using he
  have hnorm := primitive_denominatorProduct hab' hbc' hcd' he' hprim
  have hs := denominatorProduct_mul g (a/g) (b/g) (c/g) (d/g)
  rw [ha',hb',hc',hd',hnorm] at hs
  have hk := defect_mul g (a/g) (b/g) (c/g) (d/g)
  rw [ha',hb',hc',hd'] at hk
  change denominatorProduct a b c d = defect a b c d * g^2
  rw [hs,hk]
  ring

/-- An exact height relation: after normalization, the product of the three
conic heights is one positive-definite quadratic form in the largest root
and the root-sum defect. -/
theorem heights_product_exact {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    3*(heights a b c d 0 * heights a b c d 1 * heights a b c d 2) *
      (rootGcd a b c d)^2 =
        3*d^2+3*d*defect a b c d+(defect a b c d)^2 := by
  have hk := defect_pos hab hbc hcd he
  have hG := denominatorProduct_eq hab hbc hcd he
  have hprod : (heights a b c d 0 * heights a b c d 1 * heights a b c d 2) *
      denominatorProduct a b c d = (b-a)*(c-a)*(b+c) := by
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      heights_mul_denominator a b c d
  apply Nat.eq_of_mul_eq_mul_left hk
  calc
    _ = 3*((heights a b c d 0 * heights a b c d 1 * heights a b c d 2) *
      (defect a b c d * (rootGcd a b c d)^2)) := by ring
    _ = 3*((heights a b c d 0 * heights a b c d 1 * heights a b c d 2) *
      denominatorProduct a b c d) := by rw [hG]
    _ = 3*((b-a)*(c-a)*(b+c)) := by rw [hprod]
    _ = _ := product_identity hab hbc hcd he

#print axioms denominatorProduct_eq
#print axioms heights_product_exact

/-- The product bound depends on the primitive height, not on the size of a
common dilation of the four roots. -/
theorem normalized_heights_product_bound {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    3*(heights a b c d 0 * heights a b c d 1 * heights a b c d 2) ≤
      7*(d/rootGcd a b c d)^2 := by
  let g := rootGcd a b c d
  have hd : 0<d := by omega
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right c hd)
  have hgd : g ∣ d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right c d)
  have hd' : g*(d/g)=d := Nat.mul_div_cancel' hgd
  have hkd := (defect_lt hab hbc hcd).le
  have hQ : 3*d^2+3*d*defect a b c d+(defect a b c d)^2 ≤ 7*d^2 := by
    have h₁ := Nat.mul_le_mul_left d hkd
    have h₂ := Nat.pow_le_pow_left hkd 2
    nlinarith
  have hh := (heights_product_exact hab hbc hcd he).le.trans hQ
  change 3*(heights a b c d 0 * heights a b c d 1 * heights a b c d 2) ≤ 7*(d/g)^2
  apply Nat.le_of_mul_le_mul_right (c := g^2) (hc := pow_pos hg 2)
  calc
    _ ≤ 7*d^2 := hh
    _ = (7*(d/g)^2)*g^2 := by
      conv_lhs => rw [←hd']
      ring

/-- Every collision has a conic parameter of height at most a constant times
the two-thirds power of its normalized maximum root. -/
theorem exists_small_normalized_height {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    ∃ i : Fin 3, 3*(heights a b c d i)^3 ≤ 7*(d/rootGcd a b c d)^2 := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ
    (heights a b c d) Finset.univ_nonempty
  have hp := Nat.mul_le_mul
    (Nat.mul_le_mul (hi 0 (Finset.mem_univ _)) (hi 1 (Finset.mem_univ _)))
    (hi 2 (Finset.mem_univ _))
  have hp' : (heights a b c d i)^3 ≤
      heights a b c d 0 * heights a b c d 1 * heights a b c d 2 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul] using hp
  exact ⟨i,(Nat.mul_le_mul_left 3 hp').trans
    (normalized_heights_product_bound hab hbc hcd he)⟩

#print axioms normalized_heights_product_bound
#print axioms exists_small_normalized_height


end Erdos1206.ConicHeightProduct
