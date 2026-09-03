import Submission.MedianProduct

/-! Exact rational inversion of the squared-side median-product map.
This does not assert square side roots for the inverse, and does not settle
the rational median surface or Erdős 213. -/
namespace Erdos213.MedianProduct
set_option maxHeartbeats 3000000

lemma necessary_invariants {K : Type*} [CommRing K] (P Q R A B C : K)
    (hP : productSq A B C=P) (hQ : productSq B A C=Q) (hR : productSq C A B=R) :
    (deltaSq A B C)^2=deltaSq P Q R ∧
      (A+B+C)^2=P+Q+R+2*deltaSq A B C := by
  have hd := delta_identity A B C
  have hs := sum_identity A B C
  rw [hP,hQ,hR] at hd hs
  exact ⟨hd.symm,by linear_combination -hs⟩

def inverseSum (P Q R d : ℚ) : ℚ := P+Q+R+2*d

lemma signed_square_roots (P Q R : ℚ) (hP : IsSquare P) (hQ : IsSquare Q)
    (hR : IsSquare R) (hH : heronSq P Q R=0) :
    ∃ x y z : ℚ, x+y+z=0 ∧ x^2=P ∧ y^2=Q ∧ z^2=R := by
  obtain ⟨x,hx⟩ := hP
  obtain ⟨y,hy⟩ := hQ
  obtain ⟨z,hz⟩ := hR
  have hx' : x^2=P := by simpa only [pow_two] using hx.symm
  have hy' : y^2=Q := by simpa only [pow_two] using hy.symm
  have hz' : z^2=R := by simpa only [pow_two] using hz.symm
  rw [← hx',← hy',← hz'] at hH
  have hf : (x+y+z)*(-x+y+z)*(x-y+z)*(x+y-z)=0 := by
    dsimp [heronSq] at hH
    linear_combination hH
  simp only [mul_eq_zero] at hf
  rcases hf with ((h | h) | h) | h
  · exact ⟨x,y,z,h,hx',hy',hz'⟩
  · exact ⟨-x,y,z,h,by simpa only [neg_sq] using hx',hy',hz'⟩
  · exact ⟨x,-y,z,by simpa only [sub_eq_add_neg] using h,
      hx',by simpa only [neg_sq] using hy',hz'⟩
  · exact ⟨x,y,-z,by simpa only [sub_eq_add_neg] using h,
      hx',hy',by simpa only [neg_sq] using hz'⟩

lemma inverse_root_heron (P Q R d : ℚ) :
    heronSq (inverseSum P Q R d-3*P) (inverseSum P Q R d-3*Q)
      (inverseSum P Q R d-3*R)=12*(d^2-deltaSq P Q R) := by
  dsimp [heronSq,inverseSum,deltaSq]
  ring

lemma inverse_lift (P Q R S x y z : ℚ) (hs : x+y+z=0)
    (hx : S^2-3*P=x^2) (hy : S^2-3*Q=y^2) (hz : S^2-3*R=z^2) :
    productSq ((S+x)/3) ((S+y)/3) ((S+z)/3)=P ∧
    productSq ((S+y)/3) ((S+x)/3) ((S+z)/3)=Q ∧
    productSq ((S+z)/3) ((S+x)/3) ((S+y)/3)=R := by
  dsimp [productSq]
  constructor
  · linear_combination hx/3+(2/9 : ℚ)*(S+x)*hs
  constructor
  · linear_combination hy/3+(2/9 : ℚ)*(S+y)*hs
  · linear_combination hz/3+(2/9 : ℚ)*(S+z)*hs

/-- Rational preimages of the quadratic squared-side map require four
additional square conditions after choosing a discriminant root. This
criterion does NOT say the recovered squared sides are themselves squares. -/
theorem rational_inverse_iff (P Q R : ℚ) :
    (∃ A B C : ℚ, productSq A B C=P ∧ productSq B A C=Q ∧ productSq C A B=R) ↔
      ∃ d : ℚ, d^2=deltaSq P Q R ∧ IsSquare (inverseSum P Q R d) ∧
        IsSquare (inverseSum P Q R d-3*P) ∧
        IsSquare (inverseSum P Q R d-3*Q) ∧
        IsSquare (inverseSum P Q R d-3*R) := by
  constructor
  · rintro ⟨A,B,C,hP,hQ,hR⟩
    obtain ⟨hd,hs⟩ := necessary_invariants P Q R A B C hP hQ hR
    have hs' : inverseSum P Q R (deltaSq A B C)=(A+B+C)^2 := hs.symm
    refine ⟨deltaSq A B C,hd,?_,?_,?_,?_⟩
    · rw [hs']
      exact IsSquare.sq _
    · rw [hs',← hP]
      convert IsSquare.sq (2*A-B-C) using 1
      dsimp [productSq]
      ring
    · rw [hs',← hQ]
      convert IsSquare.sq (2*B-A-C) using 1
      dsimp [productSq]
      ring
    · rw [hs',← hR]
      convert IsSquare.sq (2*C-A-B) using 1
      dsimp [productSq]
      ring
  · rintro ⟨d,hd,⟨S,hS⟩,hx,hy,hz⟩
    have hS' : inverseSum P Q R d=S^2 := by simpa only [pow_two] using hS
    have hh : heronSq (inverseSum P Q R d-3*P) (inverseSum P Q R d-3*Q)
        (inverseSum P Q R d-3*R)=0 := by rw [inverse_root_heron,hd]; ring
    obtain ⟨x,y,z,hxyz,hx',hy',hz'⟩ := signed_square_roots _ _ _ hx hy hz hh
    rw [hS'] at hx' hy' hz'
    exact ⟨(S+x)/3,(S+y)/3,(S+z)/3,inverse_lift P Q R S x y z hxyz
      hx'.symm hy'.symm hz'.symm⟩

/-- The earlier rational-side, square-discriminant triangle (19,13,17)
has no rational preimage even at the squared-side level. Its medians are
not all rational, so this is NOT a counterexample to the full median locus. -/
lemma square_discriminant_not_surjective :
    ¬ ∃ A B C : ℚ, productSq A B C=19^2 ∧
      productSq B A C=13^2 ∧ productSq C A B=17^2 := by
  rintro ⟨A,B,C,hP,hQ,hR⟩
  obtain ⟨hd,hs⟩ := necessary_invariants (19^2) (13^2) (17^2) A B C hP hQ hR
  have hd' : (deltaSq A B C)^2=(168 : ℚ)^2 := by norm_num [deltaSq] at hd ⊢; exact hd
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hd' with h | h
  · rw [h] at hs
    have hh : IsSquare (1155 : ℚ) := ⟨A+B+C,by nlinarith only [hs]⟩
    norm_num at hh
  · rw [h] at hs
    have hh : IsSquare (483 : ℚ) := ⟨A+B+C,by nlinarith only [hs]⟩
    norm_num at hh

lemma no_inverse_invariants_mod23 :
    ¬ ∃ d S : ZMod 23, d^2=5053 ∧ S^2=565+2*d := by
  decide +kernel

/-- A finite-field obstruction to an automatic inverse, not to rational
points on the original surface. The target is (14^2,12^2,15^2). -/
lemma no_inverse_mod23 :
    ¬ ∃ A B C : ZMod 23, productSq A B C=14^2 ∧
      productSq B A C=12^2 ∧ productSq C A B=15^2 := by
  rintro ⟨A,B,C,hP,hQ,hR⟩
  obtain ⟨hd,hs⟩ := necessary_invariants (14^2) (12^2) (15^2) A B C hP hQ hR
  apply no_inverse_invariants_mod23
  refine ⟨deltaSq A B C,A+B+C,?_,?_⟩
  · norm_num [deltaSq] at hd ⊢
    exact hd
  · convert hs using 1

#print axioms rational_inverse_iff
#print axioms square_discriminant_not_surjective
#print axioms no_inverse_invariants_mod23
#print axioms no_inverse_mod23
end Erdos213.MedianProduct
