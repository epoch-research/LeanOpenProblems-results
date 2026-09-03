import Submission.MedianDiscriminant
import Submission.MedianDeltaSides

/-! Multiplication of each side by its opposite doubled median squares the
triangle discriminant. Its new median conditions are independent requirements;
this operation is not asserted to produce a new rational-median triangle. -/
namespace Erdos213.MedianProduct

variable {R : Type*} [CommRing R]

def deltaSq (A B C : R) : R := A^2+B^2+C^2-A*B-A*C-B*C
def heronSq (A B C : R) : R := 2*A*B+2*A*C+2*B*C-A^2-B^2-C^2
def productSq (A B C : R) : R := A*(2*B+2*C-A)
def newMedian (A B C : R) : R := (A+B+C)^2-3*(B-C)^2

lemma sum_identity (A B C : R) :
    productSq A B C+productSq B A C+productSq C A B =
      (A+B+C)^2-2*deltaSq A B C := by
  dsimp [productSq,deltaSq]
  ring

lemma delta_identity (A B C : R) :
    deltaSq (productSq A B C) (productSq B A C) (productSq C A B) =
      (deltaSq A B C)^2 := by
  dsimp [productSq,deltaSq]
  ring

lemma heron_identity (A B C : R) :
    heronSq (productSq A B C) (productSq B A C) (productSq C A B) =
      (A+B+C)^2*heronSq A B C := by
  dsimp [productSq,heronSq]
  ring

lemma median_identities (A B C : R) :
    -productSq A B C+2*productSq B A C+2*productSq C A B = newMedian A B C ∧
    2*productSq A B C-productSq B A C+2*productSq C A B = newMedian B A C ∧
    2*productSq A B C+2*productSq B A C-productSq C A B = newMedian C A B := by
  dsimp [productSq,newMedian]
  constructor
  · ring
  constructor <;> ring

lemma products (a b c u v w : R)
    (hu : u^2=2*b^2+2*c^2-a^2) (hv : v^2=2*a^2+2*c^2-b^2)
    (hw : w^2=2*a^2+2*b^2-c^2) :
    (a*u)^2=productSq (a^2) (b^2) (c^2) ∧
    (b*v)^2=productSq (b^2) (a^2) (c^2) ∧
    (c*w)^2=productSq (c^2) (a^2) (b^2) := by
  simp only [mul_pow,hu,hv,hw,productSq,and_self]

lemma product_discriminant (a b c u v w : R)
    (hu : u^2=2*b^2+2*c^2-a^2) (hv : v^2=2*a^2+2*c^2-b^2)
    (hw : w^2=2*a^2+2*b^2-c^2) :
    MedianDeltaSides.delta (a*u) (b*v) (c*w) = (MedianDeltaSides.delta a b c)^2 := by
  have he (x y z : R) : MedianDeltaSides.delta x y z=deltaSq (x^2) (y^2) (z^2) := by
    dsimp [MedianDeltaSides.delta,deltaSq]
    ring
  obtain ⟨hp,hq,hr⟩ := products a b c u v w hu hv hw
  rw [he,he,hp,hq,hr,delta_identity]

lemma product_heron (a b c u v w : R)
    (hu : u^2=2*b^2+2*c^2-a^2) (hv : v^2=2*a^2+2*c^2-b^2)
    (hw : w^2=2*a^2+2*b^2-c^2) :
    MedianDeltaSides.heron (a*u) (b*v) (c*w) =
      (a^2+b^2+c^2)^2*MedianDeltaSides.heron a b c := by
  have he (x y z : R) : MedianDeltaSides.heron x y z=heronSq (x^2) (y^2) (z^2) := by
    dsimp [MedianDeltaSides.heron,heronSq]
    ring
  obtain ⟨hp,hq,hr⟩ := products a b c u v w hu hv hw
  rw [he,he,hp,hq,hr,heron_identity]

lemma product_medians (a b c u v w : R)
    (hu : u^2=2*b^2+2*c^2-a^2) (hv : v^2=2*a^2+2*c^2-b^2)
    (hw : w^2=2*a^2+2*b^2-c^2) :
    MedianDeltaSides.median₃ (a*u) (b*v) (c*w)=newMedian (a^2) (b^2) (c^2) ∧
    MedianDeltaSides.median₂ (a*u) (b*v) (c*w)=newMedian (b^2) (a^2) (c^2) ∧
    MedianDeltaSides.median₁ (a*u) (b*v) (c*w)=newMedian (c^2) (a^2) (b^2) := by
  obtain ⟨hp,hq,hr⟩ := products a b c u v w hu hv hw
  simp only [MedianDeltaSides.median₁,MedianDeltaSides.median₂,MedianDeltaSides.median₃,
    hp,hq,hr]
  exact median_identities (a^2) (b^2) (c^2)

lemma square_div_sq_iff (x d : ℚ) (hd : d ≠ 0) :
    IsSquare (x/d^2) ↔ IsSquare x := by
  constructor
  · intro h
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hd)] using h.mul (IsSquare.sq d)
  · intro h
    exact h.div (IsSquare.sq d)

/-- Exact conditional bridge to the earlier six-square median criterion.
The new discriminant and positive area are automatic, but all three
new median squares are still required. -/
theorem admissible_product_iff (a b c u v w : ℚ)
    (hu : u^2=2*b^2+2*c^2-a^2) (hv : v^2=2*a^2+2*c^2-b^2)
    (hw : w^2=2*a^2+2*b^2-c^2) (hd : b*v ≠ 0)
    (hH : 0 < MedianDeltaSides.heron a b c) :
    MedianDiscriminant.Admissible ((a*u/(b*v))^2) ((c*w/(b*v))^2) ↔
      IsSquare (newMedian (a^2) (b^2) (c^2)) ∧
      IsSquare (newMedian (b^2) (a^2) (c^2)) ∧
      IsSquare (newMedian (c^2) (a^2) (b^2)) := by
  have hb := left_ne_zero_of_mul hd
  have hv0 := right_ne_zero_of_mul hd
  let A := (a*u/(b*v))^2
  let C := (c*w/(b*v))^2
  obtain ⟨hm₃,hm₂,hm₁⟩ := product_medians a b c u v w hu hv hw
  have h₁ : 2*A+2-C = newMedian (c^2) (a^2) (b^2)/(b*v)^2 := by
    dsimp [A,C]
    field_simp
    dsimp [MedianDeltaSides.median₁] at hm₁
    linear_combination hm₁
  have h₂ : 2*A-1+2*C = newMedian (b^2) (a^2) (c^2)/(b*v)^2 := by
    dsimp [A,C]
    field_simp
    dsimp [MedianDeltaSides.median₂] at hm₂
    linear_combination hm₂
  have h₃ : -A+2+2*C = newMedian (a^2) (b^2) (c^2)/(b*v)^2 := by
    dsimp [A,C]
    field_simp
    dsimp [MedianDeltaSides.median₃] at hm₃
    linear_combination hm₃
  have hdelta : MedianDiscriminant.delta A C =
      (MedianDeltaSides.delta a b c/(b*v)^2)^2 := by
    have hh := product_discriminant a b c u v w hu hv hw
    dsimp [MedianDiscriminant.delta,A,C]
    field_simp
    dsimp [MedianDeltaSides.delta] at hh ⊢
    linear_combination hh
  have hheron : MedianDiscriminant.heron A C =
      (a^2+b^2+c^2)^2*MedianDeltaSides.heron a b c/(b*v)^4 := by
    have hh := product_heron a b c u v w hu hv hw
    dsimp [MedianDiscriminant.heron,A,C]
    field_simp
    dsimp [MedianDeltaSides.heron] at hh ⊢
    linear_combination hh
  have hS : 0 < a^2+b^2+c^2 := by
    nlinarith [sq_nonneg a,sq_nonneg c,sq_pos_of_ne_zero hb]
  have hpos : 0 < MedianDiscriminant.heron A C := by
    rw [hheron]
    exact div_pos (mul_pos (sq_pos_of_pos hS) hH)
      (by simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hd) 2)
  have hA : IsSquare A := IsSquare.sq _
  have hC : IsSquare C := IsSquare.sq _
  change MedianDiscriminant.Admissible A C ↔ _
  rw [MedianDiscriminant.Admissible,h₁,h₂,h₃,hdelta]
  simp only [hA,hC,IsSquare.sq,square_div_sq_iff _ _ hd,hpos,true_and,and_true]
  tauto

lemma control_medians :
    (158 : ℚ)^2=2*85^2+2*87^2-68^2 ∧
    (131 : ℚ)^2=2*68^2+2*87^2-85^2 ∧
    (127 : ℚ)^2=2*68^2+2*85^2-87^2 := by norm_num

lemma control_product :
    MedianDeltaSides.delta (10744 : ℚ) 11135 11049=7778281^2 ∧
    0 < MedianDeltaSides.heron (10744 : ℚ) 11135 11049 ∧
    MedianDeltaSides.median₃ (10744 : ℚ) 11135 11049=376703716 ∧
    MedianDeltaSides.median₂ (10744 : ℚ) 11135 11049=351039649 ∧
    MedianDeltaSides.median₁ (10744 : ℚ) 11135 11049=356763121 := by
  norm_num [MedianDeltaSides.delta,MedianDeltaSides.heron,MedianDeltaSides.median₁,
    MedianDeltaSides.median₂,MedianDeltaSides.median₃]

lemma control_new_medians_not_square :
    ¬IsSquare (376703716 : ℚ) ∧ ¬IsSquare (351039649 : ℚ) ∧ ¬IsSquare (356763121 : ℚ) := by
  decide +kernel

#print axioms product_discriminant
#print axioms product_heron
#print axioms product_medians
#print axioms admissible_product_iff
#print axioms control_new_medians_not_square
end Erdos213.MedianProduct
