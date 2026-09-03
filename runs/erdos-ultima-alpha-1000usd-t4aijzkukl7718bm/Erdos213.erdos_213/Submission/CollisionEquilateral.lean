import Submission.CollisionMotion
import Submission.RationalThreeSquares

/-! An off-axis control for collision motions, and its arithmetic obstruction.
This is one explicit five-point family, not a bound on arbitrary configurations. -/
namespace Erdos213.CollisionEquilateral
open Polynomial
noncomputable section

def f (t : ℝ) : ℝ := 1-t/2-3*t^2/16
def g (t : ℝ) : ℝ := -1-t/2+3*t^2/16
def h (t : ℝ) : ℝ := 1+3*t^2/16

def px (t : ℝ) : Fin 5 → ℝ := ![t,-t/2,-t/2,f t,-g t/2]
def py (t : ℝ) : Fin 5 → ℝ := ![0,t/2,-t/2,0,g t/2]

def edgeSquared (t : ℝ) (i j : Fin 5) : ℝ :=
  (px t i-px t j)^2+3*(py t i-py t j)^2

def normMatrix (t : ℝ) : Fin 5 → Fin 5 → ℝ :=
  !![0,3*t^2,3*t^2,(f t-t)^2,(h t)^2;
     3*t^2,0,3*t^2,(h t)^2,(g t-t)^2;
     3*t^2,3*t^2,0,(h t)^2,(h t)^2;
     (f t-t)^2,(h t)^2,(h t)^2,0,(h t)^2;
     (h t)^2,(g t-t)^2,(h t)^2,(h t)^2,0]

lemma edge_squared_eq (t : ℝ) (i j : Fin 5) : edgeSquared t i j=normMatrix t i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeSquared,px,py,normMatrix,f,g,h,Matrix.cons_val] <;> ring

lemma signed_sum (t : ℝ) : (f t-t)+(g t-t) = -3*t := by dsimp [f,g]; ring
lemma h_pos (t : ℝ) : 0 < h t := by dsimp [h]; positivity

private lemma rat_of_square (x : ℝ) (q : ℚ) (h : (q : ℝ)^2=x^2) :
    ∃ p : ℚ, (p : ℝ)=x := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with he | he
  · exact ⟨q,he⟩
  · refine ⟨-q,?_⟩
    push_cast
    linarith

/-- Two signed lengths summing to three times a height are incompatible with
that height's sqrt(3)-multiple also being rational, unless the height is zero. -/
lemma signed_lengths_zero (A B K : ℝ) (p q l : ℚ) (hs : A+B = -3*K)
    (hp : (p : ℝ)^2=A^2) (hq : (q : ℝ)^2=B^2)
    (hl : (l : ℝ)^2=3*K^2) : K=0 := by
  obtain ⟨u,hu⟩ := rat_of_square A p hp
  obtain ⟨v,hv⟩ := rat_of_square B q hq
  let k : ℚ := -(u+v)/3
  have hk : (k : ℝ)=K := by
    dsimp [k]
    push_cast
    rw [hu,hv]
    linarith
  have he : l^2+(0 : ℚ)^2=3*k^2 := by
    have he' : (l : ℝ)^2+(0 : ℝ)^2=3*(k : ℝ)^2 := by rw [hk]; simpa using hl
    exact_mod_cast he'
  have hz := rat_sum_two_squares_three_mul he
  simpa [hz] using hk.symm

/-- No nonzero real common scale makes all distances in this model rational
at a nonzero real parameter. This is stronger than testing rational parameters. -/
lemma no_common_rational_scale (t c : ℝ) (ht : t ≠ 0) (hc : c ≠ 0) :
    ¬ ∃ d : Fin 5 → Fin 5 → ℚ, ∀ i j,
      (d i j : ℝ)^2=c^2*normMatrix t i j := by
  rintro ⟨d,hd⟩
  have h01 := hd 0 1
  have h03 := hd 0 3
  have h14 := hd 1 4
  norm_num [normMatrix,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.vecHead,Matrix.vecTail] at h01 h03 h14
  have hA : (d 0 3 : ℝ)^2=(c*(f t-t))^2 := by nlinarith [h03]
  have hB : (d 1 4 : ℝ)^2=(c*(g t-t))^2 := by nlinarith [h14]
  have hL : (d 0 1 : ℝ)^2=3*(c*t)^2 := by nlinarith [h01]
  have hs : c*(f t-t)+c*(g t-t) = -3*(c*t) := by
    linear_combination c*signed_sum t
  exact mul_ne_zero hc ht (signed_lengths_zero _ _ _ _ _ _ hs hA hB hL)

lemma weighted_cycle_sq (w0 w1 w2 w3 e1 e2 e3 e4 n1 n2 n3 n4 : ℝ)
    (hw0 : w0 ≠ 0) (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hw3 : w3 ≠ 0)
    (hn3 : n3 ≠ 0) (hn4 : n4 ≠ 0)
    (he1 : e1^2=(w0*w1)^2*n1) (he2 : e2^2=(w2*w3)^2*n2)
    (he3 : e3^2=(w0*w2)^2*n3) (he4 : e4^2=(w1*w3)^2*n4) :
    (e1*e2/(e3*e4))^2=n1*n2/(n3*n4) := by
  rw [div_pow,mul_pow,mul_pow,he1,he2,he3,he4]
  field_simp

/-- Even arbitrary nonzero real endpoint factors cannot repair this entire
five-point model. The assertion is algebraic; it needs no geometric inversion
lemma. It covers the endpoint scaling in the usual inversion distance formula. -/
lemma no_endpoint_weighted_model (t : ℝ) (ht : t ≠ 0) (w : Fin 5 → ℝ)
    (hw : ∀ i, w i ≠ 0) :
    ¬ ∃ d : Fin 5 → Fin 5 → ℚ, ∀ i j,
      (d i j : ℝ)^2=(w i*w j)^2*normMatrix t i j := by
  rintro ⟨d,hd⟩
  have h03 := hd 0 3
  have h21 := hd 2 1
  have h02 := hd 0 2
  have h31 := hd 3 1
  have h14 := hd 1 4
  have h20 := hd 2 0
  have h12 := hd 1 2
  have h40 := hd 4 0
  have h01 := hd 0 1
  have h43 := hd 4 3
  have h04 := hd 0 4
  have h13 := hd 1 3
  norm_num [normMatrix,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.vecHead,Matrix.vecTail] at h03 h21 h02 h31 h14 h20 h12 h40 h01 h43 h04 h13
  have hH : h t ≠ 0 := ne_of_gt (h_pos t)
  have hH2 : (h t)^2 ≠ 0 := pow_ne_zero 2 hH
  have hT : 3*t^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  let A : ℚ := d 0 3*d 2 1/(d 0 2*d 3 1)
  let B : ℚ := d 1 4*d 2 0/(d 1 2*d 4 0)
  let L : ℚ := d 0 1*d 4 3/(d 0 4*d 1 3)
  have heA := weighted_cycle_sq (w 0) (w 3) (w 2) (w 1)
    (d 0 3) (d 2 1) (d 0 2) (d 3 1) ((f t-t)^2) (3*t^2) (3*t^2) ((h t)^2)
    (hw 0) (hw 3) (hw 2) (hw 1) hT hH2 h03 h21 h02 h31
  have heB := weighted_cycle_sq (w 1) (w 4) (w 2) (w 0)
    (d 1 4) (d 2 0) (d 1 2) (d 4 0) ((g t-t)^2) (3*t^2) (3*t^2) ((h t)^2)
    (hw 1) (hw 4) (hw 2) (hw 0) hT hH2 h14 h20 h12 h40
  have heL := weighted_cycle_sq (w 0) (w 1) (w 4) (w 3)
    (d 0 1) (d 4 3) (d 0 4) (d 1 3) (3*t^2) ((h t)^2) ((h t)^2) ((h t)^2)
    (hw 0) (hw 1) (hw 4) (hw 3) hH2 hH2 h01 h43 h04 h13
  have hA : (A : ℝ)^2=((f t-t)/h t)^2 := by
    dsimp [A]
    push_cast
    rw [heA]
    field_simp
  have hB : (B : ℝ)^2=((g t-t)/h t)^2 := by
    dsimp [B]
    push_cast
    rw [heB]
    field_simp
  have hL : (L : ℝ)^2=3*(t/h t)^2 := by
    dsimp [L]
    push_cast
    rw [heL]
    field_simp
  have hs : (f t-t)/h t+(g t-t)/h t = -3*(t/h t) := by
    linear_combination (1/h t)*signed_sum t
  exact div_ne_zero ht hH (signed_lengths_zero _ _ _ A B L hs hA hB hL)

#print axioms no_endpoint_weighted_model
#print axioms edge_squared_eq
#print axioms signed_lengths_zero
#print axioms no_common_rational_scale
#print axioms weighted_cycle_sq
end
end Erdos213.CollisionEquilateral
