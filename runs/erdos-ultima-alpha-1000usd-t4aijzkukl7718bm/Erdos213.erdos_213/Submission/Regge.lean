import Mathlib.Tactic

/-! Regge's four-point edge transformation and a consistency obstruction.
This does not settle the unrestricted integral-distance conjecture. -/
namespace Erdos213.Regge

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- The determinant of twice the three-vector Gram matrix, with edge labels
AB=a, AP=b, BP=c, AQ=d, BQ=e, PQ=f. -/
def gramDet {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  det3 (2*a^2) (a^2+b^2-c^2) (a^2+d^2-e^2)
    (a^2+b^2-c^2) (2*b^2) (b^2+d^2-f^2)
    (a^2+d^2-e^2) (b^2+d^2-f^2) (2*d^2)

lemma regge_scaled_identity {R : Type*} [CommRing R] (a b c d e f : R) :
    gramDet (2*a) (c+d+e-b) (b+d+e-c) (b+c+e-d) (b+c+d-e) (2*f) =
      64*gramDet a b c d e f := by
  dsimp [gramDet,det3]
  ring

lemma regge_identity (a b c d e f : ℝ) :
    gramDet a ((b+c+d+e)/2-b) ((b+c+d+e)/2-c)
      ((b+c+d+e)/2-d) ((b+c+d+e)/2-e) f = gramDet a b c d e f := by
  dsimp [gramDet,det3]
  ring

/-- The determinant vanishes for every planar realization; D allows
characteristic coordinates (x,y*sqrt(D)) when interpreted over the reals. -/
lemma planar_gram_zero {R : Type*} [CommRing R]
    (D x y u v z w a b c d e f : R)
    (ha : a^2=x^2+D*y^2) (hb : b^2=u^2+D*v^2)
    (hc : c^2=(x-u)^2+D*(y-v)^2) (hd : d^2=z^2+D*w^2)
    (he : e^2=(x-z)^2+D*(y-w)^2) (hf : f^2=(u-z)^2+D*(v-w)^2) :
    gramDet a b c d e f = 0 := by
  dsimp [gramDet,det3]
  rw [ha,hb,hc,hd,he,hf]
  ring

/-- The proposed new distance to the first anchor from point i, as computed
using the four-point set consisting of both anchors, i, and j. -/
noncomputable def newLeft {ι : Type*} (u v : ι → ℝ) (i j : ι) : ℝ :=
  (u i+v i+u j+v j)/2-u i

noncomputable def newRight {ι : Type*} (u v : ι → ℝ) (i j : ι) : ℝ :=
  (u i+v i+u j+v j)/2-v i

lemma consistency_at_three {ι : Type*} (u v U V : ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∀ p q, p ≠ q → U p=newLeft u v p q ∧ V p=newRight u v p q) :
    U i=v i ∧ V i=u i ∧ u i+v i=u j+v j := by
  obtain ⟨hij1,hij2⟩ := h i j hij
  have hik1 := (h i k hik).1
  have hji1 := (h j i hij.symm).1
  have hjk1 := (h j k hjk).1
  dsimp [newLeft,newRight] at hij1 hij2 hik1 hji1 hjk1
  constructor
  · linarith
  constructor <;> linarith

/-- For three or more points outside the two fixed anchors, applying Regge's
operation coherently to every anchor-based four-point set is possible only
when all two-anchor distance sums agree. It then merely swaps the anchors. -/
lemma coherent_regge_iff {ι : Type*} (u v U V : ι → ℝ) (p q r : ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ i j, i ≠ j → U i=newLeft u v i j ∧ V i=newRight u v i j) ↔
      (U=v ∧ V=u ∧ ∀ i j, u i+v i=u j+v j) := by
  classical
  constructor
  · intro h
    have fresh (i : ι) : ∃ j k, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      by_cases hi : i=p
      · subst i
        exact ⟨q,r,hpq,hpr,hqr⟩
      by_cases hiq : i=q
      · subst i
        exact ⟨p,r,hpq.symm,hqr,hpr⟩
      exact ⟨p,q,hi,hiq,hpq⟩
    have hswap (i : ι) : U i=v i ∧ V i=u i := by
      obtain ⟨j,k,hij,hik,hjk⟩ := fresh i
      have hh := consistency_at_three u v U V i j k hij hik hjk h
      exact ⟨hh.1,hh.2.1⟩
    refine ⟨funext (fun i => (hswap i).1),funext (fun i => (hswap i).2),?_⟩
    intro i j
    by_cases hij : i=j
    · simp [hij]
    have hh := (h i j hij).1
    rw [(hswap i).1] at hh
    dsimp [newLeft] at hh
    linarith
  · rintro ⟨rfl,rfl,h⟩ i j _
    have hh := h i j
    dsimp [newLeft,newRight]
    constructor <;> linarith

/-- A concrete nontrivial four-point transformation. All six transformed
lengths remain positive integers, and the planar Gram determinant vanishes. -/
lemma four_point_lengths :
    ((14+15+13+24 : ℚ)/2-14=19) ∧
    ((14+15+13+24 : ℚ)/2-15=18) ∧
    ((14+15+13+24 : ℚ)/2-13=20) ∧
    ((14+15+13+24 : ℚ)/2-24=9) ∧
    gramDet (13 : ℚ) 14 15 13 24 15=0 ∧
    gramDet (13 : ℚ) 19 18 20 9 15=0 := by
  norm_num [gramDet,det3]

private def x : Fin 4 → ℤ := ![0,169,103,244]
private def y : Fin 4 → ℤ := ![0,0,60,24]
private def d : Fin 4 → Fin 4 → ℤ :=
  !![0,169,247,260; 169,0,234,117; 247,234,0,195; 260,117,195,0]

lemma transformed_integer_norms (i j : Fin 4) :
    (x i-x j)^2+14*(y i-y j)^2=(d i j)^2 := by
  fin_cases i <;> fin_cases j <;> norm_num [x,y,d,Matrix.cons_val]

lemma transformed_triangle (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (x j-x i)*(y k-y i)-(y j-y i)*(x k-x i) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [x,y,Matrix.cons_val] at *

lemma transformed_circle_determinant :
    det3 (x 1) (y 1) ((x 1)^2+14*(y 1)^2)
      (x 2) (y 2) ((x 2)^2+14*(y 2)^2)
      (x 3) (y 3) ((x 3)^2+14*(y 3)^2) ≠ 0 := by
  norm_num [det3,x,y,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

#print axioms regge_scaled_identity
#print axioms regge_identity
#print axioms planar_gram_zero
#print axioms coherent_regge_iff
#print axioms four_point_lengths
#print axioms transformed_integer_norms
#print axioms transformed_triangle
#print axioms transformed_circle_determinant
end Erdos213.Regge
