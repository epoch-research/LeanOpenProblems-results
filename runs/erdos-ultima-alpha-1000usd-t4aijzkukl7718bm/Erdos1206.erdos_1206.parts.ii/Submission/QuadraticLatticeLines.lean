import FormalConjecturesUtil

/-! Lattice-line estimates for binary quadratic forms. Auxiliary only. -/
namespace Erdos1206.QuadraticLatticeLines
open Finset
open scoped Classical

abbrev Vec := ℤ × ℤ

def ht (x : Vec) : ℤ := max |x.1| |x.2|
def form (a b c : ℤ) (x : Vec) : ℤ := a*x.1^2+b*x.1*x.2+c*x.2^2
def leftCoeff (a b : ℤ) (v : Vec) : ℤ := 2*a*v.1+b*v.2
def rightCoeff (b c : ℤ) (v : Vec) : ℤ := b*v.1+2*c*v.2
def constant (a b c : ℤ) : ℤ := 2*|a|+2*|b|+2*|c|+1

def box (N : ℕ) : Finset Vec := Icc (-(N:ℤ)) N ×ˢ Icc (-(N:ℤ)) N

lemma ht_nonneg (x : Vec) : 0 ≤ ht x := (abs_nonneg _).trans (le_max_left _ _)
lemma ht_pos {x : Vec} (hx : x ≠ 0) : 0 < ht x := by
  have h0 := ht_nonneg x
  have ha := abs_nonneg x.1
  have hb := abs_nonneg x.2
  by_contra h
  have h1 : |x.1|=0 := by dsimp [ht] at *; have := le_max_left |x.1| |x.2|; omega
  have h2 : |x.2|=0 := by dsimp [ht] at *; have := le_max_right |x.1| |x.2|; omega
  apply hx
  exact Prod.ext (abs_eq_zero.mp h1) (abs_eq_zero.mp h2)

lemma constant_pos (a b c : ℤ) : 0 < constant a b c := by
  dsimp [constant]
  positivity

lemma mem_box_iff {N : ℕ} {x : Vec} : x ∈ box N ↔ ht x ≤ N := by
  simp only [box,mem_product,mem_Icc,ht,max_le_iff,abs_le]

lemma card_box (N : ℕ) : (box N).card=(2*N+1)^2 := by
  have hi : (Icc (-(N:ℤ)) N).card=2*N+1 := by rw [Int.card_Icc]; omega
  simp only [box,card_product,hi]
  ring

lemma perpendicular_parameter {u v X Y : ℤ}
    (hcop : Int.gcd u v=1) (he : u*X+v*Y=0) :
    ∃ t : ℤ, X=t*v ∧ Y= -t*u := by
  have hh := Int.gcd_eq_gcd_ab u v
  rw [hcop] at hh
  norm_num only [Int.natCast_one] at hh
  refine ⟨X*Int.gcdB u v-Y*Int.gcdA u v,?_,?_⟩
  · linear_combination X*hh+Int.gcdA u v*he
  · linear_combination Y*hh+Int.gcdB u v*he

lemma matrix_injective {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0)
    {x : Vec} (h1 : leftCoeff a b x=0) (h2 : rightCoeff b c x=0) : x=0 := by
  have hx : (4*a*c-b^2)*x.1=0 := by
    dsimp [leftCoeff,rightCoeff] at h1 h2
    linear_combination 2*c*h1-b*h2
  have hy : (4*a*c-b^2)*x.2=0 := by
    dsimp [leftCoeff,rightCoeff] at h1 h2
    linear_combination 2*a*h2-b*h1
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hd) ((mul_eq_zero.mp hy).resolve_left hd)

lemma matrix_height (a b c : ℤ) (x : Vec) :
    ht (leftCoeff a b x,rightCoeff b c x) ≤ constant a b c*ht x := by
  have h0 := ht_nonneg x
  have hx := le_max_left |x.1| |x.2|
  have hy := le_max_right |x.1| |x.2|
  change |x.1| ≤ ht x at hx
  change |x.2| ≤ ht x at hy
  apply max_le
  · calc
      |leftCoeff a b x| ≤ |2*a*x.1|+|b*x.2| := abs_add_le _ _
      _ = 2*|a| *|x.1|+|b| *|x.2| := by simp only [abs_mul]; norm_num
      _ ≤ (2*|a|+|b|)*ht x := by
        have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*|a| by positivity)
        have h2 := mul_le_mul_of_nonneg_left hy (abs_nonneg b)
        nlinarith
      _ ≤ constant a b c*ht x := by
        apply mul_le_mul_of_nonneg_right _ h0
        dsimp [constant]
        have := abs_nonneg b
        have := abs_nonneg c
        omega
  · calc
      |rightCoeff b c x| ≤ |b*x.1|+|2*c*x.2| := abs_add_le _ _
      _ = |b| *|x.1|+2*|c| *|x.2| := by simp only [abs_mul]; norm_num
      _ ≤ (|b|+2*|c|)*ht x := by
        have h1 := mul_le_mul_of_nonneg_left hx (abs_nonneg b)
        have h2 := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*|c| by positivity)
        nlinarith
      _ ≤ constant a b c*ht x := by
        apply mul_le_mul_of_nonneg_right _ h0
        dsimp [constant]
        have := abs_nonneg a
        have := abs_nonneg b
        omega

/-- A nonzero integral point on the perpendicular line is separated from zero
by the height of its primitive normal vector, up to a coefficient constant. -/
lemma primitive_perpendicular_lower {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0)
    {v w : Vec} (hv : Int.gcd v.1 v.2=1) (hw : w ≠ 0)
    (he : leftCoeff a b v*w.1+rightCoeff b c v*w.2=0) :
    ht v ≤ constant a b c*ht w := by
  have he' : v.1*leftCoeff a b w+v.2*rightCoeff b c w=0 := by
    dsimp [leftCoeff,rightCoeff] at *
    nlinarith only [he]
  obtain ⟨t,ht1,ht2⟩ := perpendicular_parameter hv he'
  have ht0 : t ≠ 0 := by
    intro hz
    subst t
    simp only [zero_mul,neg_zero] at ht1 ht2
    exact hw (matrix_injective hd ht1 ht2)
  have ht1p : 1 ≤ |t| := by have := abs_pos.mpr ht0; omega
  have h1 : |v.1| ≤ |rightCoeff b c w| := by
    rw [ht2,abs_mul,abs_neg]
    nlinarith [abs_nonneg v.1]
  have h2 : |v.2| ≤ |leftCoeff a b w| := by
    rw [ht1,abs_mul]
    nlinarith [abs_nonneg v.2]
  calc
    ht v ≤ ht (leftCoeff a b w,rightCoeff b c w) := by
      exact max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _))
    _ ≤ _ := matrix_height a b c w


def axis (A B : ℤ) (x : Vec) : ℤ := if |A| ≤ |B| then x.1 else x.2

lemma axis_distance {A B : ℤ} (hn : A ≠ 0 ∨ B ≠ 0) {x y : Vec}
    (he : A*x.1+B*x.2=A*y.1+B*y.2) :
    ht (x-y)=|axis A B x-axis A B y| := by
  have hh : A*(x.1-y.1)= -B*(x.2-y.2) := by nlinarith only [he]
  have habs := congrArg abs hh
  simp only [abs_mul,abs_neg] at habs
  dsimp [axis,ht]
  by_cases hAB : |A| ≤ |B|
  · simp only [if_pos hAB]
    have hB : 0 < |B| := by
      rcases hn with hA | hB
      · exact (abs_pos.mpr hA).trans_le hAB
      · exact abs_pos.mpr hB
    apply max_eq_left
    have hm := mul_le_mul_of_nonneg_right hAB (abs_nonneg (x.1-y.1))
    nlinarith
  · simp only [if_neg hAB]
    have hA : 0 < |A| := lt_of_le_of_lt (abs_nonneg B) (lt_of_not_ge hAB)
    apply max_eq_right
    have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hAB))
      (abs_nonneg (x.2-y.2))
    nlinarith

lemma axis_abs_le (A B : ℤ) (x : Vec) : |axis A B x| ≤ ht x := by
  dsimp [axis,ht]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma equal_quotients_distance {x y H : ℤ} (hH : 0 < H) (he : x/H=y/H) :
    |x-y| < H := by
  have hx0 := Int.emod_nonneg x hH.ne'
  have hy0 := Int.emod_nonneg y hH.ne'
  have hx := Int.emod_lt_of_pos x hH
  have hy := Int.emod_lt_of_pos y hH
  have hx' := Int.mul_ediv_add_emod x H
  have hy' := Int.mul_ediv_add_emod y H
  rw [he] at hx'
  rw [abs_lt]
  constructor <;> omega

/-- Binning a separated integer projection bounds the number of points. -/
lemma separated_projection_card {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℤ) (C H N : ℤ) (D : ℕ) (hC : 0 < C) (hH : 0 < H)
    (hN : 0 ≤ N) (hD : 2*C*N ≤ (D:ℤ)*H)
    (hb : ∀ x∈S, |f x| ≤ N)
    (hs : ∀ x∈S, ∀ y∈S, x ≠ y → H ≤ C*|f x-f y|) :
    S.card ≤ D+1 := by
  let g (x : ι) : ℤ := (C*(f x+N))/H
  have hm : ∀ x∈S, g x∈Icc (0:ℤ) D := by
    intro x hx
    have hx' := abs_le.mp (hb x hx)
    have hlo : 0 ≤ C*(f x+N) := mul_nonneg hC.le (by omega)
    have hhi : C*(f x+N) ≤ (D:ℤ)*H := by nlinarith
    exact mem_Icc.mpr ⟨Int.ediv_nonneg hlo hH.le,Int.ediv_le_of_le_mul hH hhi⟩
  have hi : Set.InjOn g S := by
    intro x hx y hy he
    by_contra hxy
    have hsep := hs x hx y hy hxy
    have hh := equal_quotients_distance hH he
    have hid : C*(f x+N)-C*(f y+N)=C*(f x-f y) := by ring
    rw [hid,abs_mul,abs_of_pos hC] at hh
    omega
  have hc := card_le_card_of_injOn (s := S) (t := Icc (0:ℤ) D) g (fun x hx => hm x hx) hi
  have hic : (Icc (0:ℤ) D).card=D+1 := by simp [Int.card_Icc]
  rwa [hic] at hc

/-- A uniform bound for lattice points on a line with primitive quadratic
normal vector. The only dependence on the coefficients is `constant`. -/
theorem affine_line_card {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0)
    (v : Vec) (hv : Int.gcd v.1 v.2=1) (N D : ℕ) (H z : ℤ)
    (hH : 0 < H) (hvH : H ≤ ht v)
    (hD : 2*constant a b c*N ≤ (D:ℤ)*H) :
    ((box N).filter (fun x => leftCoeff a b v*x.1+rightCoeff b c v*x.2=z)).card ≤ D+1 := by
  let S := (box N).filter (fun x => leftCoeff a b v*x.1+rightCoeff b c v*x.2=z)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hv
    norm_num at hv
  have hn : leftCoeff a b v ≠ 0 ∨ rightCoeff b c v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (matrix_injective hd h.1 h.2)
  apply separated_projection_card S (axis (leftCoeff a b v) (rightCoeff b c v))
    (constant a b c) H N D (constant_pos a b c) hH (by positivity) hD
  · intro x hx
    exact (axis_abs_le _ _ x).trans (mem_box_iff.mp (mem_filter.mp hx).1)
  · intro x hx y hy hxy
    have he := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    have he' : leftCoeff a b v*(x-y).1+rightCoeff b c v*(x-y).2=0 := by
      simp only [Prod.fst_sub,Prod.snd_sub]
      nlinarith only [he]
    have hw : x-y ≠ 0 := sub_ne_zero.mpr hxy
    have hl := primitive_perpendicular_lower hd hv hw he'
    rw [axis_distance hn he] at hl
    exact hvH.trans hl

#print axioms affine_line_card
end Erdos1206.QuadraticLatticeLines
