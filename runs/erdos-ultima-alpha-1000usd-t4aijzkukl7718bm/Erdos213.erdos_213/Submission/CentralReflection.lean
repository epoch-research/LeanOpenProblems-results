import Submission.ReflectionCubic
import Submission.CentralQuadratic

/-! Complete finite algebraic certificates for the normalized central-heptad
reflection proposal. This restricted obstruction does not settle Erdős 213. -/
namespace Erdos213.CentralReflection
open ReflectionCubic
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def points (t w : ℂ) : Fin 7 → ℂ :=
  ![0,1-t^2,1-w^2,(1+t)*(1+w),(1+t)*(1-w),(1-t)*(1+w),(1-t)*(1-w)]

def single : Fin 105 → Fin 7 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]

def pair : Fin 105 → Fin 3 → Fin 2 → Fin 7 :=
  ![![![1,2],![3,4],![5,6]],
    ![![1,2],![3,5],![4,6]],
    ![![1,2],![3,6],![4,5]],
    ![![1,3],![2,4],![5,6]],
    ![![1,3],![2,5],![4,6]],
    ![![1,3],![2,6],![4,5]],
    ![![1,4],![2,3],![5,6]],
    ![![1,4],![2,5],![3,6]],
    ![![1,4],![2,6],![3,5]],
    ![![1,5],![2,3],![4,6]],
    ![![1,5],![2,4],![3,6]],
    ![![1,5],![2,6],![3,4]],
    ![![1,6],![2,3],![4,5]],
    ![![1,6],![2,4],![3,5]],
    ![![1,6],![2,5],![3,4]],
    ![![0,2],![3,4],![5,6]],
    ![![0,2],![3,5],![4,6]],
    ![![0,2],![3,6],![4,5]],
    ![![0,3],![2,4],![5,6]],
    ![![0,3],![2,5],![4,6]],
    ![![0,3],![2,6],![4,5]],
    ![![0,4],![2,3],![5,6]],
    ![![0,4],![2,5],![3,6]],
    ![![0,4],![2,6],![3,5]],
    ![![0,5],![2,3],![4,6]],
    ![![0,5],![2,4],![3,6]],
    ![![0,5],![2,6],![3,4]],
    ![![0,6],![2,3],![4,5]],
    ![![0,6],![2,4],![3,5]],
    ![![0,6],![2,5],![3,4]],
    ![![0,1],![3,4],![5,6]],
    ![![0,1],![3,5],![4,6]],
    ![![0,1],![3,6],![4,5]],
    ![![0,3],![1,4],![5,6]],
    ![![0,3],![1,5],![4,6]],
    ![![0,3],![1,6],![4,5]],
    ![![0,4],![1,3],![5,6]],
    ![![0,4],![1,5],![3,6]],
    ![![0,4],![1,6],![3,5]],
    ![![0,5],![1,3],![4,6]],
    ![![0,5],![1,4],![3,6]],
    ![![0,5],![1,6],![3,4]],
    ![![0,6],![1,3],![4,5]],
    ![![0,6],![1,4],![3,5]],
    ![![0,6],![1,5],![3,4]],
    ![![0,1],![2,4],![5,6]],
    ![![0,1],![2,5],![4,6]],
    ![![0,1],![2,6],![4,5]],
    ![![0,2],![1,4],![5,6]],
    ![![0,2],![1,5],![4,6]],
    ![![0,2],![1,6],![4,5]],
    ![![0,4],![1,2],![5,6]],
    ![![0,4],![1,5],![2,6]],
    ![![0,4],![1,6],![2,5]],
    ![![0,5],![1,2],![4,6]],
    ![![0,5],![1,4],![2,6]],
    ![![0,5],![1,6],![2,4]],
    ![![0,6],![1,2],![4,5]],
    ![![0,6],![1,4],![2,5]],
    ![![0,6],![1,5],![2,4]],
    ![![0,1],![2,3],![5,6]],
    ![![0,1],![2,5],![3,6]],
    ![![0,1],![2,6],![3,5]],
    ![![0,2],![1,3],![5,6]],
    ![![0,2],![1,5],![3,6]],
    ![![0,2],![1,6],![3,5]],
    ![![0,3],![1,2],![5,6]],
    ![![0,3],![1,5],![2,6]],
    ![![0,3],![1,6],![2,5]],
    ![![0,5],![1,2],![3,6]],
    ![![0,5],![1,3],![2,6]],
    ![![0,5],![1,6],![2,3]],
    ![![0,6],![1,2],![3,5]],
    ![![0,6],![1,3],![2,5]],
    ![![0,6],![1,5],![2,3]],
    ![![0,1],![2,3],![4,6]],
    ![![0,1],![2,4],![3,6]],
    ![![0,1],![2,6],![3,4]],
    ![![0,2],![1,3],![4,6]],
    ![![0,2],![1,4],![3,6]],
    ![![0,2],![1,6],![3,4]],
    ![![0,3],![1,2],![4,6]],
    ![![0,3],![1,4],![2,6]],
    ![![0,3],![1,6],![2,4]],
    ![![0,4],![1,2],![3,6]],
    ![![0,4],![1,3],![2,6]],
    ![![0,4],![1,6],![2,3]],
    ![![0,6],![1,2],![3,4]],
    ![![0,6],![1,3],![2,4]],
    ![![0,6],![1,4],![2,3]],
    ![![0,1],![2,3],![4,5]],
    ![![0,1],![2,4],![3,5]],
    ![![0,1],![2,5],![3,4]],
    ![![0,2],![1,3],![4,5]],
    ![![0,2],![1,4],![3,5]],
    ![![0,2],![1,5],![3,4]],
    ![![0,3],![1,2],![4,5]],
    ![![0,3],![1,4],![2,5]],
    ![![0,3],![1,5],![2,4]],
    ![![0,4],![1,2],![3,5]],
    ![![0,4],![1,3],![2,5]],
    ![![0,4],![1,5],![2,3]],
    ![![0,5],![1,2],![3,4]],
    ![![0,5],![1,3],![2,4]],
    ![![0,5],![1,4],![2,3]]]

def reflected (t w : ℂ) (m : Fin 105) : ℂ :=
  points t w (pair m 0 0)+points t w (pair m 0 1)-points t w (single m)

def PairingEquations (t w : ℂ) (m : Fin 105) : Prop :=
  points t w (pair m 0 0)+points t w (pair m 0 1)=
    points t w (pair m 1 0)+points t w (pair m 1 1) ∧
  points t w (pair m 0 0)+points t w (pair m 0 1)=
    points t w (pair m 2 0)+points t w (pair m 2 1)

private def coeff : Fin 28 → Fin 3 → ℚ :=
  !![-5,-1,-3;
    -1,-1,9;
    1,-1,-9;
    5,-1,3;
    (1/3),(5/3),(-1/3);
    (-1/9),(-1/9),(1/9);
    (1/9),(-1/9),(-1/9);
    (-1/3),(5/3),(1/3);
    3,7,-3;
    (7/3),-1,(1/3);
    -3,7,3;
    (-7/3),-1,(-1/3);
    3,-1,5;
    (-1/5),(3/5),(1/5);
    -7,-1,-1;
    (7/5),-1,(1/5);
    1,7,-1;
    9,-1,-1;
    -5,7,5;
    1,-9,-1;
    -3,-1,-5;
    (1/5),(3/5),(-1/5);
    (-7/5),-1,(-1/5);
    7,-1,1;
    5,7,-5;
    -1,-9,1;
    -1,7,1;
    -9,-1,1]

lemma cubic_no_rational_root (i : Fin 28) (q : ℚ) :
    q^3+coeff i 0*q^2+coeff i 1*q+coeff i 2≠0 := by
  fin_cases i
  · intro h
    change q^3+(-5)*q^2+(-1)*q+(-3)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (-5) (-1) (-3) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-1)*q^2+(-1)*q+(9)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (-1) (-1) (9) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(1)*q^2+(-1)*q+(-9)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (1) (-1) (-9) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(5)*q^2+(-1)*q+(3)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (5) (-1) (3) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((1/3))*q^2+((5/3))*q+((-1/3))=0 at h
    apply rational_no_root 5 (by norm_num) (3) (1) (5) (-1) (by decide +kernel) q
    linear_combination (3)*h
  · intro h
    change q^3+((-1/9))*q^2+((-1/9))*q+((1/9))=0 at h
    apply rational_no_root 5 (by norm_num) (9) (-1) (-1) (1) (by decide +kernel) q
    linear_combination (9)*h
  · intro h
    change q^3+((1/9))*q^2+((-1/9))*q+((-1/9))=0 at h
    apply rational_no_root 5 (by norm_num) (9) (1) (-1) (-1) (by decide +kernel) q
    linear_combination (9)*h
  · intro h
    change q^3+((-1/3))*q^2+((5/3))*q+((1/3))=0 at h
    apply rational_no_root 5 (by norm_num) (3) (-1) (5) (1) (by decide +kernel) q
    linear_combination (3)*h
  · intro h
    change q^3+(3)*q^2+(7)*q+(-3)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (3) (7) (-3) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((7/3))*q^2+(-1)*q+((1/3))=0 at h
    apply rational_no_root 5 (by norm_num) (3) (7) (-3) (1) (by decide +kernel) q
    linear_combination (3)*h
  · intro h
    change q^3+(-3)*q^2+(7)*q+(3)=0 at h
    apply rational_no_root 5 (by norm_num) (1) (-3) (7) (3) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((-7/3))*q^2+(-1)*q+((-1/3))=0 at h
    apply rational_no_root 5 (by norm_num) (3) (-7) (-3) (-1) (by decide +kernel) q
    linear_combination (3)*h
  · intro h
    change q^3+(3)*q^2+(-1)*q+(5)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (3) (-1) (5) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((-1/5))*q^2+((3/5))*q+((1/5))=0 at h
    apply rational_no_root 3 (by norm_num) (5) (-1) (3) (1) (by decide +kernel) q
    linear_combination (5)*h
  · intro h
    change q^3+(-7)*q^2+(-1)*q+(-1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-7) (-1) (-1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((7/5))*q^2+(-1)*q+((1/5))=0 at h
    apply rational_no_root 3 (by norm_num) (5) (7) (-5) (1) (by decide +kernel) q
    linear_combination (5)*h
  · intro h
    change q^3+(1)*q^2+(7)*q+(-1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (1) (7) (-1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(9)*q^2+(-1)*q+(-1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (9) (-1) (-1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-5)*q^2+(7)*q+(5)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-5) (7) (5) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(1)*q^2+(-9)*q+(-1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (1) (-9) (-1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-3)*q^2+(-1)*q+(-5)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-3) (-1) (-5) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+((1/5))*q^2+((3/5))*q+((-1/5))=0 at h
    apply rational_no_root 3 (by norm_num) (5) (1) (3) (-1) (by decide +kernel) q
    linear_combination (5)*h
  · intro h
    change q^3+((-7/5))*q^2+(-1)*q+((-1/5))=0 at h
    apply rational_no_root 3 (by norm_num) (5) (-7) (-5) (-1) (by decide +kernel) q
    linear_combination (5)*h
  · intro h
    change q^3+(7)*q^2+(-1)*q+(1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (7) (-1) (1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(5)*q^2+(7)*q+(-5)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (5) (7) (-5) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-1)*q^2+(-9)*q+(1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-1) (-9) (1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-1)*q^2+(7)*q+(1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-1) (7) (1) (by decide +kernel) q
    linear_combination (1)*h
  · intro h
    change q^3+(-9)*q^2+(-1)*q+(1)=0 at h
    apply rational_no_root 3 (by norm_num) (1) (-9) (-1) (1) (by decide +kernel) q
    linear_combination (1)*h

lemma no_reflection_case (t w : ℂ) (u v : ℚ)
    (hq : t^2-(u : ℂ)*t+(v : ℂ)=0)
    (hi : Function.Injective (points t w)) (m : Fin 105)
    (he : PairingEquations t w m)
    (hn : reflected t w m≠points t w (single m)) : False := by
  fin_cases m
  · have h0 : -t^2 - 2*t - w^2=0 := by
      have hh := he.1
      change (1-t^2)+(1-w^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t - w^2=0 := by
      have hh := he.2
      change (1-t^2)+(1-w^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(1)=0 := by
      linear_combination (-1/4)*h0+(1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - w^2 - 2*w=0 := by
      have hh := he.1
      change (1-t^2)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - w^2 + 2*w=0 := by
      have hh := he.2
      change (1-t^2)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hA : (w)≠0 := by
      exact hn0
    have hprod : ((w))*(1)=0 := by
      linear_combination (-1/4)*h0+(1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*t*w - w^2=0 := by
      have hh := he.1
      change (1-t^2)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t*w - w^2=0 := by
      have hh := he.2
      change (1-t^2)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hn1 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (w) * (t)≠0 := by
      exact (mul_ne_zero hn0 hn1)
    have hprod : ((w) * (t))*(1)=0 := by
      linear_combination (-1/4)*h0+(1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 + 2*t*w + w^2 + 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + t*w + 3*t + w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1+w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 - 5*t^2 - t - 3)=0 := by
      linear_combination (-t^2 + 3*t*w/2 + 11*t/2 + 3*w/2 + 1/2)*h0+(-7*t*w/2 - t/2 - 3*w^2/2 - 7*w/2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-5) (-1) (-3) u v t (cubic_no_rational_root 0) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + 2*t*w + 2*t + w^2=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + t*w + t + 3*w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 - t^2 - t + 9)=0 := by
      linear_combination (-t^2 + 3*t*w/2 + 9*t/2 + 9*w/2 + 9/2)*h0+(-7*t*w/2 - 11*t/2 - 3*w^2/2 - 3*w/2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (-1) (9) u v t (cubic_no_rational_root 1) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + 2*t + w^2 + 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 3*t*w + t + w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hn1 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hn2 : (t - w - 2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (1-t^2)+((1+t)*(1+w))-(0)=(0)
      linear_combination (-t - 1)*hf
    have hA : (w) * (t) * (t - w - 2)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((w) * (t) * (t - w - 2))*(1)=0 := by
      linear_combination (1/4 - t/4)*h0+(t/4 - w/4 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*t*w + w^2 - 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - t*w + 3*t - w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1-w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 - 5*t^2 - t - 3)=0 := by
      linear_combination (-t^2 - 3*t*w/2 + 11*t/2 - 3*w/2 + 1/2)*h0+(7*t*w/2 - t/2 - 3*w^2/2 + 7*w/2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-5) (-1) (-3) u v t (cubic_no_rational_root 0) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + 2*t + w^2 - 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - 3*t*w + t - w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hn1 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hn2 : (t + w - 2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (1-t^2)+((1+t)*(1-w))-(0)=(0)
      linear_combination (-t - 1)*hf
    have hA : (w) * (t) * (t + w - 2)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((w) * (t) * (t + w - 2))*(1)=0 := by
      linear_combination (t/4 - 1/4)*h0+(-t/4 - w/4 + 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*t*w + 2*t + w^2=0 := by
      have hh := he.1
      change (1-t^2)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - t*w + t - 3*w=0 := by
      have hh := he.2
      change (1-t^2)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 - t^2 - t + 9)=0 := by
      linear_combination (-t^2 - 3*t*w/2 + 9*t/2 - 9*w/2 + 9/2)*h0+(7*t*w/2 - 11*t/2 - 3*w^2/2 + 3*w/2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (-1) (9) u v t (cubic_no_rational_root 1) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - 2*t*w - 2*t + w^2=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - t*w - t + 3*w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 + t^2 - t - 9)=0 := by
      linear_combination (-t^2 - 3*t*w/2 - 9*t/2 + 9*w/2 + 9/2)*h0+(7*t*w/2 + 11*t/2 - 3*w^2/2 - 3*w/2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (-1) (-9) u v t (cubic_no_rational_root 2) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - 2*t + w^2 + 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - 3*t*w - t + w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1+w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hn1 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hn2 : (t + w + 2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (1-t^2)+((1-t)*(1+w))-(0)=(0)
      linear_combination (1 - t)*hf
    have hA : (w) * (t) * (t + w + 2)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((w) * (t) * (t + w + 2))*(1)=0 := by
      linear_combination (t/4 + 1/4)*h0+(-t/4 - w/4 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*t*w + w^2 + 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - t*w - 3*t + w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1+w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 + 5*t^2 - t + 3)=0 := by
      linear_combination (-t^2 - 3*t*w/2 - 11*t/2 + 3*w/2 + 1/2)*h0+(7*t*w/2 + t/2 - 3*w^2/2 - 7*w/2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (5) (-1) (3) u v t (cubic_no_rational_root 3) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - 2*t + w^2 - 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 3*t*w - t - w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1-w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (w : ℂ)≠0 := by
      intro hf
      have hh : points t w (4 : Fin 7)≠points t w 3 := fun h =>
        (show (4 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1+t)*(1-w))=((1+t)*(1+w))
      linear_combination (-2*t - 2)*hf
    have hn1 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hn2 : (t - w + 2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (1-t^2)+((1-t)*(1-w))-(0)=(0)
      linear_combination (1 - t)*hf
    have hA : (w) * (t) * (t - w + 2)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((w) * (t) * (t - w + 2))*(1)=0 := by
      linear_combination (-t/4 - 1/4)*h0+(t/4 - w/4 + 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 + 2*t*w - 2*t + w^2=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + t*w - t - 3*w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 + t^2 - t - 9)=0 := by
      linear_combination (-t^2 + 3*t*w/2 - 9*t/2 - 9*w/2 + 9/2)*h0+(-7*t*w/2 + 11*t/2 - 3*w^2/2 + 3*w/2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (-1) (-9) u v t (cubic_no_rational_root 2) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + 2*t*w + w^2 - 2*w=0 := by
      have hh := he.1
      change (1-t^2)+((1-t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + t*w - 3*t - w=0 := by
      have hh := he.2
      change (1-t^2)+((1-t)*(1-w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t : ℂ)≠0 := by
      intro hf
      have hh : points t w (5 : Fin 7)≠points t w 3 := fun h =>
        (show (5 : Fin 7)≠3 by decide) (hi h)
      apply hh
      change ((1-t)*(1+w))=((1+t)*(1+w))
      linear_combination (-2*w - 2)*hf
    have hA : (t)≠0 := by
      exact hn0
    have hprod : ((t))*(t^3 + 5*t^2 - t + 3)=0 := by
      linear_combination (-t^2 + 3*t*w/2 - 11*t/2 - 3*w/2 + 1/2)*h0+(-7*t*w/2 + t/2 - 3*w^2/2 + 7*w/2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (5) (-1) (3) u v t (cubic_no_rational_root 3) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -2*t - w^2 - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t^2 - w^2/2 - 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+(1-w^2)-(1-t^2)=(1-t^2)
      linear_combination (2)*hf
    have hA : (t^2 - w^2/2 - 1/2)≠0 := by
      exact hn0
    have hprod : ((t^2 - w^2/2 - 1/2))*(1)=0 := by
      linear_combination (1/4 - t/4)*h0+(t/4 + 1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -w^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(1)=0 := by
      linear_combination (w/4 - 1/2)*h0+(-w/4 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -2*t*w - w^2 - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t^2 - w^2/2 - 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+(1-w^2)-(1-t^2)=(1-t^2)
      linear_combination (2)*hf
    have hA : (t^2 - w^2/2 - 1/2)≠0 := by
      exact hn0
    have hprod : ((t^2 - w^2/2 - 1/2))*(1)=0 := by
      linear_combination (-t^2/2 + t*w/2 - w^2/8 + 1/8)*h0+(-t^2/2 + w^2/8 + 3/8)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : 2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : t*w + 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + t^2/3 + 5*t/3 - 1/3)=0 := by
      linear_combination (-t^2/6 + t*w/12 - t/12 + w/12 - 1/4)*h0+(t^2/3 + t/6 - w^2/12 + 7/12)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/3)) ((5/3)) ((-1/3)) u v t (cubic_no_rational_root 4) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : 2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : t*w + t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w/2 - 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1+t)*(1+w))-(1-t^2)=(1-t^2)
      linear_combination (2*t + 2)*hf
    have hA : (t + w/2 - 1/2)≠0 := by
      exact hn0
    have hprod : ((t + w/2 - 1/2))*(1)=0 := by
      linear_combination (t/8 + 3/8)*h0+(-t/4 - w/8 + 1/8)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : 2*t + w^2 + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 3*t*w + t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - t^2/9 - t/9 + 1/9)=0 := by
      linear_combination (t^2/2 + t/3 + 1/18)*h0+(-t*w/6 - 5*t/18 - w/18 - 1/6)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/9)) ((-1/9)) ((1/9)) u v t (cubic_no_rational_root 5) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t*w + 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + t^2/3 + 5*t/3 - 1/3)=0 := by
      linear_combination (-t^2/6 - t*w/12 - t/12 - w/12 - 1/4)*h0+(t^2/3 + t/6 - w^2/12 + 7/12)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/3)) ((5/3)) ((-1/3)) u v t (cubic_no_rational_root 4) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : 2*t + w^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -3*t*w + t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - t^2/9 - t/9 + 1/9)=0 := by
      linear_combination (t^2/2 + t/3 + 1/18)*h0+(t*w/6 - 5*t/18 + w/18 - 1/6)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/9)) ((-1/9)) ((1/9)) u v t (cubic_no_rational_root 5) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t*w + t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w/2 - 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1+t)*(1-w))-(1-t^2)=(1-t^2)
      linear_combination (2*t + 2)*hf
    have hA : (t - w/2 - 1/2)≠0 := by
      exact hn0
    have hprod : ((t - w/2 - 1/2))*(1)=0 := by
      linear_combination (t/8 + 3/8)*h0+(-t/4 + w/8 + 1/8)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t*w - t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w/2 + 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1-t)*(1+w))-(1-t^2)=(1-t^2)
      linear_combination (2*t - 2)*hf
    have hA : (t - w/2 + 1/2)≠0 := by
      exact hn0
    have hprod : ((t - w/2 + 1/2))*(1)=0 := by
      linear_combination (t/8 - 3/8)*h0+(-t/4 + w/8 - 1/8)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -2*t + w^2 + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -3*t*w - t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + t^2/9 - t/9 - 1/9)=0 := by
      linear_combination (-t^2/2 + t/3 - 1/18)*h0+(-t*w/6 - 5*t/18 + w/18 + 1/6)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/9)) ((-1/9)) ((-1/9)) u v t (cubic_no_rational_root 6) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t*w - 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - t^2/3 + 5*t/3 + 1/3)=0 := by
      linear_combination (t^2/6 + t*w/12 - t/12 - w/12 + 1/4)*h0+(-t^2/3 + t/6 + w^2/12 - 7/12)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/3)) ((5/3)) ((1/3)) u v t (cubic_no_rational_root 7) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -2*t + w^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 3*t*w - t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + t^2/9 - t/9 - 1/9)=0 := by
      linear_combination (-t^2/2 + t/3 - 1/18)*h0+(t*w/6 - 5*t/18 - w/18 + 1/6)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/9)) ((-1/9)) ((-1/9)) u v t (cubic_no_rational_root 6) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : 2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : t*w - t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + w/2 + 1/2 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1-t)*(1-w))-(1-t^2)=(1-t^2)
      linear_combination (2*t - 2)*hf
    have hA : (t + w/2 + 1/2)≠0 := by
      exact hn0
    have hprod : ((t + w/2 + 1/2))*(1)=0 := by
      linear_combination (t/8 - 3/8)*h0+(-t/4 - w/8 - 1/8)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : 2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : t*w - 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - t^2/3 + 5*t/3 + 1/3)=0 := by
      linear_combination (t^2/6 - t*w/12 - t/12 + w/12 + 1/4)*h0+(-t^2/3 + t/6 + w^2/12 - 7/12)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/3)) ((5/3)) ((1/3)) u v t (cubic_no_rational_root 7) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - 2*t - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(1)=0 := by
      linear_combination (t/4 - 1/2)*h0+(-t/4 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t^2 - 2*w^2 + 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+(1-t^2)-(1-w^2)=(1-w^2)
      linear_combination (-1)*hf
    have hA : (t^2 - 2*w^2 + 1)≠0 := by
      exact hn0
    have hprod : ((t^2 - 2*w^2 + 1))*(1)=0 := by
      linear_combination (w/2 - 1/2)*h0+(-w/2 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - 2*t*w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t^2 - 2*w^2 + 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+(1-t^2)-(1-w^2)=(1-w^2)
      linear_combination (-1)*hf
    have hA : (t^2 - 2*w^2 + 1)≠0 := by
      exact hn0
    have hprod : ((t^2 - 2*w^2 + 1))*(1)=0 := by
      linear_combination (-t*w/2 + w^2 - 1/2)*h0+(t*w/2 + w^2 - 1/2)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : t*w + 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 2*w - 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1+t)*(1+w))-(1-w^2)=(1-w^2)
      linear_combination (w + 1)*hf
    have hA : (t + 2*w - 1)≠0 := by
      exact hn0
    have hprod : ((t + 2*w - 1))*(1)=0 := by
      linear_combination (w/4 + 3/4)*h0+(-t/4 - w/2 + 1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : t*w + t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + 3*t^2 + 7*t - 3)=0 := by
      linear_combination (t + 3)*h0+(-2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (3) (7) (-3) u v t (cubic_no_rational_root 8) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 3*t*w + t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + 7*t^2/3 - t + 1/3)=0 := by
      linear_combination (t + 1/3)*h0+(-2/3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((7/3)) (-1) ((1/3)) u v t (cubic_no_rational_root 9) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t*w + 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 2*w - 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1+t)*(1-w))-(1-w^2)=(1-w^2)
      linear_combination (1 - w)*hf
    have hA : (t - 2*w - 1)≠0 := by
      exact hn0
    have hprod : ((t - 2*w - 1))*(1)=0 := by
      linear_combination (3/4 - w/4)*h0+(-t/4 + w/2 + 1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -3*t*w + t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + 7*t^2/3 - t + 1/3)=0 := by
      linear_combination (t + 1/3)*h0+(-2/3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((7/3)) (-1) ((1/3)) u v t (cubic_no_rational_root 9) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t*w + t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 + 3*t^2 + 7*t - 3)=0 := by
      linear_combination (t + 3)*h0+(-2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (3) (7) (-3) u v t (cubic_no_rational_root 8) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t*w - t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - 3*t^2 + 7*t + 3)=0 := by
      linear_combination (t - 3)*h0+(-2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-3) (7) (3) u v t (cubic_no_rational_root 10) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -3*t*w - t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - 7*t^2/3 - t - 1/3)=0 := by
      linear_combination (t - 1/3)*h0+(2/3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-7/3)) (-1) ((-1/3)) u v t (cubic_no_rational_root 11) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t*w - 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 2*w + 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1-t)*(1+w))-(1-w^2)=(1-w^2)
      linear_combination (-w - 1)*hf
    have hA : (t - 2*w + 1)≠0 := by
      exact hn0
    have hprod : ((t - 2*w + 1))*(1)=0 := by
      linear_combination (-w/4 - 3/4)*h0+(-t/4 + w/2 - 1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 3*t*w - t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - 7*t^2/3 - t - 1/3)=0 := by
      linear_combination (t - 1/3)*h0+(2/3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-7/3)) (-1) ((-1/3)) u v t (cubic_no_rational_root 11) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : t*w - t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hA : (1 : ℂ)≠0 := by
      norm_num
    have hprod : ((1 : ℂ))*(t^3 - 3*t^2 + 7*t + 3)=0 := by
      linear_combination (t - 3)*h0+(-2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-3) (7) (3) u v t (cubic_no_rational_root 10) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : t*w - 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 2*w + 1 : ℂ)≠0 := by
      intro hf
      apply hn
      change (0)+((1-t)*(1-w))-(1-w^2)=(1-w^2)
      linear_combination (w - 1)*hf
    have hA : (t + 2*w + 1)≠0 := by
      exact hn0
    have hprod : ((t + 2*w + 1))*(1)=0 := by
      linear_combination (w/4 - 3/4)*h0+(-t/4 - w/2 - 1/4)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 + t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hA : (t - 1) * (t - 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t - 1) * (t - 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 + t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + 3*t^2 - t + 5)=0 := by
      linear_combination (-t^2 - 2*t + 2*w + 1)*h0+(-2*t - w^2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (3) (-1) (5) u v t (cubic_no_rational_root 12) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - t^2/5 + 3*t/5 + 1/5)=0 := by
      linear_combination (-t^2 + 6*t*w/5 - 2*t/5 - 3/5)*h0+(4*t*w/5 - 2*t/5 - 3*w^2/5 - 2*w/5 + 3/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/5)) ((3/5)) ((1/5)) u v t (cubic_no_rational_root 13) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w - t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - 7*t^2 - t - 1)=0 := by
      linear_combination (t^2 - 2*t*w - 6*t + 3*w^2 + 4)*h0+(5*t*w - 5*t - 3*w^2 + 3*w - 4)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-7) (-1) (-1) u v t (cubic_no_rational_root 14) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w + t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hA : (w - 1) * (w - 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((w - 1) * (w - 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - t*w + t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + 7*t^2/5 - t + 1/5)=0 := by
      linear_combination (t^2 + 2*t/5 - w^2/5 - 2/5)*h0+(3*t*w/5 - t + w^2/5 - w/5 + 2/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((7/5)) (-1) ((1/5)) u v t (cubic_no_rational_root 15) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -t*w + 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + t^2 + 7*t - 1)=0 := by
      linear_combination (t^2 - 1)*h0+(t*w + 3*t - w + 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (7) (-1) u v t (cubic_no_rational_root 16) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - 1) * (w - 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w - 1) * (t - w))*(1)=0 := by
      linear_combination (1 - w)*h0+(-t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + 9*t^2 - t - 1)=0 := by
      linear_combination (t^2 + t*w + 7*t + 2*w^2 - 5*w - 2)*h0+(4*t*w - 6*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (9) (-1) (-1) u v t (cubic_no_rational_root 17) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -t*w - t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - 5*t^2 + 7*t + 5)=0 := by
      linear_combination (t^2 - 4*t + 3)*h0+(t*w - t - w - 3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-5) (7) (5) u v t (cubic_no_rational_root 18) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + t^2 - 9*t - 1)=0 := by
      linear_combination (t^2 - t*w + 3*t - w - 2)*h0+(2*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (-9) (-1) u v t (cubic_no_rational_root 19) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - 1) * (w - 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w - 1) * (t - w))*(1)=0 := by
      linear_combination (w + 1)*h0+(t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : 3*t*w - t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w) * (t - w)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t - w) * (t - w))*(1)=0 := by
      linear_combination (1)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - 1) * (w - 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w - 1) * (t - w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(t + 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - 1) * (w - 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w - 1) * (t - w))*(1)=0 := by
      linear_combination (1 - w)*h0+(t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hA : (t - 1) * (t - 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t - 1) * (t - 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 + t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*t*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - t^2/5 + 3*t/5 + 1/5)=0 := by
      linear_combination (-t^2 - 6*t*w/5 - 2*t/5 - 3/5)*h0+(-4*t*w/5 - 2*t/5 - 3*w^2/5 + 2*w/5 + 3/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-1/5)) ((3/5)) ((1/5)) u v t (cubic_no_rational_root 13) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + 3*t^2 - t + 5)=0 := by
      linear_combination (-t^2 - 2*t - 2*w + 1)*h0+(-2*t - w^2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (3) (-1) (5) u v t (cubic_no_rational_root 12) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w - t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - 7*t^2 - t - 1)=0 := by
      linear_combination (t^2 + 2*t*w - 6*t + 3*w^2 + 4)*h0+(-5*t*w - 5*t - 3*w^2 - 3*w - 4)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-7) (-1) (-1) u v t (cubic_no_rational_root 14) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w + t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t*w - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + 7*t^2/5 - t + 1/5)=0 := by
      linear_combination (t^2 + 2*t/5 - w^2/5 - 2/5)*h0+(-3*t*w/5 - t + w^2/5 + w/5 + 2/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((7/5)) (-1) ((1/5)) u v t (cubic_no_rational_root 15) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w + t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hA : (w + 1) * (w + 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((w + 1) * (w + 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : t*w + 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1-t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + t^2 + 7*t - 1)=0 := by
      linear_combination (t^2 - 1)*h0+(-t*w + 3*t + w + 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (7) (-1) u v t (cubic_no_rational_root 16) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + 9*t^2 - t - 1)=0 := by
      linear_combination (t^2 - t*w + 7*t + 2*w^2 + 5*w - 2)*h0+(-4*t*w - 6*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (9) (-1) (-1) u v t (cubic_no_rational_root 17) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t - 1) * (w + 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w + 1) * (t + w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(t + 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -3*t*w - t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w) * (t + w)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t + w) * (t + w))*(1)=0 := by
      linear_combination (1)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t - 1) * (w + 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w + 1) * (t + w))*(1)=0 := by
      linear_combination (1 - w)*h0+(-t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t - 1) * (w + 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w + 1) * (t + w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(1 - t)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : t*w - t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - 5*t^2 + 7*t + 5)=0 := by
      linear_combination (t^2 - 4*t + 3)*h0+(-t*w - t + w - 3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-5) (7) (5) u v t (cubic_no_rational_root 18) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + t^2 - 9*t - 1)=0 := by
      linear_combination (t^2 + t*w + 3*t + w - 2)*h0+(2*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (1) (-9) (-1) u v t (cubic_no_rational_root 19) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (-t - 1)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t - 1) * (w + 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t - 1) * (w + 1) * (t + w))*(1)=0 := by
      linear_combination (w - 1)*h0+(1 - t)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : -t^2 - t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - 3*t^2 - t - 5)=0 := by
      linear_combination (-t^2 + 2*t + 2*w + 1)*h0+(2*t - w^2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-3) (-1) (-5) u v t (cubic_no_rational_root 20) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*t*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + t^2/5 + 3*t/5 - 1/5)=0 := by
      linear_combination (-t^2 - 6*t*w/5 + 2*t/5 - 3/5)*h0+(-4*t*w/5 + 2*t/5 - 3*w^2/5 - 2*w/5 + 3/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/5)) ((3/5)) ((-1/5)) u v t (cubic_no_rational_root 21) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*t - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hA : (t + 1) * (t + 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t + 1) * (t + 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - t*w - t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hA : (w - 1) * (w - 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((w - 1) * (w - 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w - t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t*w - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - 7*t^2/5 - t - 1/5)=0 := by
      linear_combination (t^2 - 2*t/5 - w^2/5 - 2/5)*h0+(-3*t*w/5 + t + w^2/5 - w/5 + 2/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-7/5)) (-1) ((-1/5)) u v t (cubic_no_rational_root 22) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w + t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + 7*t^2 - t + 1)=0 := by
      linear_combination (t^2 + 2*t*w + 6*t + 3*w^2 + 4)*h0+(-5*t*w + 5*t - 3*w^2 + 3*w - 4)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (7) (-1) (1) u v t (cubic_no_rational_root 23) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : t*w + t + 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 + 5*t^2 + 7*t - 5)=0 := by
      linear_combination (t^2 + 4*t + 3)*h0+(-t*w + t - w - 3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (5) (7) (-5) u v t (cubic_no_rational_root 24) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + 1) * (w - 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w - 1) * (t + w))*(1)=0 := by
      linear_combination (w + 1)*h0+(-t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - t^2 - 9*t + 1)=0 := by
      linear_combination (t^2 + t*w - 3*t - w - 2)*h0+(2 - 2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (-9) (1) u v t (cubic_no_rational_root 25) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -3*t*w + t - w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w) * (t + w)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t + w) * (t + w))*(1)=0 := by
      linear_combination (1)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + 1) * (w - 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w - 1) * (t + w))*(1)=0 := by
      linear_combination (1 - w)*h0+(-t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + 1) * (w - 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w - 1) * (t + w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(1 - t)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : t*w - 3*t - w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - t^2 + 7*t + 1)=0 := by
      linear_combination (t^2 - 1)*h0+(-t*w - 3*t - w + 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (7) (1) u v t (cubic_no_rational_root 26) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w - 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (-w - 1)*hf
    have hn2 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + 1) * (w - 1) * (t + w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w - 1) * (t + w))*(1)=0 := by
      linear_combination (1 - w)*h0+(t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1-w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t - w)*hf
    have hA : (t + w)≠0 := by
      exact hn0
    have hprod : ((t + w))*(t^3 - 9*t^2 - t + 1)=0 := by
      linear_combination (t^2 - t*w - 7*t + 2*w^2 - 5*w - 2)*h0+(-4*t*w + 6*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-9) (-1) (1) u v t (cubic_no_rational_root 27) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 - t*w - t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 + 2*t*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + t^2/5 + 3*t/5 - 1/5)=0 := by
      linear_combination (-t^2 + 6*t*w/5 + 2*t/5 - 3/5)*h0+(4*t*w/5 + 2*t/5 - 3*w^2/5 + 2*w/5 + 3/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((1/5)) ((3/5)) ((-1/5)) u v t (cubic_no_rational_root 21) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - 3*t^2 - t - 5)=0 := by
      linear_combination (-t^2 + 2*t - 2*w + 1)*h0+(2*t - w^2 - 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-3) (-1) (-5) u v t (cubic_no_rational_root 20) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : -t^2 + t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-t^2)=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -t^2 - 2*t - 1=0 := by
      have hh := he.2
      change (0)+(1-t^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hA : (t + 1) * (t + 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t + 1) * (t + 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - t*w - t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t*w - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - 7*t^2/5 - t - 1/5)=0 := by
      linear_combination (t^2 - 2*t/5 - w^2/5 - 2/5)*h0+(3*t*w/5 + t + w^2/5 + w/5 + 2/5)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root ((-7/5)) (-1) ((-1/5)) u v t (cubic_no_rational_root 22) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w - t - w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hA : (w + 1) * (w + 1)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((w + 1) * (w + 1))*(1)=0 := by
      linear_combination (0)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + t*w + t - w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+(1-w^2)=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t - w^2 - 1=0 := by
      have hh := he.2
      change (0)+(1-w^2)=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + 7*t^2 - t + 1)=0 := by
      linear_combination (t^2 - 2*t*w + 6*t + 3*w^2 + 4)*h0+(5*t*w + 5*t - 3*w^2 - 3*w - 4)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (7) (-1) (1) u v t (cubic_no_rational_root 23) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 + t*w + t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : 3*t*w + t + w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=((1+t)*(1-w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w) * (t - w)≠0 := by
      exact (mul_ne_zero hn0 hn0)
    have hprod : ((t - w) * (t - w))*(1)=0 := by
      linear_combination (1)*h0+(-1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : 2*t*w + 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t + 1) * (w + 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w + 1) * (t - w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(t + 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t*w + 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1+w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t*w + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t + 1) * (w + 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w + 1) * (t - w))*(1)=0 := by
      linear_combination (1 - w)*h0+(t - 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 - t*w + t + w^2 - w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -t*w + t - 3*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=((1+t)*(1+w))+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 + 5*t^2 + 7*t - 5)=0 := by
      linear_combination (t^2 + 4*t + 3)*h0+(t*w + t + w - 3)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (5) (7) (-5) u v t (cubic_no_rational_root 24) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : 2*t + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t + 1) * (w + 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w + 1) * (t - w))*(1)=0 := by
      linear_combination (w - 1)*h0+(t + 1)*h1
    apply hA
    simpa only [mul_one] using hprod
  · have h0 : t^2 + 2*t - 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1+t)*(1-w))=(1-t^2)+((1-t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t*w + w^2 - 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1+t)*(1-w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - t^2 - 9*t + 1)=0 := by
      linear_combination (t^2 - t*w - 3*t + w - 2)*h0+(2 - 2*t)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (-9) (1) u v t (cubic_no_rational_root 25) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - t*w - t + w^2 + w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+(1-w^2) at hh
      linear_combination hh
    have h1 : -t*w - 3*t + w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=((1+t)*(1+w))+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - t^2 + 7*t + 1)=0 := by
      linear_combination (t^2 - 1)*h0+(t*w - 3*t + w + 1)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-1) (7) (1) u v t (cubic_no_rational_root 26) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t*w - 2*t - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have h1 : -2*t + w^2 + 2*w - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have hn0 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t - w)≠0 := by
      exact hn0
    have hprod : ((t - w))*(t^3 - 9*t^2 - t + 1)=0 := by
      linear_combination (t^2 + t*w - 7*t + 2*w^2 + 5*w - 2)*h0+(4*t*w + 6*t + 2)*h1
    have hc := (mul_eq_zero.mp hprod).resolve_left hA
    apply no_quadratic_root (-9) (-1) (1) u v t (cubic_no_rational_root 27) hq
    convert hc using 1
    norm_num
    ring
  · have h0 : t^2 - 2*t + 2*w - 1=0 := by
      have hh := he.1
      change (0)+((1-t)*(1+w))=(1-t^2)+((1+t)*(1-w)) at hh
      linear_combination hh
    have h1 : -2*t*w - 2*t + w^2 - 1=0 := by
      have hh := he.2
      change (0)+((1-t)*(1+w))=(1-w^2)+((1+t)*(1+w)) at hh
      linear_combination hh
    have hn0 : (t + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (1 : Fin 7)≠points t w 0 := fun h =>
        (show (1 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-t^2)=(0)
      linear_combination (1 - t)*hf
    have hn1 : (w + 1 : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 0 := fun h =>
        (show (2 : Fin 7)≠0 by decide) (hi h)
      apply hh
      change (1-w^2)=(0)
      linear_combination (1 - w)*hf
    have hn2 : (t - w : ℂ)≠0 := by
      intro hf
      have hh : points t w (2 : Fin 7)≠points t w 1 := fun h =>
        (show (2 : Fin 7)≠1 by decide) (hi h)
      apply hh
      change (1-w^2)=(1-t^2)
      linear_combination (t + w)*hf
    have hA : (t + 1) * (w + 1) * (t - w)≠0 := by
      exact (mul_ne_zero (mul_ne_zero hn0 hn1) hn2)
    have hprod : ((t + 1) * (w + 1) * (t - w))*(1)=0 := by
      linear_combination (-w - 1)*h0+(1 - t)*h1
    apply hA
    simpa only [mul_one] using hprod

#print axioms cubic_no_rational_root
#print axioms no_reflection_case
end
end Erdos213.CentralReflection
