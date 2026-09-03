import Submission.CubicInverseHeight

/-!
The common cancellation factor cannot be bounded by choosing among the 24
signed permutation charts of the existing cubic parametrization. This is an
obstruction to a proposed height argument, not a settlement of Erdős 1206.
-/

set_option maxHeartbeats 2000000
set_option Elab.async false

namespace Erdos1206.ChartCancellation
open CubicBaseLocus

structure Data where
  x : ℤ
  y : ℤ
  z : ℤ
  w : ℤ
  a : ℤ
  b : ℤ
  c : ℤ
  g : ℤ
  u : ℤ
  v : ℤ
  r : ℤ

def q (t : ℤ) := 3*t^2+3*t+1
def r (t : ℤ) := 3*t^2-1
def s (t : ℤ) := 9*t^4-9*t^3+9*t^2-3*t+1
def u (t : ℤ) := 9*t^4+3*t^2+1
def v (t : ℤ) := 27*t^6+9*t^3+1

def chart (i : Fin 24) (t : ℤ) : Data :=
  match i.val with
  | 0 => ⟨1, 9 * t ^ 4, 9 * t ^ 3 + 1, 9 * t ^ 4 + 3 * t, 27 * t ^ 6 - 54 * t ^ 5 + 18 * t ^ 4 - 9 * t ^ 3 - 6 * t ^ 2 - 1, 54 * t ^ 6 - 54 * t ^ 5 + 36 * t ^ 4 - 12 * t ^ 2 + 6 * t - 2, 81 * t ^ 6 + 27 * t ^ 3 + 3, (72) * (u t * v t * s t), -90 * t ^ 5 + 108 * t ^ 4 - 54 * t ^ 3 - 6 * t ^ 2 + 26 * t - 10, 45 * t ^ 5 - 99 * t ^ 4 + 36 * t ^ 3 - 7 * t + 2, 0⟩
  | 1 => ⟨1, 9 * t ^ 4, -9 * t ^ 4 - 3 * t, -9 * t ^ 3 - 1, -6 * t ^ 2 - 3 * t, -6 * t ^ 2 + 2, 3 * t, (-24) * q t, 18 * t - 12, -18 * t + 3, 0⟩
  | 2 => ⟨1, 9 * t ^ 3 + 1, 9 * t ^ 4, 9 * t ^ 4 + 3 * t, -3 * t ^ 2 + t + 1, 2 * t, 3 * t ^ 2 + 3 * t + 1, (8) * q t, 6, 9 * t - 3, 0⟩
  | 3 => ⟨1, 9 * t ^ 3 + 1, -9 * t ^ 4 - 3 * t, -9 * t ^ 4, -27 * t ^ 6 - 9 * t ^ 5 - 12 * t ^ 3 - t - 1, -18 * t ^ 5 - 6 * t ^ 3 - 2 * t, 27 * t ^ 6 - 27 * t ^ 5 + 18 * t ^ 4 - 6 * t ^ 2 + 3 * t - 1, (-8) * (u t * v t * s t), 54 * t ^ 4 + 54 * t ^ 3 + 18 * t ^ 2 - 6, -81 * t ^ 5 - 108 * t ^ 4 - 27 * t ^ 3 - 9 * t ^ 2 - 9 * t + 3, 0⟩
  | 4 => ⟨1, -9 * t ^ 4 - 3 * t, 9 * t ^ 4, -9 * t ^ 3 - 1, -54 * t ^ 6 + 27 * t ^ 5 - 18 * t ^ 4 - 9 * t ^ 3 + 6 * t ^ 2 - 3 * t, -54 * t ^ 6 - 18 * t ^ 3 - 2, -27 * t ^ 5 - 9 * t ^ 3 - 3 * t, (24) * (u t * v t * s t), -162 * t ^ 5 - 54 * t ^ 4 - 36 * t ^ 2 - 18 * t, 162 * t ^ 5 - 27 * t ^ 4 + 27 * t ^ 3 + 27 * t ^ 2 - 3, 0⟩
  | 5 => ⟨1, -9 * t ^ 4 - 3 * t, 9 * t ^ 3 + 1, -9 * t ^ 4, -3 * t ^ 2 - 6 * t - 1, -6 * t ^ 2 - 6 * t - 2, -9 * t ^ 2 + 3, (72) * q t, 6 * t + 6, -3 * t - 6, 0⟩
  | 6 => ⟨-9 * t ^ 4, -1, 9 * t ^ 3 + 1, 9 * t ^ 4 + 3 * t, -3 * t - 2, 6 * t ^ 2 - 2, 3 * t, (24) * q t, 18 * t - 12, 9, 0⟩
  | 7 => ⟨-9 * t ^ 4, -1, -9 * t ^ 4 - 3 * t, -9 * t ^ 3 - 1, -27 * t ^ 6 - 18 * t ^ 4 - 9 * t ^ 3 + 6 * t ^ 2 - 6 * t + 1, -54 * t ^ 6 + 54 * t ^ 5 - 36 * t ^ 4 + 12 * t ^ 2 - 6 * t + 2, 81 * t ^ 6 + 27 * t ^ 3 + 3, (-72) * (u t * v t * s t), -90 * t ^ 5 + 108 * t ^ 4 - 54 * t ^ 3 - 6 * t ^ 2 + 26 * t - 10, 45 * t ^ 5 - 9 * t ^ 4 + 18 * t ^ 3 + 6 * t ^ 2 - 19 * t + 8, 0⟩
  | 8 => ⟨-9 * t ^ 4, 9 * t ^ 3 + 1, -1, 9 * t ^ 4 + 3 * t, 27 * t ^ 5 - 18 * t ^ 4 + 9 * t ^ 3 + 6 * t ^ 2 - 3 * t + 2, 54 * t ^ 6 + 18 * t ^ 3 + 2, 27 * t ^ 5 + 9 * t ^ 3 + 3 * t, (24) * (u t * v t * s t), -162 * t ^ 5 - 54 * t ^ 4 - 36 * t ^ 2 - 18 * t, 81 * t ^ 4 - 27 * t ^ 3 + 9 * t ^ 2 + 18 * t + 3, 0⟩
  | 9 => ⟨-9 * t ^ 4, 9 * t ^ 3 + 1, -9 * t ^ 4 - 3 * t, 1, -3 * t ^ 2 - 6 * t - 1, -6 * t ^ 2 - 6 * t - 2, 9 * t ^ 2 - 3, (-72) * q t, 6 * t + 6, -3 * t - 6, 0⟩
  | 10 => ⟨-9 * t ^ 4, -9 * t ^ 4 - 3 * t, -1, -9 * t ^ 3 - 1, -3 * t ^ 2 - t + 1, -2 * t, -3 * t ^ 2 - 3 * t - 1, (8) * q t, 6, -9 * t - 3, 0⟩
  | 11 => ⟨-9 * t ^ 4, -9 * t ^ 4 - 3 * t, 9 * t ^ 3 + 1, 1, -27 * t ^ 6 - 9 * t ^ 5 - 12 * t ^ 3 - t - 1, -18 * t ^ 5 - 6 * t ^ 3 - 2 * t, -27 * t ^ 6 + 27 * t ^ 5 - 18 * t ^ 4 + 6 * t ^ 2 - 3 * t + 1, (8) * (u t * v t * s t), 54 * t ^ 4 + 54 * t ^ 3 + 18 * t ^ 2 - 6, -81 * t ^ 5 - 108 * t ^ 4 - 27 * t ^ 3 - 9 * t ^ 2 - 9 * t + 3, 0⟩
  | 12 => ⟨-9 * t ^ 3 - 1, -1, 9 * t ^ 4, 9 * t ^ 4 + 3 * t, -27 * t ^ 6 + 9 * t ^ 5 - 6 * t ^ 3 + t - 1, 18 * t ^ 5 + 6 * t ^ 3 + 2 * t, 27 * t ^ 6 - 27 * t ^ 5 + 18 * t ^ 4 - 6 * t ^ 2 + 3 * t - 1, (8) * (u t * v t * s t), 54 * t ^ 4 + 54 * t ^ 3 + 18 * t ^ 2 - 6, 81 * t ^ 5 + 54 * t ^ 4 - 27 * t ^ 3 - 9 * t ^ 2 + 9 * t + 3, 0⟩
  | 13 => ⟨-9 * t ^ 3 - 1, -1, -9 * t ^ 4 - 3 * t, -9 * t ^ 4, -3 * t ^ 2 - t + 1, -2 * t, 3 * t ^ 2 + 3 * t + 1, (-8) * q t, 6, -9 * t - 3, 0⟩
  | 14 => ⟨-9 * t ^ 3 - 1, 9 * t ^ 4, -1, 9 * t ^ 4 + 3 * t, 3 * t ^ 2 + 1, 6 * t ^ 2 + 6 * t + 2, 9 * t ^ 2 - 3, (72) * q t, 6 * t + 6, -3 * t, 0⟩
  | 15 => ⟨-9 * t ^ 3 - 1, 9 * t ^ 4, -9 * t ^ 4 - 3 * t, 1, -54 * t ^ 6 + 27 * t ^ 5 - 18 * t ^ 4 - 9 * t ^ 3 + 6 * t ^ 2 - 3 * t, -54 * t ^ 6 - 18 * t ^ 3 - 2, 27 * t ^ 5 + 9 * t ^ 3 + 3 * t, (-24) * (u t * v t * s t), -162 * t ^ 5 - 54 * t ^ 4 - 36 * t ^ 2 - 18 * t, 162 * t ^ 5 - 27 * t ^ 4 + 27 * t ^ 3 + 27 * t ^ 2 - 3, 0⟩
  | 16 => ⟨-9 * t ^ 3 - 1, -9 * t ^ 4 - 3 * t, -1, -9 * t ^ 4, -27 * t ^ 6 - 18 * t ^ 4 - 9 * t ^ 3 + 6 * t ^ 2 - 6 * t + 1, -54 * t ^ 6 + 54 * t ^ 5 - 36 * t ^ 4 + 12 * t ^ 2 - 6 * t + 2, -81 * t ^ 6 - 27 * t ^ 3 - 3, (72) * (u t * v t * s t), -90 * t ^ 5 + 108 * t ^ 4 - 54 * t ^ 3 - 6 * t ^ 2 + 26 * t - 10, 45 * t ^ 5 - 9 * t ^ 4 + 18 * t ^ 3 + 6 * t ^ 2 - 19 * t + 8, 0⟩
  | 17 => ⟨-9 * t ^ 3 - 1, -9 * t ^ 4 - 3 * t, 9 * t ^ 4, 1, -6 * t ^ 2 - 3 * t, -6 * t ^ 2 + 2, -3 * t, (24) * q t, 18 * t - 12, -18 * t + 3, 0⟩
  | 18 => ⟨9 * t ^ 4 + 3 * t, -1, 9 * t ^ 4, -9 * t ^ 3 - 1, 3 * t ^ 2 + 1, 6 * t ^ 2 + 6 * t + 2, -9 * t ^ 2 + 3, (-72) * q t, 6 * t + 6, -3 * t, 0⟩
  | 19 => ⟨9 * t ^ 4 + 3 * t, -1, 9 * t ^ 3 + 1, -9 * t ^ 4, 27 * t ^ 5 - 18 * t ^ 4 + 9 * t ^ 3 + 6 * t ^ 2 - 3 * t + 2, 54 * t ^ 6 + 18 * t ^ 3 + 2, -27 * t ^ 5 - 9 * t ^ 3 - 3 * t, (-24) * (u t * v t * s t), -162 * t ^ 5 - 54 * t ^ 4 - 36 * t ^ 2 - 18 * t, 81 * t ^ 4 - 27 * t ^ 3 + 9 * t ^ 2 + 18 * t + 3, 0⟩
  | 20 => ⟨9 * t ^ 4 + 3 * t, 9 * t ^ 4, -1, -9 * t ^ 3 - 1, -27 * t ^ 6 + 9 * t ^ 5 - 6 * t ^ 3 + t - 1, 18 * t ^ 5 + 6 * t ^ 3 + 2 * t, -27 * t ^ 6 + 27 * t ^ 5 - 18 * t ^ 4 + 6 * t ^ 2 - 3 * t + 1, (-8) * (u t * v t * s t), 54 * t ^ 4 + 54 * t ^ 3 + 18 * t ^ 2 - 6, 81 * t ^ 5 + 54 * t ^ 4 - 27 * t ^ 3 - 9 * t ^ 2 + 9 * t + 3, 0⟩
  | 21 => ⟨9 * t ^ 4 + 3 * t, 9 * t ^ 4, 9 * t ^ 3 + 1, 1, -3 * t ^ 2 + t + 1, 2 * t, -3 * t ^ 2 - 3 * t - 1, (-8) * q t, 6, 9 * t - 3, 0⟩
  | 22 => ⟨9 * t ^ 4 + 3 * t, 9 * t ^ 3 + 1, -1, -9 * t ^ 4, -3 * t - 2, 6 * t ^ 2 - 2, -3 * t, (-24) * q t, 18 * t - 12, 9, 0⟩
  | _ => ⟨9 * t ^ 4 + 3 * t, 9 * t ^ 3 + 1, 9 * t ^ 4, 1, 27 * t ^ 6 - 54 * t ^ 5 + 18 * t ^ 4 - 9 * t ^ 3 - 6 * t ^ 2 - 1, 54 * t ^ 6 - 54 * t ^ 5 + 36 * t ^ 4 - 12 * t ^ 2 + 6 * t - 2, -81 * t ^ 6 - 27 * t ^ 3 - 3, (-72) * (u t * v t * s t), -90 * t ^ 5 + 108 * t ^ 4 - 54 * t ^ 3 - 6 * t ^ 2 + 26 * t - 10, 45 * t ^ 5 - 99 * t ^ 4 + 36 * t ^ 3 - 7 * t + 2, 0⟩

lemma chart_identity (i : Fin 24) (t : ℤ) :
    A (chart i t).a (chart i t).b (chart i t).c = (chart i t).g * (chart i t).x ∧
    B (chart i t).a (chart i t).b (chart i t).c = (chart i t).g * (chart i t).y ∧
    C (chart i t).a (chart i t).b (chart i t).c = (chart i t).g * (chart i t).z ∧
    D (chart i t).a (chart i t).b (chart i t).c = (chart i t).g * (chart i t).w := by
  fin_cases i <;> dsimp [chart, A, B, C, D, Q, q, u, v, s]
  all_goals exact ⟨by ring, by ring, by ring, by ring⟩

lemma chart_bezout (i : Fin 24) (t : ℤ) :
    (chart i t).a * (chart i t).u + (chart i t).b * (chart i t).v +
      (chart i t).c * (chart i t).r = 6 := by
  fin_cases i <;> norm_num [chart] <;> ring

lemma factors_positive {t : ℤ} (ht : 1 ≤ t) :
    0 < q t ∧ 0 < r t ∧ 0 < s t ∧ 0 < u t ∧ 0 < v t := by
  have ht0 : 0 < t := by omega
  have ht2 : 1 ≤ t^2 := by nlinarith
  have ht3 : 0 ≤ t^3 := by positivity
  have ht4 : 0 ≤ t^4 := by positivity
  have hsub : 0 ≤ t-1 := by omega
  have hsub3 : 0 ≤ 3*t-1 := by omega
  have hts : 0 ≤ 9*t^3*(t-1) := by positivity
  have hs : s t = 9*t^3*(t-1) + 3*t*(3*t-1) + 1 := by dsimp [s]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [q]; positivity
  · dsimp [r]; omega
  · rw [hs]; have : 0 ≤ 3*t*(3*t-1) := by positivity
    omega
  · dsimp [u]; positivity
  · dsimp [v]; positivity

lemma chart_x_ne_zero (i : Fin 24) {t : ℤ} (ht : 1 ≤ t) :
    (chart i t).x ≠ 0 := by
  have ht0 : 0 < t := by omega
  fin_cases i <;> norm_num [chart] <;> nlinarith [pow_pos ht0 3, pow_pos ht0 4]

lemma chart_inverse_ne_zero (i : Fin 24) {t : ℤ} (ht : 1 ≤ t) :
    inverseT (chart i t).x (chart i t).y (chart i t).z (chart i t).w ≠ 0 := by
  obtain ⟨hq,hr,hs,hu,hv⟩ := factors_positive ht
  have ht0 : t ≠ 0 := by omega
  have hf (j : Fin 24) : inverseT (chart j t).x (chart j t).y (chart j t).z (chart j t).w =
    (match j.val with
     | 0 => 9 * (t) * (v t)
     | 1 => 9 * (t) * (v t)
     | 2 => 3 * (q t) * (r t) * (s t)
     | 3 => 3 * (q t) * (r t) * (s t)
     | 4 => -9 * (t) * (r t) * (u t)
     | 5 => -9 * (t) * (r t) * (u t)
     | 6 => 9 * (t) * (v t)
     | 7 => 9 * (t) * (v t)
     | 8 => 9 * (t) * (r t) * (u t)
     | 9 => 9 * (t) * (r t) * (u t)
     | 10 => -3 * (q t) * (r t) * (s t)
     | 11 => -3 * (q t) * (r t) * (s t)
     | 12 => 3 * (q t) * (r t) * (s t)
     | 13 => 3 * (q t) * (r t) * (s t)
     | 14 => 9 * (t) * (r t) * (u t)
     | 15 => 9 * (t) * (r t) * (u t)
     | 16 => -9 * (t) * (v t)
     | 17 => -9 * (t) * (v t)
     | 18 => -9 * (t) * (r t) * (u t)
     | 19 => -9 * (t) * (r t) * (u t)
     | 20 => -3 * (q t) * (r t) * (s t)
     | 21 => -3 * (q t) * (r t) * (s t)
     | 22 => -9 * (t) * (v t)
     | _ => -9 * (t) * (v t)
    ) := by
    fin_cases j <;> norm_num [chart, inverseT, q, r, s, u, v] <;> ring
  rw [hf]
  fin_cases i <;> norm_num only [Fin.reduceFinMk] <;>
    simp_all only [mul_ne_zero_iff, ne_eq, hq.ne', hr.ne', hs.ne', hu.ne', hv.ne', ht0, not_false_eq_true, and_self, OfNat.ofNat_ne_zero] <;> norm_num

lemma chart_scale_lower (i : Fin 24) {t : ℤ} (ht : 1 ≤ t) :
    8*t^2 ≤ |(chart i t).g| := by
  obtain ⟨hq,hr,hs,hu,hv⟩ := factors_positive ht
  have hq2 : t^2 ≤ q t := by dsimp [q]; nlinarith [sq_nonneg t]
  have hu2 : t^2 ≤ u t := by dsimp [u]; nlinarith [sq_nonneg (t^2)]
  have hv1 : 1 ≤ v t := hv
  have hs1 : 1 ≤ s t := hs
  have hprod : t^2 ≤ u t * v t * s t := by
    have h1 : u t ≤ u t * v t := le_mul_of_one_le_right hu.le hv1
    have h2 : u t * v t ≤ u t * v t * s t :=
      le_mul_of_one_le_right (mul_pos hu hv).le hs1
    exact hu2.trans (h1.trans h2)
  fin_cases i <;> norm_num [chart, abs_mul, abs_of_pos hq,
    abs_of_pos (mul_pos (mul_pos hu hv) hs), abs_of_pos hu, abs_of_pos hv, abs_of_pos hs] <;> nlinarith

lemma certificate_cross_general {a b t g x y z w : ℤ} (hg : g ≠ 0)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    t*inverseA x y z w = a*inverseT x y z w ∧
    t*inverseB x y z w = b*inverseT x y z w := by
  obtain ⟨hu,hv⟩ := inverse_cross_identities a b t
  obtain ⟨hiA,hiB,hiT⟩ := inverse_homogeneous x y z w g
  rw [hA,hB,hC,hD,hiA,hiT] at hu
  rw [hA,hB,hC,hD,hiB,hiT] at hv
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 2 hg)
    nlinarith only [hu]
  · apply mul_left_cancel₀ (pow_ne_zero 2 hg)
    nlinarith only [hv]

lemma primitive_collinear_integer_signed {a b t u v q : ℤ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (ht : t ≠ 0) (hu : t*u=a*q) (hv : t*v=b*q) :
    ∃ m : ℤ, u=m*a ∧ v=m*b ∧ q=m*t := by
  let d := Int.gcd a b
  let α : ℤ := Int.gcdA a b * Int.gcdA (d : ℤ) t
  let β : ℤ := Int.gcdB a b * Int.gcdA (d : ℤ) t
  let γ : ℤ := Int.gcdB (d : ℤ) t
  have hdt : Int.gcd (d : ℤ) t = 1 := by simpa [Int.gcd_eq_natAbs,d] using hprim
  have hlin : a*α+b*β+t*γ=1 := by
    have hd := Int.gcd_eq_gcd_ab a b
    have hh := Int.gcd_eq_gcd_ab (d : ℤ) t
    rw [hdt] at hh
    calc
      _ = (d : ℤ)*Int.gcdA (d : ℤ) t+t*Int.gcdB (d : ℤ) t := by
        dsimp only [α,β,γ,d]
        rw [hd]
        ring
      _ = 1 := by simpa using hh.symm
  let m : ℤ := u*α+v*β+q*γ
  have htm : t*m=q := by
    calc
      _ = (t*u)*α+(t*v)*β+q*t*γ := by dsimp [m]; ring
      _ = q*(a*α+b*β+t*γ) := by rw [hu,hv]; ring
      _ = q := by rw [hlin,mul_one]
  refine ⟨m,?_,?_,by linarith⟩
  · apply mul_left_cancel₀ ht
    nlinarith only [hu,congrArg (fun s : ℤ => a*s) htm]
  · apply mul_left_cancel₀ ht
    nlinarith only [hv,congrArg (fun s : ℤ => b*s) htm]

lemma certificate_scale_bound {a b t g x y z w α β τ G U V W : ℤ}
    (hg : g ≠ 0) (hG : G ≠ 0) (hx : x ≠ 0)
    (hInv : inverseT x y z w ≠ 0)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    (hα : A α β τ = G*x) (hβ : B α β τ = G*y)
    (hτ : C α β τ = G*z) (hδ : D α β τ = G*w)
    (hBez : α*U+β*V+τ*W=6) : |G| ≤ 216 * |g| := by
  obtain ⟨hcA,hcB⟩ := certificate_cross_general hg hA hB hC hD
  obtain ⟨hcα,hcβ⟩ := certificate_cross_general hG hα hβ hτ hδ
  have ht : t ≠ 0 := by
    intro ht
    have ha : a = 0 := (mul_eq_zero.mp (by simpa [ht] using hcA.symm)).resolve_right hInv
    have hb : b = 0 := (mul_eq_zero.mp (by simpa [ht] using hcB.symm)).resolve_right hInv
    simp [ha,hb,ht] at hprim
  have hcrossA : t*α=a*τ := by
    apply mul_right_cancel₀ hInv
    linear_combination τ*hcA-t*hcα
  have hcrossB : t*β=b*τ := by
    apply mul_right_cancel₀ hInv
    linear_combination τ*hcB-t*hcβ
  obtain ⟨m,hmα,hmβ,hmτ⟩ := primitive_collinear_integer_signed hprim ht hcrossA hcrossB
  have hm6 : m ∣ (6 : ℤ) := by
    rw [← hBez,hmα,hmβ,hmτ]
    exact ⟨a*U+b*V+t*W,by ring⟩
  have hmabs : |m| ≤ 6 := by
    have hh := Int.natAbs_le_of_dvd_ne_zero hm6 (by norm_num)
    have hh' : (m.natAbs : ℤ) ≤ 6 := by exact_mod_cast hh
    simpa using hh'
  have hGg : G = m^3*g := by
    apply mul_right_cancel₀ hx
    calc
      G*x = A α β τ := hα.symm
      _ = m^3*A a b t := by rw [hmα,hmβ,hmτ,(homogeneous a b t m).1]
      _ = (m^3*g)*x := by rw [hA]; ring
  rw [hGg,abs_mul,abs_pow]
  have hm3 : |m|^3 ≤ (6:ℤ)^3 := pow_le_pow_left₀ (abs_nonneg m) hmabs 3
  exact mul_le_mul_of_nonneg_right (by norm_num at hm3 ⊢; exact hm3) (abs_nonneg g)


lemma chart_cancellation_lower (i : Fin 24) {T : ℤ} (hT : 1 ≤ T)
    {a b t g : ℤ} (hg : g ≠ 0)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*(chart i T).x) (hB : B a b t = g*(chart i T).y)
    (hC : C a b t = g*(chart i T).z) (hD : D a b t = g*(chart i T).w) :
    8*T^2 ≤ 216*|g| := by
  have hscale := chart_scale_lower i hT
  have hG : (chart i T).g ≠ 0 := by
    intro h
    rw [h,abs_zero] at hscale
    nlinarith [sq_nonneg (T-1)]
  obtain ⟨hα,hβ,hτ,hδ⟩ := chart_identity i T
  have hb := certificate_scale_bound hg hG (chart_x_ne_zero i hT)
    (chart_inverse_ne_zero i hT) hprim hA hB hC hD hα hβ hτ hδ (chart_bezout i T)
  exact hscale.trans hb

def signedFamily (t : ℤ) : Fin 4 → ℤ := ![1, -9*t^4, -(9*t^3+1), 9*t^4+3*t]

def chartIndices (i : Fin 24) : Fin 4 → Fin 4 :=
  match i.val with
  | 0 => ![0, 1, 2, 3]
  | 1 => ![0, 1, 3, 2]
  | 2 => ![0, 2, 1, 3]
  | 3 => ![0, 2, 3, 1]
  | 4 => ![0, 3, 1, 2]
  | 5 => ![0, 3, 2, 1]
  | 6 => ![1, 0, 2, 3]
  | 7 => ![1, 0, 3, 2]
  | 8 => ![1, 2, 0, 3]
  | 9 => ![1, 2, 3, 0]
  | 10 => ![1, 3, 0, 2]
  | 11 => ![1, 3, 2, 0]
  | 12 => ![2, 0, 1, 3]
  | 13 => ![2, 0, 3, 1]
  | 14 => ![2, 1, 0, 3]
  | 15 => ![2, 1, 3, 0]
  | 16 => ![2, 3, 0, 1]
  | 17 => ![2, 3, 1, 0]
  | 18 => ![3, 0, 1, 2]
  | 19 => ![3, 0, 2, 1]
  | 20 => ![3, 1, 0, 2]
  | 21 => ![3, 1, 2, 0]
  | 22 => ![3, 2, 0, 1]
  | _ => ![3, 2, 1, 0]

lemma chartIndices_injective (i : Fin 24) : Function.Injective (chartIndices i) := by
  fin_cases i <;> decide

lemma chartIndices_exhaustive (p : Fin 4 → Fin 4) (hp : Function.Injective p) :
    ∃ i : Fin 24, ∀ j, chartIndices i j = p j := by
  have h : ∀ p : Fin 4 → Fin 4, Function.Injective p →
      ∃ i : Fin 24, ∀ j, chartIndices i j = p j := by decide +kernel
  exact h p hp

lemma chart_roots (i : Fin 24) (t : ℤ) :
    (chart i t).x = signedFamily t (chartIndices i 0) ∧
    (chart i t).y = -signedFamily t (chartIndices i 1) ∧
    (chart i t).z = -signedFamily t (chartIndices i 2) ∧
    (chart i t).w = signedFamily t (chartIndices i 3) := by
  fin_cases i <;> norm_num [chart,chartIndices,signedFamily, Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals repeat' constructor
  all_goals ring

lemma permutation_cancellation_lower {T : ℤ} (hT : 1 ≤ T)
    (p : Equiv.Perm (Fin 4)) {a b t g : ℤ} (hg : g ≠ 0)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*signedFamily T (p 0))
    (hB : B a b t = -g*signedFamily T (p 1))
    (hC : C a b t = -g*signedFamily T (p 2))
    (hD : D a b t = g*signedFamily T (p 3)) : 8*T^2 ≤ 216*|g| := by
  obtain ⟨i,hi⟩ := chartIndices_exhaustive p p.injective
  obtain ⟨hx,hy,hz,hw⟩ := chart_roots i T
  simp only [hi] at hx hy hz hw
  apply chart_cancellation_lower i hT hg hprim
  · simpa only [hx] using hA
  · simpa only [hy,mul_neg,neg_mul] using hB
  · simpa only [hz,mul_neg,neg_mul] using hC
  · simpa only [hw] using hD

/-- No uniform bound on primitive-certificate cancellation can be obtained
by choosing one of the 24 signed permutation charts for each collision. -/
theorem unbounded_cancellation_all_permutations (K : ℕ) :
    ∃ T : ℕ, 2 ≤ T ∧
      1+(9*T^4+3*T)^3=(9*T^4)^3+(9*T^3+1)^3 ∧
      ∀ p : Equiv.Perm (Fin 4), ∀ a b t g : ℤ, g ≠ 0 →
        Nat.gcd (Int.gcd a b) t.natAbs = 1 →
        A a b t = g*signedFamily T (p 0) →
        B a b t = -g*signedFamily T (p 1) →
        C a b t = -g*signedFamily T (p 2) →
        D a b t = g*signedFamily T (p 3) → K < g.natAbs := by
  let T := 216*(K+1)+1
  refine ⟨T,by dsimp [T]; omega,by ring,?_⟩
  intro p a b t g hg hp hA hB hC hD
  have hT : (1 : ℤ) ≤ T := by dsimp [T]; omega
  have hh := permutation_cancellation_lower hT p hg hp hA hB hC hD
  have hK : (216 : ℤ)*K < 8*(T : ℤ)^2 := by
    dsimp [T]
    push_cast
    nlinarith [sq_nonneg (K : ℤ)]
  have hlt : (K : ℤ) < |g| := by nlinarith
  rw [← Int.natCast_natAbs] at hlt
  exact_mod_cast hlt

#print axioms chart_cancellation_lower
#print axioms permutation_cancellation_lower
#print axioms unbounded_cancellation_all_permutations

end Erdos1206.ChartCancellation
