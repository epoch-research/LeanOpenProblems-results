import Submission.TwoAnchorGeometry

/-! A moving-anchor degree bound and a genuine cubic positive control.
These are rational-function identities, not a settlement of Erdős 213. -/
namespace Erdos213.MovingAnchorPolynomial
open Polynomial EuclideanGeometry GeneralQuadraticType
noncomputable section
set_option maxHeartbeats 2000000

/-- A radial polynomial motion off the real axis, at square polynomial
distance from the moving anchor `t`, has degree at most two. No incidence
assumption at the initial parameter and no a priori degree bound are used. -/
theorem radial_degree_le_two (F : ℝ[X]) (x y : ℝ) (hy : y≠0)
    (hsq : IsSquare ((C x*F-X)^2+(C y*F)^2)) : F.natDegree≤2 := by
  obtain ⟨q,hq⟩ := hsq
  rw [←pow_two] at hq
  let M : ℝ := x^2+y^2
  have hM : 0<M := by dsimp [M]; nlinarith [sq_nonneg x,sq_pos_of_ne_zero hy]
  let L : ℝ := Real.sqrt M
  have hL : L^2=M := Real.sq_sqrt hM.le
  let A : ℝ[X] := C M*F-C x*X
  let U : ℝ[X] := C L*q-A
  let V : ℝ[X] := C L*q+A
  have hCL : (C L : ℝ[X])^2=C M := by rw [←map_pow,hL]
  have he : U*V=C (y^2)*X^2 := by
    calc
      _ = (C L)^2*q^2-A^2 := by dsimp [U,V]; ring
      _ = C M*((C x*F-X)^2+(C y*F)^2)-A^2 := by rw [hCL,hq]
      _ = _ := by dsimp [A,M]; simp only [map_add,map_pow]; ring
  have hr : (C (y^2)*X^2 : ℝ[X])≠0 :=
    mul_ne_zero (C_ne_zero.mpr (pow_ne_zero 2 hy)) (pow_ne_zero 2 X_ne_zero)
  have hU : U≠0 := by intro hh; rw [hh,zero_mul] at he; exact hr he.symm
  have hV : V≠0 := by intro hh; rw [hh,mul_zero] at he; exact hr he.symm
  have hd : U.natDegree+V.natDegree=2 := by
    rw [←natDegree_mul hU hV,he,natDegree_C_mul (pow_ne_zero 2 hy),natDegree_X_pow]
  have hU2 : U.natDegree≤2 := by omega
  have hV2 : V.natDegree≤2 := by omega
  have ha : C (2 : ℝ)*A=V-U := by dsimp [V,U]; norm_num only [map_ofNat]; ring
  have hA : A.natDegree≤2 := by
    calc
      _ = (C (2 : ℝ)*A).natDegree := by rw [natDegree_C_mul (by norm_num)]
      _ = (V-U).natDegree := by rw [ha]
      _ ≤ max V.natDegree U.natDegree := natDegree_sub_le _ _
      _ ≤ 2 := max_le hV2 hU2
  have hf : C M*F=A+C x*X := by dsimp [A]; ring
  calc
    _ = (C M*F).natDegree := by rw [natDegree_C_mul (ne_of_gt hM)]
    _ = (A+C x*X).natDegree := by rw [hf]
    _ ≤ max A.natDegree (C x*X).natDegree := natDegree_add_le _ _
    _ ≤ 2 := max_le hA (by
      have hh := natDegree_C_mul_le x (X : ℝ[X])
      exact hh.trans (by simp))

lemma radial_degree_le_two_ratFunc (F : ℝ[X]) (x y : ℝ) (hy : y≠0)
    (hsq : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) ((C x*F-X)^2+(C y*F)^2))) :
    F.natDegree≤2 :=
  radial_degree_le_two F x y hy (CircleLineRigidity.polynomial_square_of_ratFunc_square _ hsq)

/-- At any degree, a squarefree complex polynomial with square norm has a
fixed complex direction. Its nonzero constant coefficient sets that direction.
Thus genuinely nonradial polynomial distance identities require repeated roots. -/
theorem squarefree_norm_constant_direction (f : ℂ[X]) (ha : f.coeff 0≠0)
    (hsf : Squarefree f) (hsq : IsSquare (f*f.map (starRingEnd ℂ))) :
    ∀ n, QuadraticMotion.cross (f.coeff 0) (f.coeff n)=0 := by
  have hf : f≠0 := by intro hh; apply ha; simp [hh]
  obtain ⟨q,hq⟩ := CircleLineRigidity.squarefree_dvd_partner hf hsf hsq
  have hg : f.map (starRingEnd ℂ)≠0 := by simpa using hf
  have hq0 : q≠0 := by intro hh; apply hg; simp [hq,hh]
  have hd := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change (f.map (starRingEnd ℂ)).natDegree=(f*q).natDegree at hd
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,natDegree_mul hf hq0] at hd
  have hdegree : q.natDegree=0 := by omega
  rw [eq_C_of_natDegree_eq_zero hdegree] at hq
  have h0 := congrArg (fun p : ℂ[X] => p.coeff 0) hq
  simp only [coeff_map,coeff_mul_C] at h0
  intro n
  have hn := congrArg (fun p : ℂ[X] => p.coeff n) hq
  simp only [coeff_map,coeff_mul_C] at hn
  have hh : f.coeff 0*(starRingEnd ℂ (f.coeff n))-
      f.coeff n*(starRingEnd ℂ (f.coeff 0))=0 := by rw [hn,h0]; ring
  have hi := congrArg Complex.im hh
  simp only [Complex.sub_im,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.zero_im] at hi
  dsimp only [QuadraticMotion.cross]
  linarith

/-- Necessary cubic edge classification. In degree exactly three, a square
norm implies either zero cubic discriminant or a fixed complex direction.
The discriminant branch alone is not asserted to be sufficient. -/
theorem cubic_norm_type (a b c d : ℂ) (ha : a≠0) (hd : d≠0)
    (hsq : IsSquare ((Cubic.mk d c b a).toPoly*
      (Cubic.mk d c b a).toPoly.map (starRingEnd ℂ))) :
    (Cubic.mk d c b a).discr=0 ∨
      (QuadraticMotion.cross a b=0 ∧ QuadraticMotion.cross a c=0 ∧
        QuadraticMotion.cross a d=0) := by
  let P : Cubic ℂ := ⟨d,c,b,a⟩
  by_cases hdisc : P.discr=0
  · exact Or.inl hdisc
  right
  have hsplit : P.toPoly.Splits := IsAlgClosed.splits _
  have hcoeff : P.toPoly.coeff 0=a := by simp [P,Cubic.toPoly]
  have hf : P.toPoly≠0 := by
    intro hh
    apply ha
    rw [←hcoeff,hh]
    simp
  have hn := (Cubic.discr_ne_zero_iff_roots_nodup (P:=P) (φ:=RingHom.id ℂ)
    hd (by simpa using hsplit)).mp hdisc
  have hn' : P.toPoly.roots.Nodup := by simpa [Cubic.roots,Cubic.map] using hn
  have hsep := (nodup_roots_iff_of_splits hf hsplit).mp hn'
  have ht := squarefree_norm_constant_direction P.toPoly (by rwa [hcoeff]) hsep.squarefree hsq
  constructor
  · simpa [P,Cubic.toPoly] using ht 1
  constructor
  · simpa [P,Cubic.toPoly] using ht 2
  · simpa [P,Cubic.toPoly] using ht 3

/-- A cubic two-anchor family, scaled to integral coefficients. -/
def px {R : Type*} [CommRing R] (t : R) : Fin 4 → R :=
  ![0,125*t,-7+169*t-16*t^2-192*t^3,-7+169*t-16*t^2-192*t^3]
def py {R : Type*} [CommRing R] (t : R) : Fin 4 → R :=
  ![0,0,-24+8*t+288*t^2+256*t^3,24-8*t-288*t^2-256*t^3]
def length {R : Type*} [CommRing R] (t : R) : Fin 4 → Fin 4 → R :=
  let d := 5*(1+t)*(5-16*t+64*t^2)
  let e := 5*(1-4*t)*(5+16*t+16*t^2)
  let f := 16*(1+t)*(4*t-1)*(8*t+3)
  !![0,125*t,d,d;125*t,0,e,e;d,e,0,f;d,e,f,0]

theorem cubic_control_squares {R : Type*} [CommRing R] (t : R) (i j : Fin 4) :
    (px t i-px t j)^2+(py t i-py t j)^2=length t i j^2 := by
  fin_cases i <;> fin_cases j <;> simp [px,py,length] <;> ring

def point (t : ℝ) (i : Fin 4) : ℂ := ⟨px t i,py t i⟩

lemma cubic_control_distance (t : ℝ) (i j : Fin 4) :
    dist (point t i) (point t j)=|length t i j| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [sq_abs,dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simpa [point,Complex.sub_re,Complex.sub_im,pow_two] using cubic_control_squares t i j

theorem cubic_control_integral (t : ℤ) (i j : Fin 4) :
    dist (point t i) (point t j)∈Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨|length t i j|,?_⟩
  rw [cubic_control_distance,Int.cast_abs]
  congr 1
  fin_cases i <;> fin_cases j <;> norm_num [length]

lemma initial_collision : point 0 0=point 0 1 := by apply Complex.ext <;> norm_num [point,px,py,Matrix.cons_val_succ]
lemma exterior_initial_distinct : point 0 2≠point 0 3 := by
  intro hh
  have hi := congrArg Complex.im hh
  change (-24+8*0+288*0^2+256*0^3 : ℝ)=24-8*0-288*0^2-256*0^3 at hi
  norm_num at hi
lemma exterior_initial_nonzero (i : Fin 2) : point 0 (i.natAdd 2)≠0 := by
  intro hh
  have hr := congrArg Complex.re hh
  fin_cases i <;> norm_num [point,px,Fin.natAdd,Fin.addNat,Matrix.cons_val_succ] at hr

private lemma collinear_cross_zero (a b c : ℂ) (h : Collinear ℝ {a,b,c}) :
    (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℂ))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp [Complex.real_smul,Complex.mul_re,Complex.mul_im]
  ring

lemma cubic_control_injective : Function.Injective (point 1) := by
  intro i j hh
  have hr := congrArg Complex.re hh
  have hi := congrArg Complex.im hh
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [point,px,py,Matrix.cons_val_succ] at *

lemma cubic_control_nontrilinear : NonTrilinear (Set.range (point 1)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik hc
  have hi : i≠j := fun h => hij (by rw [h])
  have hj : j≠k := fun h => hjk (by rw [h])
  have hk : i≠k := fun h => hik (by rw [h])
  have hh := collinear_cross_zero _ _ _ hc
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [point,px,py,Matrix.cons_val_succ] at *

lemma cubic_control_not_cospherical : ¬Cospherical (Set.range (point 1)) := by
  rintro ⟨o,r,ho⟩
  have hs (i : Fin 4) := congrArg (fun x : ℝ => x^2) (ho (point 1 i) ⟨i,rfl⟩)
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  simp only [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    at h0 h1 h2 h3
  have hx : (point 1 2).re=(-46 : ℝ) := by
    change -7+169*1-16*1^2-192*1^3=(-46 : ℝ)
    norm_num
  have hx' : (point 1 3).re=(-46 : ℝ) := hx
  have hy : (point 1 2).im=(528 : ℝ) := by
    change -24+8*1+288*1^2+256*1^3=(528 : ℝ)
    norm_num
  have hy' : (point 1 3).im=(-528 : ℝ) := by
    change 24-8*1-288*1^2-256*1^3=(-528 : ℝ)
    norm_num
  rw [hx,hy] at h2
  rw [hx',hy'] at h3
  norm_num [point,px,py,Matrix.cons_val_succ] at h0 h1
  nlinarith

/-- The control produces four distinct GP points with integral distances
at t=1. This is not a cardinality improvement over the main file. -/
theorem cubic_control_general_position :
    Function.Injective (point 1) ∧ NonTrilinear (Set.range (point 1)) ∧
      ¬Cospherical (Set.range (point 1)) :=
  ⟨cubic_control_injective,cubic_control_nontrilinear,cubic_control_not_cospherical⟩

lemma cubic_control_degree_three : (py (X : ℤ[X]) 2).coeff 3=256 := by
  change (-24+8*X+288*X^2+256*X^3 : ℤ[X]).coeff 3=256
  norm_num [coeff_add,coeff_sub,coeff_mul,coeff_X_pow,coeff_X]

#print axioms cubic_norm_type
#print axioms squarefree_norm_constant_direction
#print axioms radial_degree_le_two_ratFunc
#print axioms cubic_control_integral
#print axioms cubic_control_degree_three
#print axioms cubic_control_general_position
end
end Erdos213.MovingAnchorPolynomial
