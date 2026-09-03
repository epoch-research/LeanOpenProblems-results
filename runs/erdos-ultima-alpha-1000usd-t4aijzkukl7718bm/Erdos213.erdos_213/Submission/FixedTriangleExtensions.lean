import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Algebra.Polynomial.Roots

/-! A diameter-unrestricted finite reduction for extensions of one fixed
noncollinear integral triangle. This does not bound the size or scale of
arbitrary integral-distance configurations. -/
namespace Erdos213.FixedTriangleExtensions

def heron {R : Type*} [CommRing R] (a b c : R) : R :=
  4*a^2*b^2-(a^2+b^2-c^2)^2

def qa {R : Type*} [CommRing R] (a b c k l : R) : R :=
  4*(b^2*k^2-(a^2+b^2-c^2)*k*l+a^2*l^2)-heron a b c

def qb {R : Type*} [CommRing R] (a b c k l : R) : R :=
  -4*b^2*k*(a^2-k^2)+2*(a^2+b^2-c^2)*((a^2-k^2)*l+(b^2-l^2)*k)
    -4*a^2*l*(b^2-l^2)

def qc {R : Type*} [CommRing R] (a b c k l : R) : R :=
  b^2*(a^2-k^2)^2-(a^2+b^2-c^2)*(a^2-k^2)*(b^2-l^2)+a^2*(b^2-l^2)^2

lemma discriminant_identity {R : Type*} [CommRing R] (a b c k l : R) :
    qb a b c k l ^ 2 - 4 * qa a b c k l * qc a b c k l =
      4*heron a b c*(a^2-k^2)*(b^2-l^2)*(c^2-(k-l)^2) := by
  simp only [qa,qb,qc,heron]
  ring

def qhalf {R : Type*} [CommRing R] (a b c k l : R) : R :=
  -2*b^2*k*(a^2-k^2)+(a^2+b^2-c^2)*((a^2-k^2)*l+(b^2-l^2)*k)
    -2*a^2*l*(b^2-l^2)

lemma qb_eq_two_qhalf {R : Type*} [CommRing R] (a b c k l : R) :
    qb a b c k l=2*qhalf a b c k l := by
  simp only [qb,qhalf]; ring

lemma half_discriminant_identity {R : Type*} [CommRing R] (a b c k l : R) :
    qhalf a b c k l ^ 2 - qa a b c k l * qc a b c k l =
      heron a b c*(a^2-k^2)*(b^2-l^2)*(c^2-(k-l)^2) := by
  simp only [qa,qhalf,qc,heron]; ring

lemma radius_isSquare {R : Type*} [CommRing R] {a b c k l r : R}
    (h : qa a b c k l*r^2+qb a b c k l*r+qc a b c k l=0) :
    IsSquare (heron a b c*(a^2-k^2)*(b^2-l^2)*(c^2-(k-l)^2)) := by
  refine ⟨qa a b c k l*r+qhalf a b c k l,?_⟩
  rw [← half_discriminant_identity]
  rw [qb_eq_two_qhalf] at h
  linear_combination -qa a b c k l*h

lemma positive_constant {a b c k l : ℝ} (hb : 0<b)
    (hH : 0<heron a b c) (hl : |l|<b) : 0<qc a b c k l := by
  have hv : 0<b^2-l^2 := by nlinarith [abs_lt.mp hl, sq_abs l]
  have hpos : 0<heron a b c*(b^2-l^2)^2 := mul_pos hH (sq_pos_of_pos hv)
  have hid : 4*b^2*qc a b c k l =
      (2*b^2*(a^2-k^2)-(a^2+b^2-c^2)*(b^2-l^2))^2 +
      heron a b c*(b^2-l^2)^2 := by simp only [qc,heron]; ring
  have hprod : 0<4*b^2*qc a b c k l := by
    nlinarith [sq_nonneg (2*b^2*(a^2-k^2)-(a^2+b^2-c^2)*(b^2-l^2))]
  exact pos_of_mul_pos_right hprod (by positivity)

lemma radius_equation {a b c k l r x y u v : ℝ}
    (hb : u^2+v^2=b^2) (hc : (u-a)^2+v^2=c^2)
    (hr : x^2+y^2=r^2)
    (hs : (x-a)^2+y^2=(r+k)^2)
    (ht : (x-u)^2+(y-v)^2=(r+l)^2) :
    qa a b c k l*r^2+qb a b c k l*r+qc a b c k l=0 := by
  have hu : a^2+b^2-c^2=2*a*u := by nlinarith only [hb,hc]
  have hx : a^2-k^2-2*k*r=2*a*x := by nlinarith only [hr,hs]
  have hy : b^2-l^2-2*l*r=2*u*x+2*v*y := by nlinarith only [hb,hr,ht]
  have hid : qa a b c k l*r^2+qb a b c k l*r+qc a b c k l =
      b^2*(a^2-k^2-2*k*r)^2
      -(a^2+b^2-c^2)*(a^2-k^2-2*k*r)*(b^2-l^2-2*l*r)
      +a^2*(b^2-l^2-2*l*r)^2-heron a b c*r^2 := by
    simp only [qa,qb,qc,heron]; ring
  rw [hid,hx,hy]
  unfold heron
  rw [hu,← hb,← hr]
  ring

lemma radius_square_discriminant {a b c k l r : ℝ}
    (h : qa a b c k l*r^2+qb a b c k l*r+qc a b c k l=0) :
    (2*qa a b c k l*r+qb a b c k l)^2 =
      4*heron a b c*(a^2-k^2)*(b^2-l^2)*(c^2-(k-l)^2) := by
  rw [← discriminant_identity]
  linear_combination 4*qa a b c k l*h

lemma heron_of_coordinates {a b c u v : ℝ}
    (hb : u^2+v^2=b^2) (hc : (u-a)^2+v^2=c^2) :
    heron a b c=4*a^2*v^2 := by
  have hh : a^2+b^2-c^2=2*a*u := by nlinarith only [hb,hc]
  unfold heron
  rw [hh,← hb]
  ring

lemma complex_dist_sq (p q : ℂ) :
    dist p q ^ 2=(p.re-q.re)^2+(p.im-q.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im]
  ring

lemma complex_radius_equation {a b c k l r : ℝ} {z p : ℂ}
    (hb : ‖z‖=b) (hc : dist z (a : ℂ)=c)
    (hr : ‖p‖=r) (hs : dist p (a : ℂ)=r+k) (ht : dist p z=r+l) :
    qa a b c k l*r^2+qb a b c k l*r+qc a b c k l=0 := by
  have h1 := Complex.sq_norm z
  have h2 := complex_dist_sq z (a : ℂ)
  have h3 := Complex.sq_norm p
  have h4 := complex_dist_sq p (a : ℂ)
  have h5 := complex_dist_sq p z
  rw [hb,Complex.normSq_apply] at h1
  rw [hc,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h2
  rw [hr,Complex.normSq_apply] at h3
  rw [hs,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h4
  rw [ht] at h5
  exact radius_equation (by nlinarith only [h1]) h2.symm
    (by nlinarith only [h3]) h4.symm h5.symm

lemma norm_injective_on_fiber {a : ℝ} {z : ℂ} {k l : ℤ}
    (ha : a≠0) (hz : z.im≠0) :
    Set.InjOn (fun p : ℂ => ‖p‖)
      {p | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧ dist p z=‖p‖+(l : ℝ)} := by
  intro p hp q hq he
  change ‖p‖=‖q‖ at he
  have h1 := complex_dist_sq p (a : ℂ)
  have h2 := complex_dist_sq q (a : ℂ)
  have h3 := complex_dist_sq p z
  have h4 := complex_dist_sq q z
  have h5 := Complex.sq_norm p
  have h6 := Complex.sq_norm q
  rw [hp.1] at h1
  rw [hq.1,← he] at h2
  rw [hp.2] at h3
  rw [hq.2,← he] at h4
  rw [← he] at h6
  simp only [Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h1 h2
  simp only [Complex.normSq_apply] at h5 h6
  have hre : p.re=q.re := by
    apply (mul_left_cancel₀ ha)
    nlinarith only [h1,h2,h5,h6]
  have him : p.im=q.im := by
    apply (mul_left_cancel₀ hz)
    rw [hre] at h3 h5
    nlinarith only [h3,h4,h5,h6]
  exact Complex.ext hre him

noncomputable def radiusPolynomial (a b c k l : ℝ) : Polynomial ℝ :=
  Polynomial.C (qa a b c k l)*Polynomial.X^2+
    Polynomial.C (qb a b c k l)*Polynomial.X+Polynomial.C (qc a b c k l)

lemma finite_fiber {a b c : ℝ} {z : ℂ} {k l : ℤ}
    (ha : a≠0) (hb : 0<b) (hz : z.im≠0)
    (hn : ‖z‖=b) (hc : dist z (a : ℂ)=c) (hl : |(l : ℝ)|<b) :
    Set.Finite {p : ℂ | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧
      dist p z=‖p‖+(l : ℝ)} := by
  have hH : 0<heron a b c := by
    have h1 := Complex.sq_norm z
    rw [hn,Complex.normSq_apply] at h1
    have h2 := complex_dist_sq z (a : ℂ)
    rw [hc,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h2
    rw [heron_of_coordinates (by nlinarith only [h1]) h2.symm]
    positivity
  have hp : radiusPolynomial a b c k l ≠ 0 := by
    intro hh
    have he := congrArg (Polynomial.eval 0) hh
    simp only [radiusPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,zero_pow (by decide : 2≠0),
      mul_zero,zero_add,Polynomial.eval_zero] at he
    exact (ne_of_gt (positive_constant hb hH hl)) he
  apply Set.Finite.of_finite_image (f := fun p : ℂ => ‖p‖)
    (s := {p : ℂ | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧ dist p z=‖p‖+(l : ℝ)})
  · apply (Polynomial.finite_setOf_isRoot hp).subset
    rintro r ⟨p,hp,rfl⟩
    change (radiusPolynomial a b c k l).eval ‖p‖=0
    simp only [radiusPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    exact complex_radius_equation hn hc rfl hp.1 hp.2
  · exact norm_injective_on_fiber ha hz

lemma strict_difference_bound {u v p : ℂ}
    (h : ¬ Collinear ℝ ({u,v,p} : Set ℂ)) :
    |dist p v-dist p u|<dist u v := by
  have h1 : dist p v<dist p u+dist u v := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro he
    apply h
    convert he.collinear using 1
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have h2 : dist p u<dist p v+dist u v := by
    rw [dist_comm u v]
    apply dist_lt_dist_add_dist_iff.mpr
    intro he
    apply h
    convert he.collinear using 1
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- Completeness of the finite difference-pair reduction. No diameter bound
on the new point is assumed. The two excluded anchor lines suffice here;
the enumeration also excludes the third line when imposing general position. -/
theorem normalized_extensions_finite {a b : ℕ} {z : ℂ}
    (ha : 0<a) (hb : 0<b) (hz : z.im≠0) (hn : ‖z‖=(b : ℝ)) :
    Set.Finite {p : ℂ |
      (dist p 0 ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (dist p (a : ℂ) ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (dist p z ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ¬ Collinear ℝ ({0,(a : ℂ),p} : Set ℂ) ∧
      ¬ Collinear ℝ ({0,z,p} : Set ℂ)} := by
  let K : Finset ℤ := Finset.Ioo (-(a : ℤ)) a
  let L : Finset ℤ := Finset.Ioo (-(b : ℤ)) b
  let F (k l : ℤ) : Set ℂ :=
    {p | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧ dist p z=‖p‖+(l : ℝ)}
  have hf : Set.Finite (⋃ k∈(K : Set ℤ), ⋃ l∈(L : Set ℤ), F k l) := by
    apply K.finite_toSet.biUnion
    intro k hk
    apply L.finite_toSet.biUnion
    intro l hl
    have hl' : -(b : ℤ)<l ∧ l<(b : ℤ) := Finset.mem_Ioo.mp hl
    apply finite_fiber (c := dist z (a : ℂ))
      (by exact_mod_cast (ne_of_gt ha)) (by exact_mod_cast hb) hz hn rfl
    exact_mod_cast (abs_lt.mpr hl')
  apply hf.subset
  rintro p ⟨⟨r,hr⟩,⟨s,hs⟩,⟨t,ht⟩,hpa,hpz⟩
  have hr' : ‖p‖=(r : ℝ) := by simpa only [dist_zero_right] using hr.symm
  have hka := strict_difference_bound hpa
  have hlz := strict_difference_bound hpz
  rw [← hr,← hs] at hka
  rw [← hr,← ht,dist_zero_left,hn] at hlz
  have hna : dist (0 : ℂ) (a : ℂ)=(a : ℝ) := by
    simp
  rw [hna] at hka
  have hk : s-r ∈ (K : Set ℤ) := by
    change s-r ∈ Finset.Ioo (-(a : ℤ)) a
    apply Finset.mem_Ioo.mpr
    exact_mod_cast (abs_lt.mp hka)
  have hl : t-r ∈ (L : Set ℤ) := by
    change t-r ∈ Finset.Ioo (-(b : ℤ)) b
    apply Finset.mem_Ioo.mpr
    exact_mod_cast (abs_lt.mp hlz)
  apply Set.mem_iUnion.mpr ⟨s-r,?_⟩
  apply Set.mem_iUnion.mpr ⟨hk,?_⟩
  apply Set.mem_iUnion.mpr ⟨t-r,?_⟩
  apply Set.mem_iUnion.mpr ⟨hl,?_⟩
  change dist p (a : ℂ)=‖p‖+((s-r : ℤ) : ℝ) ∧
    dist p z=‖p‖+((t-r : ℤ) : ℝ)
  rw [hr',Int.cast_sub,Int.cast_sub]
  constructor <;> linarith

/-- The vanishing-leading-coefficient case really occurs inside the strict
triangle ranges; a search may not silently divide by `qa`. -/
lemma linear_control :
    qa (5780 : ℚ) 5916 10744 2140 2484=0 ∧
    qb (5780 : ℚ) 5916 10744 2140 2484≠0 ∧
    qa (5780 : ℚ) 5916 10744 2140 2484*(6241/2)^2+
      qb (5780 : ℚ) 5916 10744 2140 2484*(6241/2)+
      qc (5780 : ℚ) 5916 10744 2140 2484=0 := by
  norm_num [qa,qb,qc,heron]

/-- An actual difference pair from the seven-point example has TWO positive
rational roots. Discarding the larger or smaller root is not valid. -/
lemma two_root_control :
    let a : ℚ := 5780
    let b : ℚ := 5916
    let c : ℚ := 10744
    let k : ℚ := -1020
    let l : ℚ := 5616
    let r : ℚ := 14450
    let s : ℚ := 2588162050/721993
    0<r ∧ 0<s ∧ 0<r+k ∧ 0<s+k ∧ 0<r+l ∧ 0<s+l ∧ r≠s ∧
      qa a b c k l*r^2+qb a b c k l*r+qc a b c k l=0 ∧
      qa a b c k l*s^2+qb a b c k l*s+qc a b c k l=0 := by
  norm_num [qa,qb,qc,heron]

#print axioms discriminant_identity
#print axioms radius_isSquare
#print axioms linear_control
#print axioms two_root_control
#print axioms radius_equation
#print axioms radius_square_discriminant
#print axioms complex_radius_equation
#print axioms finite_fiber
#print axioms normalized_extensions_finite
end Erdos213.FixedTriangleExtensions
