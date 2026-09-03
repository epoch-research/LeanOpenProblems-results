import Submission.PolynomialPellClassification

/-! Polynomial reflection restrictions. None is an upper bound for arbitrary
integral-distance point sets. -/
namespace Erdos213.ReflectedPolynomialMotion
open Polynomial MovingAnchorPell PolynomialPellClassification
noncomputable section
set_option maxHeartbeats 2000000

lemma difference_squares_degree_bound (p q R : ℝ[X]) (hR : R≠0)
    (he : p^2-q^2=R) : q.natDegree≤R.natDegree := by
  let u := p-q
  let v := p+q
  have huv : u*v=R := by dsimp [u,v]; linear_combination he
  have hu : u≠0 := by intro hz; rw [hz,zero_mul] at huv; exact hR huv.symm
  have hv : v≠0 := by intro hz; rw [hz,mul_zero] at huv; exact hR huv.symm
  have hd : u.natDegree+v.natDegree=R.natDegree := by
    rw [←natDegree_mul hu hv,huv]
  have hq : C (2 : ℝ)*q=v-u := by dsimp [u,v]; simp only [map_ofNat]; ring
  calc
    _ = (C (2 : ℝ)*q).natDegree := by rw [natDegree_C_mul (by norm_num)]
    _ = (v-u).natDegree := by rw [hq]
    _ ≤ max v.natDegree u.natDegree := natDegree_sub_le _ _
    _ ≤ R.natDegree := by omega

/-- A high-degree off-axis polynomial two-anchor motion cannot also have
square polynomial distance to its image under `P ↦ X-P`. -/
theorem high_degree_midpoint_reflection_nonsquare (x y : ℝ[X]) (hy : y≠0)
    (hdeg : 2<x.natDegree ∨ 2<y.natDegree)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2)) :
    ¬IsSquare ((2*x-X)^2+(2*y)^2) := by
  obtain ⟨a,b,s,n,u,v,hb,hs,hn,hx,hy2,hu,hv⟩ :=
    high_degree_motion_classification x y hy hdeg h0 h1
  have hpell : u^2-movingD a b*v^2=1 :=
    (moving_pell_classification a b s hb (ne_of_gt hs) hn u v).mpr ⟨n,hu,hv⟩
  obtain ⟨hpos,hyd,hxd⟩ := motion_degrees a b s hb (ne_of_gt hs) hn n x y u v hy hx hy2 hu hv
  have hnd : 2≤n := by omega
  have hud : u.natDegree=n := by
    have hh := (moving_power_degrees a b s hb (ne_of_gt hs) hn n).1
    rcases hu with hu | hu <;> simpa [hu] using hh
  have hu0 : u≠0 := by intro hz; simp [hz] at hud; omega
  have hD := (moving_degrees a b s hb (ne_of_gt hs) hn).1
  have hD0 : movingD a b≠0 := by intro hz; simp [hz] at hD
  have he : (2*x-X)^2+(2*y)^2=(X*u)^2-movingD a b := by
    have hxx : 2*x-X=(C a*X+C b)*u := by linear_combination hx
    rw [hxx,hy2]
    dsimp [movingD] at hpell ⊢
    linear_combination -(X^2-(C a*X+C b)^2)*hpell
  rintro ⟨q,hq⟩
  rw [←pow_two] at hq
  have hqR : q^2-(X*u)^2= -movingD a b := by linear_combination he-hq
  have hh := difference_squares_degree_bound q (X*u) (-movingD a b)
    (neg_ne_zero.mpr hD0) hqR
  rw [natDegree_X_mul hu0,natDegree_neg,hD,hud] at hh
  omega

/-- In particular, polynomial centrally symmetric doubling around the
midpoint of linear anchors is confined to degree at most two. -/
theorem midpoint_reflection_degree_le_two (x y : ℝ[X]) (hy : y≠0)
    (h0 : IsSquare (x^2+y^2)) (h1 : IsSquare ((x-X)^2+y^2))
    (href : IsSquare ((2*x-X)^2+(2*y)^2)) :
    x.natDegree≤2 ∧ y.natDegree≤2 := by
  by_contra hh
  have hd : 2<x.natDegree ∨ 2<y.natDegree := by omega
  exact high_degree_midpoint_reflection_nonsquare x y hy hd h0 h1 href

/-- The squarefree norm lemma with arbitrary coefficient pivots. In
particular, zero constant coefficients and leading degree drops require no
assumption about distinct initial positions. -/
theorem squarefree_norm_all_directions (f : ℂ[X]) (hsf : Squarefree f)
    (hsq : IsSquare (f*f.map (starRingEnd ℂ))) :
    ∀ i j, QuadraticMotion.cross (f.coeff i) (f.coeff j)=0 := by
  have hf : f≠0 := hsf.ne_zero
  obtain ⟨q,hq⟩ := CircleLineRigidity.squarefree_dvd_partner hf hsf hsq
  have hg : f.map (starRingEnd ℂ)≠0 := by simpa using hf
  have hq0 : q≠0 := by intro hh; apply hg; simp [hq,hh]
  have hd := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change (f.map (starRingEnd ℂ)).natDegree=(f*q).natDegree at hd
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,natDegree_mul hf hq0] at hd
  have hdegree : q.natDegree=0 := by omega
  rw [eq_C_of_natDegree_eq_zero hdegree] at hq
  intro i j
  have hi := congrArg (fun p : ℂ[X] => p.coeff i) hq
  have hj := congrArg (fun p : ℂ[X] => p.coeff j) hq
  simp only [coeff_map,coeff_mul_C] at hi hj
  have he : f.coeff i*(starRingEnd ℂ (f.coeff j))-
      f.coeff j*(starRingEnd ℂ (f.coeff i))=0 := by rw [hi,hj]; ring
  have hm := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.zero_im] at hm
  dsimp only [QuadraticMotion.cross]
  linarith

#print axioms difference_squares_degree_bound
#print axioms high_degree_midpoint_reflection_nonsquare
#print axioms midpoint_reflection_degree_le_two
#print axioms squarefree_norm_all_directions
end
end Erdos213.ReflectedPolynomialMotion
