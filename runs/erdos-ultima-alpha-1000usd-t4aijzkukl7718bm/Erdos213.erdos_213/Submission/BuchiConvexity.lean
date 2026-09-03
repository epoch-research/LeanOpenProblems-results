import FormalConjecturesUtil

/-! Necessary convexity and divisibility conditions for the positive-height
quadratic-square search. These do not supply a global denominator bound. -/
namespace Erdos213.BuchiConvexity
set_option maxHeartbeats 2000000

lemma root_step_bounds {L b c x y : ℝ}
    (hL : 0<L) (hb : 0<b) (hC : 0<4*L^2*c-b^2)
    (hx : 0≤x) (hy : 0≤y) (hx2 : x^2=c) (hy2 : y^2=L^2+b+c) :
    0<y-x ∧ y-x<L := by
  have hL2 : 0<L^2 := sq_pos_of_pos hL
  have hxy : x<y := by nlinarith
  have hbL : b<2*L*x := by
    have hnn : 0≤2*L*x := by positivity
    apply (sq_lt_sq₀ hb.le hnn).mp
    nlinarith only [hC,hx2]
  constructor
  · linarith
  · have hn : 0≤x+L := by positivity
    have hs : y^2<(x+L)^2 := by nlinarith only [hx2,hy2,hbL]
    have hh := (sq_lt_sq₀ hy hn).mp hs
    linarith

lemma three_roots_strict_convex {L b c x y z : ℝ}
    (hC : 0<4*L^2*c-b^2)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hx2 : x^2=c) (hy2 : y^2=L^2+b+c) (hz2 : z^2=4*L^2+2*b+c) :
    y-x<z-y := by
  by_contra! h
  have hs : (x+z)^2≤(2*y)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    linarith only [h]
  have hp : x*z≤b+c := by nlinarith only [hs,hx2,hy2,hz2]
  have hn : 0≤b+c := (mul_nonneg hx hz).trans hp
  have hs' : (x*z)^2≤(b+c)^2 := (sq_le_sq₀ (mul_nonneg hx hz) hn).mpr hp
  have he : (x*z)^2-(b+c)^2=4*L^2*c-b^2 := by
    rw [mul_pow,hx2,hz2]
    ring
  linarith

/-- The real inequalities justify the search's strictly increasing positive
integer root differences, each smaller than L. -/
lemma integer_difference_bounds {L b c x y z : ℤ}
    (hL : 0<L) (hb : 0<b) (hC : 0<4*L^2*c-b^2)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hx2 : x^2=c) (hy2 : y^2=L^2+b+c) (hz2 : z^2=4*L^2+2*b+c) :
    0<y-x ∧ y-x<z-y ∧ z-y<L := by
  have hL' : (0 : ℝ)<L := by exact_mod_cast hL
  have hb' : (0 : ℝ)<b := by exact_mod_cast hb
  have hC' : (0 : ℝ)<4*(L : ℝ)^2*c-(b : ℝ)^2 := by exact_mod_cast hC
  have hx' : (0 : ℝ)≤x := by exact_mod_cast hx
  have hy' : (0 : ℝ)≤y := by exact_mod_cast hy
  have hz' : (0 : ℝ)≤z := by exact_mod_cast hz
  have hx2' : (x : ℝ)^2=c := by exact_mod_cast hx2
  have hy2' : (y : ℝ)^2=(L : ℝ)^2+b+c := by exact_mod_cast hy2
  have hz2' : (z : ℝ)^2=4*(L : ℝ)^2+2*b+c := by exact_mod_cast hz2
  have hfirst := root_step_bounds hL' hb' hC' hx' hy' hx2' hy2'
  have hmid := three_roots_strict_convex hC' hx' hy' hz' hx2' hy2' hz2'
  have hlast := root_step_bounds (b := (b : ℝ)+2*(L : ℝ)^2)
    (c := (L : ℝ)^2+b+c) hL' (by positivity) (by nlinarith only [hC']) hy' hz' hy2'
    (by nlinarith only [hz2'])
  exact_mod_cast (show (0 : ℝ)<(y : ℝ)-x ∧ (y : ℝ)-x<(z : ℝ)-y ∧ (z : ℝ)-y<L from
    ⟨hfirst.1,hmid,hlast.2⟩)

/-- The second root difference is even. -/
lemma even_second_difference {L x y z : ℤ}
    (h : z^2-2*y^2+x^2=2*L^2) : Even (z-2*y+x) := by
  have he : Even (z^2-2*y^2+x^2) := ⟨L^2, by linarith only [h]⟩
  simpa [parity_simps] using he

/-- Exact algebraic parameterization used in the integer search. -/
lemma initial_root_identity {L x y z q : ℤ}
    (h : z^2-2*y^2+x^2=2*L^2) (hq : z-2*y+x=2*q) :
    L^2-(y-x)^2=2*q*(x+2*(y-x)+q) := by
  have hz : z = 2*q+2*y-x := by omega
  rw [hz] at h
  nlinarith only [h]

lemma initial_root_divisibility {L x y z q : ℤ}
    (h : z^2-2*y^2+x^2=2*L^2) (hq : z-2*y+x=2*q) :
    2*q ∣ L^2-(y-x)^2 :=
  ⟨x+2*(y-x)+q,initial_root_identity h hq⟩

#print axioms integer_difference_bounds
#print axioms even_second_difference
#print axioms initial_root_divisibility
end Erdos213.BuchiConvexity
