import FormalConjecturesUtil

/-! Elementary geometry of vector quadratics with fixed nonzero determinant.
This file makes no theta-exclusion or extremal-exponent assertion. -/
namespace Erdos713DeterminantQuadraticGeometry
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

abbrev Vec (K : Type*) := K × K
abbrev Quad (K : Type*) := Vec K × Vec K × Vec K

def det (u v : Vec K) : K := u.1*v.2-u.2*v.1

def lin (u v : Vec K) (t : K) : Vec K := (u.1*t+v.1,u.2*t+v.2)

def eval (f : Quad K) (t : K) : Vec K :=
  (f.1.1*t^2+f.2.1.1*t+f.2.2.1,f.1.2*t^2+f.2.1.2*t+f.2.2.2)

def Admissible (f : Quad K) : Prop := det f.1 f.2.1 = 1

def residual (f : Quad K) (t : K) : Vec K :=
  (f.2.1.1+t*f.1.1,f.2.1.2+t*f.1.2)

lemma det_lin (u v : Vec K) (x y : K) :
    det (lin u v x) (lin u v y) = (x-y)*det u v := by
  dsimp [det,lin]
  ring

lemma vec_eq_of_det_eq {p q v w : Vec K} (hpq : det p q ≠ 0)
    (hp : det p v = det p w) (hq : det q v = det q w) : v = w := by
  have h1 : det p q*(v.1-w.1) = 0 := by
    dsimp [det] at hp hq ⊢
    linear_combination q.1*hp-p.1*hq
  have h2 : det p q*(v.2-w.2) = 0 := by
    dsimp [det] at hp hq ⊢
    linear_combination q.2*hp-p.2*hq
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hpq))
    (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hpq))

lemma lin_eq_of_two {u v u' v' : Vec K} {x y : K} (hxy : x ≠ y)
    (hx : lin u v x = lin u' v' x) (hy : lin u v y = lin u' v' y) :
    u = u' ∧ v = v' := by
  have hx1 := congrArg Prod.fst hx
  have hx2 := congrArg Prod.snd hx
  have hy1 := congrArg Prod.fst hy
  have hy2 := congrArg Prod.snd hy
  dsimp [lin] at hx1 hx2 hy1 hy2
  have h1 : (x-y)*(u.1-u'.1) = 0 := by linear_combination hx1-hy1
  have h2 : (x-y)*(u.2-u'.2) = 0 := by linear_combination hx2-hy2
  have hu : u = u' := Prod.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hxy)))
    (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hxy)))
  subst u'
  refine ⟨rfl,Prod.ext ?_ ?_⟩
  · linear_combination hx1
  · linear_combination hx2

/-- Three determinant-one affine maps cannot form a triangle at distinct
parameters unless the first two maps coincide. -/
lemma lin_triangle {u v u' v' u'' v'' : Vec K} {x y z : K}
    (hf : det u v = 1) (hg : det u' v' = 1) (hh : det u'' v'' = 1)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hfg : lin u v x = lin u' v' x)
    (hfh : lin u v y = lin u'' v'' y)
    (hgh : lin u' v' z = lin u'' v'' z) : u = u' ∧ v = v' := by
  have hpq : det (lin u v x) (lin u v y) ≠ 0 := by
    rw [det_lin,hf,mul_one]
    exact sub_ne_zero.mpr hxy
  have hp : det (lin u v x) (lin u' v' z) = det (lin u v x) (lin u v z) := by
    rw [hfg,det_lin,hg,← hfg,det_lin,hf]
  have hq : det (lin u v y) (lin u' v' z) = det (lin u v y) (lin u v z) := by
    rw [hfh,hgh,det_lin,hh,← hfh,det_lin,hf]
  have hz := vec_eq_of_det_eq hpq hp hq
  exact lin_eq_of_two hxz hfg hz.symm

lemma residual_det (f : Quad K) (t : K) : det f.1 (residual f t) = det f.1 f.2.1 := by
  dsimp [det,residual]
  ring

lemma eval_sub_factor (f : Quad K) (t x : K) :
    eval f x-eval f t = (x-t) • lin f.1 (residual f t) x := by
  apply Prod.ext <;> dsimp [eval,lin,residual] <;> ring

lemma residual_eq_of_evals {f g : Quad K} {t x : K} (hxt : x ≠ t)
    (ht : eval f t = eval g t) (hx : eval f x = eval g x) :
    lin f.1 (residual f t) x = lin g.1 (residual g t) x := by
  have he : (x-t) • lin f.1 (residual f t) x = (x-t) • lin g.1 (residual g t) x := by
    rw [← eval_sub_factor,← eval_sub_factor,ht,hx]
  apply Prod.ext
  · exact mul_left_cancel₀ (sub_ne_zero.mpr hxt) (congrArg Prod.fst he)
  · exact mul_left_cancel₀ (sub_ne_zero.mpr hxt) (congrArg Prod.snd he)

lemma quad_eq_of_residual {f g : Quad K} {t : K}
    (hU : f.1 = g.1) (hV : residual f t = residual g t)
    (ht : eval f t = eval g t) : f = g := by
  have hV1 := congrArg Prod.fst hV
  have hV2 := congrArg Prod.snd hV
  have hU1 := congrArg Prod.fst hU
  have hU2 := congrArg Prod.snd hU
  have ht1 := congrArg Prod.fst ht
  have ht2 := congrArg Prod.snd ht
  dsimp [residual] at hV1 hV2
  dsimp [eval] at ht1 ht2
  apply Prod.ext hU
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · linear_combination hV1-t*hU1
  · linear_combination hV2-t*hU2
  · linear_combination ht1-t*hV1
  · linear_combination ht2-t*hV2

lemma quad_eq_of_three {f g : Quad K} {t x y : K}
    (hxt : x ≠ t) (hyt : y ≠ t) (hxy : x ≠ y)
    (ht : eval f t = eval g t) (hx : eval f x = eval g x) (hy : eval f y = eval g y) :
    f = g := by
  obtain ⟨hU,hV⟩ := lin_eq_of_two hxy
    (residual_eq_of_evals hxt ht hx) (residual_eq_of_evals hyt ht hy)
  exact quad_eq_of_residual hU hV ht

/-- Three admissible quadratics through one point cannot form an additional
three-row, three-column incidence hexagon away from that point. -/
theorem common_point_triangle {f g h : Quad K} {t x y z : K}
    (hf : Admissible f) (hg : Admissible g) (hh : Admissible h)
    (hxt : x ≠ t) (hyt : y ≠ t) (hzt : z ≠ t)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hfg0 : eval f t = eval g t) (hfh0 : eval f t = eval h t)
    (hfg : eval f x = eval g x) (hfh : eval f y = eval h y)
    (hgh : eval g z = eval h z) : f = g := by
  have hfg' := residual_eq_of_evals hxt hfg0 hfg
  have hfh' := residual_eq_of_evals hyt hfh0 hfh
  have hgh' := residual_eq_of_evals hzt (hfg0.symm.trans hfh0) hgh
  have hf' : det f.1 (residual f t) = 1 := (residual_det f t).trans hf
  have hg' : det g.1 (residual g t) = 1 := (residual_det g t).trans hg
  have hh' : det h.1 (residual h t) = 1 := (residual_det h t).trans hh
  obtain ⟨hU,hV⟩ := lin_triangle hf' hg' hh' hxy hxz hfg' hfh' hgh'
  exact quad_eq_of_residual hU hV hfg0

#print axioms lin_triangle
#print axioms quad_eq_of_three
#print axioms common_point_triangle
end Erdos713DeterminantQuadraticGeometry
