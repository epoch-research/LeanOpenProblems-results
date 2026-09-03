import Submission.GeneralQuadraticType
import Submission.SquaredBimedians

/-! A restricted obstruction for quadratic motions with splitting anchors 0,t.
Square conditions are rational-function identities, not conditions at just one
specialization. This is not an obstruction to arbitrary rational-distance sets. -/
namespace Erdos213.TwoAnchorGeometry
open EuclideanGeometry Polynomial QuadraticMotion GeneralQuadraticType
noncomputable section
set_option maxHeartbeats 2000000

def Compatible (a b c : ℂ) : Prop :=
  b^2-4*a*c=0 ∨ (cross a b=0 ∧ cross a c=0)

lemma cross_mul (s a b : ℂ) : cross (s*a) (s*b)=Complex.normSq s*cross a b := by
  simp only [cross,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

lemma Compatible.mul {a b c : ℂ} (h : Compatible a b c) (s : ℂ) :
    Compatible (s*a) (s*b) (s*c) := by
  rcases h with h | ⟨h,h'⟩
  · left
    linear_combination s^2*h
  · right
    rw [cross_mul,cross_mul,h,h']
    simp

inductive Shape | left | right | middle deriving DecidableEq, Fintype

def root (x y : ℝ) : ℂ := ⟨x,y⟩
def base (x y : ℝ) : ℂ := (root x y)⁻¹
def velocity : Shape → ℝ → ℝ → ℂ
  | .left,x,y => (x : ℂ)*base x y
  | .right,x,y => 1-(x : ℂ)*base x y
  | .middle,_,_ => 1/2

def acceleration : Shape → ℝ → ℝ → ℂ
  | .left,x,y => (-y^2/4 : ℝ)*base x y
  | .right,x,y => (-y^2/4 : ℝ)*base x y
  | .middle,x,y => root x y/16

def point (k : Shape) (x y t : ℝ) : ℂ :=
  base x y+velocity k x y*t+acceleration k x y*t^2

def PairType (k l : Shape) (x y u v : ℝ) : Prop :=
  Compatible (base x y-base u v) (velocity k x y-velocity l u v)
    (acceleration k x y-acceleration l u v)

lemma root_ne_zero {x y : ℝ} (hy : y≠0) : root x y≠0 := by
  intro h
  exact hy (congrArg Complex.im h)

lemma norm_root_ne_zero {x y : ℝ} (hy : y≠0) : x^2+y^2≠0 := by
  nlinarith [sq_pos_of_ne_zero hy]

lemma scaled_difference (z w b d c e : ℂ) (hz : z≠0) (hw : w≠0) :
    (z*w)*(z⁻¹-w⁻¹)=w-z ∧
    (z*w)*(b*z⁻¹-d*w⁻¹)=b*w-d*z ∧
    (z*w)*(c*z⁻¹-e*w⁻¹)=c*w-e*z := by
  constructor
  · field_simp
  constructor <;> field_simp

/-- Same radial type: either equal reciprocal imaginary parts, or the two
phase products vanish. All denominators have been cleared. -/
lemma same_type (k : Shape) (hk : k≠.middle) (x y u v : ℝ)
    (hy : y≠0) (hv : v≠0) (h : PairType k k x y u v) :
    y=v ∨ ((x-u)*(x*v-u*y)=0 ∧ (y-v)*(y+v)*(x*v-u*y)=0) := by
  have hz := root_ne_zero (x:=x) hy
  have hw := root_ne_zero (x:=u) hv
  have hs := h.mul (root x y*root u v)
  have he := scaled_difference (root x y) (root u v) x u
    (-y^2/4) (-v^2/4) hz hw
  have hA : (root x y*root u v)*(base x y-base u v)=root u v-root x y := he.1
  have hC : (root x y*root u v)*(acceleration k x y-acceleration k u v)=
      (-y^2/4 : ℝ)*(root u v)-(-v^2/4 : ℝ)*(root x y) := by
    cases k <;> simp_all only [ne_eq,not_true_eq_false]
    all_goals simpa only [acceleration,base,Complex.ofReal_div,Complex.ofReal_neg,
      Complex.ofReal_pow,Complex.ofReal_ofNat] using he.2.2
  have hB : (root x y*root u v)*(velocity k x y-velocity k u v)=
      (if k=.left then 1 else -1)*( (x : ℂ)*root u v-(u : ℂ)*root x y) := by
    cases k
    · simpa only [velocity,base,if_pos,one_mul] using he.2.1
    · simp only [velocity,base,show (Shape.right=Shape.left) = False by decide,if_false,neg_one_mul]
      linear_combination -he.2.1
    · exact False.elim (hk rfl)
  rw [hA,hB,hC] at hs
  have hd : ( (x : ℂ)*root u v-(u : ℂ)*root x y)^2-
      4*(root u v-root x y)*((-y^2/4 : ℝ)*root u v-(-v^2/4 : ℝ)*root x y)=
      -((y-v : ℝ) : ℂ)^2*root x y*root u v := by
    apply Complex.ext <;>
      simp only [root,pow_two,Complex.mul_re,Complex.mul_im,Complex.sub_re,
        Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,
        Complex.neg_im,Complex.re_ofNat,Complex.im_ofNat] <;> ring
  rcases hs with hs | ⟨hs,hs'⟩
  · left
    have hh : -((y-v : ℝ) : ℂ)^2*root x y*root u v=0 := by
      rw [←hd]
      split_ifs at hs <;> simpa only [one_mul,neg_one_mul,neg_sq] using hs
    have hh' := ((mul_eq_zero.mp hh).resolve_right hw)
    have hh'' := (mul_eq_zero.mp hh').resolve_right hz
    have : (y-v : ℝ)=0 := by exact_mod_cast (sq_eq_zero_iff.mp (neg_eq_zero.mp hh''))
    exact sub_eq_zero.mp this
  · right
    have hphase : cross (root u v-root x y)
        ((x : ℂ)*root u v-(u : ℂ)*root x y)=0 := by
      split_ifs at hs
      · simpa only [one_mul] using hs
      · simp only [neg_one_mul] at hs
        simp only [cross,Complex.neg_re,Complex.neg_im] at hs ⊢
        linear_combination -hs
    simp only [cross,root,Complex.sub_re,Complex.sub_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] at hphase hs'
    constructor
    · linear_combination -hphase
    · linear_combination 4*hs'

lemma mixed_type (x y u v : ℝ) (hy : y≠0) (hv : v≠0)
    (h : PairType .left .right x y u v) :
    (y-v)^2*(u*y+v*x)=0 ∨
      ((y-v)*(u*x+v*y)=0 ∧ (y-v)*(y+v)*(x*v-u*y)=0) := by
  have hz := root_ne_zero (x:=x) hy
  have hw := root_ne_zero (x:=u) hv
  have hs := h.mul (root x y*root u v)
  have he := scaled_difference (root x y) (root u v) x u
    (-y^2/4) (-v^2/4) hz hw
  have hA : (root x y*root u v)*(base x y-base u v)=root u v-root x y := he.1
  have hC : (root x y*root u v)*(acceleration .left x y-acceleration .right u v)=
      (-y^2/4 : ℝ)*root u v-(-v^2/4 : ℝ)*root x y := by
    simpa only [acceleration,base,Complex.ofReal_div,Complex.ofReal_neg,
      Complex.ofReal_pow,Complex.ofReal_ofNat] using he.2.2
  have hB : (root x y*root u v)*(velocity .left x y-velocity .right u v)=
      (x : ℂ)*root u v+(u : ℂ)*root x y-root x y*root u v := by
    dsimp [velocity,base]
    field_simp
    ring
  rw [hA,hB,hC] at hs
  rcases hs with hs | ⟨hs,hs'⟩
  · left
    have hi := congrArg Complex.im hs
    simp only [root,pow_two,Complex.sub_im,Complex.mul_im,Complex.add_im,
      Complex.sub_re,Complex.mul_re,Complex.add_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.zero_im] at hi
    linear_combination -hi
  · right
    simp only [cross,root,Complex.sub_im,Complex.mul_im,Complex.add_im,
      Complex.sub_re,Complex.mul_re,Complex.add_re,Complex.ofReal_re,
      Complex.ofReal_im] at hs hs'
    constructor
    · linear_combination hs
    · linear_combination 4*hs'

lemma PairType.symm {k l : Shape} {x y u v : ℝ} (h : PairType k l x y u v) :
    PairType l k u v x y := by
  have hh := h.mul (-1)
  simpa only [neg_one_mul,neg_sub] using hh

lemma base_re (x y : ℝ) : (base x y).re=x/(x^2+y^2) := by
  simp [base,root,Complex.inv_re,Complex.normSq_apply,pow_two]
lemma base_im (x y : ℝ) : (base x y).im=-y/(x^2+y^2) := by
  simp [base,root,Complex.inv_im,Complex.normSq_apply,pow_two]

lemma left_radial (x y t : ℝ) :
    point .left x y t = ((1+x*t-y^2*t^2/4 : ℝ) : ℂ)*base x y := by
  dsimp [point,velocity,acceleration]
  push_cast
  ring
lemma right_radial (x y t : ℝ) :
    point .right x y t-(t : ℂ) = ((1-x*t-y^2*t^2/4 : ℝ) : ℂ)*base x y := by
  dsimp [point,velocity,acceleration]
  push_cast
  ring

def radialAnchor (k : Shape) (t : ℝ) : ℂ := if k=.left then 0 else t

lemma radial_collinear (k : Shape) (hk : k≠.middle) (x y u v t : ℝ)
    (hy : y≠0) (hv : v≠0) (h : x*v-u*y=0) :
    Collinear ℝ {radialAnchor k t,point k x y t,point k u v t} := by
  have hb : cross (base x y) (base u v)=0 := by
    simp only [cross,base_re,base_im]
    field_simp [norm_root_ne_zero hy,norm_root_ne_zero hv]
    linear_combination -h
  apply SquaredBimedians.collinear_of_cross
  change cross (point k x y t-radialAnchor k t)
    (point k u v t-radialAnchor k t)=0
  cases k
  · simp only [radialAnchor,if_pos,sub_zero,left_radial]
    rw [cross_smul_left,cross_smul_right,hb]
    ring
  · simp only [radialAnchor,show (Shape.right=Shape.left)=False by decide,if_false,
      right_radial]
    rw [cross_smul_left,cross_smul_right,hb]
    ring
  · exact False.elim (hk rfl)

lemma circle_equation (k : Shape) (hk : k≠.middle) (x y t : ℝ) (hy : y≠0) :
    (point k x y t).re^2+(point k x y t).im^2-
      t*(point k x y t).re-(-1/y+y*t^2/4)*(point k x y t).im=0 := by
  cases k
  case middle => exact False.elim (hk rfl)
  all_goals
    simp only [point,velocity,acceleration,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,←Complex.ofReal_pow,
      base_re,base_im,Complex.one_re,Complex.one_im]
    field_simp [hy,norm_root_ne_zero hy]
    ring

lemma cospherical_of_equations (t K : ℝ) (z w : ℂ)
    (hz : z.re^2+z.im^2-t*z.re-K*z.im=0)
    (hw : w.re^2+w.im^2-t*w.re-K*w.im=0) :
    Cospherical ({0,(t : ℂ),z,w} : Set ℂ) := by
  let o : ℂ := ⟨t/2,K/2⟩
  refine ⟨o,dist 0 o,?_⟩
  rintro p (rfl | rfl | rfl | rfl)
  · rfl
  all_goals
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.zero_re,Complex.zero_im]
    dsimp [o]
    nlinarith

/-- Points of either radial type with the same reciprocal height lie on a
single circle through both splitting anchors. -/
lemma equal_height_cospherical (k l : Shape) (hk : k≠.middle) (hl : l≠.middle)
    (x u y t : ℝ) (hy : y≠0) :
    Cospherical ({0,(t : ℂ),point k x y t,point l u y t} : Set ℂ) :=
  cospherical_of_equations t (-1/y+y*t^2/4) _ _
    (circle_equation k hk x y t hy) (circle_equation l hl u y t hy)

lemma same_type_conjugate (k : Shape) (hk : k≠.middle) (x y u v t : ℝ)
    (hy : y≠0) (hv : v≠0) (h : PairType k k x y u v)
    (hline : ¬Collinear ℝ {radialAnchor k t,point k x y t,point k u v t})
    (hcircle : ¬Cospherical ({0,(t : ℂ),point k x y t,point k u v t} : Set ℂ)) :
    u=x ∧ v=-y ∧ x≠0 := by
  have hf : x*v-u*y≠0 := fun hh => hline (radial_collinear k hk x y u v t hy hv hh)
  have hne : y≠v := by
    intro hh
    subst v
    exact hcircle (equal_height_cospherical k k hk hk x u y t hy)
  obtain he | ⟨he,he'⟩ := same_type k hk x y u v hy hv h
  · exact False.elim (hne he)
  have hx : x=u := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hf)
  have hsum : y+v=0 := (mul_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hf)).resolve_left
    (sub_ne_zero.mpr hne)
  have hv' : v=-y := by linarith
  refine ⟨hx.symm,hv',?_⟩
  intro hh
  apply hf
  rw [←hx,hh]
  ring

lemma mixed_constraint (x y u v : ℝ) (hy : y≠0) (hv : v≠0)
    (h : PairType .left .right x y u v) (hne : y≠v) (hopp : y≠-v) :
    u*y+v*x=0 := by
  have hnv : y-v≠0 := sub_ne_zero.mpr hne
  have hsum : y+v≠0 := by intro hh; apply hopp; linarith
  obtain h | ⟨h,h'⟩ := mixed_type x y u v hy hv h
  · exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hnv)
  have hdot : u*x+v*y=0 := (mul_eq_zero.mp h).resolve_left hnv
  have hcross : x*v-u*y=0 := (mul_eq_zero.mp h').resolve_left (mul_ne_zero hnv hsum)
  have hh : v*(x^2+y^2)=0 := by linear_combination y*hdot+x*hcross
  exact False.elim ((mul_ne_zero hv (norm_root_ne_zero hy)) hh)

lemma mixed_constraint_either (k l : Shape) (hk : k≠.middle) (hl : l≠.middle)
    (hkl : k≠l) (x y u v : ℝ) (hy : y≠0) (hv : v≠0)
    (h : PairType k l x y u v) (hne : y≠v) (hopp : y≠-v) :
    u*y+v*x=0 := by
  cases k <;> cases l
  all_goals try contradiction
  · exact mixed_constraint x y u v hy hv h hne hopp
  · have hh := mixed_constraint u v x y hv hy h.symm hne.symm
      (by intro hh; apply hopp; linarith)
    linear_combination hh

/-- A conjugate pair of one radial type cannot coexist in general position
with a point of the other radial type. -/
lemma conjugate_pair_mixed_obstruction (k l : Shape) (hk : k≠.middle)
    (hl : l≠.middle) (hkl : k≠l) (x y u v t : ℝ)
    (hx : x≠0) (hy : y≠0) (hv : v≠0)
    (h : PairType k l x y u v) (h' : PairType k l x (-y) u v)
    (hc : ¬Cospherical ({0,(t : ℂ),point k x y t,point l u v t} : Set ℂ))
    (hc' : ¬Cospherical ({0,(t : ℂ),point k x (-y) t,point l u v t} : Set ℂ)) :
    False := by
  have hn : y≠v := by
    intro hh; subst v
    exact hc (equal_height_cospherical k l hk hl x u y t hy)
  have hn' : -y≠v := by
    intro hh; subst v
    exact hc' (equal_height_cospherical k l hk hl x u (-y) t (neg_ne_zero.mpr hy))
  have hh := mixed_constraint_either k l hk hl hkl x y u v hy hv h hn
    (by intro he; apply hn'; linarith)
  have hh' := mixed_constraint_either k l hk hl hkl x (-y) u v (neg_ne_zero.mpr hy)
    hv h' hn' (by intro he; apply hn; linarith)
  apply mul_ne_zero hv hx
  linear_combination (hh+hh')/2

lemma middle_product_real (x y u v : ℝ) (hy : y≠0) (hv : v≠0)
    (hne : root x y≠root u v) (h : PairType .middle .middle x y u v) :
    u*y+v*x=0 := by
  have hz := root_ne_zero (x:=x) hy
  have hw := root_ne_zero (x:=u) hv
  have hs := h.mul (root x y*root u v)
  have hA := (scaled_difference (root x y) (root u v) 0 0 0 0 hz hw).1
  have hB : (root x y*root u v)*(velocity .middle x y-velocity .middle u v)=0 := by
    simp [velocity]
  have hC : (root x y*root u v)*
      (acceleration .middle x y-acceleration .middle u v)=
      ((1/16 : ℝ) : ℂ)*(root x y-root u v)*(root x y*root u v) := by
    dsimp [acceleration]
    push_cast
    ring
  change (root x y*root u v)*(base x y-base u v)=root u v-root x y at hA
  rw [hA,hB,hC] at hs
  rcases hs with hs | ⟨_,hs⟩
  · have hh : (root u v-root x y)^2*root x y*root u v=0 := by
      push_cast at hs
      linear_combination 4*hs
    exact False.elim ((mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (sub_ne_zero.mpr hne.symm)) hz) hw) hh)
  · have hn : (u-x)^2+(v-y)^2≠0 := by
      intro hh
      have hr : u=x := by nlinarith [sq_nonneg (v-y)]
      have hi : v=y := by nlinarith [sq_nonneg (u-x)]
      exact hne (by rw [hr,hi])
    have hh : (u*y+v*x)*((u-x)^2+(v-y)^2)=0 := by
      simp only [cross,root,Complex.sub_re,Complex.sub_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] at hs
      linear_combination -16*hs
    exact (mul_eq_zero.mp hh).resolve_right hn

lemma middle_re (y t : ℝ) : (point .middle 0 y t).re=t/2 := by
  simp [point,velocity,acceleration,base_re,root,pow_two,
    Complex.mul_re,Complex.mul_im]
  ring

lemma middle_triple_collinear (x y u v r s t : ℝ) (hy : y≠0) (hv : v≠0) (hs : s≠0)
    (h01 : root x y≠root u v) (h02 : root x y≠root r s) (h12 : root u v≠root r s)
    (h : PairType .middle .middle x y u v)
    (h' : PairType .middle .middle x y r s)
    (h'' : PairType .middle .middle u v r s) :
    Collinear ℝ {point .middle x y t,point .middle u v t,point .middle r s t} := by
  have h0 := middle_product_real x y u v hy hv h01 h
  have h1 := middle_product_real x y r s hy hs h02 h'
  have h2 := middle_product_real u v r s hv hs h12 h''
  have hh : x*v*s=0 := by linear_combination (v*h1+s*h0-y*h2)/2
  have hx : x=0 := (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hs)).resolve_right hv
  have hu : u=0 := by
    rw [hx,mul_zero,add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right hy
  have hr : r=0 := by
    rw [hx,mul_zero,add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hy
  rw [hx,hu,hr]
  apply SquaredBimedians.collinear_of_cross
  change cross (point .middle 0 v t-point .middle 0 y t)
    (point .middle 0 s t-point .middle 0 y t)=0
  simp [cross,middle_re]

set_option maxRecDepth 100000 in
lemma five_shapes : ∀ f : Fin 5 → Shape, ∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧
    ((f i=f j ∧ f j=f k) ∨
      (f i=f j ∧ f i≠.middle ∧ f k≠.middle ∧ f i≠f k)) := by decide

/-- Indexed general-position conditions needed by the obstruction. The four
point condition always includes the two splitting anchors. -/
structure SplittingGP {ι : Type*} (t : ℝ) (p : ι → ℂ) : Prop where
  injective : Function.Injective p
  anchor_line : ∀ i, ¬Collinear ℝ {0,(t : ℂ),p i}
  left_line : ∀ i j, i≠j → ¬Collinear ℝ {0,p i,p j}
  right_line : ∀ i j, i≠j → ¬Collinear ℝ {(t : ℂ),p i,p j}
  outer_line : ∀ i j k, i≠j → i≠k → j≠k → ¬Collinear ℝ {p i,p j,p k}
  circle : ∀ i j, i≠j → ¬Cospherical ({0,(t : ℂ),p i,p j} : Set ℂ)

lemma SplittingGP.radial_line {ι : Type*} {t : ℝ} {p : ι → ℂ} (h : SplittingGP t p)
    (k : Shape) (i j : ι) (hij : i≠j) :
    ¬Collinear ℝ {radialAnchor k t,p i,p j} := by
  dsimp [radialAnchor]
  split_ifs
  · exact h.left_line i j hij
  · exact h.right_line i j hij

/-- In the normalized two-anchor model there cannot be five exterior points
in general position, if their nonreal initial positions are distinct and all
pairwise quadratic norm polynomials satisfy the square-type classification. -/
theorem no_five_exterior_shapes (k : Fin 5 → Shape) (x y : Fin 5 → ℝ)
    (hy : ∀ i, y i≠0) (hinit : Function.Injective (fun i => root (x i) (y i)))
    (hpair : ∀ i j, i≠j → PairType (k i) (k j) (x i) (y i) (x j) (y j)) (t : ℝ) :
    ¬SplittingGP t (fun i => point (k i) (x i) (y i) t) := by
  intro hg
  obtain ⟨i,j,l,hij,hil,hjl,hshape⟩ := five_shapes k
  rcases hshape with ⟨he,he'⟩ | ⟨he,hk,hl,hkl⟩
  · by_cases hk : k i=.middle
    · have hj : k j=.middle := he ▸ hk
      have hl : k l=.middle := he' ▸ hj
      apply hg.outer_line i j l hij hil hjl
      simp only [hk,hj,hl]
      exact middle_triple_collinear (x i) (y i) (x j) (y j) (x l) (y l) t
        (hy i) (hy j) (hy l) (hinit.ne hij) (hinit.ne hil) (hinit.ne hjl)
        (by simpa only [hk,hj] using hpair i j hij)
        (by simpa only [hk,hl] using hpair i l hil)
        (by simpa only [hj,hl] using hpair j l hjl)
    · have hab := same_type_conjugate (k i) hk (x i) (y i) (x j) (y j) t
        (hy i) (hy j) (by simpa only [←he] using hpair i j hij)
        (by simpa only [←he] using hg.radial_line (k i) i j hij)
        (by simpa only [←he] using hg.circle i j hij)
      have hac := same_type_conjugate (k i) hk (x i) (y i) (x l) (y l) t
        (hy i) (hy l) (by simpa only [←he',←he] using hpair i l hil)
        (by simpa only [←he',←he] using hg.radial_line (k i) i l hil)
        (by simpa only [←he',←he] using hg.circle i l hil)
      apply hjl
      apply hinit
      dsimp only
      rw [hab.1,hab.2.1,hac.1,hac.2.1]
  · have hab := same_type_conjugate (k i) hk (x i) (y i) (x j) (y j) t
      (hy i) (hy j) (by simpa only [←he] using hpair i j hij)
      (by simpa only [←he] using hg.radial_line (k i) i j hij)
      (by simpa only [←he] using hg.circle i j hij)
    exact conjugate_pair_mixed_obstruction (k i) (k l) hk hl hkl
      (x i) (y i) (x l) (y l) t hab.2.2 (hy i) (hy l) (hpair i l hil)
      (by simpa only [←he,hab.1,hab.2.1] using hpair j l hjl)
      (hg.circle i l hil)
      (by simpa only [←he,hab.1,hab.2.1] using hg.circle j l hjl)

lemma root_re_im (a : ℂ) : root a.re a.im=a := rfl

lemma base_inverse (a : ℂ) : base (a⁻¹).re (a⁻¹).im=a := by
  rw [base,root_re_im,inv_inv]

lemma normal_form_shape (a b c : ℂ) (hai : a.im≠0)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a b c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a (b-1) c))) :
    ∃ k : Shape, b=velocity k (a⁻¹).re (a⁻¹).im ∧
      c=acceleration k (a⁻¹).re (a⁻¹).im := by
  rcases two_anchor_normal_form a b c hai h0 h1 with h | h | h
  · exact ⟨.left,by simpa only [velocity,acceleration,base_inverse] using h⟩
  · exact ⟨.right,by simpa only [velocity,acceleration,base_inverse] using h⟩
  · refine ⟨.middle,h.1,?_⟩
    rw [h.2,acceleration,root_re_im]
    simp only [mul_inv_rev,div_eq_mul_inv]
    ring

lemma real_initial_collinear (a b c : ℂ) (ha : a≠0) (hai : a.im=0)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a b c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a (b-1) c))) (t : ℝ) :
    Collinear ℝ {0,(t : ℂ),a+b*t+c*t^2} := by
  have he : (a.re : ℂ)=a := Complex.ext (by simp) (by simpa using hai.symm)
  have har : a.re≠0 := by intro hh; apply ha; rw [←he,hh]; simp
  have hs0 : squaredNorm a b c=normPolynomial a.re b c := by
    simp only [squaredNorm,normPolynomial,hai]
  have hs1 : squaredNorm a (b-1) c=normPolynomial a.re (b-1) c := by
    simp only [squaredNorm,normPolynomial,hai]
  have hh := real_initial_coefficients a.re har b c (by rwa [←hs0]) (by rwa [←hs1])
  apply SquaredBimedians.collinear_of_cross
  change cross ((t : ℂ)-0) (a+b*t+c*t^2-0)=0
  simp [cross,Complex.mul_im,Complex.mul_re,pow_two,hai,hh.1,hh.2]

/-- Seven-point obstruction in the normalized quadratic splitting model.
The initial exterior points must be distinct and nonzero. All square
hypotheses are identities in `ℝ(t)`; no conclusion follows merely from
rational distances at one specialization. -/
theorem no_five_exterior_quadratics (a b c : Fin 5 → ℂ)
    (ha : ∀ i, a i≠0) (hinit : Function.Injective a)
    (h0 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm (a i) (b i) (c i))))
    (h1 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm (a i) (b i-1) (c i))))
    (hp : ∀ i j, i≠j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a j) (b i-b j) (c i-c j)))) (t : ℝ) :
    ¬SplittingGP t (fun i => a i+b i*t+c i*t^2) := by
  intro hg
  have hai : ∀ i, (a i).im≠0 := by
    intro i hi
    exact hg.anchor_line i (real_initial_collinear (a i) (b i) (c i)
      (ha i) hi (h0 i) (h1 i) t)
  choose k hk using fun i => normal_form_shape (a i) (b i) (c i) (hai i) (h0 i) (h1 i)
  let x : Fin 5 → ℝ := fun i => ((a i)⁻¹).re
  let y : Fin 5 → ℝ := fun i => ((a i)⁻¹).im
  have hbase : ∀ i, base (x i) (y i)=a i := fun i => base_inverse (a i)
  have hy : ∀ i, y i≠0 := by
    intro i
    dsimp [y]
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr (hai i)) (ne_of_gt (Complex.normSq_pos.mpr (ha i)))
  have hi : Function.Injective (fun i => root (x i) (y i)) := by
    intro i j he
    apply hinit
    change (a i)⁻¹=(a j)⁻¹ at he
    exact inv_injective he
  have ht : ∀ i j, i≠j → PairType (k i) (k j) (x i) (y i) (x j) (y j) := by
    intro i j hij
    dsimp only [PairType]
    rw [hbase i,hbase j,←(hk i).1,←(hk j).1,←(hk i).2,←(hk j).2]
    exact GeneralQuadraticType.quadratic_type_ratFunc (a i-a j) (b i-b j) (c i-c j)
      (sub_ne_zero.mpr (hinit.ne hij)) (hp i j hij)
  have he : (fun i => point (k i) (x i) (y i) t)=(fun i => a i+b i*t+c i*t^2) := by
    funext i
    dsimp only [point]
    rw [hbase i,←(hk i).1,←(hk i).2]
  apply no_five_exterior_shapes k x y hy hi ht t
  rwa [he]

lemma SplittingGP.of_set {ι : Type*} (S : Set ℂ) (t : ℝ) (p : ι → ℂ)
    (ht : t≠0) (hinj : Function.Injective p) (hp0 : ∀ i, p i≠0)
    (hpt : ∀ i, p i≠(t : ℂ)) (h0S : 0∈S) (htS : (t : ℂ)∈S) (hpS : ∀ i, p i∈S)
    (htri : NonTrilinear S)
    (hcirc : ∀ Q : Set ℂ, Q⊆S ∧ Q.ncard=4 → ¬Cospherical Q) :
    SplittingGP t p := by
  have ht' : (t : ℂ)≠0 := by exact_mod_cast ht
  refine ⟨hinj,?_,?_,?_,?_,?_⟩
  · intro i
    exact htri h0S htS (hpS i) ht'.symm (hpt i).symm (hp0 i).symm
  · intro i j hij
    exact htri h0S (hpS i) (hpS j) (hp0 i).symm (hinj.ne hij) (hp0 j).symm
  · intro i j hij
    exact htri htS (hpS i) (hpS j) (hpt i).symm (hinj.ne hij) (hpt j).symm
  · intro i j k hij hik hjk
    exact htri (hpS i) (hpS j) (hpS k) (hinj.ne hij) (hinj.ne hjk) (hinj.ne hik)
  · intro i j hij
    apply hcirc {0,(t : ℂ),p i,p j}
    constructor
    · rintro z (rfl | rfl | rfl | rfl)
      · exact h0S
      · exact htS
      · exact hpS i
      · exact hpS j
    · exact Set.ncard_eq_four.mpr ⟨0,(t : ℂ),p i,p j,ht'.symm,(hp0 i).symm,
        (hp0 j).symm,(hpt i).symm,(hpt j).symm,hinj.ne hij,rfl⟩

/-- Set-level form: a general-position set cannot contain the seven distinct
points of such a normalized quadratic splitting family. No assertion is
made that an arbitrary rational-distance set admits this kind of family. -/
theorem no_seven_quadratic_splitting (a b c : Fin 5 → ℂ)
    (ha : ∀ i, a i≠0) (hinit : Function.Injective a)
    (h0 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm (a i) (b i) (c i))))
    (h1 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm (a i) (b i-1) (c i))))
    (hp : ∀ i j, i≠j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a j) (b i-b j) (c i-c j))))
    (S : Set ℂ) (t : ℝ) (ht : t≠0)
    (hinj : Function.Injective (fun i => a i+b i*t+c i*t^2))
    (hp0 : ∀ i, a i+b i*t+c i*t^2≠0)
    (hpt : ∀ i, a i+b i*t+c i*t^2≠(t : ℂ))
    (h0S : 0∈S) (htS : (t : ℂ)∈S) (hpS : ∀ i, a i+b i*t+c i*t^2∈S) :
    ¬ (NonTrilinear S ∧ (∀ Q : Set ℂ, Q⊆S ∧ Q.ncard=4 → ¬Cospherical Q)) := by
  rintro ⟨htri,hcirc⟩
  exact no_five_exterior_quadratics a b c ha hinit h0 h1 hp t
    (SplittingGP.of_set S t _ ht hinj hp0 hpt h0S htS hpS htri hcirc)

#print axioms no_five_exterior_shapes
#print axioms no_five_exterior_quadratics
#print axioms no_seven_quadratic_splitting
end
end Erdos213.TwoAnchorGeometry
