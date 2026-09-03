import Submission.DirectionNineBound
import Submission.HeptadCircleCubic
import Submission.ThreeRowBuchi

/-! Every admissible input to the standard two-variable heptad is in general
position. This proves a property of seven points only, not Erdős 213. -/
open EuclideanGeometry
namespace Erdos213.HeptadAutomaticGP
open DirectionInvolutions
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The complete list of irreducible determinant factors. -/
def factor (r s : ℚ) : Fin 16 → ℚ :=
  ![r,s,r+s+1,2*r+2*s-1,2*r-s+2,r-2*s-2,r-1,s-1,r-s,
    r+s-1,r-s+1,r-s-1,2*r-s-1,r+s-2,r-2*s+1,HeptadCircleCubic.cubic r s]

lemma factors_ne_zero {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    ∀ i : Fin 16, factor r (r+2*x+1) i≠0 := by
  obtain ⟨hxhalf,hr1,hrs⟩ := old_norm_excludes_symmetry hr hsq
  obtain ⟨hx0,hxm1,_⟩ := old_norm_excludes_midpoints hr hsq
  obtain ⟨hrx,_,_,_⟩ := old_norm_more_exclusions hr hsq
  have hr0 : 0<r := lt_of_le_of_lt (sq_nonneg x) hr
  have hs0 : 0<r+2*x+1 := by nlinarith [sq_nonneg (x+1)]
  have hn3 : ¬IsSquare (3 : ℚ) := by norm_num
  intro i
  fin_cases i
  · exact ne_of_gt hr0
  · exact ne_of_gt hs0
  · change r+(r+2*x+1)+1≠0; positivity
  · change 2*r+2*(r+2*x+1)-1≠0
    have hp : 0<2*r+2*(r+2*x+1)-1 := by nlinarith [sq_nonneg (2*x+1)]
    exact ne_of_gt hp
  · change 2*r-(r+2*x+1)+2≠0
    have hp : 0<2*r-(r+2*x+1)+2 := by nlinarith [sq_nonneg (x-1)]
    exact ne_of_gt hp
  · change r-2*(r+2*x+1)-2≠0
    have hp : r-2*(r+2*x+1)-2<0 := by nlinarith [sq_nonneg (x+2)]
    exact ne_of_lt hp
  · change r-1≠0; exact sub_ne_zero.mpr hr1
  · change r+2*x+1-1≠0; intro h; apply hrs; linarith
  · change r-(r+2*x+1)≠0; intro h; apply hxhalf; linarith
  · change r+(r+2*x+1)-1≠0; intro h; apply hrx; linarith
  · change r-(r+2*x+1)+1≠0; intro h; apply hx0; linarith
  · change r-(r+2*x+1)-1≠0; intro h; apply hxm1; linarith
  · change 2*r-(r+2*x+1)-1≠0
    intro h
    obtain ⟨a,ha⟩ := hsq 3
    change (1 : ℚ)^2-2*x*1*1+r*1^2=a*a at ha
    apply hn3
    exact ⟨a,by nlinarith only [h,ha]⟩
  · change r+(r+2*x+1)-2≠0
    intro h
    obtain ⟨a,ha⟩ := hsq 4
    change (-1 : ℚ)^2-2*x*(-1)*2+r*2^2=a*a at ha
    apply hn3
    exact ⟨a,by nlinarith only [h,ha]⟩
  · change r-2*(r+2*x+1)+1≠0
    intro h
    obtain ⟨a,ha⟩ := hsq 5
    change (-2 : ℚ)^2-2*x*(-2)*1+r*1^2=a*a at ha
    apply hn3
    exact ⟨a,by nlinarith only [h,ha]⟩
  · exact HeptadCircleCubic.cubic_ne_zero_of_positive hr0 hs0

def px (x r : ℚ) : Fin 7 → ℚ :=
  ![0,x,-2*x^2+r-x,-x-1,-4*x^2+2*r,-2,-4*x^2+2*r-4*x-2]
def py (x : ℚ) : Fin 7 → ℚ := ![0,1,-2*x-1,-1,-4*x,0,-4*x-4]
def sqDist (x r : ℚ) (i j : Fin 7) : ℚ :=
  (px x r i-px x r j)^2+(r-x^2)*(py x i-py x j)^2
def triangle (x r : ℚ) (i j k : Fin 7) : ℚ :=
  (px x r j-px x r i)*(py x k-py x i)-(py x j-py x i)*(px x r k-px x r i)
def circle (x r : ℚ) (i j k l : Fin 7) : ℚ :=
  ThreeRowBuchi.det3 (px x r j-px x r i) (py x j-py x i) (sqDist x r i j)
    (px x r k-px x r i) (py x k-py x i) (sqDist x r i k)
    (px x r l-px x r i) (py x l-py x i) (sqDist x r i l)

def triIndices : Fin 35 → Fin 7 × Fin 7 × Fin 7 :=
  ![(0,1,2),(0,1,3),(0,1,4),(0,1,5),(0,1,6),(0,2,3),(0,2,4),(0,2,5),(0,2,6),(0,3,4),(0,3,5),(0,3,6),(0,4,5),(0,4,6),(0,5,6),(1,2,3),(1,2,4),(1,2,5),(1,2,6),(1,3,4),(1,3,5),(1,3,6),(1,4,5),(1,4,6),(1,5,6),(2,3,4),(2,3,5),(2,3,6),(2,4,5),(2,4,6),(2,5,6),(3,4,5),(3,4,6),(3,5,6),(4,5,6)]

def triValue (r s : ℚ) : Fin 35 → ℚ :=
  ![(-1)*(factor r s 0),
    (1),
    (-2)*(factor r s 0),
    (2),
    (-2)*(factor r s 6),
    (-1)*(factor r s 1),
    (2)*(factor r s 0),
    (2)*(factor r s 8),
    (-2)*(factor r s 1),
    (2)*(factor r s 7),
    (-2),
    (2)*(factor r s 1),
    (4)*(factor r s 10),
    (-4)*(factor r s 9),
    (-4)*(factor r s 11),
    (-1)*(factor r s 2),
    (3)*(factor r s 0),
    (factor r s 5),
    (factor r s 5),
    (factor r s 3),
    (-3),
    (factor r s 3),
    (2)*(factor r s 14),
    (-2)*(factor r s 3),
    (-2)*(factor r s 5),
    (-1)*(factor r s 4),
    (-1)*(factor r s 4),
    (3)*(factor r s 1),
    (2)*(factor r s 4),
    (-2)*(factor r s 13),
    (-2)*(factor r s 5),
    (2)*(factor r s 4),
    (-2)*(factor r s 3),
    (-2)*(factor r s 12),
    (4)*(factor r s 2)]

lemma triValue_ne_zero (r s : ℚ) (h : ∀ i, factor r s i≠0) (j : Fin 35) :
    triValue r s j≠0 := by
  fin_cases j <;> simp [triValue,h]

lemma trifactorization (x r : ℚ) (a : Fin 35) :
    triangle x r (triIndices a).1 (triIndices a).2.1 (triIndices a).2.2=triValue r (r+2*x+1) a := by
  fin_cases a <;> dsimp [triIndices,triValue,triangle,sqDist,px,py,ThreeRowBuchi.det3,factor,HeptadCircleCubic.cubic] <;> ring

lemma triIndices_complete : ∀ i j k : Fin 7, i<j → j<k → ∃ a, triIndices a=(i,j,k) := by
  decide +kernel

lemma triangle_sorted_ne {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (i j k : Fin 7) (hij : i<j) (hjk : j<k) : triangle x r i j k≠0 := by
  obtain ⟨a,ha⟩ := triIndices_complete i j k hij hjk
  have he := trifactorization x r a
  rw [ha] at he
  rw [he]
  exact triValue_ne_zero r (r+2*x+1) (factors_ne_zero hr hsq) a

def cirIndices : Fin 35 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(0,1,2,3),(0,1,2,4),(0,1,2,5),(0,1,2,6),(0,1,3,4),(0,1,3,5),(0,1,3,6),(0,1,4,5),(0,1,4,6),(0,1,5,6),(0,2,3,4),(0,2,3,5),(0,2,3,6),(0,2,4,5),(0,2,4,6),(0,2,5,6),(0,3,4,5),(0,3,4,6),(0,3,5,6),(0,4,5,6),(1,2,3,4),(1,2,3,5),(1,2,3,6),(1,2,4,5),(1,2,4,6),(1,2,5,6),(1,3,4,5),(1,3,4,6),(1,3,5,6),(1,4,5,6),(2,3,4,5),(2,3,4,6),(2,3,5,6),(2,4,5,6),(3,4,5,6)]

def cirValue (r s : ℚ) : Fin 35 → ℚ :=
  ![(-3)*(factor r s 0)*(factor r s 1),
    (-2)*(factor r s 0)^2*(factor r s 12),
    (2)*(factor r s 0)*(factor r s 5),
    (2)*(factor r s 0)*(factor r s 1)*(factor r s 5),
    (2)*(factor r s 0)*(factor r s 3),
    (-2)*(factor r s 13),
    (2)*(factor r s 1)*(factor r s 3),
    (-4)*(factor r s 0)*(factor r s 2),
    (4)*(factor r s 0)*(factor r s 11)*(factor r s 3),
    (-4)*(factor r s 5)*(factor r s 9),
    (-2)*(factor r s 0)*(factor r s 1)*(factor r s 4),
    (-2)*(factor r s 1)*(factor r s 4),
    (2)*(factor r s 1)^2*(factor r s 14),
    (-4)*(factor r s 0)*(factor r s 11)*(factor r s 4),
    (4)*(factor r s 0)*(factor r s 1)*(factor r s 2),
    (-4)*(factor r s 1)*(factor r s 5)*(factor r s 10),
    (4)*(factor r s 9)*(factor r s 4),
    (-4)*(factor r s 1)*(factor r s 10)*(factor r s 3),
    (-4)*(factor r s 1)*(factor r s 2),
    (-16)*(factor r s 15),
    (-1)*(factor r s 0)*(factor r s 4)*(factor r s 3),
    (factor r s 5)*(factor r s 4),
    (factor r s 1)*(factor r s 5)*(factor r s 3),
    (-2)*(factor r s 0)*(factor r s 5)*(factor r s 4),
    (-2)*(factor r s 0)*(factor r s 5)*(factor r s 3),
    (-2)*(factor r s 7)*(factor r s 5)^2,
    (2)*(factor r s 4)*(factor r s 3),
    (-2)*(factor r s 8)*(factor r s 3)^2,
    (2)*(factor r s 5)*(factor r s 3),
    (-4)*(factor r s 5)*(factor r s 10)*(factor r s 3),
    (2)*(factor r s 6)*(factor r s 4)^2,
    (-2)*(factor r s 1)*(factor r s 4)*(factor r s 3),
    (2)*(factor r s 1)*(factor r s 5)*(factor r s 4),
    (-4)*(factor r s 5)*(factor r s 9)*(factor r s 4),
    (-4)*(factor r s 11)*(factor r s 4)*(factor r s 3)]

lemma cirValue_ne_zero (r s : ℚ) (h : ∀ i, factor r s i≠0) (j : Fin 35) :
    cirValue r s j≠0 := by
  fin_cases j <;> simp [cirValue,h]

lemma cirfactorization (x r : ℚ) (a : Fin 35) :
    circle x r (cirIndices a).1 (cirIndices a).2.1 (cirIndices a).2.2.1 (cirIndices a).2.2.2=cirValue r (r+2*x+1) a := by
  fin_cases a <;> dsimp [cirIndices,cirValue,circle,sqDist,px,py,ThreeRowBuchi.det3,factor,HeptadCircleCubic.cubic] <;> ring

lemma cirIndices_complete : ∀ i j k l : Fin 7, i<j → j<k → k<l → ∃ a, cirIndices a=(i,j,k,l) := by
  decide +kernel

lemma circle_sorted_ne {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (i j k l : Fin 7) (hij : i<j) (hjk : j<k) (hkl : k<l) : circle x r i j k l≠0 := by
  obtain ⟨a,ha⟩ := cirIndices_complete i j k l hij hjk hkl
  have he := cirfactorization x r a
  rw [ha] at he
  rw [he]
  exact cirValue_ne_zero r (r+2*x+1) (factors_ne_zero hr hsq) a

def normFactor (x r : ℚ) : Fin 5 → ℚ := ![r,r+2*x+1,r-2*x+1,4*r+4*x+1,r+4*x+4]
lemma normFactor_square {x r : ℚ}
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) (j : Fin 5) :
    IsSquare (normFactor x r j) := by
  have h1 := hsq 1; have h2 := hsq 2; have h3 := hsq 3
  have h4 := hsq 4; have h5 := hsq 5
  dsimp [form,oldRoot] at h1 h2 h3 h4 h5
  fin_cases j <;> dsimp [normFactor]
  · convert h1 using 1; ring
  · convert h2 using 1; ring
  · convert h3 using 1; ring
  · convert h4 using 1; ring
  · convert h5 using 1; ring

lemma normFactor_pos {x r : ℚ} (hr : x^2<r) (j : Fin 5) : 0<normFactor x r j := by
  fin_cases j <;> norm_num [normFactor]
  all_goals nlinarith [sq_nonneg x,sq_nonneg (x+1),sq_nonneg (x-1),sq_nonneg (2*x+1),sq_nonneg (x+2)]

def distIndices : Fin 21 → Fin 7 × Fin 7 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

def distValue (x r : ℚ) : Fin 21 → ℚ :=
  ![(normFactor x r 0),
    (normFactor x r 0)*(normFactor x r 1),
    (normFactor x r 1),
    (2 : ℚ)^2*(normFactor x r 0)^2,
    (2 : ℚ)^2,
    (2 : ℚ)^2*(normFactor x r 1)^2,
    (normFactor x r 0)*(normFactor x r 4),
    (normFactor x r 3),
    (normFactor x r 0)*(normFactor x r 3),
    (normFactor x r 4),
    (normFactor x r 4)*(normFactor x r 3),
    (normFactor x r 2)*(normFactor x r 1),
    (normFactor x r 0)*(normFactor x r 2),
    (normFactor x r 2)*(normFactor x r 4),
    (normFactor x r 1)*(normFactor x r 4),
    (normFactor x r 2)*(normFactor x r 3),
    (normFactor x r 2),
    (normFactor x r 1)*(normFactor x r 3),
    (2 : ℚ)^2*(normFactor x r 2)*(normFactor x r 1),
    (2 : ℚ)^2*(normFactor x r 3),
    (2 : ℚ)^2*(normFactor x r 0)*(normFactor x r 4)]

lemma distValue_square (x r : ℚ) (h : ∀ i, IsSquare (normFactor x r i)) (j : Fin 21) :
    IsSquare (distValue x r j) := by
  fin_cases j
  · exact (h 0)
  · exact ((h 0).mul (h 1))
  · exact (h 1)
  · exact ((IsSquare.sq (2 : ℚ)).mul (IsSquare.pow 2 (h 0)))
  · exact (IsSquare.sq (2 : ℚ))
  · exact ((IsSquare.sq (2 : ℚ)).mul (IsSquare.pow 2 (h 1)))
  · exact ((h 0).mul (h 4))
  · exact (h 3)
  · exact ((h 0).mul (h 3))
  · exact (h 4)
  · exact ((h 4).mul (h 3))
  · exact ((h 2).mul (h 1))
  · exact ((h 0).mul (h 2))
  · exact ((h 2).mul (h 4))
  · exact ((h 1).mul (h 4))
  · exact ((h 2).mul (h 3))
  · exact (h 2)
  · exact ((h 1).mul (h 3))
  · exact (((IsSquare.sq (2 : ℚ)).mul (h 2)).mul (h 1))
  · exact ((IsSquare.sq (2 : ℚ)).mul (h 3))
  · exact (((IsSquare.sq (2 : ℚ)).mul (h 0)).mul (h 4))

lemma distValue_pos {x r : ℚ} (hr : x^2<r) (j : Fin 21) : 0<distValue x r j := by
  have h0 := normFactor_pos hr 0; have h1 := normFactor_pos hr 1
  have h2 := normFactor_pos hr 2; have h3 := normFactor_pos hr 3
  have h4 := normFactor_pos hr 4
  fin_cases j <;> dsimp [distValue] <;> positivity

lemma distfactorization (x r : ℚ) (a : Fin 21) :
    sqDist x r (distIndices a).1 (distIndices a).2=distValue x r a := by
  fin_cases a <;> dsimp [distIndices,distValue,sqDist,px,py,normFactor] <;> ring

lemma distIndices_complete : ∀ i j : Fin 7, i<j → ∃ a, distIndices a=(i,j) := by
  decide +kernel

lemma sqDist_pos_sorted {x r : ℚ} (hr : x^2<r) {i j : Fin 7} (hij : i<j) :
    0<sqDist x r i j := by
  obtain ⟨a,ha⟩ := distIndices_complete i j hij
  have he := distfactorization x r a
  rw [ha] at he
  rw [he]
  exact distValue_pos hr a

lemma sqDist_square_sorted {x r : ℚ}
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) {i j : Fin 7} (hij : i<j) :
    IsSquare (sqDist x r i j) := by
  obtain ⟨a,ha⟩ := distIndices_complete i j hij
  have he := distfactorization x r a
  rw [ha] at he
  rw [he]
  exact distValue_square x r (normFactor_square hsq) a

lemma sqDist_comm (x r : ℚ) (i j : Fin 7) : sqDist x r i j=sqDist x r j i := by
  dsimp [sqDist]; ring

lemma sqDist_square {x r : ℚ}
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) (i j : Fin 7) :
    IsSquare (sqDist x r i j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact sqDist_square_sorted hsq h
  · simp [sqDist]
  · rw [sqDist_comm]; exact sqDist_square_sorted hsq h

def point (x r : ℚ) (i : Fin 7) : ℝ² :=
  !₂[(px x r i : ℝ), (py x i : ℝ)*Real.sqrt ((r-x^2 : ℚ) : ℝ)]

lemma point_dist_sq {x r : ℚ} (hr : x^2<r) (i j : Fin 7) :
    dist (point x r i) (point x r j)^2=(sqDist x r i j : ℝ) := by
  rw [InversionReduction.distance_sq]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,sqDist]
  push_cast
  have hH : 0≤((r-x^2 : ℚ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hr.le)
  have hsqrt := Real.sq_sqrt hH
  push_cast at hsqrt
  linear_combination ((py x i : ℝ)-py x j)^2 * hsqrt

lemma point_injective {x r : ℚ} (hr : x^2<r) : Function.Injective (point x r) := by
  intro i j he
  have hz : sqDist x r i j=0 := by
    have hd := point_dist_sq hr i j
    rw [he,dist_self,zero_pow (by decide : 2≠0)] at hd
    exact_mod_cast hd.symm
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (ne_of_gt (sqDist_pos_sorted hr h) hz)
  · exact h
  · rw [sqDist_comm] at hz
    exact False.elim (ne_of_gt (sqDist_pos_sorted hr h) hz)

lemma point_rational_distances {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) (i j : Fin 7) :
    dist (point x r i) (point x r j)∈Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨a,ha⟩ := sqDist_square hsq i j
  refine ⟨|a|,?_⟩
  have he := point_dist_sq hr i j
  rw [ha] at he
  push_cast at he ⊢
  apply (sq_eq_sq₀ (abs_nonneg _) dist_nonneg).mp
  rw [sq_abs]
  nlinarith only [he]

lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

lemma sorted_not_collinear {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (i j k : Fin 7) (hij : i<j) (hjk : j<k) :
    ¬Collinear ℝ {point x r i,point x r j,point x r k} := by
  intro h
  have hz := collinear_det_zero h
  have he : (triangle x r i j k : ℝ)*Real.sqrt ((r-x^2 : ℚ) : ℝ)=0 := by
    convert hz using 1
    simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,triangle]
    push_cast
    ring
  have hn : (triangle x r i j k : ℝ)≠0 := by exact_mod_cast triangle_sorted_ne hr hsq i j k hij hjk
  exact mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast (sub_pos.mpr hr))) he

lemma point_circleEval {x r : ℚ} (hr : x^2<r) (i j k l : Fin 7) :
    CircleCoverReduction.circleEval (point x r i) (point x r j) (point x r k) (point x r l)=
      (circle x r i j k l : ℝ)*Real.sqrt ((r-x^2 : ℚ) : ℝ) := by
  rw [ThreeRowBuchi.circleEval_eq_distdet]
  simp only [point_dist_sq hr]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,circle,ThreeRowBuchi.det3]
  push_cast
  ring

lemma sorted_not_generalized {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (i j k l : Fin 7) (hij : i<j) (hjk : j<k) (hkl : k<l) :
    ¬InversionReduction.OnGeneralizedCircle {point x r i,point x r j,point x r k,point x r l} := by
  intro h
  have he := CircleCoverReduction.generalized_subset_circleEval h
    (by simp : point x r i∈({point x r i,point x r j,point x r k,point x r l} : Set ℝ²))
    (by simp : point x r j∈({point x r i,point x r j,point x r k,point x r l} : Set ℝ²))
    (by simp : point x r k∈({point x r i,point x r j,point x r k,point x r l} : Set ℝ²))
    (by simp : point x r l∈({point x r i,point x r j,point x r k,point x r l} : Set ℝ²))
  change CircleCoverReduction.circleEval (point x r i) (point x r j) (point x r k) (point x r l)=0 at he
  rw [point_circleEval hr] at he
  have hn : (circle x r i j k l : ℝ)≠0 := by exact_mod_cast circle_sorted_ne hr hsq i j k l hij hjk hkl
  exact mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast (sub_pos.mpr hr))) he

lemma point_nontrilinear {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    NonTrilinear (Set.range (point x r)) := by
  classical
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij' hjk' hik' hcol
  have hij : i≠j := fun h => hij' (h ▸ rfl)
  have hik : i≠k := fun h => hik' (h ▸ rfl)
  have hjk : j≠k := fun h => hjk' (h ▸ rfl)
  let B : Finset (Fin 7) := {i,j,k}
  have hB : B.card=3 := by simp [B,hij,hik,hjk]
  let e : Fin 3 ↪o Fin 7 := B.orderEmbOfFin hB
  have hm (a : Fin 3) : point x r (e a)∈({point x r i,point x r j,point x r k} : Set ℝ²) := by
    have hh := B.orderEmbOfFin_mem hB a
    change e a∈B at hh
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh <;> rw [hh] <;> simp
  apply sorted_not_collinear hr hsq (e 0) (e 1) (e 2)
    (e.strictMono (by decide)) (e.strictMono (by decide))
  apply hcol.subset
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 2

lemma point_no_four {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    InversionReduction.NoFourGeneralized (Set.range (point x r)) := by
  classical
  intro Q hQ hcard hgen
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a∈({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b∈({point x r i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c∈({point x r i,point x r j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d∈({point x r i,point x r j,point x r k,d} : Set ℝ²))
  have hij : i≠j := fun h => hab (h ▸ rfl)
  have hik : i≠k := fun h => hac (h ▸ rfl)
  have hil : i≠l := fun h => had (h ▸ rfl)
  have hjk : j≠k := fun h => hbc (h ▸ rfl)
  have hjl : j≠l := fun h => hbd (h ▸ rfl)
  have hkl : k≠l := fun h => hcd (h ▸ rfl)
  let B : Finset (Fin 7) := {i,j,k,l}
  have hB : B.card=4 := Finset.card_eq_four.mpr ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩
  let e : Fin 4 ↪o Fin 7 := B.orderEmbOfFin hB
  have hm (a : Fin 4) : point x r (e a)∈
      ({point x r i,point x r j,point x r k,point x r l} : Set ℝ²) := by
    have hh := B.orderEmbOfFin_mem hB a
    change e a∈B at hh
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh <;> rw [hh] <;> simp
  apply sorted_not_generalized hr hsq (e 0) (e 1) (e 2) (e 3)
    (e.strictMono (by decide)) (e.strictMono (by decide)) (e.strictMono (by decide))
  apply InversionReduction.generalized_mono hgen
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3

/-- Arithmetic admissibility automatically excludes all triangle and circle
degeneracies for this particular seven-point formula. -/
theorem point_general_position {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    InGeneralPosition (Set.range (point x r)) := by
  refine ⟨point_nontrilinear hr hsq,?_⟩
  intro Q hQ h4 hc
  exact point_no_four hr hsq Q hQ h4 (InversionReduction.generalized_of_cospherical hc)

/-- The concrete standard heptad, not just an abstract seven-point witness,
has all the desired properties for every admissible arithmetic input. -/
theorem standard_heptad {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    (Set.range (point x r)).ncard=7 ∧
    InGeneralPosition (Set.range (point x r)) ∧
    ∀ i j : Fin 7, dist (point x r i) (point x r j)∈Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨?_,point_general_position hr hsq,point_rational_distances hr hsq⟩
  rw [Set.ncard_range_of_injective (point_injective hr)]
  simp

#print axioms factors_ne_zero
#print axioms triangle_sorted_ne
#print axioms circle_sorted_ne
#print axioms point_rational_distances
#print axioms point_general_position
#print axioms standard_heptad
end
end Erdos213.HeptadAutomaticGP
