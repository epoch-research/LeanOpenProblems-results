import Submission.FixedSourceLocal

/-! A fixed-source obstruction to finite-local sufficiency, not a solution of
Erdős 213. The eighth point below deliberately has irrational distances. -/
open EuclideanGeometry
namespace Erdos213.FixedHeptadLocal
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [p4_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)


def threshold : ℤ := 1640000000000000
def px (t : ℤ) : Fin 8 → ℤ :=
  ![0,49595290,19079044,32142553,17615968,26127018,7344908,-2001*t]
def py (t : ℤ) : Fin 8 → ℤ :=
  ![0,0,54168,-411864,-238464,-932064,-411864,2*t]
def sqDist (t : ℤ) (i j : Fin 8) : ℤ :=
  (px t i-px t j)^2+2002*(py t i-py t j)^2
def triangle (t : ℤ) (i j k : Fin 8) : ℤ :=
  (px t j-px t i)*(py t k-py t i)-(py t j-py t i)*(px t k-px t i)
def circle (t : ℤ) (i j k l : Fin 8) : ℤ :=
  det3 (px t j-px t i) (py t j-py t i) (sqDist t i j)
    (px t k-px t i) (py t k-py t i) (sqDist t i k)
    (px t l-px t i) (py t l-py t i) (sqDist t i l)

lemma px_injective {t : ℤ} (ht : threshold≤t) : Function.Injective (px t) := by
  have ht0 : 0<t := by dsimp [threshold] at ht; omega
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num [px] at he
  all_goals first | rfl | exfalso; linarith

lemma triangle_ne {t : ℤ} (ht : threshold≤t)
    (i j k : Fin 8) (hij : i≠j) (hjk : j≠k) (hik : i≠k) : triangle t i j k≠0 := by
  let s := t-threshold
  have hs : 0≤s := sub_nonneg.mpr ht
  have he : t=threshold+s := by dsimp [s]; ring
  rw [he]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k
  all_goals norm_num at hjk
  all_goals norm_num at hik
  all_goals norm_num [triangle,px,py,threshold]
  all_goals ring_nf
  all_goals first
    | exact ne_of_gt (by positivity)
    | apply neg_ne_zero.mp; ring_nf; exact ne_of_gt (by positivity)

lemma circle_sorted_ne {t : ℤ} (ht : threshold≤t)
    (i j k l : Fin 8) (hij : i<j) (hjk : j<k) (hkl : k<l) : circle t i j k l≠0 := by
  let s := t-threshold
  have hs : 0≤s := sub_nonneg.mpr ht
  have he : t=threshold+s := by dsimp [s]; ring
  rw [he]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k <;> norm_num at hjk
  all_goals fin_cases l <;> norm_num at hkl
  all_goals norm_num [circle,det3,sqDist,px,py,threshold]
  all_goals ring_nf
  all_goals first
    | exact ne_of_gt (by positivity)
    | apply neg_ne_zero.mp; ring_nf; exact ne_of_gt (by positivity)

noncomputable def point (t : ℤ) (i : Fin 8) : ℝ² :=
  !₂[(px t i : ℝ),(py t i : ℝ)*Real.sqrt 2002]

lemma point_dist_sq (t : ℤ) (i j : Fin 8) :
    dist (point t i) (point t j)^2=(sqDist t i j : ℝ) := by
  rw [p4_dist_sq]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,sqDist]
  push_cast
  linear_combination ((py t i : ℝ)-py t j)^2 * (Real.sq_sqrt (by norm_num : (0 : ℝ)≤2002))

lemma point_injective {t : ℤ} (ht : threshold≤t) : Function.Injective (point t) := by
  intro i j he
  apply px_injective ht
  have h := congrArg (fun p : ℝ² => p 0) he
  change (px t i : ℝ)=(px t j : ℝ) at h
  exact_mod_cast h

lemma point_nontrilinear {t : ℤ} (ht : threshold≤t) : NonTrilinear (Set.range (point t)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik hcol
  have h := collinear_det_zero hcol
  have he : (triangle t i j k : ℝ)*Real.sqrt 2002=0 := by
    convert h using 1
    simp [point,triangle]
    ring
  have hn : (triangle t i j k : ℝ)≠0 := by
    exact_mod_cast triangle_ne ht i j k (fun h => hij (h ▸ rfl))
      (fun h => hjk (h ▸ rfl)) (fun h => hik (h ▸ rfl))
  exact mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by norm_num)) he

lemma sorted_not_cospherical {t : ℤ} (ht : threshold≤t)
    (i j k l : Fin 8) (hij : i<j) (hjk : j<k) (hkl : k<l) :
    ¬Cospherical {point t i,point t j,point t k,point t l} := by
  intro hcos
  have h := cospherical_det_zero hcos
  simp only [point_dist_sq] at h
  have he : (circle t i j k l : ℝ)*Real.sqrt 2002=0 := by
    convert h using 1
    simp [point,circle,det3]
    ring
  have hn : (circle t i j k l : ℝ)≠0 := by exact_mod_cast circle_sorted_ne ht i j k l hij hjk hkl
  exact mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by norm_num)) he

lemma point_no_four {t : ℤ} (ht : threshold≤t) (Q : Set ℝ²)
    (hQ : Q⊆Set.range (point t)) (hcard : Q.ncard=4) : ¬Cospherical Q := by
  classical
  intro hcos
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a∈({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b∈({point t i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c∈({point t i,point t j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d∈({point t i,point t j,point t k,d} : Set ℝ²))
  have hij : i≠j := fun h => hab (h ▸ rfl)
  have hik : i≠k := fun h => hac (h ▸ rfl)
  have hil : i≠l := fun h => had (h ▸ rfl)
  have hjk : j≠k := fun h => hbc (h ▸ rfl)
  have hjl : j≠l := fun h => hbd (h ▸ rfl)
  have hkl : k≠l := fun h => hcd (h ▸ rfl)
  let B : Finset (Fin 8) := {i,j,k,l}
  have hB : B.card=4 := Finset.card_eq_four.mpr ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩
  let e : Fin 4 ↪o Fin 8 := B.orderEmbOfFin hB
  have hm (r : Fin 4) : point t (e r)∈
      ({point t i,point t j,point t k,point t l} : Set ℝ²) := by
    have hh := B.orderEmbOfFin_mem hB r
    change e r∈B at hh
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh <;> rw [hh] <;> simp
  apply sorted_not_cospherical ht (e 0) (e 1) (e 2) (e 3)
    (e.strictMono (by decide)) (e.strictMono (by decide)) (e.strictMono (by decide))
  apply hcos.subset
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3

lemma geometric_eight {t : ℤ} (ht : threshold≤t) :
    (Set.range (point t)).Finite ∧ (Set.range (point t)).ncard=8 ∧
    InGeneralPosition (Set.range (point t)) := by
  refine ⟨Set.finite_range _,?_,point_nontrilinear ht,?_⟩
  · rw [Set.ncard_range_of_injective (point_injective ht)]; simp
  · intro Q hQ hcard
    exact point_no_four ht Q hQ hcard

def radii : Fin 6 → ℤ := ![49595290,19232372,37050599,20595296,49212246,19838116]
def dots : Fin 6 → ℤ := ![-99240175290,-37960278372,-65966352009,-36204361824,-56012147274,-16346264364]
def oldIndex (i : Fin 6) : Fin 8 := i.succ.castSucc

lemma ray_formula (t : ℤ) (i : Fin 6) :
    sqDist t 7 (oldIndex i)=2003^2*t^2-2*dots i*t+(radii i)^2 := by
  fin_cases i <;> dsimp [sqDist,px,py,oldIndex,dots,radii] <;> ring

lemma ray_positive (i : Fin 6) : 0<2003^2*(radii i)^2-(dots i)^2 := by
  fin_cases i <;> norm_num [radii,dots]

lemma ray_bound {t : ℤ} (ht : threshold≤t) (i : Fin 6) :
    2003^2*(radii i)^2-(dots i)^2≤2003^2*t-dots i := by
  fin_cases i <;> norm_num [radii,dots] <;> dsimp [threshold] at ht <;> omega

lemma ray_global_nonsquare {t : ℤ} (ht : threshold≤t) (i : Fin 6) :
    ¬IsSquare ((sqDist t 7 (oldIndex i) : ℤ) : ℚ) := by
  rw [ray_formula]
  exact FixedSourceLocal.ray_quadratic_not_rational_square (ray_positive i) (ray_bound ht i)

lemma ray_distance_irrational {t : ℤ} (ht : threshold≤t) (i : Fin 6) :
    dist (point t 7) (point t (oldIndex i))∉Set.range ((↑) : ℚ → ℝ) := by
  rintro ⟨q,hq⟩
  apply ray_global_nonsquare ht i
  refine ⟨q,?_⟩
  have hh := point_dist_sq t 7 (oldIndex i)
  rw [← hq] at hh
  have : (((sqDist t 7 (oldIndex i) : ℤ) : ℚ) : ℝ)=(q*q : ℚ) := by
    push_cast
    nlinarith only [hh]
  exact_mod_cast this

#print axioms geometric_eight
#print axioms ray_distance_irrational
end Erdos213.FixedHeptadLocal
