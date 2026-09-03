import Submission.CircleCoverReduction

/-! A conditional eight-point construction from seven consecutive square values
of a positive quadratic. Their existence is not asserted. -/
open EuclideanGeometry
namespace Erdos213.ThreeRowBuchi
open InversionReduction
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def px (t : ℚ) : Fin 9 → ℚ := ![-1,0,1,t+5,t+7,t+9,-t-9,-t-7,-t-5]
def py : Fin 9 → ℚ := ![0,0,0,1,1,1,-1,-1,-1]
def sqDist (t D : ℚ) (i j : Fin 9) : ℚ := (px t i-px t j)^2+D*(py i-py j)^2

def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def circle (t D : ℚ) (i j k l : Fin 9) : ℚ :=
  det3 (px t j-px t i) (py j-py i) (sqDist t D i j)
    (px t k-px t i) (py k-py i) (sqDist t D i k)
    (px t l-px t i) (py l-py i) (sqDist t D i l)

lemma px_injective {t : ℚ} (ht : 0<t) : Function.Injective (px t) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num [px] at he
  all_goals first | rfl | exfalso; linarith

lemma distances_square (t D : ℚ)
    (h : ∀ k : Fin 7, IsSquare ((t+(k.val : ℚ)+4)^2+D)) (i j : Fin 9) :
    IsSquare (sqDist t D i j) := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  have h20 := (IsSquare.sq (2 : ℚ)).mul h0
  have h21 := (IsSquare.sq (2 : ℚ)).mul h1
  have h22 := (IsSquare.sq (2 : ℚ)).mul h2
  have h23 := (IsSquare.sq (2 : ℚ)).mul h3
  have h24 := (IsSquare.sq (2 : ℚ)).mul h4
  have h25 := (IsSquare.sq (2 : ℚ)).mul h5
  have h26 := (IsSquare.sq (2 : ℚ)).mul h6
  norm_num at h0 h1 h2 h3 h4 h5 h6 h20 h21 h22 h23 h24 h25 h26
  fin_cases i <;> fin_cases j <;> norm_num [sqDist,px,py]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h20 h21 h22 h23 h24 h25 h26 ⊢
  all_goals assumption

lemma circle_sorted_ne {t D : ℚ} (ht : 0<t) (hD : 0<D)
    (i j k l : Fin 9) (hij : i<j) (hjk : j<k) (hkl : k<l) :
    circle t D i j k l≠0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k <;> norm_num at hjk
  all_goals fin_cases l <;> norm_num at hkl
  all_goals norm_num [circle,det3,sqDist,px,py]
  all_goals ring_nf
  all_goals first
    | exact ne_of_gt (by positivity)
    | apply neg_ne_zero.mp; ring_nf; exact ne_of_gt (by positivity)

noncomputable def point (t D : ℚ) (i : Fin 9) : ℝ² :=
  !₂[(px t i : ℝ), (py i : ℝ)*Real.sqrt (D : ℝ)]

lemma point_dist_sq {t D : ℚ} (hD : 0<D) (i j : Fin 9) :
    dist (point t D i) (point t D j)^2=(sqDist t D i j : ℝ) := by
  rw [distance_sq]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,sqDist]
  push_cast
  linear_combination ((py i : ℝ)-py j)^2 * (Real.sq_sqrt (show 0≤(D : ℝ) by exact_mod_cast hD.le))

lemma point_injective {t D : ℚ} (ht : 0<t) : Function.Injective (point t D) := by
  intro i j he
  apply px_injective ht
  have he' := congrArg (fun p : ℝ² => p 0) he
  change (px t i : ℝ)=(px t j : ℝ) at he'
  exact_mod_cast he'

lemma point_rational_distances {t D : ℚ} (hD : 0<D)
    (h : ∀ k : Fin 7, IsSquare ((t+(k.val : ℚ)+4)^2+D)) (i j : Fin 9) :
    dist (point t D i) (point t D j)∈Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := distances_square t D h i j
  refine ⟨|r|,?_⟩
  have he := point_dist_sq (t := t) hD i j
  rw [hr] at he
  push_cast at he ⊢
  apply (sq_eq_sq₀ (abs_nonneg _) dist_nonneg).mp
  rw [sq_abs]
  nlinarith only [he]

lemma circleEval_eq_distdet (a b c d : ℝ²) :
    CircleCoverReduction.circleEval a b c d =
      det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
        (c 0-a 0) (c 1-a 1) (dist a c^2)
        (d 0-a 0) (d 1-a 1) (dist a d^2) := by
  simp only [CircleCoverReduction.circleEval,CircleCoverReduction.ca,
    CircleCoverReduction.cb,CircleCoverReduction.cc,CircleCoverReduction.qnorm_eq_dist,
    CircleCoverReduction.dx,CircleCoverReduction.dy,det3]
  rw [dist_comm b a,dist_comm c a,dist_comm d a]
  ring

lemma point_circleEval {t D : ℚ} (hD : 0<D) (i j k l : Fin 9) :
    CircleCoverReduction.circleEval (point t D i) (point t D j)
      (point t D k) (point t D l) =
        (circle t D i j k l : ℝ)*Real.sqrt (D : ℝ) := by
  rw [circleEval_eq_distdet]
  simp only [point_dist_sq hD]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,circle,det3]
  push_cast
  ring

lemma sorted_not_generalized {t D : ℚ} (ht : 0<t) (hD : 0<D)
    (i j k l : Fin 9) (hij : i<j) (hjk : j<k) (hkl : k<l) :
    ¬OnGeneralizedCircle {point t D i,point t D j,point t D k,point t D l} := by
  intro h
  have he := CircleCoverReduction.generalized_subset_circleEval h
    (by simp : point t D i∈({point t D i,point t D j,point t D k,point t D l} : Set ℝ²))
    (by simp : point t D j∈({point t D i,point t D j,point t D k,point t D l} : Set ℝ²))
    (by simp : point t D k∈({point t D i,point t D j,point t D k,point t D l} : Set ℝ²))
    (by simp : point t D l∈({point t D i,point t D j,point t D k,point t D l} : Set ℝ²))
  change CircleCoverReduction.circleEval (point t D i) (point t D j)
    (point t D k) (point t D l)=0 at he
  rw [point_circleEval hD] at he
  have hn : (circle t D i j k l : ℝ)≠0 := by exact_mod_cast circle_sorted_ne ht hD i j k l hij hjk hkl
  exact mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD)) he

lemma point_no_four {t D : ℚ} (ht : 0<t) (hD : 0<D) :
    NoFourGeneralized (Set.range (point t D)) := by
  classical
  intro Q hQ hcard hgen
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a∈({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b∈({point t D i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c∈({point t D i,point t D j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d∈({point t D i,point t D j,point t D k,d} : Set ℝ²))
  have hij : i≠j := fun h => hab (h ▸ rfl)
  have hik : i≠k := fun h => hac (h ▸ rfl)
  have hil : i≠l := fun h => had (h ▸ rfl)
  have hjk : j≠k := fun h => hbc (h ▸ rfl)
  have hjl : j≠l := fun h => hbd (h ▸ rfl)
  have hkl : k≠l := fun h => hcd (h ▸ rfl)
  let B : Finset (Fin 9) := {i,j,k,l}
  have hB : B.card=4 := Finset.card_eq_four.mpr ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩
  let e : Fin 4 ↪o Fin 9 := B.orderEmbOfFin hB
  have hm (r : Fin 4) : point t D (e r)∈
      ({point t D i,point t D j,point t D k,point t D l} : Set ℝ²) := by
    have hh := B.orderEmbOfFin_mem hB r
    change e r∈B at hh
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh <;> rw [hh] <;> simp
  apply sorted_not_generalized ht hD (e 0) (e 1) (e 2) (e 3)
    (e.strictMono (by decide)) (e.strictMono (by decide)) (e.strictMono (by decide))
  apply generalized_mono hgen
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3

/-- Seven consecutive positive quadratic square values, starting beyond 4,
suffice for a weak nine-point source and therefore an eight-point solution.
No rational parameters satisfying these assumptions have been supplied. -/
theorem erdos213For_eight_of_seven_squares (t D : ℚ) (ht : 0<t) (hD : 0<D)
    (h : ∀ k : Fin 7, IsSquare ((t+(k.val : ℚ)+4)^2+D)) : Erdos213For 8 := by
  apply weak_to_strong
  refine ⟨Set.range (point t D),Set.finite_range _,?_,point_no_four ht hD,?_⟩
  · rw [Set.ncard_range_of_injective (point_injective ht)]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact point_rational_distances hD h i j

#print axioms distances_square
#print axioms circle_sorted_ne
#print axioms point_rational_distances
#print axioms point_no_four
#print axioms erdos213For_eight_of_seven_squares
end
end Erdos213.ThreeRowBuchi
