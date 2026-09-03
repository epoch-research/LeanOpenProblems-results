import Submission.GridQuarterBuchi
import Submission.ThreeRowBuchi

/-! Euclidean realization of the oblique grid restrictions. The resulting
eight-point existence theorems are conditional on an unconstructed metric. -/
open EuclideanGeometry
namespace Erdos213.GridCircleGeometry
open ObliqueMedianBridge GridCircleResonance GridQuarterBuchi
open InversionReduction CircleCoverReduction
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def ix : Fin 9 → Fin 3 := ![0,0,0,1,1,1,2,2,2]
def iy : Fin 9 → Fin 3 := ![0,1,2,0,1,2,0,1,2]

lemma ix_val (i : Fin 9) : ((ix i).val : ℚ)=gx i := by
  fin_cases i <;> norm_num [ix,gx]
lemma iy_val (i : Fin 9) : ((iy i).val : ℚ)=gy i := by
  fin_cases i <;> norm_num [iy,gy]

lemma coordinates_injective : Function.Injective (fun i : Fin 9 => (gx i,gy i)) := by
  decide

lemma grid_norm_square {B H : ℚ} (h : Directions 1 B H) (i j : Fin 9) :
    IsSquare (ObliqueMedianBridge.norm 1 B H (gx i-gx j) (gy i-gy j)) := by
  have hh := (grid_iff_directions 1 B H).mpr h (ix i,iy i) (ix j,iy j)
  simpa only [ix_val,iy_val] using hh

def point (B H : ℚ) (i : Fin 9) : ℝ² :=
  !₂[(gx i+H*gy i : ℚ), (gy i : ℝ)*Real.sqrt (B-H^2 : ℚ)]

lemma point_dist_sq {B H : ℚ} (hp : 0<B-H^2) (i j : Fin 9) :
    dist (point B H i) (point B H j)^2=
      (ObliqueMedianBridge.norm 1 B H (gx i-gx j) (gy i-gy j) : ℝ) := by
  rw [distance_sq]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    ObliqueMedianBridge.norm]
  push_cast
  have hs := Real.sq_sqrt (show 0≤((B-H^2 : ℚ) : ℝ) by exact_mod_cast hp.le)
  push_cast at hs
  linear_combination ((gy i : ℝ)-gy j)^2*hs

lemma point_injective {B H : ℚ} (hp : 0<B-H^2) : Function.Injective (point B H) := by
  intro i j he
  have h₀ := congrArg (fun p : ℝ² => p 0) he
  have h₁ := congrArg (fun p : ℝ² => p 1) he
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at h₀ h₁
  have hs : Real.sqrt ((B-H^2 : ℚ) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp)
  have hy : gy i=gy j := by exact_mod_cast mul_right_cancel₀ hs h₁
  have hx : gx i=gx j := by
    have hh : gx i+H*gy i=gx j+H*gy j := by exact_mod_cast h₀
    rw [hy] at hh
    linarith
  exact coordinates_injective (Prod.ext hx hy)

lemma rational_distances {B H : ℚ} (hp : 0<B-H^2) (h : Directions 1 B H)
    (i j : Fin 9) : dist (point B H i) (point B H j)∈Set.range (Rat.cast : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := grid_norm_square h i j
  refine ⟨|r|,?_⟩
  have he := point_dist_sq hp i j
  rw [hr] at he
  push_cast at he ⊢
  apply (sq_eq_sq₀ (abs_nonneg _) dist_nonneg).mp
  rw [sq_abs]
  nlinarith only [he]

lemma point_circle {B H : ℚ} (hp : 0<B-H^2) (i j k l : Fin 9) :
    circleEval (point B H i) (point B H j) (point B H k) (point B H l)=
      (circle 1 B H i j k l : ℝ)*Real.sqrt (B-H^2 : ℚ) := by
  rw [ThreeRowBuchi.circleEval_eq_distdet]
  simp only [point_dist_sq hp]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    circle,ThreeRowBuchi.det3,ObliqueMedianBridge.norm]
  push_cast
  ring

lemma sorted_not_generalized {B H : ℚ} (hp : 0<B-H^2)
    (i j k l : Fin 9) (hn : circle 1 B H i j k l ≠ 0) :
    ¬OnGeneralizedCircle {point B H i,point B H j,point B H k,point B H l} := by
  intro h
  have hz := generalized_subset_circleEval h
    (by simp : point B H i∈({point B H i,point B H j,point B H k,point B H l} : Set ℝ²))
    (by simp : point B H j∈({point B H i,point B H j,point B H k,point B H l} : Set ℝ²))
    (by simp : point B H k∈({point B H i,point B H j,point B H k,point B H l} : Set ℝ²))
    (by simp : point B H l∈({point B H i,point B H j,point B H k,point B H l} : Set ℝ²))
  change circleEval (point B H i) (point B H j) (point B H k) (point B H l)=0 at hz
  rw [point_circle hp] at hz
  exact mul_ne_zero (by exact_mod_cast hn)
    (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp)) hz

lemma point_no_four {B H : ℚ} (hp : 0<B-H^2)
    (hn : ∀ i j k l : Fin 9, i<j → j<k → k<l → circle 1 B H i j k l ≠ 0) :
    NoFourGeneralized (Set.range (point B H)) := by
  classical
  intro Q hQ hcard hgen
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a∈({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b∈({point B H i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c∈({point B H i,point B H j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d∈({point B H i,point B H j,point B H k,d} : Set ℝ²))
  have hij : i≠j := fun h => hab (h ▸ rfl)
  have hik : i≠k := fun h => hac (h ▸ rfl)
  have hil : i≠l := fun h => had (h ▸ rfl)
  have hjk : j≠k := fun h => hbc (h ▸ rfl)
  have hjl : j≠l := fun h => hbd (h ▸ rfl)
  have hkl : k≠l := fun h => hcd (h ▸ rfl)
  let F : Finset (Fin 9) := {i,j,k,l}
  have hF : F.card=4 := Finset.card_eq_four.mpr ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩
  let e : Fin 4 ↪o Fin 9 := F.orderEmbOfFin hF
  have hm (r : Fin 4) : point B H (e r)∈
      ({point B H i,point B H j,point B H k,point B H l} : Set ℝ²) := by
    have hh := F.orderEmbOfFin_mem hF r
    change e r∈F at hh
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh <;> rw [hh] <;> simp
  apply sorted_not_generalized hp (e 0) (e 1) (e 2) (e 3)
    (hn _ _ _ _ (e.strictMono (by decide)) (e.strictMono (by decide)) (e.strictMono (by decide)))
  apply generalized_mono hgen
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3

lemma erdos213For_eight_of_circle_ne {B H : ℚ} (hp : 0<B-H^2) (h : Directions 1 B H)
    (hn : ∀ i j k l : Fin 9, i<j → j<k → k<l → circle 1 B H i j k l ≠ 0) :
    Erdos213For 8 := by
  apply weak_to_strong
  refine ⟨Set.range (point B H),Set.finite_range _,?_,point_no_four hp hn,?_⟩
  · rw [Set.ncard_range_of_injective (point_injective hp)]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact rational_distances hp h i j

/-- A positive rational-distance metric with no quarter resonance suffices
for GP8. No such metric is supplied by this theorem. -/
theorem erdos213For_eight_of_nonresonant_grid {B H : ℚ}
    (hp : 0<B-H^2) (h : Directions 1 B H)
    (haP : 1+4*H ≠ 0) (haM : 1-4*H ≠ 0)
    (hbP : B+4*H ≠ 0) (hbM : B-4*H ≠ 0) : Erdos213For 8 := by
  apply erdos213For_eight_of_circle_ne hp h
  exact sorted_circle_ne (by simpa using hp) h haP haM hbP hbM

/-- Unconditional dichotomy given a positive full-grid metric: either GP8
exists, or there is a positive monic symmetric ten-square input. Neither
alternative is established here without the metric hypothesis. -/
theorem grid_dichotomy {B H : ℚ} (hp : 0<B-H^2) (h : Directions 1 B H) :
    Erdos213For 8 ∨ ∃ C : ℚ, 0<C ∧ SymmetricTen C := by
  by_cases ht : ∃ C : ℚ, 0<C ∧ SymmetricTen C
  · exact Or.inr ht
  · left
    apply erdos213For_eight_of_circle_ne hp h
    intro i j k l hij hjk hkl hz
    exact ht (circle_zero_requires_ten (by simpa using hp) h i j k l hij hjk hkl hz)

/-- The same dichotomy for an arbitrary, unnormalized binary metric. -/
theorem full_grid_dichotomy {A B H : ℚ} (hp : 0<A*B-H^2)
    (h : GridSquares A B H) :
    Erdos213For 8 ∨ ∃ C : ℚ, 0<C ∧ SymmetricTen C := by
  have hd := (grid_iff_directions A B H).mp h
  obtain ⟨hA,_⟩ := positive_diagonal hp hd
  have hA0 := ne_of_gt hA
  have he : B/A-(H/A)^2=(A*B-H^2)/A^2 := by
    field_simp
  have hp' : 0<B/A-(H/A)^2 := by
    rw [he]
    exact div_pos hp (sq_pos_of_pos hA)
  exact grid_dichotomy hp' (normalize hA0 hd)

#print axioms full_grid_dichotomy
#print axioms point_injective
#print axioms rational_distances
#print axioms point_circle
#print axioms point_no_four
#print axioms erdos213For_eight_of_nonresonant_grid
#print axioms grid_dichotomy
end
end Erdos213.GridCircleGeometry
