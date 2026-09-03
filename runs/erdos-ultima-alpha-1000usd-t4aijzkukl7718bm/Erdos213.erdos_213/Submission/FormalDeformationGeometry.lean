import Submission.FormalDeformation
import FormalConjecturesForMathlib.Geometry.«2d»

/-! A real-geometric control on formal-deformation arguments. Six points have
formal distance roots and general position at t=1, but at no nonzero real t
are all actual Euclidean distances rational. This does not exclude arbitrary
configurations. -/
open EuclideanGeometry
namespace Erdos213.FormalDeformationGeometry
open FormalDeformation
noncomputable section
set_option maxHeartbeats 2000000

private def xs : Fin 6 → ℤ := ![0,1,1,2,3,4]
private def ys : Fin 6 → ℤ := ![0,0,1,4,9,16]

def point (t : ℝ) (i : Fin 6) : ℝ² := !₂[(xs i : ℝ), t*(ys i : ℝ)]

lemma dist_sq (t : ℝ) (i j : Fin 6) :
    dist (point t i) (point t j)^2 =
      ((xs i : ℝ)-xs j)^2+t^2*((ys i : ℝ)-ys j)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,point]
  ring

/-- The repeated initial x-coordinate causes no formal obstruction: that
particular edge already has length X. All other edges have nonzero constant
terms and lift by the general square-root theorem. -/
theorem all_formal_distances : ∀ i j : Fin 6,
    IsSquare ((PowerSeries.C ((xs i-xs j : ℤ) : ℚ))^2 +
      PowerSeries.X^2*(PowerSeries.C ((ys i-ys j : ℤ) : ℚ))^2) := by
  intro i j
  by_cases hx : xs i-xs j=0
  · simp only [hx, Int.cast_zero, map_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact (IsSquare.sq _).mul (IsSquare.sq _)
  · apply isSquare_of_constantCoeff_square (a := ((xs i-xs j : ℤ) : ℚ))
    · exact_mod_cast hx
    · simp

/-- Only three selected edges are needed to block all nonzero real parameters. -/
theorem real_distances_force_zero (t : ℝ)
    (h : ∀ i j : Fin 6, dist (point t i) (point t j) ∈ Set.range ((↑) : ℚ → ℝ)) :
    t=0 := by
  obtain ⟨v,hv⟩ := h 1 2
  obtain ⟨r,hr⟩ := h 2 3
  obtain ⟨s,hs⟩ := h 3 5
  have hv' : (v : ℝ)^2=t^2 := by
    rw [hv,dist_sq]
    norm_num only [show xs 1=1 from rfl, show xs 2=1 from rfl,
      show ys 1=0 from rfl, show ys 2=1 from rfl, Int.cast_one, Int.cast_zero]
    ring
  have hr' : (r : ℝ)^2=1+9*t^2 := by
    rw [hr,dist_sq]
    norm_num only [show xs 2=1 from rfl, show xs 3=2 from rfl,
      show ys 2=1 from rfl, show ys 3=4 from rfl, Int.cast_one, Int.cast_ofNat]
    ring
  have hs' : (s : ℝ)^2=4+144*t^2 := by
    rw [hs,dist_sq]
    change ((2 : ℝ)-4)^2+t^2*(4-16)^2=4+144*t^2
    ring
  have h12 : IsSquare (sqDistance v 1 2) := by
    refine ⟨r,?_⟩
    apply Rat.cast_injective (α := ℝ)
    dsimp [sqDistance]
    push_cast
    nlinarith only [hr',hv']
  have h24 : IsSquare (sqDistance v 2 4) := by
    refine ⟨s,?_⟩
    apply Rat.cast_injective (α := ℝ)
    dsimp [sqDistance]
    push_cast
    nlinarith only [hs',hv']
  have hv0 := two_edges_force_zero h12 h24
  rw [hv0] at hv'
  norm_num at hv'
  nlinarith only [hv']

/-- The fixed unit edge makes the obstruction invariant under arbitrary real
scaling. Irrational scale factors cannot turn this family into an integral
configuration either. Rigid motions do not change the distances. -/
theorem scaled_real_distances_force_zero (t u : ℝ) (hu : u ≠ 0)
    (h : ∀ i j : Fin 6,
      dist (u • point t i) (u • point t j) ∈ Set.range ((↑) : ℚ → ℝ)) : t=0 := by
  have hd : dist (point t 0) (point t 1)=1 := by
    have he := dist_sq t 0 1
    norm_num only [show xs 0=0 from rfl, show xs 1=1 from rfl,
      show ys 0=0 from rfl, show ys 1=0 from rfl, Int.cast_one, Int.cast_zero] at he
    nlinarith [dist_nonneg (x := point t 0) (y := point t 1)]
  obtain ⟨q,hq⟩ := h 0 1
  rw [dist_smul₀,hd,mul_one,Real.norm_eq_abs] at hq
  have hn : (q : ℝ) ≠ 0 := by rw [hq]; exact abs_ne_zero.mpr hu
  apply real_distances_force_zero
  intro i j
  obtain ⟨r,hr⟩ := h i j
  refine ⟨r/q,?_⟩
  push_cast
  apply (div_eq_iff hn).mpr
  rw [hr,dist_smul₀,Real.norm_eq_abs,hq,mul_comm]

/-- A direct set-pairwise version with integer distances, as in the original
conjecture, for this particular six-point deformation family only. -/
theorem no_integral_scaled_specialization {t u : ℝ} (ht : t ≠ 0) (hu : u ≠ 0) :
    ¬ ((Set.range (fun i : Fin 6 => u • point t i)).Pairwise fun p q =>
      dist p q ∈ Set.range ((↑) : ℤ → ℝ)) := by
  intro h
  apply ht
  apply scaled_real_distances_force_zero t u hu
  intro i j
  by_cases hij : u • point t i = u • point t j
  · exact ⟨0, by simp [hij]⟩
  · obtain ⟨r,hr⟩ := h (Set.mem_range_self i) (Set.mem_range_self j) hij
    exact ⟨(r : ℚ), by simpa using hr⟩

private def intTriangle (i j k : Fin 6) : ℤ :=
  (xs j-xs i)*(ys k-ys i)-(ys j-ys i)*(xs k-xs i)

private def intNorm (i j : Fin 6) : ℤ := (xs i-xs j)^2+(ys i-ys j)^2

private def intCircle (i j k l : Fin 6) : ℤ :=
  det3 (xs j-xs i) (ys j-ys i) (intNorm i j)
    (xs k-xs i) (ys k-ys i) (intNorm i k)
    (xs l-xs i) (ys l-ys i) (intNorm i l)

private lemma triangle_certificate : ∀ i j k : Fin 6,
    i ≠ j → i ≠ k → j ≠ k → intTriangle i j k ≠ 0 := by decide

private lemma circle_certificate : ∀ i j k l : Fin 6,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → intCircle i j k l ≠ 0 := by decide

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma general_dist_sq (a b : ℝ²) :
    dist a b^2=(a 0-b 0)^2+(a 1-b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2)=0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [general_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1))*(hb-ha)+
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1))*(hc-ha)+
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1))*(hd-ha)

lemma at_one_injective : Function.Injective (point 1) := by
  have hxy : Function.Injective (fun i : Fin 6 => (xs i,ys i)) := by decide
  intro i j hij
  apply hxy
  apply Prod.ext
  · have he := congrArg (fun p : ℝ² => p 0) hij
    simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero] at he
    exact_mod_cast he
  · have he := congrArg (fun p : ℝ² => p 1) hij
    simp only [point,PiLp.toLp_apply,Matrix.cons_val_one,Matrix.cons_val_zero,one_mul] at he
    exact_mod_cast he

lemma at_one_nontrilinear : NonTrilinear (Set.range (point 1)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik hline
  have hz := collinear_det_zero hline
  have hz' : (intTriangle i j k : ℝ)=0 := by
    simpa [intTriangle,point] using hz
  exact triangle_certificate i j k (fun he => hij (he ▸ rfl))
    (fun he => hik (he ▸ rfl)) (fun he => hjk (he ▸ rfl)) (by exact_mod_cast hz')

lemma at_one_no_four_cospherical (Q : Set ℝ²)
    (hQ : Q ⊆ Set.range (point 1)) (hc : Q.ncard=4) : ¬Cospherical Q := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hc
  subst Q
  obtain ⟨i,rfl⟩ := hQ (by simp : a∈({a,b,c,d} : Set ℝ²))
  obtain ⟨j,rfl⟩ := hQ (by simp : b∈({point 1 i,b,c,d} : Set ℝ²))
  obtain ⟨k,rfl⟩ := hQ (by simp : c∈({point 1 i,point 1 j,c,d} : Set ℝ²))
  obtain ⟨l,rfl⟩ := hQ (by simp : d∈({point 1 i,point 1 j,point 1 k,d} : Set ℝ²))
  intro hcos
  have hz := cospherical_det_zero hcos
  have hz' : (intCircle i j k l : ℝ)=0 := by
    simp only [dist_sq] at hz
    simpa [intCircle,intNorm,det3,point] using hz
  exact circle_certificate i j k l (fun he => hab (he ▸ rfl))
    (fun he => hac (he ▸ rfl)) (fun he => had (he ▸ rfl))
    (fun he => hbc (he ▸ rfl)) (fun he => hbd (he ▸ rfl))
    (fun he => hcd (he ▸ rfl)) (by exact_mod_cast hz')

theorem at_one_general_position :
    (Set.range (point 1)).ncard=6 ∧ NonTrilinear (Set.range (point 1)) ∧
    ∀ Q : Set ℝ², Q ⊆ Set.range (point 1) → Q.ncard=4 → ¬Cospherical Q := by
  refine ⟨?_,at_one_nontrilinear,at_one_no_four_cospherical⟩
  rw [Set.ncard_range_of_injective at_one_injective]
  simp

#print axioms all_formal_distances
#print axioms real_distances_force_zero
#print axioms at_one_general_position
#print axioms scaled_real_distances_force_zero
#print axioms no_integral_scaled_specialization
end
end Erdos213.FormalDeformationGeometry
