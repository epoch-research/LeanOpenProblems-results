import Submission.UnitEdge
import Mathlib.Data.Rat.Lemmas

/-! A fixed integral triangle has general-position rational-distance extensions
with arbitrarily large distance-difference denominators. This is a four-point
control, not a construction of arbitrary cardinality. -/
open EuclideanGeometry
namespace Erdos213.FixedTriangleDenominators

def height (m : ℕ) : ℚ := 72*m-1/(2*m)
def radius (m : ℕ) : ℚ := 72*m+1/(2*m)

lemma height_gt {m : ℕ} (hm : 0<m) : 5<height m := by
  have hmQ : (1 : ℚ)≤m := by exact_mod_cast hm
  have hi : (1 : ℚ)/(2*m)≤1/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  dsimp [height]
  linarith

lemma radius_pos {m : ℕ} (hm : 0<m) : 0<radius m := by
  unfold radius
  have hmQ : (0 : ℚ)<m := by exact_mod_cast hm
  positivity

lemma radius_sq {m : ℕ} (hm : 0<m) : height m^2+144=radius m^2 := by
  have hmQ : (m : ℚ)≠0 := by exact_mod_cast (ne_of_gt hm)
  unfold height radius
  field_simp
  ring

lemma difference {m : ℕ} (hm : 0<m) :
    height m-5-radius m=(-5 : ℤ)-(m : ℚ)⁻¹ := by
  have hmQ : (m : ℚ)≠0 := by exact_mod_cast (ne_of_gt hm)
  unfold height radius
  field_simp
  ring

lemma difference_den {m : ℕ} (hm : 0<m) :
    (height m-5-radius m).den=m := by
  rw [difference hm,Rat.intCast_sub_den,Rat.den_inv_of_ne_zero]
  · simp
  · exact_mod_cast (ne_of_gt hm)

noncomputable def point (m : ℕ) : Fin 4 → ℝ² :=
  ![!₂[-12,0],!₂[12,0],!₂[0,5],!₂[0,(height m : ℝ)]]

def length (m : ℕ) : Fin 4 → Fin 4 → ℚ :=
  !![0,24,13,radius m;
     24,0,13,radius m;
     13,13,0,height m-5;
     radius m,radius m,height m-5,0]

private lemma dist_sq (a b : ℝ²) :
    dist a b^2=(a 0-b 0)^2+(a 1-b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq]

lemma point_dist {m : ℕ} (hm : 0<m) (i j : Fin 4) :
    dist (point m i) (point m j)=(length m i j : ℝ) := by
  have hh : (height m : ℝ)^2+144=(radius m : ℝ)^2 := by
    exact_mod_cast (radius_sq hm)
  have hpos : 0≤(length m i j : ℝ) := by
    have htQ := height_gt hm
    have hrQ := radius_pos hm
    have ht : (5 : ℝ)<height m := by exact_mod_cast (height_gt hm)
    have hr : (0 : ℝ)<radius m := by exact_mod_cast (radius_pos hm)
    fin_cases i <;> fin_cases j <;> norm_num [length] <;> linarith
  apply (sq_eq_sq₀ (dist_nonneg) hpos).mp
  rw [dist_sq]
  fin_cases i <;> fin_cases j <;> norm_num [point,length] <;> nlinarith only [hh]

lemma length_pos {m : ℕ} (hm : 0<m) {i j : Fin 4} (hij : i≠j) :
    0<length m i j := by
  have ht := height_gt hm
  have hr := radius_pos hm
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [length] <;> linarith

lemma point_injective {m : ℕ} (hm : 0<m) : Function.Injective (point m) := by
  intro i j he
  by_contra hij
  have hh := point_dist hm i j
  rw [he,dist_self] at hh
  have hp : (0 : ℝ)<length m i j := by exact_mod_cast (length_pos hm hij)
  linarith

private def triangle (a b c : ℝ²) : ℝ :=
  (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)

private lemma triangle_zero_of_collinear {a b c : ℝ²}
    (h : Collinear ℝ {a,b,c}) : triangle a b c=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp [triangle]
  ring

lemma point_not_collinear {m : ℕ} (hm : 0<m) {i j k : Fin 4}
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ¬ Collinear ℝ {point m i,point m j,point m k} := by
  intro h
  have he := triangle_zero_of_collinear h
  have htQ := height_gt hm
  have ht : (5 : ℝ)<height m := by exact_mod_cast (height_gt hm)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals norm_num [triangle,point] at he <;> linarith

lemma point_not_cospherical {m : ℕ} (hm : 0<m) :
    ¬ Cospherical {point m 0,point m 1,point m 2,point m 3} := by
  rintro ⟨o,r,hh⟩
  have h0 := congrArg (fun z : ℝ => z^2) (hh (point m 0) (by simp))
  have h1 := congrArg (fun z : ℝ => z^2) (hh (point m 1) (by simp))
  have h2 := congrArg (fun z : ℝ => z^2) (hh (point m 2) (by simp))
  have h3 := congrArg (fun z : ℝ => z^2) (hh (point m 3) (by simp))
  simp only [dist_sq] at h0 h1 h2 h3
  norm_num [point,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h0 h1 h2 h3
  have hx : o 0=0 := by nlinarith only [h0,h1]
  rw [hx] at h0 h2 h3
  have hy : 10*o 1 = -119 := by nlinarith only [h0,h2]
  have ht : (5 : ℝ)<height m := by exact_mod_cast (height_gt hm)
  have hp : 5*(height m : ℝ)^2+119*(height m : ℝ)-720=0 := by
    linear_combination 5*(h3-h0)+(height m : ℝ)*hy
  nlinarith [sq_nonneg ((height m : ℝ)-5)]

lemma range_eq (m : ℕ) : Set.range (point m)=
    {point m 0,point m 1,point m 2,point m 3} := by
  ext p
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> tauto
  · rintro (rfl|rfl|rfl|rfl) <;> exact ⟨_,rfl⟩

lemma general_position_rational {m : ℕ} (hm : 0<m) :
    (Set.range (point m)).Finite ∧ (Set.range (point m)).ncard=4 ∧
    NonTrilinear (Set.range (point m)) ∧
    ¬ Cospherical (Set.range (point m)) ∧
    (Set.range (point m)).Pairwise
      (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) := by
  refine ⟨Set.finite_range _,?_,?_,?_,?_⟩
  · rw [Set.ncard_range_of_injective (point_injective hm)]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    apply point_not_collinear hm
    · exact fun he => hij (he ▸ rfl)
    · exact fun he => hjk (he ▸ rfl)
    · exact fun he => hik (he ▸ rfl)
  · rw [range_eq]
    exact point_not_cospherical hm
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact ⟨length m i j,(point_dist hm i j).symm⟩

/-- The first three points are fixed, and only the fourth changes with m. -/
lemma fixed_anchors (m : ℕ) :
    point m 0=!₂[-12,0] ∧ point m 1=!₂[12,0] ∧ point m 2=!₂[0,5] := by
  norm_num [point,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

/-- For one fixed noncollinear integral triangle, even imposing general
position on each four-point extension gives no uniform difference-denominator
bound. This does NOT extend the whole infinite family at once. -/
theorem no_uniform_difference_denominator (N : ℕ) :
    ∃ m : ℕ, 0<m ∧
      (Set.range (point m)).Finite ∧ (Set.range (point m)).ncard=4 ∧
      NonTrilinear (Set.range (point m)) ∧
      ¬ Cospherical (Set.range (point m)) ∧
      (Set.range (point m)).Pairwise
        (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) ∧
      dist (point m 3) (!₂[-12,0])=(radius m : ℝ) ∧
      dist (point m 3) (!₂[0,5])=((height m-5 : ℚ) : ℝ) ∧
      N<(height m-5-radius m).den := by
  let m := N+1
  have hm : 0<m := by omega
  obtain ⟨hf,hc,ht,hs,hd⟩ := general_position_rational hm
  refine ⟨m,hm,hf,hc,ht,hs,hd,?_,?_,?_⟩
  · simpa only [point,length,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three] using point_dist hm 3 0
  · simpa only [point,length,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three] using point_dist hm 3 2
  · rw [difference_den hm]
    omega

lemma unbounded_three_power_control (e : ℕ) :
    (height (3^e)-5-radius (3^e)).den=3^e ∧
    NonTrilinear (Set.range (point (3^e))) ∧
    ¬ Cospherical (Set.range (point (3^e))) := by
  have hm : 0<(3 : ℕ)^e := by positivity
  have hg := general_position_rational hm
  exact ⟨difference_den hm,hg.2.2.1,hg.2.2.2.1⟩

/-- The family cannot be combined into a larger GP configuration: two extension
points and the fixed apex lie on the same vertical line. -/
lemma extensions_collinear (m n : ℕ) :
    Collinear ℝ ({(!₂[0,5] : ℝ²),point m 3,point n 3} : Set ℝ²) := by
  apply (collinear_iff_of_mem (by simp : (!₂[0,5] : ℝ²) ∈
    ({(!₂[0,5] : ℝ²),point m 3,point n 3} : Set ℝ²))).mpr
  refine ⟨!₂[0,1],?_⟩
  rintro p (rfl|rfl|rfl)
  · refine ⟨0,?_⟩
    simp
  · refine ⟨(height m : ℝ)-5,?_⟩
    ext i
    fin_cases i <;> norm_num [point,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · refine ⟨(height n : ℝ)-5,?_⟩
    ext i
    fin_cases i <;> norm_num [point,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

#print axioms unbounded_three_power_control
#print axioms extensions_collinear
#print axioms difference_den
#print axioms general_position_rational
#print axioms no_uniform_difference_denominator
end Erdos213.FixedTriangleDenominators
