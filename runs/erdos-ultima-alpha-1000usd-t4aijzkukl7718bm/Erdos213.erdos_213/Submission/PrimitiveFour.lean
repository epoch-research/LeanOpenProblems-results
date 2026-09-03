import Submission.UnitEdge

/-! Primitivity alone does not bound the minimum distance, even for four points
in general position. This family is not a construction of arbitrary cardinality. -/
open EuclideanGeometry
namespace Erdos213.PrimitiveFour
set_option maxHeartbeats 1000000

private def xs (m : ℤ) : Fin 4 → ℤ := ![-8*m,8*m,0,0]
private def ys (m : ℤ) : Fin 4 → ℤ := ![0,0,4*m^2-4,16*m^2-1]
noncomputable def point (m : ℕ) (i : Fin 4) : ℝ² :=
  !₂[(xs m i : ℝ),(ys m i : ℝ)]
def length (m : ℕ) : Fin 4 → Fin 4 → ℕ :=
  !![0,16*m,4*m^2+4,16*m^2+1;
     16*m,0,4*m^2+4,16*m^2+1;
     4*m^2+4,4*m^2+4,0,12*m^2+3;
     16*m^2+1,16*m^2+1,12*m^2+3,0]

private lemma dist_sq (a b : ℝ²) :
    dist a b^2=(a 0-b 0)^2+(a 1-b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq]

lemma point_dist (m : ℕ) (i j : Fin 4) :
    dist (point m i) (point m j)=(length m i j : ℝ) := by
  have hh : dist (point m i) (point m j)^2=(length m i j : ℝ)^2 := by
    rw [dist_sq]
    fin_cases i <;> fin_cases j <;>
      norm_num [point,xs,ys,length] <;> ring
  nlinarith only [hh,dist_nonneg (x := point m i) (y := point m j),
    Nat.cast_nonneg (α := ℝ) (length m i j)]

lemma length_ge {m : ℕ} (hm : 4≤m) {i j : Fin 4} (hij : i ≠ j) :
    16*m≤length m i j := by
  have hh : 4*m≤m^2 := by nlinarith only [hm]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [length] <;> omega

lemma point_injective {m : ℕ} (hm : 4≤m) : Function.Injective (point m) := by
  intro i j he
  by_contra hij
  have hh := length_ge hm hij
  have hl : length m i j=0 := by
    have hz : (length m i j : ℝ)=0 := by rw [← point_dist,he,dist_self]
    exact_mod_cast hz
  omega

private def triangle (a b c : ℝ²) : ℝ :=
  (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)

private lemma triangle_zero_of_collinear {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    triangle a b c=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp [triangle]
  ring

lemma point_not_collinear {m : ℕ} (hm : 4≤m) {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ {point m i,point m j,point m k} := by
  intro h
  have hh := triangle_zero_of_collinear h
  have hmR : (4 : ℝ)≤m := by exact_mod_cast hm
  have h0 : (0 : ℝ)<m := by linarith only [hmR]
  have h1 : (0 : ℝ)<(m : ℝ)*((m : ℝ)^2-1) :=
    mul_pos h0 (by nlinarith only [hmR])
  have h2 : (0 : ℝ)<(m : ℝ)*(16*(m : ℝ)^2-1) :=
    mul_pos h0 (by nlinarith only [hmR])
  have h3 : (0 : ℝ)<(m : ℝ)*(4*(m : ℝ)^2+1) := by positivity
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals simp only [triangle,point,xs,ys,PiLp.toLp_apply,Matrix.cons_val_zero,
    Matrix.cons_val_succ',Matrix.cons_val_one] at hh
  all_goals push_cast at hh
  all_goals nlinarith only [h1,h2,h3,hh]

private def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2)=0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1))*(hb-ha)+
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1))*(hc-ha)+
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1))*(hd-ha)

lemma point_not_cospherical {m : ℕ} (hm : 4≤m) :
    ¬ Cospherical {point m 0,point m 1,point m 2,point m 3} := by
  intro h
  have hh := cospherical_det_zero h
  have he : 192*(m : ℝ)*(4*(m : ℝ)^2+1)*
      (4*(m : ℝ)^2-3*(m : ℝ)+1)*(4*(m : ℝ)^2+3*(m : ℝ)+1)=0 := by
    convert hh using 1
    simp only [point_dist]
    norm_num [det3,point,xs,ys,length,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.vecHead,Matrix.vecTail]
    ring
  have hmR : (4 : ℝ)≤m := by exact_mod_cast hm
  have h0 : (0 : ℝ)<m := by linarith only [hmR]
  have h1 : 0<4*(m : ℝ)^2-3*(m : ℝ)+1 := by nlinarith only [hmR]
  have h2 : 0<192*(m : ℝ)*(4*(m : ℝ)^2+1)*
      (4*(m : ℝ)^2-3*(m : ℝ)+1)*(4*(m : ℝ)^2+3*(m : ℝ)+1) := by positivity
  linarith only [he,h2]

lemma two_lengths_coprime (m : ℕ) : (16*m).Coprime (16*m^2+1) := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  apply Nat.eq_one_of_dvd_one
  have h1 : Nat.gcd (16*m) (16*m^2+1) ∣ (16*m)*m :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) m
  have h2 : Nat.gcd (16*m) (16*m^2+1) ∣ (16*m)*m+1 := by
    convert Nat.gcd_dvd_right (16*m) (16*m^2+1) using 1 <;> ring
  exact (Nat.dvd_add_right h1).mp h2

noncomputable def configuration (m : ℕ) : Set ℝ² := Set.range (point m)

lemma configuration_eq (m : ℕ) :
    configuration m={point m 0,point m 1,point m 2,point m 3} := by
  apply Set.Subset.antisymm
  · rintro z ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

lemma configuration_ncard {m : ℕ} (hm : 4≤m) : (configuration m).ncard=4 := by
  rw [configuration,Set.ncard_range_of_injective (point_injective hm)]
  simp

lemma configuration_nontrilinear {m : ℕ} (hm : 4≤m) :
    NonTrilinear (configuration m) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
  exact point_not_collinear hm (fun he => hij (he ▸ rfl))
    (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl))

lemma configuration_no_four_cospherical {m : ℕ} (hm : 4≤m)
    {Q : Set ℝ²} (hQ : Q ⊆ configuration m) (hcard : Q.ncard=4) : ¬ Cospherical Q := by
  have he : Q=configuration m := Set.eq_of_subset_of_ncard_le hQ
    (by rw [configuration_ncard hm,hcard]) (Set.finite_range _)
  rw [he,configuration_eq]
  exact point_not_cospherical hm

lemma configuration_integral (m : ℕ) :
    (configuration m).Pairwise (fun a b => dist a b ∈ Set.range ((↑) : ℤ → ℝ)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
  exact ⟨(length m i j : ℤ),by rw [point_dist]; simp⟩

lemma configuration_separation {m : ℕ} (hm : 4≤m) {a b : ℝ²}
    (ha : a ∈ configuration m) (hb : b ∈ configuration m) (hab : a ≠ b) :
    (16*m : ℕ) ≤ dist a b := by
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  rw [point_dist]
  exact_mod_cast length_ge hm (i := i) (j := j) (fun he => hab (he ▸ rfl))

def HasCoprimeDistances (S : Set ℝ²) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ r s : ℕ,
    r.Coprime s ∧ dist a b=(r : ℝ) ∧ dist a c=(s : ℝ)

lemma configuration_primitive (m : ℕ) : HasCoprimeDistances (configuration m) := by
  refine ⟨point m 0,⟨0,rfl⟩,point m 1,⟨1,rfl⟩,point m 3,⟨3,rfl⟩,
    16*m,16*m^2+1,two_lengths_coprime m,?_,?_⟩ <;>
    rw [point_dist] <;>
    norm_num [length,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

/-- The minimum distance is unbounded even for primitive four-point GP
configurations. This rules out a short-edge conclusion from primitivity alone;
it does not rule out an obstruction specific to larger cardinalities. -/
theorem primitive_min_distance_unbounded (B : ℕ) :
    ∃ S : Set ℝ², S.Finite ∧ S.ncard=4 ∧ NonTrilinear S ∧
      (∀ Q : Set ℝ², Q ⊆ S → Q.ncard=4 → ¬ Cospherical Q) ∧
      (S.Pairwise (fun a b => dist a b ∈ Set.range ((↑) : ℤ → ℝ))) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (B : ℝ)<dist a b) ∧ HasCoprimeDistances S := by
  let m := B+4
  have hm : 4≤m := by omega
  refine ⟨configuration m,Set.finite_range _,configuration_ncard hm,
    configuration_nontrilinear hm,?_,configuration_integral m,?_,configuration_primitive m⟩
  · intro Q hQ hcard
    exact configuration_no_four_cospherical hm hQ hcard
  · intro a ha b hb hab
    have he := configuration_separation hm ha hb hab
    have hB : B<16*m := by dsimp [m]; omega
    have hBR : (B : ℝ)<(16*m : ℕ) := by exact_mod_cast hB
    exact hBR.trans_le he

#print axioms point_dist
#print axioms point_not_collinear
#print axioms point_not_cospherical
#print axioms two_lengths_coprime
#print axioms primitive_min_distance_unbounded
end Erdos213.PrimitiveFour
