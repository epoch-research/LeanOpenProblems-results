import Submission.CentralQuadratic

/-! An arithmetic counterexample to general-position preservation by the
central quadratic seven-point map. This does NOT disprove Erdős 213. -/
open EuclideanGeometry
namespace Erdos213.CentralDegeneration
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

private noncomputable def latticePoint (D : ℕ) (x y : ℤ) : ℝ² := !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]

private def latticeNorm (D : ℕ) (x y x' y' : ℤ) : ℤ :=
  (x-x')^2 + (D : ℤ)*(y-y')^2

private def latticeTriangle (x y : Fin n → ℤ) (i j k : Fin n) : ℤ :=
  (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)

private def latticeCircle (D : ℕ) (x y : Fin n → ℤ) (i j k l : Fin n) : ℤ :=
  det3 (x j-x i) (y j-y i) (latticeNorm D (x i) (y i) (x j) (y j))
    (x k-x i) (y k-y i) (latticeNorm D (x i) (y i) (x k) (y k))
    (x l-x i) (y l-y i) (latticeNorm D (x i) (y i) (x l) (y l))

private lemma latticePoint_dist_sq (D : ℕ) (x y x' y' : ℤ) :
    dist (latticePoint D x y) (latticePoint D x' y')^2 = (latticeNorm D x y x' y' : ℝ) := by
  rw [p4_dist_sq]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    latticeNorm]
  push_cast
  linear_combination ((y : ℝ)-y')^2 * (Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity))

private lemma lattice_not_collinear {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k : Fin n} (ht : latticeTriangle x y i j k ≠ 0) :
    ¬Collinear ℝ {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k)} := by
  intro h
  have hz := collinear_det_zero h
  have hz' : (latticeTriangle x y i j k : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeTriangle]
    ring
  have hn : (latticeTriangle x y i j k : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

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

private lemma lattice_not_cospherical {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k l : Fin n} (ht : latticeCircle D x y i j k l ≠ 0) :
    ¬Cospherical {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k), latticePoint D (x l) (y l)} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [latticePoint_dist_sq] at hz
  have hz' : (latticeCircle D x y i j k l : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeCircle, det3]
    ring
  have hn : (latticeCircle D x y i j k l : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma integral_configuration_certificate (D n : ℕ) (hD : 0 < D)
    (x y : Fin n → ℤ) (d : Fin n → Fin n → ℕ)
    (hinj : Function.Injective x)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → latticeTriangle x y i j k ≠ 0)
    (hcirc : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      latticeCircle D x y i j k l ≠ 0)
    (hdist : ∀ i j, latticeNorm D (x i) (y i) (x j) (y j) = (d i j : ℤ)^2) :
    (Set.range (fun i => latticePoint D (x i) (y i))).Finite ∧
    (Set.range (fun i => latticePoint D (x i) (y i))).ncard = n ∧
    NonTrilinear (Set.range (fun i => latticePoint D (x i) (y i))) ∧
    (∀ Q : Set ℝ², Q ⊆ Set.range (fun i => latticePoint D (x i) (y i)) ∧ Q.ncard = 4 → ¬Cospherical Q) ∧
    ((Set.range (fun i => latticePoint D (x i) (y i))).Pairwise
      fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) := by
  let p : Fin n → ℝ² := fun i => latticePoint D (x i) (y i)
  have hp : Function.Injective p := by
    intro i j hij
    apply hinj
    have he := congrArg (fun z : ℝ² => z 0) hij
    change (x i : ℝ) = (x j : ℝ) at he
    exact_mod_cast he
  refine ⟨Set.finite_range _, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact lattice_not_collinear hD (htri i j k (fun he => hij (he ▸ rfl))
      (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl)))
  · intro Q hQ hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hQ.2
    subst Q
    obtain ⟨i,rfl⟩ := hQ.1 (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ.1 (by simp : b ∈ ({p i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ.1 (by simp : c ∈ ({p i,p j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ.1 (by simp : e ∈ ({p i,p j,p k,e} : Set ℝ²))
    exact lattice_not_cospherical hD (hcirc i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl))) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    refine ⟨(d i j : ℤ), ?_⟩
    have he := latticePoint_dist_sq D (x i) (y i) (x j) (y j)
    rw [hdist] at he
    push_cast at he ⊢
    change (d i j : ℝ) = dist (latticePoint D (x i) (y i)) (latticePoint D (x j) (y j))
    nlinarith [dist_nonneg (x := latticePoint D (x i) (y i)) (y := latticePoint D (x j) (y j)),
      Nat.cast_nonneg (α := ℝ) (d i j)]

def sourceX : Fin 6 → ℤ := ![1183,-1183,981,-981,202,-202]
def sourceY : Fin 6 → ℤ := ![0,0,120,-120,120,-120]
def sourceLength : Fin 6 → Fin 6 → ℕ :=
  !![0,2366,598,2236,1131,1495;
     2366,0,2236,598,1495,1131;
     598,2236,0,2262,779,1633;
     2236,598,2262,0,1633,779;
     1131,1495,779,1633,0,1196;
     1495,1131,1633,779,1196,0]

noncomputable def src (i : Fin 6) : ℝ² := latticePoint 22 (sourceX i) (sourceY i)

theorem source_general_position_integral :
    (Set.range src).Finite ∧ (Set.range src).ncard = 6 ∧
    NonTrilinear (Set.range src) ∧
    (∀ Q : Set ℝ², Q ⊆ Set.range src ∧ Q.ncard = 4 → ¬Cospherical Q) ∧
    ((Set.range src).Pairwise fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) := by
  apply integral_configuration_certificate 22 6 (by norm_num) sourceX sourceY sourceLength
  · decide
  · decide
  · decide
  · decide

def outputX : Fin 7 → ℤ := ![0,753928,1675485,2680340,2439684,596570,-118638]
def outputY : Fin 7 → ℤ := ![0,-235440,-48480,425880,-141960,-141960,-141960]
noncomputable def out (i : Fin 7) : ℝ² := latticePoint 22 (outputX i) (outputY i)

@[simp] private lemma sourceX_0 : sourceX 0 = 1183 := rfl
@[simp] private lemma sourceX_1 : sourceX 1 = -1183 := rfl
@[simp] private lemma sourceX_2 : sourceX 2 = 981 := rfl
@[simp] private lemma sourceX_3 : sourceX 3 = -981 := rfl
@[simp] private lemma sourceX_4 : sourceX 4 = 202 := rfl
@[simp] private lemma sourceX_5 : sourceX 5 = -202 := rfl
@[simp] private lemma sourceY_0 : sourceY 0 = 0 := rfl
@[simp] private lemma sourceY_1 : sourceY 1 = 0 := rfl
@[simp] private lemma sourceY_2 : sourceY 2 = 120 := rfl
@[simp] private lemma sourceY_3 : sourceY 3 = -120 := rfl
@[simp] private lemma sourceY_4 : sourceY 4 = 120 := rfl
@[simp] private lemma sourceY_5 : sourceY 5 = -120 := rfl
@[simp] private lemma outputX_0 : outputX 0 = 0 := rfl
@[simp] private lemma outputX_1 : outputX 1 = 753928 := rfl
@[simp] private lemma outputX_2 : outputX 2 = 1675485 := rfl
@[simp] private lemma outputX_3 : outputX 3 = 2680340 := rfl
@[simp] private lemma outputX_4 : outputX 4 = 2439684 := rfl
@[simp] private lemma outputX_5 : outputX 5 = 596570 := rfl
@[simp] private lemma outputX_6 : outputX 6 = -118638 := rfl
@[simp] private lemma outputY_0 : outputY 0 = 0 := rfl
@[simp] private lemma outputY_1 : outputY 1 = -235440 := rfl
@[simp] private lemma outputY_2 : outputY 2 = -48480 := rfl
@[simp] private lemma outputY_3 : outputY 3 = 425880 := rfl
@[simp] private lemma outputY_4 : outputY 4 = -141960 := rfl
@[simp] private lemma outputY_5 : outputY 5 = -141960 := rfl
@[simp] private lemma outputY_6 : outputY 6 = -141960 := rfl

noncomputable def complexEmbed (p : ℝ²) : ℂ := p 0 + p 1 * Complex.I

lemma output_is_quadratic (i : Fin 7) :
    complexEmbed (out i) = CentralQuadratic.point
      (complexEmbed (src 0)) (complexEmbed (src 2)) (complexEmbed (src 4)) i := by
  have hs : Real.sqrt 22 ^ 2 = (22 : ℝ) := Real.sq_sqrt (by norm_num)
  fin_cases i <;> apply Complex.ext
  all_goals norm_num [complexEmbed,out,src,latticePoint,outputX,outputY,
    CentralQuadratic.point,Matrix.cons_val_succ,Matrix.cons_val_succ',Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,pow_two]
  all_goals nlinarith [hs]

lemma output_collinear : Collinear ℝ {out 4,out 5,out 6} := by
  apply (collinear_iff_of_mem (by simp : out 4 ∈ ({out 4,out 5,out 6} : Set ℝ²))).mpr
  refine ⟨!₂[(1 : ℝ),0],?_⟩
  intro p hp
  rcases hp with rfl | hp
  · exact ⟨0,by simp⟩
  rcases hp with rfl | hp
  · refine ⟨-1843114,?_⟩
    ext k
    fin_cases k <;> norm_num [out,latticePoint,Matrix.cons_val_succ,Matrix.cons_val_succ']
  have hp' : p = out 6 := Set.mem_singleton_iff.mp hp
  subst p
  refine ⟨-2558322,?_⟩
  ext k
  fin_cases k <;> norm_num [out,latticePoint,Matrix.cons_val_succ,Matrix.cons_val_succ']

lemma output_not_general_position : ¬NonTrilinear (Set.range out) := by
  intro h
  apply h ⟨4,rfl⟩ ⟨5,rfl⟩ ⟨6,rfl⟩ ?_ ?_ ?_ output_collinear
  all_goals intro he
  all_goals have hh := congrArg (fun p : ℝ² => p 0) he
  all_goals norm_num [out,latticePoint,Matrix.cons_val_succ,Matrix.cons_val_succ'] at hh

#print axioms source_general_position_integral

lemma complexEmbed_distance (p q : ℝ²) :
    dist (complexEmbed p) (complexEmbed q) = dist p q := by
  have hs : dist (complexEmbed p) (complexEmbed q)^2 = dist p q ^2 := by
    rw [Complex.dist_eq, Complex.sq_norm, p4_dist_sq]
    simp [complexEmbed, Complex.normSq_apply, pow_two]
  nlinarith [dist_nonneg (x := complexEmbed p) (y := complexEmbed q),
    dist_nonneg (x := p) (y := q)]

lemma source_complex_coordinates (i : Fin 6) :
    complexEmbed (src i) = CentralQuadratic.source
      (complexEmbed (src 0)) (complexEmbed (src 2)) (complexEmbed (src 4)) i := by
  have h0 : complexEmbed (src 0) = (1183 : ℂ) := by simp [complexEmbed,src,latticePoint]
  have h2 : complexEmbed (src 2) = 981 + 120 * (Real.sqrt 22 : ℂ) * Complex.I := by
    simp [complexEmbed,src,latticePoint]
  have h4 : complexEmbed (src 4) = 202 + 120 * (Real.sqrt 22 : ℂ) * Complex.I := by
    simp [complexEmbed,src,latticePoint]
  rw [h0,h2,h4]
  fin_cases i <;> apply Complex.ext
  all_goals norm_num [complexEmbed,src,latticePoint,sourceX,sourceY,CentralQuadratic.source,
    Matrix.cons_val_succ,Matrix.cons_val_succ']

lemma source_distance_rational (i j : Fin 6) :
    dist (src i) (src j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  by_cases h : src i = src j
  · exact ⟨0,by simp [h]⟩
  obtain ⟨z,hz⟩ := source_general_position_integral.2.2.2.2 ⟨i,rfl⟩ ⟨j,rfl⟩ h
  exact ⟨(z : ℚ),by simpa using hz⟩

lemma output_distance_rational (i j : Fin 7) :
    dist (out i) (out j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  rw [← complexEmbed_distance, output_is_quadratic, output_is_quadratic]
  apply CentralQuadratic.point_rational_distances
  apply CentralQuadratic.source_factors_rational
  intro k l
  rw [← source_complex_coordinates, ← source_complex_coordinates, complexEmbed_distance]
  exact source_distance_rational k l

#print axioms complexEmbed_distance
#print axioms source_complex_coordinates
#print axioms source_distance_rational
#print axioms output_distance_rational

#print axioms output_is_quadratic
#print axioms output_collinear
#print axioms output_not_general_position
end Erdos213.CentralDegeneration
