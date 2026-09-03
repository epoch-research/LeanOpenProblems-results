import Submission.HyperbolaTupleExtraction

/-! Common-square-class version of the conditional hyperbola construction.
The common scaling is real, not necessarily rational. No unbounded arithmetic
existence premise is proved, and Erdős 213 remains unresolved. -/
open EuclideanGeometry
namespace Erdos213.HyperbolaCommonClassExtraction
open HyperbolaTupleExtraction
set_option maxHeartbeats 2000000

lemma erdos213For_of_common_squared_distances {n : ℕ} (p : Fin n → ℝ²)
    (hp : Function.Injective p) (hgen : InGeneralPosition (Set.range p))
    (δ : ℚ) (hδ : 0 < δ)
    (hsq : ∀ i j, i ≠ j → ∃ r : ℚ, dist (p i) (p j)^2 = (δ : ℝ)*(r : ℝ)^2) :
    Erdos213For n := by
  apply (erdos213For_iff_rational n).mpr
  let c : ℝ := (Real.sqrt (δ : ℝ))⁻¹
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hδr)
  have hinj : Function.Injective (fun i => c • p i) := by
    intro i j h
    apply hp
    have hh := congrArg (fun x : ℝ² => c⁻¹ • x) h
    simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hc),one_smul] using hh
  refine ⟨Set.range (fun i => c • p i),Set.finite_range _,?_,?_,?_⟩
  · rw [Set.ncard_range_of_injective hinj]
    simp
  · rw [Set.range_comp']
    exact general_position_scale hgen (ne_of_gt hc)
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
    obtain ⟨r,hr⟩ := hsq i j (fun he => hij (he ▸ rfl))
    refine ⟨|r|,?_⟩
    rw [Rat.cast_abs,dist_smul₀,Real.norm_eq_abs,abs_of_pos hc]
    apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg hc.le dist_nonneg)).mp
    rw [sq_abs]
    symm
    dsimp [c]
    rw [mul_pow,inv_pow,Real.sq_sqrt hδr.le,hr]
    field_simp

lemma points_general_position {n : ℕ} (N : ℚ) (hN : 0 < N) (t : Fin n → ℚ)
    (hpos : ∀ i, 0 < t i) (hprod : ∀ i j k l, t i*t j*t k*t l ≠ N) :
    InGeneralPosition (Set.range (fun i => point N (t i))) := by
  let p : Fin n → ℝ² := fun i => point N (t i)
  have hne (i : Fin n) : t i ≠ 0 := ne_of_gt (hpos i)
  refine ⟨?_,?_⟩
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact point_not_collinear hN (hne i) (hne j) (hne k)
      (fun he => hij (congrArg (point N) he))
      (fun he => hik (congrArg (point N) he))
      (fun he => hjk (congrArg (point N) he))
  · intro Q hQ h4 hcos
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp h4
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({p i,b,c,d} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({p i,p j,c,d} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : d ∈ ({p i,p j,p k,d} : Set ℝ²))
    exact point_not_cospherical hN (hne i) (hne j) (hne k) (hne l)
      (fun he => hab (congrArg (point N) he)) (fun he => hac (congrArg (point N) he))
      (fun he => had (congrArg (point N) he)) (fun he => hbc (congrArg (point N) he))
      (fun he => hbd (congrArg (point N) he)) (fun he => hcd (congrArg (point N) he))
      (hprod i j k l) hcos

lemma common_class_distance {N δ a b : ℚ} (hN : 0 ≤ N) (hδ : δ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hsq : IsSquare (((a*b)^2+N)/δ)) :
    ∃ r : ℚ, dist (point N a) (point N b)^2 = (δ : ℝ)*(r : ℝ)^2 := by
  obtain ⟨u,hu⟩ := hsq
  have hnum : (a*b)^2+N = δ*u^2 := by
    have hh := (div_eq_iff hδ).mp hu
    nlinarith only [hh]
  have he : TwistedHyperbola.distanceSq N a b = δ*(((a-b)/(a*b))*u)^2 := by
    rw [TwistedHyperbola.distance_factor N a b ha hb,hnum]
    ring
  refine ⟨((a-b)/(a*b))*u,?_⟩
  rw [point_dist_sq hN]
  exact_mod_cast he

/-- The normalized product squares suffice even when δ is nonsquare. -/
theorem certificate_common_class {n : ℕ} (N δ : ℚ) (hN : 0 < N) (hδ : 0 < δ)
    (t : Fin n → ℚ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (hprod : ∀ i j k l, t i*t j*t k*t l ≠ N)
    (hsq : ∀ i j, i ≠ j → IsSquare (((t i*t j)^2+N)/δ)) : Erdos213For n := by
  apply erdos213For_of_common_squared_distances (fun i => point N (t i))
    ((point_injective N).comp ht) (points_general_position N hN t hpos hprod) δ hδ
  intro i j hij
  exact common_class_distance hN.le (ne_of_gt hδ) (ne_of_gt (hpos i))
    (ne_of_gt (hpos j)) (hsq i j hij)

/-- Extract n GP points from 2n parameters in one common norm square class. -/
theorem erdos213For_of_common_class_tuple {n : ℕ} (N δ : ℚ) (hN : 0 < N) (hδ : 0 < δ)
    (S : Finset ℚ) (hpos : ∀ a ∈ S, 0 < a) (hcard : 2*n ≤ S.card)
    (hsq : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsSquare (((a*b)^2+N)/δ)) :
    Erdos213For n := by
  classical
  obtain ⟨T,hTS,hTc,hside⟩ := extract_half (N := N) hpos hcard
  let e : Fin n ≃ T := (Fintype.equivFinOfCardEq (show Fintype.card T = n by simpa using hTc)).symm
  let t : Fin n → ℚ := fun i => e i
  have ht : Function.Injective t := Subtype.val_injective.comp e.injective
  have hmem (i : Fin n) : t i ∈ T := (e i).property
  apply certificate_common_class N δ hN hδ t ht (fun i => hpos _ (hTS (hmem i)))
  · intro i j k l
    exact hside.product_ne hN (fun a ha => hpos a (hTS ha))
      (hmem i) (hmem j) (hmem k) (hmem l)
  · intro i j hij
    exact hsq _ (hTS (hmem i)) _ (hTS (hmem j)) (ht.ne hij)

/-- This premise is not established by the present development. -/
def UnboundedCommonClassTuples : Prop :=
  ∀ m : ℕ, ∃ N δ : ℚ, 0 < N ∧ 0 < δ ∧ ∃ S : Finset ℚ, m ≤ S.card ∧
    (∀ a ∈ S, 0 < a) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsSquare (((a*b)^2+N)/δ))

theorem conjecture_of_unbounded_common_class_tuples (h : UnboundedCommonClassTuples) :
    ∀ n : ℕ, n ≥ 4 → Erdos213For n := by
  intro n _
  obtain ⟨N,δ,hN,hδ,S,hcard,hpos,hsq⟩ := h (2*n)
  exact erdos213For_of_common_class_tuple N δ hN hδ S hpos hcard hsq

private def controlParameter : Fin 3 → ℚ := ![1,7,1/7]
private def controlRoot : Fin 3 → Fin 3 → ℚ :=
  !![0,5,5/7; 5,0,1; 5/7,1,0]

/-- A three-parameter metric control in the genuinely nonsquare class 2.
It is not an unbounded tuple construction or a cardinality improvement. -/
lemma common_class_control : ∀ i j : Fin 3, i ≠ j →
    IsSquare (((controlParameter i*controlParameter j)^2+1)/2) := by
  intro i j hij
  refine ⟨controlRoot i j,?_⟩
  fin_cases i <;> fin_cases j <;> norm_num [controlParameter,controlRoot] at *

#print axioms common_class_control
#print axioms erdos213For_of_common_squared_distances
#print axioms points_general_position
#print axioms common_class_distance
#print axioms certificate_common_class
#print axioms erdos213For_of_common_class_tuple
#print axioms conjecture_of_unbounded_common_class_tuples
end Erdos213.HyperbolaCommonClassExtraction
