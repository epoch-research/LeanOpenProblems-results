import Submission.RectangleBudgetStep

/-! The first positive-exponent current family is integer-valued. The padded
current count splits into this dominant layer and a residual convex average. -/
namespace Erdos7CurrentIntegerLayer
open scoped BigOperators
open Erdos7CompleteFamilyModel
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A padded average with one specified atom of weight w splits into that
atom and a residual average. No integrality of the residual is asserted. -/
theorem padded_average_split {J : Type*} [Fintype J] [DecidableEq J]
    (w x : J → ℝ) (H : ℝ) (i : J)
    (hw : ∀ j, 0 ≤ w j) (hs : (∑ j,w j) ≤ 1)
    (hwi : w i < 1) (hH : 1 ≤ H) (hx : ∀ j, 1 ≤ x j ∧ x j ≤ H) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ H ∧
      (1-∑ j,w j)+∑ j,w j*x j = w i*x i+(1-w i)*R := by
  let T := Finset.univ.erase i
  let R := ((1-∑ j,w j)+∑ j ∈ T,w j*x j)/(1-w i)
  have hpos : 0 < 1-w i := by linarith
  have hsum : (∑ j,w j) = w i+∑ j ∈ T,w j := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hsumx : (∑ j,w j*x j) = w i*x i+∑ j ∈ T,w j*x j := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hl : (∑ j ∈ T,w j) ≤ ∑ j ∈ T,w j*x j := by
    exact Finset.sum_le_sum (fun j _ => by nlinarith [mul_nonneg (hw j) (sub_nonneg.mpr (hx j).1)])
  have hu : (∑ j ∈ T,w j*x j) ≤ (∑ j ∈ T,w j)*H := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j).2 (hw j))
  refine ⟨R,?_,?_,?_⟩
  · apply (le_div_iff₀ hpos).mpr
    linarith
  · apply (div_le_iff₀ hpos).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hH)
    nlinarith
  · dsimp only [R]
    rw [mul_div_cancel₀ _ (ne_of_gt hpos),hsumx]
    ring

/-- The residual in the dominant-layer split is a genuine convex average,
so its test can be charged to the original families by Jensen. -/
theorem residual_jensen {J : Type*} [Fintype J] [DecidableEq J]
    (w x : J → ℝ) (i : J) (hw : ∀ j,0 ≤ w j) (hs : (∑ j,w j) ≤ 1)
    (hwi : w i < 1) (U : ℝ → ℝ) (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U) :
    U (((1-∑ j,w j)+∑ j ∈ Finset.univ.erase i,w j*x j)/(1-w i)) ≤
      ((1-∑ j,w j)*U 1+∑ j ∈ Finset.univ.erase i,w j*U (x j))/(1-w i) := by
  let T := Finset.univ.erase i
  have hpos : 0 < 1-w i := by linarith
  have hn := ne_of_gt hpos
  have hsum : (∑ j,w j) = w i+∑ j ∈ T,w j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hnorm : (∑ j ∈ T,w j/(1-w i)) ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hpos).mpr
    linarith
  have hid (z : J → ℝ) (a : ℝ) :
      ((1-∑ j,w j)*a+∑ j ∈ T,w j*z j)/(1-w i) =
        (1-∑ j ∈ T,w j/(1-w i))*a+∑ j ∈ T,(w j/(1-w i))*z j := by
    have he : (∑ j ∈ T,(w j/(1-w i))*z j) = (∑ j ∈ T,w j*z j)/(1-w i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he,← Finset.sum_div,hsum]
    field_simp
    <;> ring
  have harg := hid x 1
  simp only [mul_one] at harg
  have hh := Erdos7FamilyBudgetStep.padded_jensen T (fun j => w j/(1-w i)) x U hU hmU 1
    (((1-∑ j,w j)+∑ j ∈ T,w j*x j)/(1-w i))
    (fun j _ => div_nonneg (hw j) hpos.le) hnorm (le_of_eq (by simpa only [mul_one] using harg))
  rw [← hid (fun j => U (x j)) (U 1)] at hh
  exact hh

section Concrete
variable {n : ℕ} (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
    [∀ i,DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i))

/-- Integrality holds for an actual current slice of multiplicity one, not
for an arbitrary normalized family obtained after compression. -/
theorem currentFamily_integer (t : ℕ) (ht : t < n) (a : Fin (E ⟨t,ht⟩))
    (x : ∀ i,A i) : ∃ k : ℕ, count A X (currentFamily E t ht a) x = k := by
  classical
  let B := (currentFamily E t ht a).labels
  let S := B.filter (fun k => indicator A t (exponent E k) (X k) x = 1)
  refine ⟨S.card,?_⟩
  simp only [count,currentFamily,sliceFamily_multiplicity,Nat.cast_one,div_one]
  change (∑ k ∈ B,indicator A t (exponent E k) (X k) x) = (S.card:ℝ)
  rw [show (S.card:ℝ) = ∑ k ∈ B, if indicator A t (exponent E k) (X k) x = 1 then 1 else 0 from
    (Finset.sum_boole _ B).symm]
  apply Finset.sum_congr rfl
  intro k _
  rcases indicator_eq_zero_or_one A t (exponent E k) (X k) x with hk | hk <;> simp [hk]

/-- The concrete padded current count has a dominant integer component. -/
theorem currentCount_integer_split (t : ℕ) (ht : t < n) (q : ℝ) (r : ℕ → ℝ)
    (hw : ∀ a : Fin (E ⟨t,ht⟩),0 ≤ q*r a.val)
    (hs : (∑ a : Fin (E ⟨t,ht⟩),q*r a.val) ≤ 1)
    (a : Fin (E ⟨t,ht⟩)) (ha : q*r a.val < 1) (x : ∀ i,A i) :
    ∃ (k : ℕ) (R : ℝ), 1 ≤ k ∧ k ≤ capacity E t ∧ 1 ≤ R ∧ R ≤ capacity E t ∧
      currentCount A E X t ht q r x = q*r a.val*(k:ℝ)+(1-q*r a.val)*R := by
  classical
  obtain ⟨k,hk⟩ := currentFamily_integer A E X t ht a x
  have hcount (b : Fin (E ⟨t,ht⟩)) : 1 ≤ count A X (currentFamily E t ht b) x ∧
      count A X (currentFamily E t ht b) x ≤ capacity E t :=
    ⟨count_lower A X _ x,count_upper A X (exponent_bound E) _ ht.le x⟩
  obtain ⟨R,hRl,hRu,hR⟩ := padded_average_split
    (fun b : Fin (E ⟨t,ht⟩) => q*r b.val) (fun b => count A X (currentFamily E t ht b) x)
    (capacity E t) a hw hs ha (by exact_mod_cast capacity_pos E t) hcount
  have hka := hcount a
  rw [hk] at hka hR
  exact ⟨k,R,by exact_mod_cast hka.1,by exact_mod_cast hka.2,hRl,hRu,hR⟩
end Concrete

#print axioms padded_average_split
#print axioms residual_jensen
#print axioms currentFamily_integer
#print axioms currentCount_integer_split
end Erdos7CurrentIntegerLayer
