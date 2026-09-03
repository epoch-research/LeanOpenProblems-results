import Submission.TranslateKernelAveragingExplore

/-! Exact averaging under shears that fix the first horizontal row.
The weighted identity retains spatial restrictions rather than replacing
restricted roots by a proportion of their complete count. -/
namespace Erdos66FirstRowFixingShear
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66ShearedParabolaPrefix Erdos66TranslateKernelAveraging
open scoped Classical
set_option maxHeartbeats 1400000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def rowShear (b : F) : (F × F) ≃+ (F × F) where
  toFun z := (z.1 + b*z.2, z.2)
  invFun z := (z.1 - b*z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> dsimp; ring

noncomputable def shearSet (b : F) (B : Finset (F × F)) : Finset (F × F) :=
  B.image (rowShear b)

omit [Fintype F] in
lemma shearSet_first_row (b : F) (B : Finset (F × F)) (x : F) :
    (x,0) ∈ shearSet b B ↔ (x,0) ∈ B := by
  have he : (x,0) = rowShear b (x,0) := by simp [rowShear]
  conv_lhs => rw [he]
  simp only [shearSet, Finset.mem_image, (rowShear b).injective.eq_iff, exists_eq_right]

omit [Fintype F] in
lemma shearSet_count (b : F) (B C : Finset (F × F)) (t s : F) :
    pairCount (shearSet b B) (shearSet b C) (t,s) = pairCount B C (t-b*s,s) := by
  have he : (t,s) = rowShear b (t-b*s,s) := by simp [rowShear]
  rw [he]
  exact pairCount_addEquiv (rowShear b) B C _

omit [Fintype F] in
/-- A common shear permutes complete low targets; it does not improve
an all-target error bound for the complete count in a horizontal slice. -/
lemma shearSet_uniform_bound_iff (b : F) (B C : Finset (F × F)) (s : F)
    (μ E : ℝ) :
    (∀ t : F, |(pairCount (shearSet b B) (shearSet b C) (t,s) : ℝ)-μ| ≤ E) ↔
      (∀ t : F, |(pairCount B C (t,s) : ℝ)-μ| ≤ E) := by
  simp_rw [shearSet_count]
  constructor
  · intro h t
    simpa only [add_sub_cancel_right] using h (t+b*s)
  · intro h t
    exact h (t-b*s)

noncomputable def weightedPair (A B : Finset F) (t : F) (w : F → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ c ∈ B, if a+c=t then w a else 0

omit [Fintype F] in
lemma weightedPair_one (A B : Finset F) (t : F) :
    weightedPair A B t (fun _ ↦ 1) = (pairCount A B t : ℝ) := by
  unfold weightedPair pairCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  have he (c : F) : a+c=t ↔ c=t-a := by constructor <;> intro h <;> linear_combination h
  simp_rw [he]
  simp

omit [Fintype F] in
lemma weightedPair_shift (A B : Finset F) (a c t : F) (w : F → ℝ) :
    weightedPair (shiftSet A a) (shiftSet B c) t w =
      ∑ x ∈ A, ∑ y ∈ B, if x+y+a+c=t then w (a+x) else 0 := by
  unfold weightedPair shiftSet
  rw [Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  simp_rw [Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [show (a+x)+(c+y)=x+y+a+c by ring]

/-- Exact spatially weighted average for two rows. The weight remains on
a linear combination of the two original row coordinates. -/
theorem weighted_row_shear_average (A B : Finset F) (y v t : F)
    (hs : y+v ≠ 0) (w : F → ℝ) :
    (∑ b : F, weightedPair (shiftSet A (b*y)) (shiftSet B (b*v)) t w) =
      ∑ a ∈ A, ∑ c ∈ B, w ((v*a-y*c+y*t)/(y+v)) := by
  simp_rw [weightedPair_shift]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  have he (b : F) : a+c+b*y+b*v=t ↔ b=(t-a-c)/(y+v) := by
    rw [eq_div_iff hs]
    constructor <;> intro h <;> linear_combination h
  simp_rw [he]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  congr 1
  field_simp
  ring

lemma row_shear_complete_average (A B : Finset F) (y v t : F) (hs : y+v ≠ 0) :
    (∑ b : F, (pairCount (shiftSet A (b*y)) (shiftSet B (b*v)) t : ℝ)) =
      (A.card : ℝ)*B.card := by
  have hh := weighted_row_shear_average A B y v t hs (fun _ ↦ 1)
  simpa only [weightedPair_one, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

/-- For a retained first row the average depends on its actual prefix mass,
not merely its total cardinality. -/
lemma retained_row_weighted_average (A B : Finset F) (v t : F) (hv : v ≠ 0)
    (w : F → ℝ) :
    (∑ b : F, weightedPair A (shiftSet B (b*v)) t w) =
      (B.card : ℝ) * ∑ a ∈ A, w a := by
  have hh := weighted_row_shear_average A B 0 v t (by simpa using hv) w
  have hzero : shiftSet A (0 : F) = A := by simp [shiftSet]
  simp only [mul_zero, hzero, zero_mul, sub_zero, add_zero, zero_add] at hh
  simp only [mul_div_cancel_left₀ _ hv, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  exact hh

end Erdos66FirstRowFixingShear
