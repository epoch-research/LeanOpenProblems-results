import Submission.PairedMatrix

/-! Exact quadratic-form and mass identities for the finite paired blocks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.Paired

variable {ι τ : Type*} [Fintype ι] [Fintype τ]

omit [Fintype ι] in
lemma indicator_nonneg (s : Finset ι) (i : ι) : 0 ≤ indicator s i := by
  classical
  simp only [indicator]
  split <;> norm_num

lemma sum_mul_indicator (s : Finset ι) (x : ι → ℝ) :
    (∑ i, x i * indicator s i) = ∑ i ∈ s, x i := by
  classical
  simp [indicator, mul_ite]

lemma sum_indicator (s : Finset ι) : (∑ i, indicator s i) = (s.card : ℝ) := by
  simpa using sum_mul_indicator s (fun _ => 1)

lemma qform_outer (w : ℝ) (v x : ι → ℝ) :
    qform (fun i j => w * v i * v j) x = w * (∑ i, x i * v i) ^ 2 := by
  unfold qform
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma qform_sum (K : τ → ι → ι → ℝ) (x : ι → ℝ) :
    qform (fun i j => ∑ t, K t i j) x = ∑ t, qform (K t) x := by
  unfold qform
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ t, x i * x j * K t i j) =
        ∑ i, ∑ t, ∑ j, x i * x j * K t i j := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, x i * x j * K t i j := Finset.sum_comm

noncomputable def Block.traceMass (b : Block ι) : ℝ :=
  b.weight * ((b.left.card : ℝ) + (b.right.card : ℝ))
noncomputable def Block.crossMass (b : Block ι) : ℝ :=
  2 * b.weight * (b.left.card : ℝ) * (b.right.card : ℝ)
noncomputable def Block.imbalanceMass (b : Block ι) : ℝ :=
  b.weight * ((b.left.card : ℝ) - (b.right.card : ℝ)) ^ 2

omit [Fintype ι] in
lemma Block.gram_outer (b : Block ι) (i j : ι) :
    b.gram i j = b.weight * (indicator b.left i - indicator b.right i) *
      (indicator b.left j - indicator b.right j) := by
  unfold Block.gram Block.diag Block.cross
  ring

lemma Block.qform_gram (b : Block ι) (x : ι → ℝ) :
    qform b.gram x = b.weight * ((∑ i ∈ b.left, x i) - (∑ i ∈ b.right, x i)) ^ 2 := by
  have he : b.gram = fun i j => b.weight *
      (indicator b.left i - indicator b.right i) *
      (indicator b.left j - indicator b.right j) := by
    funext i j
    exact b.gram_outer i j
  rw [he, qform_outer]
  simp_rw [mul_sub, Finset.sum_sub_distrib, sum_mul_indicator]

lemma Block.psd_gram (b : Block ι) (hw : 0 ≤ b.weight) : PSD b.gram := by
  intro x
  rw [Block.qform_gram]
  exact mul_nonneg hw (sq_nonneg _)

omit [Fintype ι] in
lemma Block.cross_symm (b : Block ι) (i j : ι) : b.cross i j = b.cross j i := by
  unfold Block.cross
  ring

omit [Fintype ι] in
lemma Block.cross_nonneg (b : Block ι) (hw : 0 ≤ b.weight) (i j : ι) :
    0 ≤ b.cross i j := by
  unfold Block.cross
  exact mul_nonneg hw (add_nonneg
    (mul_nonneg (indicator_nonneg _ _) (indicator_nonneg _ _))
    (mul_nonneg (indicator_nonneg _ _) (indicator_nonneg _ _)))

omit [Fintype ι] in
lemma Block.cross_self (b : Block ι) (hb : b.Valid) (i : ι) : b.cross i i = 0 := by
  classical
  by_cases hl : i ∈ b.left
  · have hr := hb.2.2.1 i hl
    simp [Block.cross, indicator, hl, hr]
  · simp [Block.cross, indicator, hl]

omit [Fintype ι] in
lemma Block.gram_self (b : Block ι) (hb : b.Valid) (i : ι) :
    b.gram i i = b.weight * (indicator b.left i + indicator b.right i) := by
  classical
  rw [Block.gram, b.cross_self hb i]
  by_cases hl : i ∈ b.left <;> by_cases hr : i ∈ b.right <;>
    simp [Block.diag, indicator, hl, hr]

lemma Block.trace_gram (b : Block ι) (hb : b.Valid) :
    traceSum b.gram = b.traceMass := by
  unfold traceSum Block.traceMass
  simp_rw [b.gram_self hb, ← Finset.mul_sum, Finset.sum_add_distrib, sum_indicator]

lemma totalSum_outer (w : ℝ) (u v : ι → ℝ) :
    totalSum (fun i j => w * u i * v j) = w * (∑ i, u i) * (∑ j, v j) := by
  unfold totalSum
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

lemma Block.total_cross (b : Block ι) : totalSum b.cross = b.crossMass := by
  have he : totalSum b.cross =
      totalSum (fun i j => b.weight * indicator b.left i * indicator b.right j) +
      totalSum (fun i j => b.weight * indicator b.right i * indicator b.left j) := by
    simp [totalSum, Block.cross, mul_add, mul_assoc, Finset.sum_add_distrib]
  rw [he, totalSum_outer, totalSum_outer, sum_indicator, sum_indicator]
  unfold Block.crossMass
  ring

lemma Block.qform_one_gram (b : Block ι) :
    qform b.gram (fun _ => 1) = b.imbalanceMass := by
  rw [Block.qform_gram]
  simp [Block.imbalanceMass]

omit [Fintype ι] in
lemma gramSum_eq_sum (b : τ → Block ι) (i j : ι) :
    gramSum b i j = ∑ t, (b t).gram i j := by
  simp [gramSum, diagSum, crossSum, Block.gram, Finset.sum_sub_distrib]

lemma qform_gramSum (b : τ → Block ι) (x : ι → ℝ) :
    qform (gramSum b) x = ∑ t, qform (b t).gram x := by
  have he : gramSum b = fun i j => ∑ t, (b t).gram i j := by
    funext i j
    exact gramSum_eq_sum b i j
  rw [he, qform_sum]

lemma gramSum_psd (b : τ → Block ι) (hb : ∀ t, (b t).Valid) : PSD (gramSum b) := by
  intro x
  rw [qform_gramSum]
  exact Finset.sum_nonneg fun t _ => (b t).psd_gram (hb t).2.2.2 x

lemma gramSum_diag_nonneg (b : τ → Block ι) (hb : ∀ t, (b t).Valid) (i : ι) :
    0 ≤ gramSum b i i := by
  have h := gramSum_psd b hb (basis i)
  rwa [qform_basis] at h

lemma trace_gramSum (b : τ → Block ι) (hb : ∀ t, (b t).Valid) :
    traceSum (gramSum b) = ∑ t, (b t).traceMass := by
  unfold traceSum
  simp_rw [gramSum_eq_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (b t).trace_gram (hb t)

lemma total_crossSum (b : τ → Block ι) :
    totalSum (crossSum b) = ∑ t, (b t).crossMass := by
  rw [← qform_one]
  change qform (fun i j => ∑ t, (b t).cross i j) (fun _ => 1) = _
  rw [qform_sum]
  simp_rw [qform_one, Block.total_cross]

lemma qform_one_gramSum (b : τ → Block ι) :
    qform (gramSum b) (fun _ => 1) = ∑ t, (b t).imbalanceMass := by
  rw [qform_gramSum]
  simp_rw [Block.qform_one_gram]

omit [Fintype ι] in
lemma crossSum_symm (b : τ → Block ι) (i j : ι) : crossSum b i j = crossSum b j i := by
  unfold crossSum
  exact Finset.sum_congr rfl fun t _ => (b t).cross_symm i j

omit [Fintype ι] in
lemma crossSum_self (b : τ → Block ι) (hb : ∀ t, (b t).Valid) (i : ι) :
    crossSum b i i = 0 := by
  simp [crossSum, fun t => (b t).cross_self (hb t) i]

omit [Fintype ι] in
lemma crossSum_nonneg (b : τ → Block ι) (hb : ∀ t, (b t).Valid) (i j : ι) :
    0 ≤ crossSum b i j :=
  Finset.sum_nonneg fun t _ => (b t).cross_nonneg (hb t).2.2.2 i j

/-- The local root orientation charges twice the block cross mass to its
Gram quadratic form, without any balance assumption. -/
lemma Block.oriented_crossMass (b : Block ι) (hw : 0 ≤ b.weight) (x : ι → ℝ)
    (hl : ∀ i ∈ b.left, x i = 1) (hr : ∀ i ∈ b.right, x i = -1) :
    2 * b.crossMass ≤ qform b.gram x := by
  rw [Block.qform_gram]
  have hleft : (∑ i ∈ b.left, x i) = (b.left.card : ℝ) := by
    simp [Finset.sum_congr rfl hl]
  have hright : (∑ i ∈ b.right, x i) = -(b.right.card : ℝ) := by
    simp [Finset.sum_congr rfl hr]
  rw [hleft, hright]
  unfold Block.crossMass
  nlinarith [mul_nonneg hw (sq_nonneg ((b.left.card : ℝ) - (b.right.card : ℝ)))]

/-- Integer side sizes outside the ratio-five range cost at least twice
their total size in squared imbalance. -/
lemma unbalanced_sizes (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hbad : ¬ (a ≤ 5 * b ∧ b ≤ 5 * a)) :
    2 * ((a : ℝ) + (b : ℝ)) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
  have one_side (a b : ℕ) (hb : 0 < b) (h : 5 * b < a) :
      2 * ((a : ℝ) + (b : ℝ)) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hab : 5 * (b : ℝ) < a := by exact_mod_cast h
    have hd : 0 ≤ (a : ℝ) - b := by linarith
    have hd4 : 0 ≤ (a : ℝ) - b - 4 := by linarith
    nlinarith [mul_nonneg hd hd4]
  by_cases h : a ≤ 5 * b
  · have h' : 5 * a < b := by omega
    have := one_side b a ha h'
    nlinarith
  · exact one_side a b hb (by omega)

omit [Fintype ι] in
lemma Block.bad_mass (b : Block ι) (hb : b.Valid) (hbad : ¬ b.Balanced 5) :
    2 * b.traceMass ≤ b.imbalanceMass := by
  have h := unbalanced_sizes b.left.card b.right.card
    (Finset.card_pos.mpr hb.1) (Finset.card_pos.mpr hb.2.1) hbad
  have hw := hb.2.2.2
  unfold Block.traceMass Block.imbalanceMass
  nlinarith [mul_le_mul_of_nonneg_left h hw]

/-- Coverage of both sides realizes the whole diagonal mass using one
mate, even if the same mate covers several nested blocks. -/
lemma Block.covered_trace (b : Block ι) (hb : b.Valid) (F : ι → ι)
    (hl : ∀ i ∈ b.left, F i ∈ b.right)
    (hr : ∀ i ∈ b.right, F i ∈ b.left) :
    b.traceMass = ∑ i, b.cross i (F i) := by
  have he : ∀ i, b.gram i i = b.cross i (F i) := by
    intro i
    classical
    rw [b.gram_self hb]
    by_cases hil : i ∈ b.left
    · have hir := hb.2.2.1 i hil
      have hFr := hl i hil
      have hFl : F i ∉ b.left := fun h => hb.2.2.1 (F i) h hFr
      simp [Block.cross, indicator, hil, hir, hFr, hFl]
    · by_cases hir : i ∈ b.right
      · have hFl := hr i hir
        have hFr := hb.2.2.1 (F i) hFl
        simp [Block.cross, indicator, hil, hir, hFl, hFr]
      · simp [Block.cross, indicator, hil, hir]
  rw [← b.trace_gram hb]
  exact Finset.sum_congr rfl fun i _ => he i

end Erdos126Aux.Paired
