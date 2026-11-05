import Submission.SparseBoundary
import Submission.UnitGap
import Submission.DensityReduction

/-!
# A final conditional matching-to-density bridge

The finite counting argument needs **injective** opposite-sign maps, separately
for the two source signs. Sources are the clean vertices of `[2,N]`; targets
are all opposite-sign vertices of that same interval, and may be dirty.
Two such maps need not be the restrictions of one common involution.

`CleanOppositeSignCover` states exactly this unit-capacity assumption.
`ActualCleanCover` additionally requires an edge sharing an actual greatest
prime factor or actual cofactor, using the relations from `UnitGap`.
The counting argument forgets only this extra edge condition.

Neither cover is proved here. In particular, the total seed-existence results
in `UnitGap` do NOT provide injectivity and are NOT used as a matching.
The final theorems retain a visible `∀ N, 3 ≤ N → ...` cover hypothesis.
Only under that hypothesis do the unconditional sparse-boundary theorem and
the verified density equivalence give the exact original density one half.
No original conjecture theorem or specification file is imported or used.

The interval sum is exactly the existing inclusive `comparisonSum N`.
Both integer and real normalized bounds are given; division by a zero
cardinality at `N ≤ 1` is harmless because the interval and sum are empty.
The passage to the original `range N` density uses `DensityReduction`'s
endpoint-correct equivalence, not an identification of the two intervals.
-/

open Filter
open scoped Topology

namespace Erdos371.MatchingReduction

section Finite

variable {α : Type*} [DecidableEq α]

/-- Vertices of a specified integer sign in a finite ambient set. -/
def signVertices (V : Finset α) (s : α → ℤ) (ε : ℤ) : Finset α :=
  V.filter (fun a => s a = ε)

/-- Unit capacity separately for each source sign. Only the source is required
 to lie outside `B`; the image can be any opposite-sign vertex of `V`.
`InjOn` imposes no conditions on the chosen ambient function outside its domain. -/
def CleanSignCover (V B : Finset α) (s : α → ℤ) : Prop :=
  ∀ ε : ℤ, ε = 1 ∨ ε = -1 → ∃ f : α → α,
    Set.MapsTo f (signVertices (V \ B) s ε : Set α)
      (signVertices V s (-ε) : Set α) ∧
    Set.InjOn f (signVertices (V \ B) s ε : Set α)

/-- Injectivity, not just existence of an image for each source, gives this count. -/
theorem clean_sign_card_le_opposite (V B : Finset α) (s : α → ℤ)
    (hcover : CleanSignCover V B s) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (signVertices (V \ B) s ε).card ≤ (signVertices V s (-ε)).card := by
  obtain ⟨f, hf, hinj⟩ := hcover ε hε
  exact Finset.card_le_card_of_injOn f hf hinj

/-- Deleting the boundary loses at most `B.card` vertices of any fixed sign.
No inclusion hypothesis on `B` is needed for this generic bound. -/
theorem sign_card_le_clean_add_dirty (V B : Finset α) (s : α → ℤ) (ε : ℤ) :
    (signVertices V s ε).card ≤ (signVertices (V \ B) s ε).card + B.card := by
  have hdiff : signVertices V s ε \ B = signVertices (V \ B) s ε := by
    ext a
    simp only [signVertices, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  simpa only [hdiff] using
    (Finset.card_le_card_sdiff_add_card :
      (signVertices V s ε).card ≤ (signVertices V s ε \ B).card + B.card)

/-- The difference between the two sign counts is bounded by the boundary count. -/
theorem abs_sign_card_sub_le_dirty (V B : Finset α) (s : α → ℤ)
    (hcover : CleanSignCover V B s) :
    |((signVertices V s 1).card : ℤ) - ((signVertices V s (-1)).card : ℤ)| ≤
      (B.card : ℤ) := by
  have hpos := (sign_card_le_clean_add_dirty V B s 1).trans
    (Nat.add_le_add_right
      (clean_sign_card_le_opposite V B s hcover (Or.inl rfl)) B.card)
  have hneg' := (sign_card_le_clean_add_dirty V B s (-1)).trans
    (Nat.add_le_add_right
      (clean_sign_card_le_opposite V B s hcover (Or.inr rfl)) B.card)
  have hneg : (signVertices V s (-1)).card ≤ (signVertices V s 1).card + B.card := by
    simpa only [neg_neg] using hneg'
  apply abs_le.mpr
  constructor <;> omega

omit [DecidableEq α] in
/-- Exact finite signed-sum identity: ascending count minus descending count. -/
theorem sum_sign_eq_card_sub (V : Finset α) (s : α → ℤ)
    (hs : ∀ a ∈ V, s a = 1 ∨ s a = -1) :
    (∑ a ∈ V, s a) =
      ((signVertices V s 1).card : ℤ) - ((signVertices V s (-1)).card : ℤ) := by
  have hnot : V.filter (fun a => ¬ s a = 1) = signVertices V s (-1) := by
    unfold signVertices
    apply Finset.filter_congr
    intro a ha
    rcases hs a ha with h | h <;> simp [h]
  calc
    (∑ a ∈ V, s a) = ∑ a ∈ V, if s a = 1 then (1 : ℤ) else -1 := by
      apply Finset.sum_congr rfl
      intro a ha
      rcases hs a ha with h | h <;> simp [h]
    _ = _ := by simp [Finset.sum_ite, hnot, signVertices, sub_eq_add_neg]

/-- Generic finite cancellation bound under the explicit unit-capacity cover. -/
theorem abs_sum_le_dirty_of_cover (V B : Finset α) (s : α → ℤ)
    (hs : ∀ a ∈ V, s a = 1 ∨ s a = -1) (hcover : CleanSignCover V B s) :
    |∑ a ∈ V, s a| ≤ (B.card : ℤ) := by
  rw [sum_sign_eq_card_sub V s hs]
  exact abs_sign_card_sub_le_dirty V B s hcover

end Finite

/-- The exact inclusive vertex interval of `comparisonSum`. -/
def vertices (N : ℕ) : Finset ℕ := Finset.Icc 2 N

/-- Dirty comparisons in the original interval, as defined by `SparseBoundary`. -/
noncomputable def dirtyVertices (N : ℕ) : Finset ℕ :=
  open scoped Classical in
  (vertices N).filter (fun n => n ∈ SparseBoundary.dirtyComparison)

/-- All and only the clean comparison sources in the original interval. -/
noncomputable def cleanVertices (N : ℕ) : Finset ℕ := vertices N \ dirtyVertices N

/-- The source condition uses the actual two roots, including the source `2`. -/
theorem mem_cleanVertices_iff (N n : ℕ) :
    n ∈ cleanVertices N ↔ 2 ≤ n ∧ n ≤ N ∧ UnitGap.CleanComparison n := by
  classical
  simp only [cleanVertices, dirtyVertices, vertices, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_Icc, SparseBoundary.dirtyComparison,
    Set.mem_setOf_eq, UnitGap.CleanComparison, UnitGap.CleanRoot]
  tauto

/-- The interval has `N - 1` vertices, with natural subtraction at small endpoints. -/
theorem vertices_card (N : ℕ) : (vertices N).card = N - 1 := by
  rw [vertices, Nat.card_Icc]
  omega

/-- Both small inclusive intervals are empty, not singleton intervals. -/
theorem vertices_eq_empty_of_le_one {N : ℕ} (hN : N ≤ 1) : vertices N = ∅ := by
  exact Finset.Icc_eq_empty_of_lt (by omega)

/-- No dirty comparisons are counted at the two junk endpoints. -/
theorem dirtyVertices_eq_empty_of_le_one {N : ℕ} (hN : N ≤ 1) :
    dirtyVertices N = ∅ := by
  classical
  simp only [dirtyVertices, vertices_eq_empty_of_le_one hN, Finset.filter_empty]

/-- The existing sum also vanishes at `N = 0` and `N = 1`. -/
theorem comparisonSum_eq_zero_of_le_one {N : ℕ} (hN : N ≤ 1) : comparisonSum N = 0 := by
  change (∑ n ∈ vertices N, comparisonSign n) = 0
  rw [vertices_eq_empty_of_le_one hN, Finset.sum_empty]

/-- The sign-only finite hypothesis; targets need not be clean. -/
def CleanOppositeSignCover (N : ℕ) : Prop :=
  CleanSignCover (vertices N) (dirtyVertices N) comparisonSign

/-- An actual opposite-sign edge sharing a maximum or cofactor of the actual roots. -/
def ActualEdge (n t : ℕ) : Prop :=
  comparisonSign t = -comparisonSign n ∧
    (UnitGap.SharesActualPrime n t ∨ UnitGap.SharesActualCofactor n t)

/-- The stronger actual-graph unit-capacity hypothesis. The functions are injective
on clean sources of each sign, and their targets lie in ALL of `[2,N]`.
No injectivity of the particular seed rule is assumed or inferred. -/
def ActualCleanCover (N : ℕ) : Prop :=
  ∀ ε : ℤ, ε = 1 ∨ ε = -1 → ∃ f : ℕ → ℕ,
    (∀ n ∈ signVertices (cleanVertices N) comparisonSign ε,
      f n ∈ vertices N ∧ ActualEdge n (f n)) ∧
    Set.InjOn f (signVertices (cleanVertices N) comparisonSign ε : Set ℕ)

/-- Counting uses only the opposite-sign and injectivity parts of an actual cover. -/
theorem actualCleanCover_implies_signCover {N : ℕ} (hcover : ActualCleanCover N) :
    CleanOppositeSignCover N := by
  intro ε hε
  obtain ⟨f, hf, hinj⟩ := hcover ε hε
  refine ⟨f, ?_, hinj⟩
  intro n hn
  obtain ⟨ht, hs, _hedge⟩ := hf n hn
  change n ∈ (cleanVertices N).filter (fun n => comparisonSign n = ε) at hn
  change f n ∈ (vertices N).filter (fun t => comparisonSign t = -ε)
  apply Finset.mem_filter.mpr
  refine ⟨ht, ?_⟩
  rw [hs, (Finset.mem_filter.mp hn).2]

/-- The original interval sum is exactly its two sign counts' difference. -/
theorem comparisonSum_eq_card_sub (N : ℕ) :
    comparisonSum N = ((signVertices (vertices N) comparisonSign 1).card : ℤ) -
      ((signVertices (vertices N) comparisonSign (-1)).card : ℤ) := by
  exact sum_sign_eq_card_sub (vertices N) comparisonSign
    (fun n _ => comparisonSign_eq_one_or_neg_one n)

/-- The unnormalized finite bound, in integers, at the same original cutoff `N`. -/
theorem abs_comparisonSum_le_dirty_of_cover {N : ℕ} (hcover : CleanOppositeSignCover N) :
    |comparisonSum N| ≤ ((dirtyVertices N).card : ℤ) := by
  exact abs_sum_le_dirty_of_cover (vertices N) (dirtyVertices N) comparisonSign
    (fun n _ => comparisonSign_eq_one_or_neg_one n) hcover

/-- Actual edges add constraints to the hypothesis but do not change the bound. -/
theorem abs_comparisonSum_le_dirty_of_actualCover {N : ℕ} (hcover : ActualCleanCover N) :
    |comparisonSum N| ≤ ((dirtyVertices N).card : ℤ) :=
  abs_comparisonSum_le_dirty_of_cover (actualCleanCover_implies_signCover hcover)

/-- The normalized average is bounded by the dirty proportion, also at zero card.
For `N ≤ 1`, both numerator counts and `comparisonSum` are zero. -/
theorem abs_normalized_comparisonSum_card_le {N : ℕ} (hcover : CleanOppositeSignCover N) :
    |(comparisonSum N : ℝ) / (vertices N).card| ≤
      ((dirtyVertices N).card : ℝ) / (vertices N).card := by
  simp only [abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast abs_comparisonSum_le_dirty_of_cover hcover

/-- The normalization used by the density reduction, with no endpoint shift in the sum. -/
theorem abs_normalized_comparisonSum_le {N : ℕ} (hcover : CleanOppositeSignCover N) :
    |(comparisonSum N : ℝ) / N| ≤ ((dirtyVertices N).card : ℝ) / N := by
  simp only [abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast abs_comparisonSum_le_dirty_of_cover hcover

/-- Inclusive dirty counts have strict-prefix endpoint `N + 1`, not `N`. -/
theorem dirtyVertices_card_eq_countBelow (N : ℕ) :
    (dirtyVertices N).card = DensityReduction.countBelow SparseBoundary.dirtyComparison (N + 1) := by
  classical
  unfold dirtyVertices vertices DensityReduction.countBelow
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_hn2, hnN⟩, hdirty⟩
    exact ⟨by omega, hdirty⟩
  · rintro ⟨hnN, hdirty⟩
    exact ⟨⟨hdirty.1, by omega⟩, hdirty⟩

/-- Unconditional sparsity of the actual inclusive dirty count, normalized by `N`. -/
theorem dirtyVertices_normalized_tendsto_zero :
    Tendsto (fun N : ℕ => ((dirtyVertices N).card : ℝ) / N) atTop (𝓝 0) := by
  have hdirty : Tendsto (fun N : ℕ =>
      (DensityReduction.countBelow SparseBoundary.dirtyComparison N : ℝ) / N)
      atTop (𝓝 0) := by
    simpa only [Set.HasDensity, DensityReduction.partialDensity_eq_countBelow_div] using
      SparseBoundary.dirtyComparison_hasDensity_zero
  simpa only [dirtyVertices_card_eq_countBelow] using
    SparseBoundary.shifted_count_normalized_tendsto_zero SparseBoundary.dirtyComparison hdirty

/-- Conditional cancellation: the missing cover is explicitly required at every `N ≥ 3`. -/
theorem comparisonSum_normalized_tendsto_zero_of_cover
    (hcover : ∀ N : ℕ, 3 ≤ N → CleanOppositeSignCover N) :
    Tendsto (fun N : ℕ => (comparisonSum N : ℝ) / N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ dirtyVertices_normalized_tendsto_zero
  filter_upwards [eventually_ge_atTop 3] with N hN
  simpa only [Real.norm_eq_abs] using abs_normalized_comparisonSum_le (hcover N hN)

/-- The exact original density statement, CONDITIONAL on all-scale unit capacity.
The endpoint-correct equivalence is verified independently of the conjecture. -/
theorem original_hasDensity_half_of_cover
    (hcover : ∀ N : ℕ, 3 ≤ N → CleanOppositeSignCover N) :
    {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) :=
  original_density_iff_comparisonSum.mpr
    (comparisonSum_normalized_tendsto_zero_of_cover hcover)

/-- The final actual-graph bridge. The quantified matching hypothesis remains
visible; neither this theorem nor the imported seeds establish that hypothesis. -/
theorem original_hasDensity_half_of_actualCover
    (hcover : ∀ N : ℕ, 3 ≤ N → ActualCleanCover N) :
    {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) := by
  apply original_hasDensity_half_of_cover
  intro N hN
  exact actualCleanCover_implies_signCover (hcover N hN)

end Erdos371.MatchingReduction

#print axioms Erdos371.MatchingReduction.signVertices
#print axioms Erdos371.MatchingReduction.CleanSignCover
#print axioms Erdos371.MatchingReduction.clean_sign_card_le_opposite
#print axioms Erdos371.MatchingReduction.sign_card_le_clean_add_dirty
#print axioms Erdos371.MatchingReduction.abs_sign_card_sub_le_dirty
#print axioms Erdos371.MatchingReduction.sum_sign_eq_card_sub
#print axioms Erdos371.MatchingReduction.abs_sum_le_dirty_of_cover
#print axioms Erdos371.MatchingReduction.vertices
#print axioms Erdos371.MatchingReduction.dirtyVertices
#print axioms Erdos371.MatchingReduction.cleanVertices
#print axioms Erdos371.MatchingReduction.mem_cleanVertices_iff
#print axioms Erdos371.MatchingReduction.vertices_card
#print axioms Erdos371.MatchingReduction.vertices_eq_empty_of_le_one
#print axioms Erdos371.MatchingReduction.dirtyVertices_eq_empty_of_le_one
#print axioms Erdos371.MatchingReduction.comparisonSum_eq_zero_of_le_one
#print axioms Erdos371.MatchingReduction.CleanOppositeSignCover
#print axioms Erdos371.MatchingReduction.ActualEdge
#print axioms Erdos371.MatchingReduction.ActualCleanCover
#print axioms Erdos371.MatchingReduction.actualCleanCover_implies_signCover
#print axioms Erdos371.MatchingReduction.comparisonSum_eq_card_sub
#print axioms Erdos371.MatchingReduction.abs_comparisonSum_le_dirty_of_cover
#print axioms Erdos371.MatchingReduction.abs_comparisonSum_le_dirty_of_actualCover
#print axioms Erdos371.MatchingReduction.abs_normalized_comparisonSum_card_le
#print axioms Erdos371.MatchingReduction.abs_normalized_comparisonSum_le
#print axioms Erdos371.MatchingReduction.dirtyVertices_card_eq_countBelow
#print axioms Erdos371.MatchingReduction.dirtyVertices_normalized_tendsto_zero
#print axioms Erdos371.MatchingReduction.comparisonSum_normalized_tendsto_zero_of_cover
#print axioms Erdos371.MatchingReduction.original_hasDensity_half_of_cover
#print axioms Erdos371.MatchingReduction.original_hasDensity_half_of_actualCover
