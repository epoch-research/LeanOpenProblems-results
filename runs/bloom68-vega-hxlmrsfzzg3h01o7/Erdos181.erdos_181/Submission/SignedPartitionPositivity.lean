import FormalConjecturesUtil

/-!
# A finite signed-polymer positivity criterion

This file is independent of `Submission.Spec`. It proves a finite combinatorial
component useful for signed-activity expansions, not an embedding conjecture.

A catalogue `P : Finset (Finset α)` specifies the allowed polymers. A family is
another finite set of polymers; it is admissible in `W` if its members are
subsets of `W` and are pairwise disjoint. `partition w P W` is exactly the sum
of the products of activities over such families, including the empty family
with weight one. Uncovered vertices have weight one. The final specialization
uses the catalogue of **all** subsets of a finite vertex set with cardinality
at least two. No bound is imposed on positive activities.

The inverse power `(τ⁻¹) ^ (U.card - 1)` denotes `τ^{-(|U|-1)}`; all powers in
this file have natural-number exponents. The proof works for every real
`0 < τ ≤ 1` and uses only finite sums, finite products, and elementary order
inequalities.

Main declarations:
* `signed_partition_positivity`: the requested three quantitative inequalities.
* `Z_pos`: their strict-positivity corollary.
* `partition_vertex` and `partition_positive_expansion`: the exact combinatorial identities.
* `negative_ratios`: both negative-only deletion-ratio bounds on every subset.
* `signed_partition_lower_bound`: the stronger finite-catalogue/subset version.
-/

namespace SignedPartitionPositivity

open Finset

variable {α : Type*} [DecidableEq α]

/-- Pairwise disjoint polymers, each contained in the available vertex set. -/
def Admissible (W : Finset α) (F : Finset (Finset α)) : Prop :=
  (∀ U ∈ F, U ⊆ W) ∧
    ∀ U ∈ F, ∀ T ∈ F, U ≠ T → Disjoint U T

/-- A family contributes its product of activities if admissible, and zero otherwise. -/
noncomputable def familyWeight (w : Finset α → ℝ) (W : Finset α)
    (F : Finset (Finset α)) : ℝ := by
  classical
  exact if Admissible W F then ∏ U ∈ F, w U else 0

/-- The hard-core partition function for the finite catalogue `P` in `W`. -/
noncomputable def partition (w : Finset α → ℝ) (P : Finset (Finset α))
    (W : Finset α) : ℝ :=
  ∑ F ∈ P.powerset, familyWeight w W F

/-- Vertices left over after choosing a family. -/
def unused (W : Finset α) (F : Finset (Finset α)) : Finset α :=
  W \ F.biUnion id

omit [DecidableEq α] in
@[simp] theorem admissible_empty (W : Finset α) : Admissible W ∅ := by
  simp [Admissible]

omit [DecidableEq α] in
@[simp] theorem familyWeight_empty (w : Finset α → ℝ) (W : Finset α) :
    familyWeight w W ∅ = 1 := by
  simp [familyWeight]

omit [DecidableEq α] in
@[simp] theorem partition_empty_catalogue (w : Finset α → ℝ) (W : Finset α) :
    partition w ∅ W = 1 := by
  simp [partition]

@[simp] theorem unused_empty (W : Finset α) : unused W ∅ = W := by
  simp [unused]

omit [DecidableEq α] in
theorem admissible_mono {W R : Finset α} {F : Finset (Finset α)}
    (hWR : W ⊆ R) (hF : Admissible W F) : Admissible R F :=
  ⟨fun U hU ↦ (hF.1 U hU).trans hWR, hF.2⟩

/-- Inserting one polymer leaves exactly the vertices outside that polymer available. -/
theorem admissible_insert {W U : Finset α} {F : Finset (Finset α)}
    (hUF : U ∉ F) :
    Admissible W (insert U F) ↔ U ⊆ W ∧ Admissible (W \ U) F := by
  constructor
  · intro h
    refine ⟨h.1 U (mem_insert_self _ _), ?_, ?_⟩
    · intro T hT
      exact subset_sdiff.mpr ⟨h.1 T (mem_insert_of_mem hT),
        h.2 T (mem_insert_of_mem hT) U (mem_insert_self _ _)
          (by rintro rfl; exact hUF hT)⟩
    · intro T hT R hR hTR
      exact h.2 T (mem_insert_of_mem hT) R (mem_insert_of_mem hR) hTR
  · rintro ⟨hUW, hF⟩
    refine ⟨?_, ?_⟩
    · intro T hT
      rcases mem_insert.mp hT with rfl | hT
      · exact hUW
      · exact (hF.1 T hT).trans sdiff_subset
    · intro T hT R hR hTR
      rcases mem_insert.mp hT with hTU | hTF
      · subst T
        have hR' : R ∈ F := (mem_insert.mp hR).resolve_left (Ne.symm hTR)
        exact (subset_sdiff.mp (hF.1 R hR')).2.symm
      · rcases mem_insert.mp hR with hRU | hRF
        · rw [hRU]
          exact (subset_sdiff.mp (hF.1 T hTF)).2
        · exact hF.2 T hTF R hRF hTR

theorem familyWeight_insert (w : Finset α → ℝ) (W U : Finset α)
    (F : Finset (Finset α)) (hUF : U ∉ F) :
    familyWeight w W (insert U F) =
      if U ⊆ W then w U * familyWeight w (W \ U) F else 0 := by
  classical
  simp only [familyWeight, admissible_insert hUF, prod_insert hUF]
  by_cases hU : U ⊆ W <;> by_cases hF : Admissible (W \ U) F <;> simp [hU, hF]

/-- The elementary include/exclude recurrence for a single polymer. -/
theorem partition_insert (w : Finset α → ℝ) (P : Finset (Finset α))
    (W U : Finset α) (hUP : U ∉ P) :
    partition w (insert U P) W = partition w P W +
      if U ⊆ W then w U * partition w P (W \ U) else 0 := by
  classical
  rw [partition, sum_powerset_insert hUP]
  congr 1
  calc
    (∑ F ∈ P.powerset, familyWeight w W (insert U F)) =
        ∑ F ∈ P.powerset,
          if U ⊆ W then w U * familyWeight w (W \ U) F else 0 := by
      apply sum_congr rfl
      intro F hF
      exact familyWeight_insert w W U F (fun hUF ↦ hUP (mem_powerset.mp hF hUF))
    _ = _ := by by_cases h : U ⊆ W <;> simp [h, partition, mul_sum]

omit [DecidableEq α] in
/-- Activities only matter on the catalogue. -/
theorem partition_congr {w z : Finset α → ℝ} (P : Finset (Finset α))
    (W : Finset α) (h : ∀ U ∈ P, w U = z U) :
    partition w P W = partition z P W := by
  classical
  apply sum_congr rfl
  intro F hF
  unfold familyWeight
  split_ifs
  · exact prod_congr rfl (fun U hU ↦ h U (mem_powerset.mp hF hU))
  · rfl

omit [DecidableEq α] in
/-- Adding zero-activity polymers does not change the partition function. -/
theorem partition_subset_of_zero (w : Finset α → ℝ)
    {Q P : Finset (Finset α)} (W : Finset α) (hQP : Q ⊆ P)
    (hzero : ∀ U ∈ P, U ∉ Q → w U = 0) :
    partition w Q W = partition w P W := by
  classical
  apply sum_subset (powerset_mono.mpr hQP)
  intro F hFP hFQ
  have hn : ¬ F ⊆ Q := by simpa using hFQ
  obtain ⟨U, hUF, hUQ⟩ := not_subset.mp hn
  have hz : ∏ T ∈ F, w T = 0 :=
    prod_eq_zero hUF (hzero U (mem_powerset.mp hFP hUF) hUQ)
  simp [familyWeight, hz]

omit [DecidableEq α] in
/-- With no empty polymer, the empty vertex set has partition function one. -/
theorem partition_empty_vertices (w : Finset α → ℝ) (P : Finset (Finset α))
    (hne : ∀ U ∈ P, U.Nonempty) : partition w P ∅ = 1 := by
  classical
  unfold partition
  rw [sum_eq_single ∅]
  · exact familyWeight_empty w ∅
  · intro F hFP hF
    have hn : ¬ Admissible (∅ : Finset α) F := by
      intro h
      obtain ⟨U, hUF⟩ := Finset.nonempty_iff_ne_empty.mpr hF
      have hU := hne U (mem_powerset.mp hFP hUF)
      exact hU.ne_empty (subset_empty.mp (h.1 U hUF))
    simp [familyWeight, hn]
  · simp

/-- The sum over families marked by the presence of a prescribed polymer. -/
theorem partition_marked (w : Finset α → ℝ) (P : Finset (Finset α))
    (W U : Finset α) (hUP : U ∈ P) :
    (∑ F ∈ P.powerset, if U ∈ F then familyWeight w W F else 0) =
      if U ⊆ W then w U * partition w (P.erase U) (W \ U) else 0 := by
  classical
  conv_lhs => rw [← insert_erase hUP]
  rw [sum_powerset_insert (notMem_erase U P)]
  have hnot : ∀ F ∈ (P.erase U).powerset, U ∉ F := by
    intro F hF hUF
    exact notMem_erase U P (mem_powerset.mp hF hUF)
  simp only [mem_insert_self, ite_true]
  have hz : (∑ F ∈ (P.erase U).powerset,
      if U ∈ F then familyWeight w W F else 0) = 0 := by
    apply sum_eq_zero
    intro F hF
    simp [hnot F hF]
  rw [hz, zero_add]
  calc
    (∑ F ∈ (P.erase U).powerset, familyWeight w W (insert U F)) =
        ∑ F ∈ (P.erase U).powerset,
          if U ⊆ W then w U * familyWeight w (W \ U) F else 0 := by
      apply sum_congr rfl
      intro F hF
      exact familyWeight_insert w W U F (hnot F hF)
    _ = _ := by by_cases h : U ⊆ W <;> simp [h, partition, mul_sum]

/-- A nonempty polymer cannot be selected after its vertices have been removed. -/
theorem partition_erase_polymer (w : Finset α → ℝ) (P : Finset (Finset α))
    (W U : Finset α) (hUP : U ∈ P) (hne : U.Nonempty) :
    partition w P (W \ U) = partition w (P.erase U) (W \ U) := by
  have hn : ¬ U ⊆ W \ U := by
    intro h
    obtain ⟨v, hv⟩ := hne
    exact (mem_sdiff.mp (h hv)).2 hv
  conv_lhs => rw [← insert_erase hUP]
  rw [partition_insert w (P.erase U) (W \ U) U (notMem_erase U P)]
  simp [hn]

/-- At most one member of an admissible family can cover a given vertex. -/
theorem familyWeight_vertex (w : Finset α → ℝ) (P : Finset (Finset α))
    (W : Finset α) (v : α) (F : Finset (Finset α)) (hFP : F ⊆ P) :
    familyWeight w W F = familyWeight w (W.erase v) F +
      ∑ U ∈ P, if U ∈ F ∧ v ∈ U then familyWeight w W F else 0 := by
  classical
  by_cases hF : Admissible W F
  · by_cases hv : ∃ U ∈ F, v ∈ U
    · obtain ⟨U, hUF, hvU⟩ := hv
      have hn : ¬ Admissible (W.erase v) F := by
        intro h
        exact (mem_erase.mp (h.1 U hUF hvU)).1 rfl
      have hs : (∑ T ∈ P, if T ∈ F ∧ v ∈ T then familyWeight w W F else 0) =
          familyWeight w W F := by
        rw [sum_eq_single U]
        · simp [hUF, hvU]
        · intro T _ hTU
          have ht : ¬ (T ∈ F ∧ v ∈ T) := by
            rintro ⟨hTF, hvT⟩
            exact disjoint_left.mp (hF.2 T hTF U hUF hTU) hvT hvU
          simp [ht]
        · exact fun hUP ↦ (hUP (hFP hUF)).elim
      rw [hs]
      simp [familyWeight, hn]
    · have hv' : ∀ U ∈ F, v ∉ U := by simpa using hv
      have he : Admissible (W.erase v) F :=
        ⟨fun U hU ↦ subset_erase.mpr ⟨hF.1 U hU, hv' U hU⟩, hF.2⟩
      have hs : (∑ U ∈ P, if U ∈ F ∧ v ∈ U then familyWeight w W F else 0) = 0 := by
        apply sum_eq_zero
        intro U _
        have h : ¬ (U ∈ F ∧ v ∈ U) := fun h ↦ hv' U h.1 h.2
        simp [h]
      rw [hs]
      simp [familyWeight, hF, he]
  · have he : ¬ Admissible (W.erase v) F :=
      fun h ↦ hF (admissible_mono (erase_subset v W) h)
    simp [familyWeight, hF, he]

/-- The exact vertex recurrence, valid for arbitrary real activities. -/
theorem partition_vertex (w : Finset α → ℝ) (P : Finset (Finset α))
    (W : Finset α) (v : α) :
    partition w P W = partition w P (W.erase v) +
      ∑ U ∈ P.filter (fun U ↦ U ⊆ W ∧ v ∈ U), w U * partition w P (W \ U) := by
  classical
  calc
    partition w P W = ∑ F ∈ P.powerset,
        (familyWeight w (W.erase v) F +
          ∑ U ∈ P, if U ∈ F ∧ v ∈ U then familyWeight w W F else 0) := by
      apply sum_congr rfl
      intro F hF
      exact familyWeight_vertex w P W v F (mem_powerset.mp hF)
    _ = partition w P (W.erase v) +
        ∑ U ∈ P, ∑ F ∈ P.powerset,
          if U ∈ F ∧ v ∈ U then familyWeight w W F else 0 := by
      rw [sum_add_distrib, sum_comm]
      rfl
    _ = _ := by
      congr 1
      rw [sum_filter]
      apply sum_congr rfl
      intro U hUP
      by_cases hv : v ∈ U
      · simp only [hv, and_true]
        rw [partition_marked w P W U hUP]
        by_cases hUW : U ⊆ W
        · simp only [hUW, ite_true]
          rw [partition_erase_polymer w P W U hUP ⟨v, hv⟩]
        · simp [hUW]
      · simp [hv]

/-- Inserting a family member removes its vertices before the remaining family. -/
theorem unused_insert (W U : Finset α) (F : Finset (Finset α)) :
    unused W (insert U F) = unused (W \ U) F := by
  ext v
  simp [unused, and_assoc]

/-- Exact conditioning on a family from one of two disjoint catalogues. -/
theorem partition_union_expansion (w : Finset α → ℝ)
    (P Q : Finset (Finset α)) (W : Finset α) (hPQ : Disjoint P Q) :
    partition w (P ∪ Q) W =
      ∑ F ∈ P.powerset, familyWeight w W F * partition w Q (unused W F) := by
  classical
  induction P using Finset.induction_on generalizing W with
  | empty => simp
  | @insert U P hUP ih =>
    have hUQ : U ∉ Q := disjoint_left.mp hPQ (mem_insert_self _ _)
    have hPQ' : Disjoint P Q := hPQ.mono_left (subset_insert _ _)
    have hnot : U ∉ P ∪ Q := by simp [hUP, hUQ]
    rw [insert_union, partition_insert w (P ∪ Q) W U hnot,
      sum_powerset_insert hUP, ih W hPQ', ih (W \ U) hPQ']
    congr 1
    symm
    calc
      (∑ F ∈ P.powerset,
          familyWeight w W (insert U F) * partition w Q (unused W (insert U F))) =
          ∑ F ∈ P.powerset, if U ⊆ W then
            w U * (familyWeight w (W \ U) F * partition w Q (unused (W \ U) F))
            else 0 := by
        apply sum_congr rfl
        intro F hF
        rw [familyWeight_insert w W U F (fun hUF ↦ hUP (mem_powerset.mp hF hUF)),
          unused_insert]
        by_cases h : U ⊆ W <;> simp [h, mul_assoc]
      _ = _ := by by_cases h : U ⊆ W <;> simp [h, mul_sum]

/-- The magnitude of the negative part of an activity. -/
noncomputable def negativePart (w : Finset α → ℝ) (U : Finset α) : ℝ :=
  max (-w U) 0

/-- The positive part of an activity. -/
noncomputable def positivePart (w : Finset α → ℝ) (U : Finset α) : ℝ :=
  max (w U) 0

omit [DecidableEq α] in
theorem negativePart_nonneg (w : Finset α → ℝ) (U : Finset α) :
    0 ≤ negativePart w U := le_max_right _ _

omit [DecidableEq α] in
theorem positivePart_nonneg (w : Finset α → ℝ) (U : Finset α) :
    0 ≤ positivePart w U := le_max_right _ _

omit [DecidableEq α] in
/-- The positive partition function ignores every nonpositive-activity polymer. -/
theorem partition_positive_restriction (w : Finset α → ℝ)
    (P : Finset (Finset α)) (W : Finset α) :
    partition (positivePart w) P W =
      partition (positivePart w) (P.filter (fun U ↦ 0 < w U)) W := by
  classical
  symm
  apply partition_subset_of_zero _ W (filter_subset _ _)
  intro U hUP hU
  have hn : w U ≤ 0 := le_of_not_gt (fun h ↦ hU (mem_filter.mpr ⟨hUP, h⟩))
  exact max_eq_right hn

omit [DecidableEq α] in
/-- On the nonpositive catalogue, the signed activity is exactly minus its negative part. -/
theorem partition_negative_restriction (w : Finset α → ℝ)
    (P : Finset (Finset α)) (W : Finset α) :
    partition (fun U ↦ -negativePart w U) P W =
      partition w (P.filter (fun U ↦ ¬ 0 < w U)) W := by
  classical
  calc
    partition (fun U ↦ -negativePart w U) P W =
        partition (fun U ↦ -negativePart w U) (P.filter (fun U ↦ ¬ 0 < w U)) W := by
      symm
      apply partition_subset_of_zero _ W (filter_subset _ _)
      intro U hUP hU
      have hp : 0 < w U := by
        by_contra h
        exact hU (mem_filter.mpr ⟨hUP, h⟩)
      simp [negativePart, max_eq_right (neg_nonpos.mpr hp.le)]
    _ = _ := by
      apply partition_congr
      intro U hU
      have hn : w U ≤ 0 := le_of_not_gt (mem_filter.mp hU).2
      simp [negativePart, max_eq_left (neg_nonneg.mpr hn)]

/--
The full positive-background expansion. The sum runs over positive-polymer
families; its remaining factor is the negative-only partition function on the
unused vertices. Inadmissible families contribute zero. This is an identity,
not an additional assumption of the positivity theorem.
-/
theorem partition_positive_expansion (w : Finset α → ℝ)
    (P : Finset (Finset α)) (W : Finset α) :
    partition w P W =
      ∑ F ∈ (P.filter (fun U ↦ 0 < w U)).powerset,
        familyWeight (positivePart w) W F *
          partition (fun U ↦ -negativePart w U) P (unused W F) := by
  classical
  let Pp := P.filter (fun U ↦ 0 < w U)
  let Pn := P.filter (fun U ↦ ¬ 0 < w U)
  have hu : Pp ∪ Pn = P := filter_union_filter_not_eq _ _
  have hd : Disjoint Pp Pn := disjoint_filter_filter_not _ _ _
  calc
    partition w P W = partition w (Pp ∪ Pn) W := by rw [hu]
    _ = ∑ F ∈ Pp.powerset, familyWeight w W F * partition w Pn (unused W F) :=
      partition_union_expansion w Pp Pn W hd
    _ = _ := by
      apply sum_congr rfl
      intro F hF
      rw [partition_negative_restriction]
      congr 1
      unfold familyWeight
      split_ifs
      · apply prod_congr rfl
        intro U hUF
        have hp : 0 < w U := (mem_filter.mp (mem_powerset.mp hF hUF)).2
        exact (max_eq_left hp.le).symm
      · rfl

omit [DecidableEq α] in
/-- Products of nonnegative activities have nonnegative family weights. -/
theorem familyWeight_nonneg (w : Finset α → ℝ) (W : Finset α)
    (F : Finset (Finset α)) (hw : ∀ U ∈ F, 0 ≤ w U) :
    0 ≤ familyWeight w W F := by
  classical
  unfold familyWeight
  split_ifs
  · exact prod_nonneg hw
  · exact le_rfl

omit [DecidableEq α] in
/-- The empty family alone contributes one for nonnegative activities. -/
theorem one_le_partition (w : Finset α → ℝ) (P : Finset (Finset α))
    (W : Finset α) (hw : ∀ U ∈ P, 0 ≤ w U) : 1 ≤ partition w P W := by
  classical
  calc
    1 = familyWeight w W ∅ := (familyWeight_empty w W).symm
    _ ≤ partition w P W := single_le_sum
      (fun F hF ↦ familyWeight_nonneg w W F (fun U hU ↦ hw U (mem_powerset.mp hF hU)))
      (empty_mem_powerset P)

/-- Iterating one-vertex lower ratios over an arbitrary set of deleted vertices. -/
theorem iterate_deletion_bound (τ : ℝ) (f : Finset α → ℝ) (R : Finset α)
    (hτ : 0 ≤ τ)
    (hratio : ∀ S ⊆ R, ∀ v ∈ S, τ * f (S.erase v) ≤ f S)
    (D : Finset α) (hDR : D ⊆ R) :
    τ ^ D.card * f (R \ D) ≤ f R := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert v D hvD ih =>
    have hD : D ⊆ R := (subset_insert _ _).trans hDR
    have hv : v ∈ R \ D := mem_sdiff.mpr ⟨hDR (mem_insert_self _ _), hvD⟩
    have he : R \ insert v D = (R \ D).erase v := by
      ext x
      simp [and_left_comm]
    rw [card_insert_of_notMem hvD, pow_succ, he]
    calc
      (τ ^ D.card * τ) * f ((R \ D).erase v) =
          τ ^ D.card * (τ * f ((R \ D).erase v)) := mul_assoc _ _ _
      _ ≤ τ ^ D.card * f (R \ D) :=
        mul_le_mul_of_nonneg_left (hratio _ sdiff_subset v hv) (pow_nonneg hτ _)
      _ ≤ f R := ih hD

/-- The vertex recurrence with nonpositive activities, in subtraction form. -/
theorem partition_negative_vertex (a : Finset α → ℝ) (P : Finset (Finset α))
    (W : Finset α) (v : α) :
    partition (fun U ↦ -a U) P W = partition (fun U ↦ -a U) P (W.erase v) -
      ∑ U ∈ P.filter (fun U ↦ U ⊆ W ∧ v ∈ U),
        a U * partition (fun T ↦ -a T) P (W \ U) := by
  rw [partition_vertex (fun U ↦ -a U) P W v]
  simp only [neg_mul, sum_neg_distrib, sub_eq_add_neg]

/--
Negative-only positivity and the two one-vertex ratio bounds, written without
division. The load condition is inherited by every subset of `V`.

The strong induction proves positivity and ratios together. For a polymer
`U` containing `v`, the already-proved ratios on proper subsets are iterated
over `U.erase v`, giving the factor `(τ⁻¹)^(U.card - 1)`.
-/
theorem negative_ratio_bounds (a : Finset α → ℝ) (P : Finset (Finset α))
    (V : Finset α) (τ : ℝ) (hτ : 0 < τ)
    (hne : ∀ U ∈ P, U.Nonempty) (ha : ∀ U ∈ P, 0 ≤ a U)
    (hload : ∀ v ∈ V,
      (∑ U ∈ P.filter (fun U ↦ v ∈ U), a U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ)
    (W : Finset α) (hWV : W ⊆ V) :
    0 < partition (fun U ↦ -a U) P W ∧
      ∀ v ∈ W,
        τ * partition (fun U ↦ -a U) P (W.erase v) ≤ partition (fun U ↦ -a U) P W ∧
        partition (fun U ↦ -a U) P W ≤ partition (fun U ↦ -a U) P (W.erase v) := by
  classical
  revert hWV
  refine Finset.strongInductionOn W ?_
  intro W ih hWV
  let z : Finset α → ℝ := partition (fun U ↦ -a U) P
  have hrat : ∀ v ∈ W, τ * z (W.erase v) ≤ z W ∧ z W ≤ z (W.erase v) := by
    intro v hvW
    have heV : W.erase v ⊆ V := (erase_subset v W).trans hWV
    have hep : 0 < z (W.erase v) := (ih _ (erase_ssubset hvW) heV).1
    let C := P.filter (fun U ↦ U ⊆ W ∧ v ∈ U)
    have hsmall : ∀ U ∈ C, W \ U ⊂ W := by
      intro U hU
      exact sdiff_ssubset (mem_filter.mp hU).2.1 ⟨v, (mem_filter.mp hU).2.2⟩
    have hzsmall : ∀ U ∈ C, 0 ≤ z (W \ U) := by
      intro U hU
      exact (ih _ (hsmall U hU) (sdiff_subset.trans hWV)).1.le
    have hlocal : ∀ S ⊆ W.erase v, ∀ x ∈ S, τ * z (S.erase x) ≤ z S := by
      intro S hS x hx
      exact ((ih S (Finset.ssubset_of_subset_of_ssubset hS (erase_ssubset hvW))
        (hS.trans heV)).2 x hx).1
    have hpoly : ∀ U ∈ C,
        z (W \ U) ≤ (τ⁻¹) ^ (U.card - 1) * z (W.erase v) := by
      intro U hU
      have hUW : U ⊆ W := (mem_filter.mp hU).2.1
      have hvU : v ∈ U := (mem_filter.mp hU).2.2
      have hi := iterate_deletion_bound τ z (W.erase v) hτ.le hlocal
        (U.erase v) (erase_subset_erase v hUW)
      have he : (W.erase v) \ (U.erase v) = W \ U := by
        ext x
        by_cases hx : x = v <;> simp [hx, hvU]
      rw [card_erase_of_mem hvU, he] at hi
      have hb : z (W \ U) ≤ z (W.erase v) / τ ^ (U.card - 1) :=
        (le_div_iff₀ (pow_pos hτ _)).mpr (by simpa [mul_comm] using hi)
      simpa [div_eq_mul_inv, inv_pow, mul_comm] using hb
    have hC : C ⊆ P.filter (fun U ↦ v ∈ U) := by
      intro U hU
      exact mem_filter.mpr ⟨(mem_filter.mp hU).1, (mem_filter.mp hU).2.2⟩
    have hload' : (∑ U ∈ C, a U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ := by
      apply le_trans (sum_le_sum_of_subset_of_nonneg hC ?_) (hload v (hWV hvW))
      intro U hU _
      exact mul_nonneg (ha U (mem_filter.mp hU).1) (pow_nonneg (inv_nonneg.mpr hτ.le) _)
    have hs : (∑ U ∈ C, a U * z (W \ U)) ≤ (1 - τ) * z (W.erase v) := by
      calc
        (∑ U ∈ C, a U * z (W \ U)) ≤
            ∑ U ∈ C, a U * ((τ⁻¹) ^ (U.card - 1) * z (W.erase v)) := by
          apply sum_le_sum
          intro U hU
          exact mul_le_mul_of_nonneg_left (hpoly U hU) (ha U (mem_filter.mp hU).1)
        _ = (∑ U ∈ C, a U * (τ⁻¹) ^ (U.card - 1)) * z (W.erase v) := by
          simp only [sum_mul, mul_assoc]
        _ ≤ (1 - τ) * z (W.erase v) := mul_le_mul_of_nonneg_right hload' hep.le
    have hs0 : 0 ≤ ∑ U ∈ C, a U * z (W \ U) := by
      apply sum_nonneg
      intro U hU
      exact mul_nonneg (ha U (mem_filter.mp hU).1) (hzsmall U hU)
    have heq : z W = z (W.erase v) - ∑ U ∈ C, a U * z (W \ U) :=
      partition_negative_vertex a P W v
    constructor <;> nlinarith only [heq, hs, hs0]
  refine ⟨?_, hrat⟩
  by_cases hW : W = ∅
  · subst W
    rw [partition_empty_vertices _ P hne]
    exact zero_lt_one
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    have hp : 0 < z (W.erase v) :=
      (ih _ (erase_ssubset hv) ((erase_subset v W).trans hWV)).1
    exact lt_of_lt_of_le (mul_pos hτ hp) (hrat v hv).1

/-- The negative-only partition function is bounded below by `τ` to the volume. -/
theorem negative_power_lower_bound (a : Finset α → ℝ) (P : Finset (Finset α))
    (V : Finset α) (τ : ℝ) (hτ : 0 < τ)
    (hne : ∀ U ∈ P, U.Nonempty) (ha : ∀ U ∈ P, 0 ≤ a U)
    (hload : ∀ v ∈ V,
      (∑ U ∈ P.filter (fun U ↦ v ∈ U), a U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ)
    (W : Finset α) (hWV : W ⊆ V) :
    τ ^ W.card ≤ partition (fun U ↦ -a U) P W := by
  have hi := iterate_deletion_bound τ (partition (fun U ↦ -a U) P) W hτ.le
    (fun S hS v hv ↦
      ((negative_ratio_bounds a P V τ hτ hne ha hload S (hS.trans hWV)).2 v hv).1)
    W Subset.rfl
  simpa [partition_empty_vertices _ P hne] using hi

/-- The division form of the negative-only one-vertex bounds. -/
theorem negative_ratios (a : Finset α → ℝ) (P : Finset (Finset α))
    (V : Finset α) (τ : ℝ) (hτ : 0 < τ)
    (hne : ∀ U ∈ P, U.Nonempty) (ha : ∀ U ∈ P, 0 ≤ a U)
    (hload : ∀ v ∈ V,
      (∑ U ∈ P.filter (fun U ↦ v ∈ U), a U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ)
    (W : Finset α) (hWV : W ⊆ V) (v : α) (hv : v ∈ W) :
    τ ≤ partition (fun U ↦ -a U) P W / partition (fun U ↦ -a U) P (W.erase v) ∧
      partition (fun U ↦ -a U) P W / partition (fun U ↦ -a U) P (W.erase v) ≤ 1 := by
  have hp := (negative_ratio_bounds a P V τ hτ hne ha hload
    (W.erase v) ((erase_subset v W).trans hWV)).1
  have hb := (negative_ratio_bounds a P V τ hτ hne ha hload W hWV).2 v hv
  exact ⟨(le_div_iff₀ hp).mpr hb.1, (div_le_iff₀ hp).mpr (by simpa using hb.2)⟩

/--
The signed comparison for any finite catalogue of nonempty polymers, uniformly
on subsets `W ⊆ V`. Positive activities are unrestricted. Each coefficient in
the positive-background expansion is nonnegative, and its unused-vertex
factor is at least `τ ^ W.card`.
-/
theorem signed_partition_lower_bound (w : Finset α → ℝ) (P : Finset (Finset α))
    (V : Finset α) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hne : ∀ U ∈ P, U.Nonempty)
    (hload : ∀ v ∈ V,
      (∑ U ∈ P.filter (fun U ↦ v ∈ U),
        negativePart w U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ)
    (W : Finset α) (hWV : W ⊆ V) :
    τ ^ W.card * partition (positivePart w) P W ≤ partition w P W := by
  classical
  calc
    τ ^ W.card * partition (positivePart w) P W =
        ∑ F ∈ (P.filter (fun U ↦ 0 < w U)).powerset,
          τ ^ W.card * familyWeight (positivePart w) W F := by
      rw [partition_positive_restriction, partition, mul_sum]
    _ ≤ ∑ F ∈ (P.filter (fun U ↦ 0 < w U)).powerset,
        familyWeight (positivePart w) W F *
          partition (fun U ↦ -negativePart w U) P (unused W F) := by
      apply sum_le_sum
      intro F _
      have hrem : unused W F ⊆ W := sdiff_subset
      have hvol : τ ^ W.card ≤ τ ^ (unused W F).card :=
        pow_le_pow_of_le_one hτ.le hτ1 (card_le_card hrem)
      have hz := negative_power_lower_bound (negativePart w) P V τ hτ hne
        (fun U _ ↦ negativePart_nonneg w U) hload (unused W F) (hrem.trans hWV)
      have hw := familyWeight_nonneg (positivePart w) W F
        (fun U _ ↦ positivePart_nonneg w U)
      rw [mul_comm (τ ^ W.card)]
      exact mul_le_mul_of_nonneg_left (hvol.trans hz) hw
    _ = partition w P W := (partition_positive_expansion w P W).symm

/-- All polymers of size at least two inside the finite vertex set `V`. -/
def polymers (V : Finset α) : Finset (Finset α) :=
  V.powerset.filter (fun U ↦ 2 ≤ U.card)

omit [DecidableEq α] in
@[simp] theorem mem_polymers (V U : Finset α) :
    U ∈ polymers V ↔ U ⊆ V ∧ 2 ≤ U.card := by
  simp [polymers]

omit [DecidableEq α] in
theorem polymers_nonempty (V : Finset α) : ∀ U ∈ polymers V, U.Nonempty := by
  intro U hU
  apply card_pos.mp
  have h := (mem_polymers V U).mp hU
  omega

/--
`Z w W` is the sum over all pairwise disjoint families of subsets of `W` of
size at least two, with summand the product of their real activities. The
empty family contributes one; vertices not in any selected polymer are free.
-/
noncomputable def Z (w : Finset α → ℝ) (W : Finset α) : ℝ :=
  partition w (polymers W) W

/--
**Finite signed-polymer positivity criterion.** Set `a U = max (-w U) 0` and
`w₊ U = max (w U) 0`. If `0 < τ ≤ 1` and for each `v ∈ V`

`∑ U ⊆ V, |U| ≥ 2, v ∈ U, a U * (τ⁻¹)^(|U|-1) ≤ 1 - τ`,

then `Z(w;V) ≥ τ^|V| Z(w₊;V) ≥ τ^|V| > 0`. These are exactly the three
conjuncts below (written in Lean's increasing-order convention). In particular,
the hypotheses control only negative activities, not the positive background.
-/
theorem signed_partition_positivity (V : Finset α) (w : Finset α → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hload : ∀ v ∈ V,
      (∑ U ∈ (polymers V).filter (fun U ↦ v ∈ U),
        negativePart w U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ) :
    τ ^ V.card * Z (positivePart w) V ≤ Z w V ∧
      τ ^ V.card ≤ τ ^ V.card * Z (positivePart w) V ∧
      0 < τ ^ V.card := by
  refine ⟨signed_partition_lower_bound w (polymers V) V τ hτ hτ1
    (polymers_nonempty V) hload V Subset.rfl, ?_, pow_pos hτ _⟩
  have hp : 1 ≤ Z (positivePart w) V :=
    one_le_partition _ _ _ (fun U _ ↦ positivePart_nonneg w U)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (pow_nonneg hτ.le V.card)

/-- Strict positivity, as an immediately usable corollary of the quantitative bound. -/
theorem Z_pos (V : Finset α) (w : Finset α → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hload : ∀ v ∈ V,
      (∑ U ∈ (polymers V).filter (fun U ↦ v ∈ U),
        negativePart w U * (τ⁻¹) ^ (U.card - 1)) ≤ 1 - τ) : 0 < Z w V := by
  have h := signed_partition_positivity V w τ hτ hτ1 hload
  exact lt_of_lt_of_le h.2.2 (h.2.1.trans h.1)

end SignedPartitionPositivity

-- Kernel axiom audits of the combinatorial identities and principal estimates.
#print axioms SignedPartitionPositivity.partition_vertex
#print axioms SignedPartitionPositivity.partition_negative_vertex
#print axioms SignedPartitionPositivity.partition_positive_expansion
#print axioms SignedPartitionPositivity.negative_ratio_bounds
#print axioms SignedPartitionPositivity.negative_ratios
#print axioms SignedPartitionPositivity.negative_power_lower_bound
#print axioms SignedPartitionPositivity.signed_partition_lower_bound
#print axioms SignedPartitionPositivity.signed_partition_positivity
#print axioms SignedPartitionPositivity.Z_pos
