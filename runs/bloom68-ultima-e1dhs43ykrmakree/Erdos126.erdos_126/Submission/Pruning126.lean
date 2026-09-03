import FormalConjecturesUtil
import Submission.Model126
import Submission.LogKernel126

/-!
# Finite laminar pruning for Erdős problem 126

A zero-sum energy bound for a nonnegative laminar kernel gives a constant
baseline outside a small exceptional set, up to an error of `2 * M / t`.
The symmetric bad sets consist of pairs in nodes of cardinality less than `t`.
All estimates concern the unsigned kernel.
-/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

namespace Pruning126

/-- Nodes through a common point are ordered by their cardinalities. -/
lemma subset_of_common_point (W : LaminarFamily ι) {B C : Finset ι}
    (hB : B ∈ W.nodes) (hC : C ∈ W.nodes) {i : ι}
    (hiB : i ∈ B) (hiC : i ∈ C) (hcard : B.card ≤ C.card) : B ⊆ C := by
  rcases W.laminar B hB C hC with hBC | hCB | hd
  · exact hBC
  · have heq : C = B := Finset.eq_of_subset_of_card_le hCB hcard
    rw [heq]
  · exact (Finset.disjoint_left.mp hd hiB hiC).elim

variable [Fintype ι]

/-- The bad relation includes every pair in a small node, including its diagonal. -/
def smallNeighbours (W : LaminarFamily ι) (t : ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => ∃ B ∈ W.nodes, B.card < t ∧ i ∈ B ∧ j ∈ B)

@[simp] lemma mem_smallNeighbours (W : LaminarFamily ι) (t : ℕ) (i j : ι) :
    j ∈ smallNeighbours W t i ↔ ∃ B ∈ W.nodes, B.card < t ∧ i ∈ B ∧ j ∈ B := by
  simp [smallNeighbours]

lemma smallNeighbours_symm (W : LaminarFamily ι) (t : ℕ) (i j : ι) :
    j ∈ smallNeighbours W t i ↔ i ∈ smallNeighbours W t j := by
  simp only [mem_smallNeighbours]
  constructor <;> rintro ⟨B, hB, hcard, hi, hj⟩
  · exact ⟨B, hB, hcard, hj, hi⟩
  · exact ⟨B, hB, hcard, hj, hi⟩

/-- All small nodes through a point lie in the largest such node. -/
lemma smallNeighbours_card_le (W : LaminarFamily ι) (t : ℕ) (i : ι) :
    (smallNeighbours W t i).card ≤ t := by
  let S := W.nodes.filter (fun B => B.card < t ∧ i ∈ B)
  by_cases hS : S.Nonempty
  · obtain ⟨B, hB, hmax⟩ := S.exists_max_image Finset.card hS
    obtain ⟨hBW, hBt, hiB⟩ := Finset.mem_filter.mp hB
    have hsub : smallNeighbours W t i ⊆ B := by
      intro j hj
      obtain ⟨C, hCW, hCt, hiC, hjC⟩ := (mem_smallNeighbours W t i j).mp hj
      have hCS : C ∈ S := Finset.mem_filter.mpr ⟨hCW, hCt, hiC⟩
      exact subset_of_common_point W hCW hBW hiC hiB (hmax C hCS) hjC
    exact (Finset.card_le_card hsub).trans hBt.le
  · have hempty : smallNeighbours W t i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨B, hBW, hBt, hiB, _⟩ := (mem_smallNeighbours W t i j).mp hj
      exact hS ⟨B, Finset.mem_filter.mpr ⟨hBW, hBt, hiB⟩⟩
    simp [hempty]

lemma sum_ind (B : Finset ι) : (∑ i, ind B i) = (B.card : ℝ) := by
  simp [ind]

/-- A normalized difference of indicators on two disjoint supports. -/
def contrast (C D : Finset ι) (i : ι) : ℝ :=
  ind C i / (C.card : ℝ) - ind D i / (D.card : ℝ)

lemma contrast_sum_zero {C D : Finset ι} (hC : 0 < C.card) (hD : 0 < D.card) :
    (∑ i, contrast C D i) = 0 := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hd : (D.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  simp only [contrast, Finset.sum_sub_distrib, ← Finset.sum_div, sum_ind,
    div_self hc, div_self hd, sub_self]

lemma contrast_norm_sq {C D : Finset ι} (hC : 0 < C.card) (hD : 0 < D.card)
    (hCD : Disjoint C D) :
    (∑ i, contrast C D i ^ 2) = 1 / (C.card : ℝ) + 1 / (D.card : ℝ) := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hd : (D.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hpoint : ∀ i, contrast C D i ^ 2 =
      ind C i / (C.card : ℝ) ^ 2 + ind D i / (D.card : ℝ) ^ 2 := by
    intro i
    by_cases hiC : i ∈ C
    · have hiD : i ∉ D := fun hiD => Finset.disjoint_left.mp hCD hiC hiD
      simp [contrast, ind, hiC, hiD]
    · by_cases hiD : i ∈ D <;> simp [contrast, ind, hiC, hiD]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, sum_ind, sum_ind]
  field_simp

/-- Every node separating the positive support from the negative support has dot product one. -/
lemma contrast_dot_one {C D A : Finset ι} (hC : 0 < C.card)
    (hCA : C ⊆ A) (hDA : Disjoint D A) :
    (∑ i, contrast C D i * ind A i) = 1 := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hpoint : ∀ i, contrast C D i * ind A i = ind C i / (C.card : ℝ) := by
    intro i
    by_cases hiA : i ∈ A
    · have hiD : i ∉ D := fun hiD => Finset.disjoint_left.mp hDA hiD hiA
      simp [contrast, ind, hiA, hiD]
    · have hiC : i ∉ C := fun hiC => hiA (hCA hiC)
      simp [contrast, ind, hiA, hiC]
  simp_rw [hpoint]
  rw [← Finset.sum_div, sum_ind, div_self hc]

/-- The energy expansion uses every original node, not just a selected chain. -/
lemma kernel_sum_squares (W : LaminarFamily ι) (q : ι → ℝ) :
    quad W.kernel q = ∑ B ∈ W.nodes, W.weight B * (∑ i, q i * ind B i) ^ 2 := by
  simpa only [quad, LaminarFamily.kernel, mul_assoc] using
    LogKernel.weighted_feature_sum W.nodes W.weight ind q

/-- The weights of a chain between `C` and `D` are bounded by a zero-sum test.
Only the two support cardinalities and the interval containments are needed. -/
lemma chain_weight_le (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    {t : ℕ} (ht : 0 < t) {C D : Finset ι} {S : Finset (Finset ι)}
    (hS : S ⊆ W.nodes) (hCD : C ⊆ D) (hCt : t ≤ C.card) (hDt : t ≤ Dᶜ.card)
    (hchain : ∀ A ∈ S, C ⊆ A ∧ A ⊆ D) :
    (∑ A ∈ S, W.weight A) ≤ 2 * M / (t : ℝ) := by
  have hC : 0 < C.card := ht.trans_le hCt
  have hD : 0 < Dᶜ.card := ht.trans_le hDt
  have hdis : Disjoint C Dᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiC hiD
    exact (Finset.mem_compl.mp hiD) (hCD hiC)
  let q := contrast C Dᶜ
  have hzero : (∑ i, q i) = 0 := contrast_sum_zero hC hD
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hnorm : (∑ i, q i ^ 2) ≤ 2 / (t : ℝ) := by
    rw [show (∑ i, q i ^ 2) = 1 / (C.card : ℝ) + 1 / (Dᶜ.card : ℝ) from
      contrast_norm_sq hC hD hdis]
    calc
      _ ≤ 1 / (t : ℝ) + 1 / (t : ℝ) := add_le_add
        (one_div_le_one_div_of_le htR (Nat.cast_le.mpr hCt))
        (one_div_le_one_div_of_le htR (Nat.cast_le.mpr hDt))
      _ = _ := by ring
  have hdot : ∀ A ∈ S, (∑ i, q i * ind A i) = 1 := by
    intro A hA
    obtain ⟨hCA, hAD⟩ := hchain A hA
    apply contrast_dot_one hC hCA
    apply Finset.disjoint_left.mpr
    intro i hiD hiA
    exact (Finset.mem_compl.mp hiD) (hAD hiA)
  calc
    (∑ A ∈ S, W.weight A) = ∑ A ∈ S, W.weight A * (∑ i, q i * ind A i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hdot A hA]
      ring
    _ ≤ ∑ A ∈ W.nodes, W.weight A * (∑ i, q i * ind A i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun A hA _ => mul_nonneg (W.weight_nonneg A hA) (sq_nonneg _))
    _ = quad W.kernel q := (kernel_sum_squares W q).symm
    _ ≤ M * ∑ i, q i ^ 2 := henergy q hzero
    _ ≤ M * (2 / (t : ℝ)) := mul_le_mul_of_nonneg_left hnorm hM
    _ = 2 * M / (t : ℝ) := by ring

/-- The common nodes left after removing all almost-full nodes. -/
def residualNodes (W : LaminarFamily ι) (t : ℕ) (i j : ι) : Finset (Finset ι) :=
  W.nodes.filter (fun B => B.card ≤ Fintype.card ι - t ∧ i ∈ B ∧ j ∈ B)

/-- A nonbad pair has small residual common depth. The extremal common nodes
supply the two supports for the normalized contrast. -/
lemma residual_weight_le (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    {t : ℕ} (ht : 0 < t) (hnt : t ≤ Fintype.card ι) (i j : ι)
    (hbad : j ∉ smallNeighbours W t i) :
    (∑ B ∈ residualNodes W t i j, W.weight B) ≤ 2 * M / (t : ℝ) := by
  let S := residualNodes W t i j
  change (∑ B ∈ S, W.weight B) ≤ 2 * M / (t : ℝ)
  by_cases hS : S.Nonempty
  · obtain ⟨C, hCS, hmin⟩ := S.exists_min_image Finset.card hS
    obtain ⟨D, hDS, hmax⟩ := S.exists_max_image Finset.card hS
    obtain ⟨hCW, _, hiC, hjC⟩ := Finset.mem_filter.mp hCS
    obtain ⟨hDW, hDt, hiD, _⟩ := Finset.mem_filter.mp hDS
    have hCt : t ≤ C.card := by
      by_contra hc
      apply hbad
      exact (mem_smallNeighbours W t i j).mpr ⟨C, hCW, by omega, hiC, hjC⟩
    have hDcompl : t ≤ Dᶜ.card := by
      rw [Finset.card_compl]
      omega
    have hCD : C ⊆ D := subset_of_common_point W hCW hDW hiC hiD (hmin D hDS)
    apply chain_weight_le W hM henergy ht
      (show S ⊆ W.nodes from Finset.filter_subset _ _) hCD hCt hDcompl
    intro A hAS
    obtain ⟨hAW, _, hiA, _⟩ := Finset.mem_filter.mp hAS
    exact ⟨subset_of_common_point W hCW hAW hiC hiA (hmin A hAS),
      subset_of_common_point W hAW hDW hiA hiD (hmax A hAS)⟩
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hM) (Nat.cast_nonneg t)

/-- The common contribution of all nodes of size greater than `n - t`. -/
def baseline (W : LaminarFamily ι) (t : ℕ) : ℝ :=
  ∑ B ∈ W.nodes.filter (fun B => Fintype.card ι - t < B.card), W.weight B

lemma baseline_nonneg (W : LaminarFamily ι) (t : ℕ) : 0 ≤ baseline W t := by
  apply Finset.sum_nonneg
  intro B hB
  exact W.weight_nonneg B (Finset.mem_filter.mp hB).1

/-- Almost-full nodes form a chain. The complement of its smallest member
has cardinality less than `t` and is the only exceptional set needed. -/
lemma exists_exceptional (W : LaminarFamily ι) {t : ℕ} (ht : 0 < t)
    (hnt : 2 * t < Fintype.card ι) :
    ∃ Z : Finset ι, Z.card < t ∧
      ∀ B ∈ W.nodes, Fintype.card ι - t < B.card → ∀ i, i ∉ Z → i ∈ B := by
  let S := W.nodes.filter (fun B => Fintype.card ι - t < B.card)
  by_cases hS : S.Nonempty
  · obtain ⟨B, hBS, hmin⟩ := S.exists_min_image Finset.card hS
    obtain ⟨hBW, hBt⟩ := Finset.mem_filter.mp hBS
    refine ⟨Bᶜ, ?_, ?_⟩
    · rw [Finset.card_compl]
      omega
    · intro A hAW hAt i hi
      have hiB : i ∈ B := by simpa only [Finset.mem_compl, not_not] using hi
      have hAS : A ∈ S := Finset.mem_filter.mpr ⟨hAW, hAt⟩
      have hsub : B ⊆ A := by
        rcases W.laminar B hBW A hAW with hBA | hAB | hd
        · exact hBA
        · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (hmin A hAS)
          rw [heq]
        · have hunion := Finset.card_le_univ (B ∪ A)
          rw [Finset.card_union_of_disjoint hd] at hunion
          omega
      exact hsub hiB
  · refine ⟨∅, by simpa using ht, ?_⟩
    intro B hBW hBt i _
    exact (hS ⟨B, Finset.mem_filter.mpr ⟨hBW, hBt⟩⟩).elim

/-- Outside the exceptional set the almost-full nodes contribute exactly the baseline. -/
lemma kernel_eq_baseline_add (W : LaminarFamily ι) (t : ℕ) (i j : ι)
    (hlarge : ∀ B ∈ W.nodes, Fintype.card ι - t < B.card → i ∈ B ∧ j ∈ B) :
    W.kernel i j = baseline W t + ∑ B ∈ residualNodes W t i j, W.weight B := by
  unfold LaminarFamily.kernel baseline residualNodes
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hBt : Fintype.card ι - t < B.card
  · obtain ⟨hiB, hjB⟩ := hlarge B hB hBt
    have hBt' : ¬B.card ≤ Fintype.card ι - t := by omega
    simp [hBt, hBt', ind, hiB, hjB]
  · have hBt' : B.card ≤ Fintype.card ι - t := by omega
    by_cases hiB : i ∈ B <;> by_cases hjB : j ∈ B <;>
      simp [hBt, hBt', ind, hiB, hjB]

end Pruning126

variable [Fintype ι]

/-- Finite laminar pruning from a zero-sum energy bound.

The bad relation is symmetric and includes every pair sharing a node smaller
than `t`. After deleting at most `t` points, all other off-diagonal entries
lie in the interval `[β, β + 2 * M / t]`, with a nonnegative common baseline.
No assertion about signed kernels is used or needed. -/
theorem LaminarFamily.pruning (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    (t : ℕ) (ht : 2 ≤ t) (hnt : 2 * t < Fintype.card ι) :
    ∃ (Z : Finset ι) (β : ℝ) (bad : ι → Finset ι),
      Z.card ≤ t ∧ 0 ≤ β ∧ (∀ i, (bad i).card ≤ t) ∧
      (∀ i j, j ∈ bad i ↔ i ∈ bad j) ∧
      ∀ i j, i ≠ j → i ∉ Z → j ∉ Z → j ∉ bad i →
        β ≤ W.kernel i j ∧ W.kernel i j ≤ β + 2 * M / (t : ℝ) := by
  have htpos : 0 < t := by omega
  obtain ⟨Z, hZ, hlarge⟩ := Pruning126.exists_exceptional W htpos hnt
  refine ⟨Z, Pruning126.baseline W t, Pruning126.smallNeighbours W t,
    hZ.le, Pruning126.baseline_nonneg W t, Pruning126.smallNeighbours_card_le W t,
    Pruning126.smallNeighbours_symm W t, ?_⟩
  intro i j _hij hi hj hbad
  have heq := Pruning126.kernel_eq_baseline_add W t i j
    (fun B hB hBt => ⟨hlarge B hB hBt i hi, hlarge B hB hBt j hj⟩)
  rw [heq]
  constructor
  · apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro B hB
    exact W.weight_nonneg B (Finset.mem_filter.mp hB).1
  · exact add_le_add le_rfl
      (Pruning126.residual_weight_le W hM henergy htpos (by omega) i j hbad)

end
end E126
