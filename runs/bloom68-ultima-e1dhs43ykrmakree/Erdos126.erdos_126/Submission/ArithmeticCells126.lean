import FormalConjecturesUtil
import Submission.Model126

/-!
# Finite opposition families from refining partitions

At each level we retain the bichromatic classes of a partition.  Repeated
supports are compressed by adding their weights, not by deleting occurrences.
This module is independent of the arithmetic used to supply the labels.
-/

open scoped BigOperators

namespace E126.ArithmeticCells126

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- A class of the partition at level `n`. -/
def cell (f : ℕ → ι → κ) (n : ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => f n j = f n i)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (f : ℕ → ι → κ) (n : ℕ) (i j : ι) :
    j ∈ cell f n i ↔ f n j = f n i := by
  simp [cell]

omit [DecidableEq ι] in
@[simp] theorem self_mem_cell (f : ℕ → ι → κ) (n : ℕ) (i : ι) :
    i ∈ cell f n i := by simp

omit [DecidableEq ι] in
lemma cell_eq_of_mem {f : ℕ → ι → κ} {n : ℕ} {i j : ι}
    (h : j ∈ cell f n i) : cell f n j = cell f n i := by
  have he := (mem_cell f n i j).mp h
  ext k
  simp [he]

/-- Activity means that both global colors occur. -/
def Active (σ : ι → Bool) (B : Finset ι) : Prop :=
  ∃ i ∈ B, ∃ j ∈ B, σ i ≠ σ j

instance activeDecidable (σ : ι → Bool) (B : Finset ι) : Decidable (Active σ B) := by
  unfold Active
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
lemma active_bichromatic {σ : ι → Bool} {B : Finset ι} (h : Active σ B)
    {i : ι} (_hi : i ∈ B) : ∃ j ∈ B, σ j ≠ σ i := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  by_cases hui : σ u = σ i
  · exact ⟨v, hv, fun hvi => huv (hui.trans hvi.symm)⟩
  · exact ⟨u, hu, hui⟩

/-- Distinct active supports at one level. -/
def cells (σ : ι → Bool) (f : ℕ → ι → κ) (n : ℕ) : Finset (Finset ι) := by
  classical
  exact (Finset.univ.image (cell f n)).filter (Active σ)

lemma mem_cells {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ} {B : Finset ι} :
    B ∈ cells σ f n ↔ (∃ i, cell f n i = B) ∧ Active σ B := by
  classical
  simp [cells]

@[simp] lemma cell_mem_cells {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ} {i : ι} :
    cell f n i ∈ cells σ f n ↔ Active σ (cell f n i) := by
  rw [mem_cells]
  exact ⟨And.right, fun h => ⟨⟨i, rfl⟩, h⟩⟩

lemma eq_cell_of_mem {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ}
    {B : Finset ι} (hB : B ∈ cells σ f n) {i : ι} (hi : i ∈ B) :
    B = cell f n i := by
  obtain ⟨⟨j, rfl⟩, _⟩ := mem_cells.mp hB
  exact (cell_eq_of_mem hi).symm

/-- All active supports up to a finite depth. -/
def allCells (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ) : Finset (Finset ι) :=
  (Finset.range K).biUnion (cells σ f)

lemma cells_subset_allCells {K n : ℕ} (hn : n ∈ Finset.range K)
    (σ : ι → Bool) (f : ℕ → ι → κ) : cells σ f n ⊆ allCells K σ f := by
  intro B hB
  exact Finset.mem_biUnion.mpr ⟨n, hn, hB⟩

lemma allCells_laminar (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j) :
    ∀ B ∈ allCells K σ f, ∀ C ∈ allCells K σ f,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  intro B hB C hC
  obtain ⟨n, hn, hB⟩ := Finset.mem_biUnion.mp hB
  obtain ⟨m, hm, hC⟩ := Finset.mem_biUnion.mp hC
  by_cases hd : Disjoint B C
  · exact Or.inr (Or.inr hd)
  · obtain ⟨i, hiB, hiC⟩ := Finset.not_disjoint_iff.mp hd
    rw [eq_cell_of_mem hB hiB, eq_cell_of_mem hC hiC]
    rcases le_total n m with hnm | hmn
    · right; left
      intro j hj
      exact (mem_cell f n i j).mpr (hf n m hnm j i ((mem_cell f m i j).mp hj))
    · left
      intro j hj
      exact (mem_cell f m i j).mpr (hf m n hmn j i ((mem_cell f n i j).mp hj))

/-- The weight includes every level at which the support occurs. -/
def levelWeight (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (w : ℝ) (B : Finset ι) : ℝ :=
  ∑ n ∈ Finset.range K, if B ∈ cells σ f n then w else 0

/-- Compress a finite refining sequence of bichromatic partitions. -/
def build (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) : OppositionFamily ι where
  nodes := allCells K σ f
  weight := levelWeight K σ f w
  weight_nonneg := by
    intro B hB
    apply Finset.sum_nonneg
    intro n hn
    split_ifs <;> positivity
  laminar := allCells_laminar K σ f hf
  sign := σ
  bichromatic := by
    intro B hB i hi
    obtain ⟨n, hn, hB⟩ := Finset.mem_biUnion.mp hB
    exact active_bichromatic (mem_cells.mp hB).2 hi

lemma layer_kernel (σ : ι → Bool) (f : ℕ → ι → κ) (n : ℕ) (w : ℝ) (i j : ι) :
    (∑ B ∈ cells σ f n, w * ind B i * ind B j) =
      if Active σ (cell f n i) ∧ f n i = f n j then w else 0 := by
  classical
  by_cases hA : Active σ (cell f n i)
  · rw [Finset.sum_eq_single_of_mem (cell f n i) (cell_mem_cells.mpr hA)]
    · by_cases hij : f n i = f n j
      · simp [ind, hA, hij]
      · simp [ind, hA, hij, Ne.symm hij]
    · intro B hB hne
      have hi : i ∉ B := fun hi => hne (eq_cell_of_mem hB hi)
      simp [ind, hi]
  · have hz : ∀ B ∈ cells σ f n, w * ind B i * ind B j = 0 := by
      intro B hB
      have hi : i ∉ B := by
        intro hi
        have he := eq_cell_of_mem hB hi
        exact hA (he ▸ (mem_cells.mp hB).2)
      simp [ind, hi]
    rw [Finset.sum_eq_zero hz]
    simp [hA]

lemma unsigned_eq_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) :
    (build K σ f hf w hw).unsigned i j =
      ∑ n ∈ Finset.range K,
        if Active σ (cell f n i) ∧ f n i = f n j then w else 0 := by
  classical
  change (∑ B ∈ allCells K σ f,
    (∑ n ∈ Finset.range K, if B ∈ cells σ f n then w else 0) * ind B i * ind B j) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← layer_kernel σ f n w i j]
  symm
  apply Finset.sum_subset_zero_on_sdiff (cells_subset_allCells hn σ f)
  · intro B hB
    simp [(Finset.mem_sdiff.mp hB).2]
  · intro B hB
    simp [hB]

/-- Opposite-colored vertices activate their own class, so no activity test remains. -/
lemma opposition_eq_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) (hij : σ i ≠ σ j) :
    (build K σ f hf w hw).opposition i j =
      ∑ n ∈ Finset.range K, if f n i = f n j then w else 0 := by
  classical
  change (if σ i = σ j then 0 else (build K σ f hf w hw).unsigned i j) = _
  rw [if_neg hij, unsigned_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases he : f n i = f n j
  · have hA : Active σ (cell f n i) :=
      ⟨i, self_mem_cell f n i, j, (mem_cell f n i j).mpr he.symm, hij⟩
    simp [he, hA]
  · simp [he]

/-- Dropping the activity test only increases the same-side kernel. -/
lemma agreement_le_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) :
    (build K σ f hf w hw).agreement i j ≤
      ∑ n ∈ Finset.range K, if f n i = f n j then w else 0 := by
  classical
  have hle : (build K σ f hf w hw).agreement i j ≤
      (build K σ f hf w hw).unsigned i j := by
    unfold OppositionFamily.agreement
    split_ifs
    · exact le_rfl
    · exact OppositionFamily.unsigned_nonneg _ _ _
  refine hle.trans ?_
  rw [unsigned_eq_sum]
  apply Finset.sum_le_sum
  intro n hn
  split_ifs <;> simp_all

/-- Counting the initial `e` levels of a tower. -/
lemma sum_initial (K e : ℕ) (w : ℝ) (he : e ≤ K) :
    (∑ n ∈ Finset.range K, if n < e then w else 0) = (e : ℝ) * w := by
  rw [← Finset.sum_filter]
  have hset : (Finset.range K).filter (fun n => n < e) = Finset.range e := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  simp

/-- A truncated initial segment has at most `e` weighted levels. -/
lemma sum_initial_le (K e : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ n ∈ Finset.range K, if n < e then w else 0) ≤ (e : ℝ) * w := by
  rcases le_total e K with h | h
  · exact (sum_initial K e w h).le
  · have heq : (∑ n ∈ Finset.range K, if n < e then w else 0) = (K : ℝ) * w := by
      calc
        _ = ∑ _n ∈ Finset.range K, w := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (lt_of_lt_of_le (Finset.mem_range.mp hn) h)]
        _ = _ := by simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) hw

end

end E126.ArithmeticCells126
