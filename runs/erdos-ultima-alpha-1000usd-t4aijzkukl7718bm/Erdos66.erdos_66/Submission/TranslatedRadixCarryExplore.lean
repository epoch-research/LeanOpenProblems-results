import Submission.TranslatedSliceLiftExplore
import Submission.RectangularRadixExplore

/-! Ordinary mixed-radix addition for the translate-averaging lift. The
lower-digit borrow is retained inside each fine mixed count. -/
namespace Erdos66TranslatedRadixCarry
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66TranslateKernelAveraging Erdos66DisjointPaletteAssembly
  Erdos66RectangularRadix Erdos66CyclicThickening
open scoped Classical
set_option maxHeartbeats 1800000

variable (L M : ℕ) [NeZero L] [NeZero M]

lemma radix_product_count (A B : Finset (ZMod L)) (P Q : Finset (ZMod M))
    (t : ZMod L) (s : ZMod M) :
    pairCount (radixSet L M (A ×ˢ P)) (radixSet L M (B ×ˢ Q)) (encode L M (t, s)) =
      ∑ x ∈ A.filter (fun x ↦ t - x ∈ B),
        pairCount P Q (s - (borrow L t x : ZMod M)) := by
  have he := mixed_count_formula L M (A ×ˢ P) (B ×ˢ Q) t s
  change pairCount _ _ _ = _ at he
  rw [he, Finset.sum_filter]
  have hin (x : ZMod L) :
      (∑ y : ZMod M,
        if (x, y) ∈ A ×ˢ P ∧ (t - x, s - y - (borrow L t x : ZMod M)) ∈ B ×ˢ Q
          then 1 else 0) =
        if x ∈ A ∧ t - x ∈ B then pairCount P Q (s - (borrow L t x : ZMod M)) else 0 := by
    by_cases hx : x ∈ A <;> by_cases htx : t - x ∈ B
    · simp only [Finset.mem_product, hx, htx, true_and, if_true]
      change _ = Erdos66OuterCarryProfile.cyclicCount M P Q _
      rw [Erdos66OuterCarryProfile.cyclicCount_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [show s - y - (borrow L t x : ZMod M) =
        (s - (borrow L t x : ZMod M)) - y by abel]
    all_goals simp [Finset.mem_product, hx, htx]
  simp_rw [hin]
  simp only [ite_and, Finset.sum_ite_mem, Finset.univ_inter]

lemma radix_product_error (A B : Finset (ZMod L)) (P Q : Finset (ZMod M))
    (μ E : ℝ) (hb : ∀ z, |(pairCount P Q z : ℝ) - μ| ≤ E)
    (t : ZMod L) (s : ZMod M) :
    |(pairCount (radixSet L M (A ×ˢ P)) (radixSet L M (B ×ˢ Q))
        (encode L M (t, s)) : ℝ) - μ * pairCount A B t| ≤ E * pairCount A B t := by
  rw [radix_product_count]
  push_cast
  have hh := (Finset.abs_sum_le_sum_abs
    (fun x ↦ (pairCount P Q (s - (borrow L t x : ZMod M)) : ℝ) - μ)
    (A.filter (fun x ↦ t - x ∈ B))).trans
      (Finset.sum_le_sum (fun x hx ↦ hb (s - (borrow L t x : ZMod M))))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hh
  change |(∑ x ∈ A.filter (fun x ↦ t - x ∈ B),
    (pairCount P Q (s - (borrow L t x : ZMod M)) : ℝ)) -
    (pairCount A B t : ℝ) * μ| ≤ (pairCount A B t : ℝ) * E at hh
  simpa only [mul_comm] using hh

variable {ι : Type*} [Fintype ι]

noncomputable def radixAssembly (C : ι → Finset (ZMod L)) (P : ι → Finset (ZMod M)) :
    Finset (ZMod (L * M)) :=
  Finset.univ.biUnion (fun i ↦ radixSet L M (C i ×ˢ P i))

lemma mem_radixAssembly (C : ι → Finset (ZMod L)) (P : ι → Finset (ZMod M))
    (x : ZMod L) (y : ZMod M) :
    encode L M (x, y) ∈ radixAssembly L M C P ↔ ∃ i : ι, x ∈ C i ∧ y ∈ P i := by
  simp only [radixAssembly, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_radixSet, Finset.mem_product]

lemma radixAssembly_pairwise (C : ι → Finset (ZMod L)) (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) :
    ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i ↦ radixSet L M (C i ×ˢ P i)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨⟨x, y⟩, rfl⟩ := (radixEquiv L M).surjective z
  change encode L M (x, y) ∈ _ at hz hz'
  rw [mem_radixSet] at hz hz'
  exact Finset.disjoint_left.mp (hP hij) (Finset.mem_product.mp hz).2
    (Finset.mem_product.mp hz').2

lemma radixAssembly_count (C : ι → Finset (ZMod L)) (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (z : ZMod (L * M)) :
    pairCount (radixAssembly L M C P) (radixAssembly L M C P) z =
      ∑ i : ι, ∑ j : ι,
        pairCount (radixSet L M (C i ×ˢ P i)) (radixSet L M (C j ×ˢ P j)) z := by
  exact pairCount_biUnion_self _ _ (radixAssembly_pairwise L M C P hP) z

lemma radixAssembly_error (C : ι → Finset (ZMod L)) (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ E : ℝ) (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ E)
    (t : ZMod L) (s : ZMod M) :
    |(pairCount (radixAssembly L M C P) (radixAssembly L M C P)
        (encode L M (t, s)) : ℝ) -
      μ * (∑ i : ι, ∑ j : ι, (pairCount (C i) (C j) t : ℝ))| ≤
        E * (∑ i : ι, ∑ j : ι, (pairCount (C i) (C j) t : ℝ)) := by
  rw [radixAssembly_count L M C P hP]
  push_cast
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _)).trans
      (Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦
        radix_product_error L M (C i) (C j) (P i) (P j) μ E (hb i j) t s))))

/-- Averaging all old translates removes the dependence on the low target.
The high count is evaluated at both possible borrow-shifted targets, never
identified with an additive image of a product group. -/
lemma translated_radix_error (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ δ : ℝ) (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : ZMod (L * M)) :
    |(pairCount (radixAssembly L M (shiftSet A) P) (radixAssembly L M (shiftSet A) P) z : ℝ) -
      μ * ((L : ℝ) * (A.card : ℝ) ^ 2)| ≤ δ * μ * ((L : ℝ) * (A.card : ℝ) ^ 2) := by
  obtain ⟨⟨t, s⟩, rfl⟩ := (radixEquiv L M).surjective z
  have he := radixAssembly_error L M (shiftSet A) P hP μ (δ * μ) hb t s
  have hs : (∑ i : ZMod L, ∑ j : ZMod L,
      (pairCount (shiftSet A i) (shiftSet A j) t : ℝ)) =
        (L : ℝ) * (A.card : ℝ) ^ 2 := by
    have hh := sum_all_translated_pairCount A A t
    rw [ZMod.card] at hh
    simpa only [pow_two] using (show (∑ i : ZMod L, ∑ j : ZMod L,
      (pairCount (shiftSet A i) (shiftSet A j) t : ℝ)) =
        (L : ℝ) * ((A.card : ℝ) * A.card) by exact_mod_cast hh)
  rwa [hs] at he

end Erdos66TranslatedRadixCarry
