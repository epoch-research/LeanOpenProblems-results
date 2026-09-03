import Submission.PatchedTranslatedRadixExplore
import Submission.PhasedResidueCountingExplore
import Submission.PrefixCopyExplore

/-! Exact row cardinalities in the translated radix lift, and the counting
obstruction to literal iteration of these complete or empty rows. -/
namespace Erdos66TranslatedRadixRowMass
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66TranslatedRadixCarry Erdos66PatchedTranslatedRadix Erdos66RectangularRadix
  Erdos66Counting Erdos66IntegerBlock Erdos66PhasedResidueCounting Erdos66PrefixCopy
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1600000

variable (L M : ℕ) [NeZero L] [NeZero M]

noncomputable def radixRow (B : Finset (ZMod (L*M))) (z : ZMod M) : Finset (ZMod L) :=
  Finset.univ.filter (fun a ↦ encode L M (a,z) ∈ B)

omit [NeZero M] in
lemma mem_radixRow (B : Finset (ZMod (L*M))) (z : ZMod M) (a : ZMod L) :
    a ∈ radixRow L M B z ↔ encode L M (a,z) ∈ B := by simp [radixRow]

lemma periodic_eq_block (B : Finset (ZMod (L*M))) :
    {n : ℕ | (n : ZMod (L*M)) ∈ B} =
      blockSet L (fun k ↦ radixRow L M B (k : ZMod M)) := by
  ext n
  change ((n : ZMod (L*M)) ∈ B) ↔ ((n : ZMod L) ∈ radixRow L M B (n/L : ℕ))
  rw [mem_radixRow, encode_nat]

lemma patched_zero_row (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M)) :
    radixRow L M (patchedRadix L M A P) 0 = A := by
  ext a
  rw [mem_radixRow]
  have he : encode L M (a,0) = (a.val : ZMod (L*M)) := by simp [encode]
  rw [he, patchedRadix_prefix L M A P a.val (ZMod.val_lt a), ZMod.natCast_zmod_val]

lemma patched_nonzero_row (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (z : ZMod M) (hz : z ≠ 0) :
    radixRow L M (patchedRadix L M A P) z = ∅ ∨
      ∃ i : ZMod L, radixRow L M (patchedRadix L M A P) z = shiftSet A i := by
  by_cases hh : ∃ i : ZMod L, z ∈ P i
  · obtain ⟨i,hi⟩ := hh
    right
    refine ⟨i, ?_⟩
    ext a
    rw [mem_radixRow, patchedRadix_off L M A P a z hz, mem_radixAssembly]
    constructor
    · rintro ⟨j,hj,hzj⟩
      have hji : j = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hP hne) hzj hi
      simpa only [hji] using hj
    · intro ha
      exact ⟨i,ha,hi⟩
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    rw [mem_radixRow, patchedRadix_off L M A P a z hz, mem_radixAssembly] at ha
    obtain ⟨i,_,hi⟩ := ha
    exact hh ⟨i,hi⟩

lemma patched_nonzero_row_card (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (z : ZMod M) (hz : z ≠ 0) :
    (radixRow L M (patchedRadix L M A P) z).card = 0 ∨
      (radixRow L M (patchedRadix L M A P) z).card = A.card := by
  rcases patched_nonzero_row L M A P hP z hz with he | ⟨i,he⟩
  · left; simp [he]
  · right
    rw [he, shiftSet, Finset.card_image_of_injective _ (add_right_injective i)]

lemma patched_two_block_count (hM : 1 < M) (A : Finset (ZMod L))
    (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) :
    let S := {n : ℕ | (n : ZMod (L*M)) ∈ patchedRadix L M A P}
    count S L = A.card ∧ (count S (2*L) = A.card ∨ count S (2*L) = 2*A.card) := by
  letI : Fact (1 < M) := ⟨hM⟩
  dsimp only
  rw [periodic_eq_block]
  have he := count_blocks L (fun k ↦ radixRow L M (patchedRadix L M A P) (k : ZMod M)) 1
  simp only [one_mul, Finset.sum_range_one, Nat.cast_zero, patched_zero_row] at he
  refine ⟨he, ?_⟩
  rw [count_blocks]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.cast_zero, Nat.cast_one, patched_zero_row]
  rcases patched_nonzero_row_card L M A P hP 1 one_ne_zero with h | h <;> simp [h, two_mul]

theorem witness_eventually_strict_two_block_mass {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ L in atTop, count A L < count A (2*L) ∧ count A (2*L) < 2*count A L := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  have h1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have h2 : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  have hh := count_multiple_ratio hc ht 2 (by decide)
  filter_upwards [hh.eventually_const_lt h1, hh.eventually_lt_const h2,
    count_pos_eventually hc ht] with L hlow hupp hpos
  have hp : (0 : ℝ) < count A L := by exact_mod_cast hpos
  have hl := (lt_div_iff₀ hp).mp hlow
  have hu := (div_lt_iff₀ hp).mp hupp
  constructor
  · exact_mod_cast (show (count A L : ℝ) < count A (2*L) by simpa using hl)
  · exact_mod_cast hu

lemma agrees_two_blocks_count (S : Set ℕ) (hM : 1 < M)
    (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (hag : ∀ n < 2*L, n ∈ S ↔ (n : ZMod (L*M)) ∈ patchedRadix L M A P) :
    count S (2*L) = count S L ∨ count S (2*L) = 2*count S L := by
  let T := {n : ℕ | (n : ZMod (L*M)) ∈ patchedRadix L M A P}
  have he (N : ℕ) (hN : N ≤ 2*L) : count S N = count T N := by
    unfold count
    congr 1
    ext n
    simp only [mem_cutoff]
    by_cases hn : n < N
    · rw [and_iff_right hn, and_iff_right hn]
      exact hag n (lt_of_lt_of_le hn hN)
    · simp only [hn, false_and]
  have hh := patched_two_block_count L M hM A P hP
  change count T L = A.card ∧ _ at hh
  rw [he (2*L) le_rfl, he L (by omega), hh.1]
  exact hh.2

theorem no_log_limit_of_frequent_row_mass_dichotomy (A : Set ℕ)
    (hd : ∀ K : ℕ, ∃ L ≥ K,
      count A (2*L) = count A L ∨ count A (2*L) = 2*count A L)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  obtain ⟨K,hK⟩ := eventually_atTop.mp (witness_eventually_strict_two_block_mass hc ht)
  obtain ⟨L,hL,hdL⟩ := hd K
  obtain ⟨hlo,hhi⟩ := hK L hL
  rcases hdL with he | he <;> omega

end Erdos66TranslatedRadixRowMass
