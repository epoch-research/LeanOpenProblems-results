import Submission.BinaryBlockTransferExplore
import Submission.ResidueCountingExplore

/-! No proper fixed low-residue template can underlie a witness, regardless
of how its occupied high blocks are selected.  This only excludes one class
of proposed constructions; it is not a disproof of Erdős Problem 66. -/
namespace Erdos66FixedTemplateObstruction
open Filter AdditiveCombinatorics Erdos66IntegerBlock Erdos66BinaryBlockTransfer
  Erdos66Counting Erdos66ResidueCounting
open scoped Classical Topology

variable (M : ℕ) [NeZero M]

/-- Omitting one fixed residue class is incompatible with a nonzero
logarithmic representation limit. -/
theorem no_missing_residue (A : Set ℕ) (z : ZMod M)
    (hz : ∀ a ∈ A, (a : ZMod M) ≠ z) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  rintro ⟨c,hc,h⟩
  have he : residueSet M A z = ∅ := by
    ext a
    simp only [residueSet,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_and]
    exact hz a
  have hl := witness_ordinary_residue_equidistribution M hc h z
  rw [he] at hl
  have hzero : ∀ N, count (∅ : Set ℕ) N = 0 := by
    intro N
    simp [count,cutoff]
  simp only [hzero,Nat.cast_zero,zero_div] at hl
  have heq : (0 : ℝ) = 1/(M : ℝ) := tendsto_nhds_unique tendsto_const_nhds hl
  have hpos : (0 : ℝ) < 1/(M : ℝ) := by
    have hm : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
    positivity
  linarith

/-- Arbitrary choices of the high-block pattern cannot wash out an omitted
low residue. -/
theorem no_proper_fixed_template (B : Finset (ZMod M)) (hB : B ≠ Finset.univ)
    (D : Set ℕ) :
    ¬ ∃ c : ℝ, c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep (binaryBlocks M B D) n : ℝ)/Real.log n)
        atTop (𝓝 c) := by
  obtain ⟨z,hz⟩ : ∃ z : ZMod M, z ∉ B := by
    by_contra h
    push_neg at h
    exact hB (Finset.eq_univ_of_forall h)
  apply no_missing_residue M (binaryBlocks M B D) z
  intro a ha he
  change (a : ZMod M) ∈ (if a/M ∈ D then B else ∅) at ha
  by_cases hd : a/M ∈ D
  · rw [if_pos hd,he] at ha
    exact hz ha
  · simp [hd] at ha

end Erdos66FixedTemplateObstruction
