import Submission.ClippedModulusExplore
import Submission.PeriodicPatternComparisonExplore

/-! One-sided periodic lifting: exact mixed counts against an arbitrary
pattern in the larger period. This retains the location of each old block. -/
namespace Erdos66CyclicLiftMixed
open Erdos66OuterCarryProfile Erdos66OuterMixedPrefix Erdos66CyclicThickening
  Erdos66ClippedModulus Erdos66PeriodicPatternComparison
open scoped Classical
set_option maxHeartbeats 1600000

variable (M K : ℕ) [NeZero M] [NeZero K]

lemma first_block_iff (a : ZMod M) (i : Fin K) :
    (blockDigit M K a i).val<M ↔ i=0 := by
  rw [blockDigit_val]
  have ha := ZMod.val_lt a
  have hm := NeZero.pos M
  constructor
  · intro hh
    apply Fin.ext
    change i.val=0
    nlinarith
  · rintro rfl
    simpa using ha

lemma first_block_prefix (A : Finset (ZMod M)) (D : Finset (ZMod (M*K)))
    (z : ZMod (M*K)) :
    prefixCount (M*K) (outerLift M K A) D z M =
      ∑ a : ZMod M, if a∈A ∧ z-(a.val : ZMod (M*K))∈D then 1 else 0 := by
  rw [prefixCount_sum,←Equiv.sum_comp (blockEquiv M K),Fintype.sum_prod_type]
  simp only [blockEquiv,Equiv.ofBijective_apply,mem_outerLift,reduce_block,first_block_iff]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ite_and,Finset.sum_ite_eq',Finset.mem_univ,if_true,blockDigit,
    Fin.val_zero,Nat.mul_zero,Nat.add_zero]

lemma outer_mixed_blocks (A : Finset (ZMod M)) (D : Finset (ZMod (M*K)))
    (z : ZMod (M*K)) :
    cyclicCount (M*K) (outerLift M K A) D z =
      ∑ i : Fin K, prefixCount (M*K) (outerLift M K A) D (z-(M*i.val:ℕ)) M := by
  rw [cyclicCount_sum,←Equiv.sum_comp (blockEquiv M K),Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [blockEquiv,Equiv.ofBijective_apply,mem_outerLift,reduce_block]
  apply Finset.sum_congr rfl
  intro i hi
  rw [first_block_prefix]
  apply Finset.sum_congr rfl
  intro a ha
  have he : z-blockDigit M K a i = (z-(M*i.val:ℕ))-(a.val:ZMod (M*K)) := by
    unfold blockDigit
    push_cast
    ring
  rw [he]

variable (L : ℕ) [NeZero L]

lemma first_block_rebase_prefix (C : Finset (ZMod L)) (D : Finset (ZMod (M*K)))
    (z : ZMod (M*K)) :
    prefixCount (M*K) (outerLift M K (rebase M L C)) D z M =
      prefixCount (M*K) (rebase (M*K) L C) D z M := by
  unfold prefixCount
  congr 1
  ext a
  simp only [Finset.mem_filter,mem_outerLift,mem_rebase,reduceDigit_val]
  by_cases ha : a.val<M
  · simp only [ha,ZMod.val_natCast_of_lt ha,true_and]
  · simp [ha]

/-- Exact mixed count of the old repeated prefix and the fresh longer prefix
of a common source pair. Both source members are allowed to differ. -/
theorem repeated_clipped_cross_identity (C D : Finset (ZMod L)) (z : ZMod (M*K)) :
    cyclicCount (M*K) (outerLift M K (rebase M L C)) (rebase (M*K) L D) z =
      ∑ i : Fin K, prefixCount (M*K) (rebase (M*K) L C) (rebase (M*K) L D)
        (z-(M*i.val:ℕ)) M := by
  rw [outer_mixed_blocks]
  simp_rw [first_block_rebase_prefix]

/-- The old and new periodic patterns have exactly the same first M bits
when they come from the same source member. -/
lemma repeated_clipped_prefix_agree (C : Finset (ZMod L)) (a : ℕ) (ha : a<M) :
    (a : ZMod (M*K))∈outerLift M K (rebase M L C) ↔
      (a : ZMod (M*K))∈rebase (M*K) L C := by
  have haN : a<M*K := ha.trans_le (Nat.le_mul_of_pos_right M (NeZero.pos K))
  simp only [mem_outerLift,map_natCast,mem_rebase,ZMod.val_natCast_of_lt ha,
    ZMod.val_natCast_of_lt haN]

end Erdos66CyclicLiftMixed
