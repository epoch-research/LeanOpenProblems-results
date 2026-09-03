import Submission.OuterCarryProfileExplore

/-! Exact comparison of mixed cyclic counts for two periodic descriptions of
one pair of natural-index membership patterns. -/
namespace Erdos66PeriodicPatternComparison
open Erdos66OuterCarryProfile Erdos66CyclicThickening
open scoped Classical

noncomputable def periodicLift (P M : ℕ) [NeZero P] [NeZero M]
    (B : Finset (ZMod M)) : Finset (ZMod P) :=
  Finset.univ.filter (fun z ↦ (z.val : ZMod M) ∈ B)

lemma reduceDigit_val (M K : ℕ) [NeZero M] [NeZero K] (z : ZMod (M*K)) :
    reduceDigit M K z = (z.val : ZMod M) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast _ _

lemma periodicLift_eq_outerLift (M K : ℕ) [NeZero M] [NeZero K]
    (B : Finset (ZMod M)) :
    periodicLift (M*K) M B = outerLift M K B := by
  ext z
  simp only [periodicLift, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_outerLift, reduceDigit_val]

lemma periodicLift_count (P M K : ℕ) [NeZero P] [NeZero M] [NeZero K]
    (hP : P=M*K) (B C : Finset (ZMod M)) (n : ℕ) :
    cyclicCount P (periodicLift P M B) (periodicLift P M C) (n : ZMod P) =
      K * cyclicCount M B C (n : ZMod M) := by
  subst P
  rw [periodicLift_eq_outerLift, periodicLift_eq_outerLift, outer_cyclicCount,
    map_natCast]

lemma periodicLift_congr (P M N : ℕ) [NeZero P] [NeZero M] [NeZero N]
    (B : Finset (ZMod M)) (D : Finset (ZMod N))
    (h : ∀ n : ℕ, (n : ZMod M) ∈ B ↔ (n : ZMod N) ∈ D) :
    periodicLift P M B = periodicLift P N D := by
  ext z
  simp only [periodicLift, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h z.val

/-- If two pairs of cyclic sets define the same periodic membership patterns,
then their mixed counts agree after scaling to a common multiple. -/
theorem periodic_mixed_count_comparison (M N a b : ℕ)
    [NeZero M] [NeZero N] [NeZero a] [NeZero b]
    (hMN : M*a=N*b) (B C : Finset (ZMod M)) (D E : Finset (ZMod N))
    (hBD : ∀ n : ℕ, (n : ZMod M) ∈ B ↔ (n : ZMod N) ∈ D)
    (hCE : ∀ n : ℕ, (n : ZMod M) ∈ C ↔ (n : ZMod N) ∈ E) (n : ℕ) :
    a * cyclicCount M B C (n : ZMod M) =
      b * cyclicCount N D E (n : ZMod N) := by
  rw [← periodicLift_count (M*a) M a rfl B C n,
    periodicLift_congr (M*a) M N B D hBD,
    periodicLift_congr (M*a) M N C E hCE,
    periodicLift_count (M*a) N b hMN D E n]

end Erdos66PeriodicPatternComparison
