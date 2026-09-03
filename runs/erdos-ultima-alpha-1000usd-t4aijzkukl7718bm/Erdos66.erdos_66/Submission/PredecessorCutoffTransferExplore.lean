import Submission.LocatedIntervalPredecessorExplore
import Submission.CompactnessExplore
import Submission.Explore

/-! Cutoff and finite-support bookkeeping for predecessor repairs. -/
namespace Erdos66PredecessorCutoffTransfer
open AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCell
  Erdos66OrderedPartialReplacement Erdos66FiniteSwapAlgebra Erdos66Compactness
  Erdos66Explore
open scoped Classical
set_option maxHeartbeats 1500000

lemma predecessor_congr_below (A B : Set ℕ) (u : ℕ)
    (h : ∀ a, a ≤ u → (a ∈ A ↔ a ∈ B)) : predecessor A u = predecessor B u := by
  unfold predecessor
  apply le_antisymm
  · by_cases he : Nat.findGreatest (fun a ↦ a ∈ A) u = 0
    · omega
    · have hm := Nat.findGreatest_of_ne_zero rfl he
      exact Nat.le_findGreatest (Nat.findGreatest_le _) ((h _ (Nat.findGreatest_le _)).mp hm)
  · by_cases he : Nat.findGreatest (fun a ↦ a ∈ B) u = 0
    · omega
    · have hm := Nat.findGreatest_of_ne_zero rfl he
      exact Nat.le_findGreatest (Nat.findGreatest_le _) ((h _ (Nat.findGreatest_le _)).mpr hm)

lemma predecessor_cutoff (A : Set ℕ) {u X : ℕ} (hu : u < X) :
    predecessor (cutoff A X : Set ℕ) u = predecessor A u := by
  apply predecessor_congr_below
  intro a ha
  simp only [Finset.mem_coe,mem_cutoff,show a < X from lt_of_le_of_lt ha hu,true_and]

lemma swap_mem_outside (A : Set ℕ) (D F : Finset ℕ) (i : ℕ) (hi : i ∉ D ∪ F) :
    i ∈ swap A D F ↔ i ∈ A := by
  have hd : i ∉ D := fun h ↦ hi (Finset.mem_union_left _ h)
  have hf : i ∉ F := fun h ↦ hi (Finset.mem_union_right _ h)
  simp [swap,hd,hf]

lemma swap_count_after (A : Set ℕ) (D F : Finset ℕ)
    (hD : (D : Set ℕ) ⊆ A) (hF : Disjoint (F : Set ℕ) A) (hc : D.card = F.card)
    (X N : ℕ) (hs : D ∪ F ⊆ Finset.range X) (hN : X ≤ N) :
    count (swap A D F) N = count A N := by
  have hd : D ⊆ Finset.range N := by
    intro u hu
    have hh := Finset.mem_range.mp (hs (Finset.mem_union_left _ hu))
    exact Finset.mem_range.mpr (by omega)
  have hf : F ⊆ Finset.range N := by
    intro u hu
    have hh := Finset.mem_range.mp (hs (Finset.mem_union_right _ hu))
    exact Finset.mem_range.mpr (by omega)
  have hh := swap_count_difference A D F hD hF N
  rw [Finset.inter_eq_left.mpr hf,Finset.inter_eq_left.mpr hd,hc,sub_self] at hh
  exact_mod_cast sub_eq_zero.mp hh

lemma sumRep_union_finset (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    sumRep (A ∪ (F : Set ℕ)) n ≤ sumRep A n + 2*F.card := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have he : A ∪ ((insert a F : Finset ℕ) : Set ℕ) = insert a (A ∪ (F : Set ℕ)) := by
      ext u
      simp only [Set.mem_union,Finset.mem_coe,Finset.mem_insert,Set.mem_insert_iff]
      tauto
    rw [he,Finset.card_insert_of_notMem ha]
    have hh := sumRep_insert_le (A ∪ (F : Set ℕ)) a n
    omega

lemma swap_rep_error (A : Set ℕ) (D F : Finset ℕ) (m : ℕ)
    (hD : D.card ≤ m) (hF : F.card ≤ m) (n : ℕ) :
    |(sumRep (swap A D F) n : ℝ)-sumRep A n| ≤ 2*m := by
  have hs : swap A D F ⊆ A ∪ (F : Set ℕ) := by
    intro a ha
    rcases ha with h | h
    · exact Or.inl h.1
    · exact Or.inr h
  have hs' : A ⊆ swap A D F ∪ (D : Set ℕ) := by
    intro a ha
    by_cases hd : a ∈ D
    · exact Or.inr hd
    · exact Or.inl (Or.inl ⟨ha,hd⟩)
  have hu := (sumRep_mono hs n).trans (sumRep_union_finset A F n)
  have hl := (sumRep_mono hs' n).trans (sumRep_union_finset (swap A D F) D n)
  have hu' : (sumRep (swap A D F) n : ℝ) ≤ sumRep A n + 2*m := by
    exact_mod_cast (show sumRep (swap A D F) n ≤ sumRep A n+2*m by omega)
  have hl' : (sumRep A n : ℝ) ≤ sumRep (swap A D F) n+2*m := by
    exact_mod_cast (show sumRep A n ≤ sumRep (swap A D F) n+2*m by omega)
  rw [abs_le]
  constructor <;> linarith

lemma cutoff_swap_rep (A : Set ℕ) (D F : Finset ℕ) {X n : ℕ} (hn : n < X) :
    sumRep (swapped (cutoff A X) D F : Set ℕ) n = sumRep (swap A D F) n := by
  rw [swapped_coe]
  apply sumRep_congr_below
  intro i hi
  simp only [swap,Set.mem_union,Set.mem_diff,Finset.mem_coe,mem_cutoff,
    show i < X from lt_of_le_of_lt hi hn,true_and]

lemma cutoff_rep (A : Set ℕ) {X n : ℕ} (hn : n < X) :
    sumRep (cutoff A X : Set ℕ) n = sumRep A n := by
  apply sumRep_congr_below
  intro i hi
  simp only [Finset.mem_coe,mem_cutoff,show i < X from lt_of_le_of_lt hi hn,true_and]

lemma cutoff_rep_zero (A : Set ℕ) (X z : ℕ) (hz : 2*X ≤ z) :
    sumRep (cutoff A X : Set ℕ) z = 0 := by
  rw [← Erdos66NatPairAlgebra.pairs_self]
  apply pairs_eq_zero_of_no_partner
  intro a ha haz hb
  have ha' := (mem_cutoff.mp ha).1
  have hb' := (mem_cutoff.mp hb).1
  omega

lemma cutoff_envelope (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) (X : ℕ) :
    ∀ z, (sumRep (cutoff A X : Set ℕ) z : ℝ) ≤ K+C*Real.log (2*(X : ℝ)+2) := by
  intro z
  by_cases hz : 2*X ≤ z
  · rw [cutoff_rep_zero A X z hz,Nat.cast_zero]
    exact add_nonneg hK (mul_nonneg hC (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)))
  · have hs : (cutoff A X : Set ℕ) ⊆ A := fun a ha ↦ (mem_cutoff.mp ha).2
    have hr : (sumRep (cutoff A X : Set ℕ) z : ℝ) ≤ sumRep A z := by
      exact_mod_cast sumRep_mono hs z
    have hz' : (z : ℝ)+2 ≤ 2*(X : ℝ)+2 := by exact_mod_cast (show z+2 ≤ 2*X+2 by omega)
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (z : ℝ)+2) hz'
    exact hr.trans ((hA z).trans (add_le_add_right (mul_le_mul_of_nonneg_left hl hC) K))

end Erdos66PredecessorCutoffTransfer
