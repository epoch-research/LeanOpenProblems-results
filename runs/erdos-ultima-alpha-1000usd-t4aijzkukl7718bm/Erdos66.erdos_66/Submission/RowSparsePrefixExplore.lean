import Submission.CompactnessExplore
import Submission.Explore
import Submission.WindowPerturbationExplore
import Submission.TransitionLinearExplore
import Submission.ShiftedFiniteExplore

/-! Row occupancy gives uniform mixed-count bounds against a short old
prefix. This is a forward estimate, not a compatible infinite construction. -/
namespace Erdos66RowSparsePrefix
open AdditiveCombinatorics Erdos66WindowPerturbation Erdos66Counting
  Erdos66NatPairAlgebra Erdos66Compactness Erdos66Explore Erdos66ShiftedFinite
open scoped Classical
set_option maxHeartbeats 1200000

def RowSparse (B : Set ℕ) (b H : ℕ) : Prop :=
  ∀ q : ℕ, localCount B (q*b) b ≤ H

lemma rowSparse_local {B : Set ℕ} {b H L : ℕ} (hb : 0<b)
    (hB : RowSparse B b H) (hL : L ≤ b) (t : ℕ) : localCount B t L ≤ 2*H := by
  let q := t/b
  have hmod := Nat.mod_lt t hb
  have hdecomp := Nat.div_add_mod' t b
  have hlo : q*b ≤ t := by dsimp [q]; omega
  have hhi : t<q*b+b := by dsimp [q]; omega
  have hsub : (Finset.Ico t (t+L)).filter (fun a ↦ a∈B) ⊆
      ((Finset.Ico (q*b) (q*b+b)).filter (fun a ↦ a∈B)) ∪
        ((Finset.Ico ((q+1)*b) ((q+1)*b+b)).filter (fun a ↦ a∈B)) := by
    intro a ha
    obtain ⟨ha,haB⟩ := Finset.mem_filter.mp ha
    obtain ⟨hat,haL⟩ := Finset.mem_Ico.mp ha
    by_cases hrow : a<q*b+b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega,hrow⟩,haB⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨?_,?_⟩,haB⟩ <;> nlinarith
  have h₁ := hB q
  have h₂ := hB (q+1)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  change localCount B t L ≤ localCount B (q*b) b+localCount B ((q+1)*b) b at hh
  omega

lemma prefix_pairs_le_local (A : Finset ℕ) (B : Set ℕ) (L n : ℕ)
    (hA : ∀ a∈A, a<L) :
    pairs A (cutoff B (n+1)) n ≤ localCount B (n+1-L) L := by
  rw [pairs_comm,pairs_eq_filter]
  apply Finset.card_le_card
  intro b hb
  obtain ⟨hb,hbn,hba⟩ := Finset.mem_filter.mp hb
  have hbB := (mem_cutoff.mp hb).2
  have ha := hA (n-b) hba
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hbB⟩

/-- No hypothesis on the number or internal structure of old points is
needed, only the spatial cutoff and the new set's row occupancy. -/
theorem prefix_pairs_bound (A : Finset ℕ) (B : Set ℕ) (L n b H : ℕ)
    (hA : ∀ a∈A, a<L) (hb : 0<b) (hL : L ≤ b) (hB : RowSparse B b H) :
    pairs A (cutoff B (n+1)) n ≤ 2*H :=
  (prefix_pairs_le_local A B L n hA).trans (rowSparse_local hb hB hL _)

lemma union_cutoff_rep (A : Finset ℕ) (B : Set ℕ) (n : ℕ) :
    sumRep ((A∪cutoff B (n+1) : Finset ℕ) : Set ℕ) n=
      sumRep ((A : Set ℕ)∪B) n := by
  apply sumRep_congr_below
  intro a ha
  simp only [Finset.mem_coe,Finset.mem_union,mem_cutoff,Set.mem_union]
  have hh : a<n+1 := by omega
  tauto

lemma cutoff_rep (B : Set ℕ) (n : ℕ) : sumRep (cutoff B (n+1) : Set ℕ) n=sumRep B n := by
  apply sumRep_congr_below
  intro a ha
  simp only [Finset.mem_coe,mem_cutoff]
  exact and_iff_right (by omega)

/-- At and beyond twice the old cutoff, the whole representation error
caused by adjoining that prefix is at most four times the new row bound. -/
theorem union_short_prefix_bound (A : Finset ℕ) (B : Set ℕ) (L b H n : ℕ)
    (hA : ∀ a∈A, a<L) (hd : Disjoint (A : Set ℕ) B)
    (hb : 0<b) (hL : L ≤ b) (hB : RowSparse B b H) (hn : 2*L ≤ n) :
    sumRep B n ≤ sumRep ((A : Set ℕ)∪B) n ∧
    sumRep ((A : Set ℕ)∪B) n ≤ sumRep B n+4*H := by
  have hdis : Disjoint A (cutoff B (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Set.disjoint_left.mp hd ha (mem_cutoff.mp hb).2
  have he := sumRep_union_self A (cutoff B (n+1)) n hdis
  rw [union_cutoff_rep,cutoff_rep,
    sumRep_zero_of_bounded (A := (A : Set ℕ)) (B := L) (fun a ha ↦ hA a ha) hn] at he
  have hm := prefix_pairs_bound A B L n b H hA hb hL hB
  constructor <;> omega

end Erdos66RowSparsePrefix
