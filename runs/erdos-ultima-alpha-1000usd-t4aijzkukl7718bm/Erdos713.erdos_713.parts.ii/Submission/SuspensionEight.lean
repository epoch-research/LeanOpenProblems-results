import FormalConjecturesUtil
import Submission.SuspensionRate

/-! Stronger bounds and reductions among the eight-vertex critical candidates. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713SuspensionEight
open Erdos713Suspension Erdos713EightCore
set_option maxHeartbeats 2000000

instance pathDecidable : DecidableRel (pathGraph 6).Adj := by
  intro i j
  exact decidable_of_iff (i.val+1=j.val ∨ j.val+1=i.val) pathGraph_adj.symm

private def parity (i : Fin 6) : Bool := decide (i.val % 2 = 1)

def pathColor : (pathGraph 6).Coloring Bool := Coloring.mk parity (by decide)
def cycleColor : (cycleGraph 6).Coloring Bool := Coloring.mk parity (by decide)

lemma path6_tree : (pathGraph 6).IsTree := by
  classical
  have he : (pathGraph 6).edgeFinset = {s(0,1),s(1,2),s(2,3),s(3,4),s(4,5)} := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [mem_edgeFinset,mem_edgeSet,pathGraph_adj]
      fin_cases a <;> fin_cases b <;> decide
  have hc : (pathGraph 6).edgeFinset.card = 5 := by rw [he]; decide
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 5,?_⟩
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using
    (show (pathGraph 6).edgeFinset.card + 1 = Fintype.card (Fin 6) by rw [hc]; rfl)

abbrev PathSusp := graph (pathGraph 6) pathColor
abbrev CycleSusp := graph (cycleGraph 6) cycleColor

noncomputable def pathIso : Graph (representative 20) ≃g PathSusp where
  toEquiv := Equiv.ofBijective
    (Sum.elim (![Sum.inr 0,Sum.inr 2,Sum.inr 4,Sum.inl false])
      (![Sum.inl true,Sum.inr 1,Sum.inr 3,Sum.inr 5]) : Fin 4 ⊕ Fin 4 → Bool ⊕ Fin 6)
    (by decide)
  map_rel_iff' := by decide

noncomputable def cycleIso : Graph (representative 27) ≃g CycleSusp where
  toEquiv := Equiv.ofBijective
    (Sum.elim (![Sum.inr 0,Sum.inr 2,Sum.inr 4,Sum.inl false])
      (![Sum.inl true,Sum.inr 1,Sum.inr 5,Sum.inr 3]) : Fin 4 ⊕ Fin 4 → Bool ⊕ Fin 6)
    (by decide)
  map_rel_iff' := by decide

lemma sixteen_contained_twenty : Graph (representative 16) ⊑ Graph (representative 20) :=
  contained_of_map _ _ id (by decide) (by decide)

lemma twenty_upper :
    (fun n : ℕ => (extremalNumber n (Graph (representative 20)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2)) :=
  (Erdos713Rate.extremal_mono_bigO ⟨pathIso.toCopy⟩).trans (tree_upper _ _ path6_tree)

lemma twenty_rate : Erdos713Rate.HasRate (Graph (representative 20)) ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper
    (middle_containments 20 (by decide) (by decide) (by decide)).1 twenty_upper

lemma sixteen_rate : Erdos713Rate.HasRate (Graph (representative 16)) ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper
    (middle_containments 16 (by decide) (by decide) (by decide)).1
    ((Erdos713Rate.extremal_mono_bigO sixteen_contained_twenty).trans twenty_upper)

lemma twenty_seven_upper :
    (fun n : ℕ => (extremalNumber n (Graph (representative 27)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((8 : ℝ)/5)) :=
  (Erdos713Rate.extremal_mono_bigO ⟨cycleIso.toCopy⟩).trans
    (cubic_upper _ _ cycleGraph_connected _ Erdos713C6.extremal_cube_le)

lemma seventeen_contained_twenty_seven : Graph (representative 17) ⊑ Graph (representative 27) :=
  contained_of_map _ _ (Sum.elim
    (fun i => Sum.inl ((![0,1,3,2] : Fin 4 → Fin 4) i))
    (fun j => Sum.inr ((![1,2,0,3] : Fin 4 → Fin 4) j))) (by decide) (by decide)

lemma twenty_three_contained_twenty_seven : Graph (representative 23) ⊑ Graph (representative 27) :=
  contained_of_map _ _ (Sum.elim
    (fun i => Sum.inl i)
    (fun j => Sum.inr ((![1,2,0,3] : Fin 4 → Fin 4) j))) (by decide) (by decide)

lemma twenty_four_contained_twenty_seven : Graph (representative 24) ⊑ Graph (representative 27) :=
  contained_of_map _ _ id (by decide) (by decide)

lemma remaining_middle_upper (k : Fin 32) (hk : k ∈ ({17,23,24,27} : Finset (Fin 32))) :
    (fun n : ℕ => (extremalNumber n (Graph (representative k)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((8 : ℝ)/5)) := by
  simp only [mem_insert,mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact (Erdos713Rate.extremal_mono_bigO seventeen_contained_twenty_seven).trans twenty_seven_upper
  · exact (Erdos713Rate.extremal_mono_bigO twenty_three_contained_twenty_seven).trans twenty_seven_upper
  · exact (Erdos713Rate.extremal_mono_bigO twenty_four_contained_twenty_seven).trans twenty_seven_upper
  · exact twenty_seven_upper


lemma irrational_rate_core_of_card_le_eight {W : Type} [Fintype W] (H : SimpleGraph W)
    (hBip : H.IsBipartite) (hcard : Fintype.card W ≤ 8)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) {α : ℝ} (hRate : Erdos713Rate.HasRate H α)
    (hIrr : α ∉ Set.range ((↑) : ℚ → ℝ)) :
    ∃ k : Fin 32, k ∈ ({1,17,23,24,27,31} : Finset (Fin 32)) ∧
      Nonempty (H ≃g Graph (representative k)) ∧
      ((k = 1 ∧ (6 : ℝ)/5 < α ∧ α < (5 : ℝ)/4) ∨
       (k ∈ ({17,23,24,27} : Finset (Fin 32)) ∧ (3 : ℝ)/2 < α ∧ α < (8 : ℝ)/5) ∨
       (k = 31 ∧ (5 : ℝ)/3 < α ∧ α < (7 : ℝ)/4)) := by
  obtain ⟨k,hk,⟨e⟩,hBounds⟩ := Erdos713EightCore.irrational_rate_core_of_card_le_eight
    H hBip hcard hd hRate hIrr
  have hKR := Erdos713Rate.iso_rate e.symm hRate
  have h16 : k ≠ 16 := by
    intro he
    subst k
    apply hIrr
    refine ⟨3/2,?_⟩
    simpa only [Rat.cast_div,Rat.cast_ofNat] using Erdos713Rate.rate_unique sixteen_rate hKR
  have h20 : k ≠ 20 := by
    intro he
    subst k
    apply hIrr
    refine ⟨3/2,?_⟩
    simpa only [Rat.cast_div,Rat.cast_ofNat] using Erdos713Rate.rate_unique twenty_rate hKR
  have hk' : k ∈ ({1,17,23,24,27,31} : Finset (Fin 32)) := by
    simp only [Exceptional,mem_insert,mem_singleton] at hk
    simp only [mem_insert,mem_singleton]
    tauto
  refine ⟨k,hk',⟨e⟩,?_⟩
  rcases hBounds with h1 | ⟨hne1,hne31,hlo,_⟩ | h31
  · exact Or.inl h1
  · have hmid : k ∈ ({17,23,24,27} : Finset (Fin 32)) := by
      simp only [mem_insert,mem_singleton] at hk' ⊢
      tauto
    refine Or.inr (Or.inl ⟨hmid,hlo,?_⟩)
    have hhi : α ≤ (8 : ℝ)/5 := hKR.lower _ (by norm_num) (remaining_middle_upper k hmid)
    apply lt_of_le_of_ne hhi
    intro he
    apply hIrr
    refine ⟨8/5,?_⟩
    simpa only [Rat.cast_div,Rat.cast_ofNat] using he.symm
  · exact Or.inr (Or.inr h31)

end Erdos713SuspensionEight
