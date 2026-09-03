import FormalConjecturesUtil
import Submission.ExpandingWitnesses

/-! Pruning a small edge loss from a finite expander. -/
open SimpleGraph Finset
namespace Erdos713ExpanderPruning
open Erdos713SwitchGluing

lemma cross_compl {V : Type*} (G : SimpleGraph V) (S : Set V) : cross G Sᶜ = cross G S := by
  ext u v
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [cross,hu,hv]

lemma cut_loss {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G) (S : Set V) :
    Nat.card (cross G S).edgeSet + Nat.card K.edgeSet ≤
      Nat.card G.edgeSet + Nat.card (cross K S).edgeSet := by
  classical
  have hi : (cross G S).edgeFinset ∩ K.edgeFinset = (cross K S).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      simp only [mem_inter,mem_edgeFinset,cross]
      constructor
      · rintro ⟨⟨_,hh⟩,hk⟩
        exact ⟨hk,hh⟩
      · rintro ⟨hk,hh⟩
        exact ⟨⟨hKG hk,hh⟩,hk⟩
  have hu : (cross G S).edgeFinset ∪ K.edgeFinset ⊆ G.edgeFinset :=
    union_subset (edgeFinset_mono (cross_le G S)) (edgeFinset_mono hKG)
  have hc := card_union_add_card_inter (cross G S).edgeFinset K.edgeFinset
  rw [hi] at hc
  have hle := card_le_card hu
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hc hle
  omega

open scoped Classical in
lemma cut_union_le {V : Type*} [Fintype V] (G : SimpleGraph V) (U S : Finset V) :
    Nat.card (cross G ((U ∪ S : Finset V) : Set V)).edgeSet ≤
      Nat.card (cross G (U : Set V)).edgeSet +
        Nat.card (cross (inside G ((Uᶜ : Finset V) : Set V)) (S : Set V)).edgeSet := by
  classical
  have hsub : (cross G ((U ∪ S : Finset V) : Set V)).edgeFinset ⊆
      (cross G (U : Set V)).edgeFinset ∪
        (cross (inside G ((Uᶜ : Finset V) : Set V)) (S : Set V)).edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;>
        by_cases hus : u ∈ S <;> by_cases hvs : v ∈ S <;>
          simp_all [cross,inside]
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh

open scoped Classical in
lemma exists_pruned_expander {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G)
    {h L : ℝ} (hh : 0 < h)
    (hExp : ∀ S : Finset V, 2*S.card ≤ Fintype.card V →
      h*S.card ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ))
    (hLoss : (Nat.card G.edgeSet : ℝ) ≤ Nat.card K.edgeSet + L)
    (hSmall : L ≤ h*(Fintype.card V : ℝ)/16) :
    ∃ U : Finset V, 8*U.card ≤ Fintype.card V ∧
      ∀ S : Finset V, S ⊆ Uᶜ → 2*S.card ≤ Fintype.card V-U.card →
        h/4*S.card ≤
          (Nat.card (cross (inside K ((Uᶜ : Finset V) : Set V)) (S : Set V)).edgeSet : ℝ) := by
  classical
  let phi : Finset V → ℝ := fun U => h/2*U.card - Nat.card (cross K (U : Set V)).edgeSet
  let T : Finset (Finset V) := univ.filter (fun U => 2*U.card ≤ Fintype.card V)
  obtain ⟨U,hU,hMax⟩ := exists_max_image T phi ⟨∅,by simp [T]⟩
  have hUhalf : 2*U.card ≤ Fintype.card V := (mem_filter.mp hU).2
  have hEmpty : phi ∅ = 0 := by
    have heq : cross K (∅ : Set V) = ⊥ := by ext u v; simp [cross]
    simp [phi,heq]
  have hPhi := hMax ∅ (by simp [T])
  rw [hEmpty] at hPhi
  have hKU : (Nat.card (cross K (U : Set V)).edgeSet : ℝ) ≤ h/2*U.card := by
    dsimp only [phi] at hPhi
    linarith
  have hULoss := cut_loss G K hKG (U : Set V)
  have hULossReal : (Nat.card (cross G (U : Set V)).edgeSet : ℝ) + Nat.card K.edgeSet ≤
      Nat.card G.edgeSet + Nat.card (cross K (U : Set V)).edgeSet := by exact_mod_cast hULoss
  have hUE := hExp U hUhalf
  have hUsmall : 8*U.card ≤ Fintype.card V := by
    have hm : h*((8 : ℝ)*U.card) ≤ h*Fintype.card V := by nlinarith
    have hh' := (mul_le_mul_iff_right₀ hh).mp hm
    exact_mod_cast hh'
  refine ⟨U,hUsmall,?_⟩
  intro S hSU hSsize
  have hDis : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvS
    exact (mem_compl.mp (hSU hvS)) hvU
  have hCard : (U ∪ S).card = U.card + S.card := card_union_of_disjoint hDis
  have hUnion := cut_union_le K U S
  have hUnionReal : (Nat.card (cross K ((U ∪ S : Finset V) : Set V)).edgeSet : ℝ) ≤
      Nat.card (cross K (U : Set V)).edgeSet +
        Nat.card (cross (inside K ((Uᶜ : Finset V) : Set V)) (S : Set V)).edgeSet := by
    exact_mod_cast hUnion
  by_cases hHalf : 2*(U ∪ S).card ≤ Fintype.card V
  · have hM := hMax (U ∪ S) (by simp [T,hHalf])
    dsimp only [phi] at hM
    rw [hCard,Nat.cast_add] at hM
    have hs : (0 : ℝ) ≤ h*S.card := mul_nonneg hh.le (Nat.cast_nonneg _)
    linarith
  · have hComp : 2*((U ∪ S)ᶜ).card ≤ Fintype.card V := by
      rw [card_compl]
      have huN : (U ∪ S).card ≤ Fintype.card V := card_le_univ _
      omega
    have hM := hMax ((U ∪ S)ᶜ) (mem_filter.mpr ⟨mem_univ _,hComp⟩)
    dsimp only [phi] at hM
    have heq : cross K (((U ∪ S)ᶜ : Finset V) : Set V) =
        cross K ((U ∪ S : Finset V) : Set V) := by
      simpa only [coe_compl] using cross_compl K ((U ∪ S : Finset V) : Set V)
    rw [heq] at hM
    have hCount : 2*U.card+S.card ≤ 2*((U ∪ S)ᶜ).card := by
      rw [card_compl,hCard]
      rw [hCard] at hHalf
      omega
    have hCountReal : 2*(U.card : ℝ)+S.card ≤ 2*(((U ∪ S)ᶜ).card : ℝ) := by
      exact_mod_cast hCount
    have hm := mul_le_mul_of_nonneg_left hCountReal hh.le
    nlinarith

#print axioms exists_pruned_expander
end Erdos713ExpanderPruning
