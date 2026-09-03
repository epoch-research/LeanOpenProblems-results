import FormalConjecturesUtil
import Submission.NearOptimalPruning

/-! Pruning a small edge loss from a finite expander. -/
open SimpleGraph Finset
namespace Erdos713QuantitativeExpanderPruning
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
    ∃ U : Finset V, 8*U.card ≤ Fintype.card V ∧ h*(U.card : ℝ) ≤ 2*L ∧
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
  have hBound : h*(U.card : ℝ) ≤ 2*L := by
    linarith
  refine ⟨U,hUsmall,hBound,?_⟩
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


lemma cross_singleton_card {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Nat.card (cross G {v}).edgeSet = Nat.card (G.neighborSet v) := by
  classical
  have he : (cross G {v}).edgeFinset = G.incidenceFinset v := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [mem_edgeFinset,mem_incidenceFinset,mk'_mem_incidenceSet_iff,cross,Set.mem_singleton_iff]
      constructor
      · rintro ⟨hab,⟨ha,_⟩ | ⟨hb,_⟩⟩
        · exact ⟨hab,Or.inl ha.symm⟩
        · exact ⟨hab,Or.inr hb.symm⟩
      · rintro ⟨hab,ha | hb⟩
        · subst a
          exact ⟨hab,Or.inl ⟨rfl,hab.ne.symm⟩⟩
        · subst b
          exact ⟨hab,Or.inr ⟨rfl,hab.ne⟩⟩
  have hh := congrArg Finset.card he
  rw [card_incidenceFinset_eq_degree] at hh
  simpa only [edgeFinset_card,← card_neighborSet_eq_degree,Fintype.card_eq_nat_card] using hh

open scoped Classical in
lemma cut_induce_image {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (S : Finset U) :
    Nat.card (cross (G.induce (U : Set V)) (S : Set U)).edgeSet =
      Nat.card (cross (inside G (U : Set V)) ((S.image Subtype.val : Finset V) : Set V)).edgeSet := by
  classical
  let f : U ↪ V := Function.Embedding.subtype (fun v => v ∈ U)
  have hm (a : U) : a.val ∈ S.image Subtype.val ↔ a ∈ S := by
    simp only [mem_image,Subtype.val_inj,exists_eq_right]
  have he : (cross (G.induce (U : Set V)) (S : Set U)).map f =
      cross (inside G (U : Set V)) ((S.image Subtype.val : Finset V) : Set V) := by
    ext u v
    rw [map_adj]
    constructor
    · rintro ⟨a,b,hab,rfl,rfl⟩
      change G.Adj a.val b.val ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)) at hab
      change (G.Adj a.val b.val ∧ a.val ∈ U ∧ b.val ∈ U) ∧
        ((a.val ∈ S.image Subtype.val ∧ b.val ∉ S.image Subtype.val) ∨
          (b.val ∈ S.image Subtype.val ∧ a.val ∉ S.image Subtype.val))
      simpa only [hm] using And.intro ⟨hab.1,a.prop,b.prop⟩ hab.2
    · rintro ⟨⟨huv,hu,hv⟩,hab⟩
      let a : U := ⟨u,hu⟩
      let b : U := ⟨v,hv⟩
      refine ⟨a,b,?_,rfl,rfl⟩
      change G.Adj u v ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S))
      exact ⟨huv,by simpa only [← hm a,← hm b] using hab⟩
  have hc := card_edgeFinset_map f (cross (G.induce (U : Set V)) (S : Set U))
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hc
  rw [he] at hc
  exact hc.symm

lemma degree_induce_le {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V) (v : U) :
    Nat.card ((G.induce (U : Set V)).neighborSet v) ≤ Nat.card (G.neighborSet v.val) := by
  let f := (Copy.induce G (U : Set V)).mapNeighborSet v
  exact Nat.card_le_card_of_injective f f.injective


lemma inside_eq_spanningCoe {V : Type*} (G : SimpleGraph V) (S : Set V) :
    inside G S = (G.induce S).spanningCoe := by
  ext v w
  constructor
  · rintro ⟨h,hv,hw⟩
    exact ⟨⟨v,hv⟩,⟨w,hw⟩,h,rfl,rfl⟩
  · rintro ⟨a,b,h,rfl,rfl⟩
    exact ⟨h,a.property,b.property⟩

lemma inside_card {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    Nat.card (inside G S).edgeSet = Nat.card (G.induce S).edgeSet := by
  classical
  rw [inside_eq_spanningCoe]
  have hh := card_edgeFinset_map (Function.Embedding.subtype (fun v => v ∈ S)) (G.induce S)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh

open scoped Classical in
/-- Vertex deletion followed by expander pruning. The bound explicitly
retains the original deleted set and its edge-loss budget. -/
lemma prune_vertex_expander {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) {h L : ℝ} (hh : 0 < h)
    (hExp : ∀ A : Finset V, 2*A.card ≤ Fintype.card V →
      h*A.card ≤ (Nat.card (cross G (A : Set V)).edgeSet : ℝ))
    (hLoss : (Nat.card G.edgeSet : ℝ) ≤ Nat.card (G.induce (S : Set V)ᶜ).edgeSet+L)
    (hSmall : L ≤ h*(Fintype.card V : ℝ)/16) :
    ∃ T : Finset V, S ⊆ T ∧ h*(T.card : ℝ) ≤ h*S.card+2*L ∧
      ∀ A : Finset V, A ⊆ Tᶜ → 2*A.card ≤ Fintype.card V-T.card →
        h/4*A.card ≤
          (Nat.card (cross (inside G ((Tᶜ : Finset V) : Set V)) (A : Set V)).edgeSet : ℝ) := by
  classical
  let K := inside G (S : Set V)ᶜ
  have hK : K ≤ G := inside_le G _
  have hLoss' : (Nat.card G.edgeSet : ℝ) ≤ Nat.card K.edgeSet+L := by
    simpa only [K,inside_card] using hLoss
  obtain ⟨U,hU,hUBound,hCuts⟩ := exists_pruned_expander G K hK hh hExp hLoss' hSmall
  let T := S ∪ U
  have hST : S ⊆ T := subset_union_left
  have hUT : U ⊆ T := subset_union_right
  have hTCard : (T.card : ℝ) ≤ (S.card : ℝ)+U.card := by
    exact_mod_cast card_union_le S U
  have hTBound : h*(T.card : ℝ) ≤ h*S.card+2*L := by
    have hm := mul_le_mul_of_nonneg_left hTCard hh.le
    linarith
  refine ⟨T,hST,hTBound,?_⟩
  intro A hAT hSize
  have hAU : A ⊆ Uᶜ := by
    intro v hv
    exact mem_compl.mpr (fun hvu => (mem_compl.mp (hAT hv)) (hUT hvu))
  have hSizeU : 2*A.card ≤ Fintype.card V-U.card := by
    have hh' := card_le_card hUT
    omega
  have hCut := hCuts A hAU hSizeU
  have heq : inside K ((Uᶜ : Finset V) : Set V) = inside G ((Tᶜ : Finset V) : Set V) := by
    ext v w
    simp only [inside,K,T,Finset.mem_coe,mem_compl,mem_union,Set.mem_compl_iff]
    tauto
  simpa only [heq] using hCut

#print axioms exists_pruned_expander
#print axioms cross_singleton_card
#print axioms cut_induce_image
#print axioms inside_card
#print axioms prune_vertex_expander
end Erdos713QuantitativeExpanderPruning
