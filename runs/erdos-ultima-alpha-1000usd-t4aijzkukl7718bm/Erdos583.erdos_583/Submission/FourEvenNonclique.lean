import Submission.FiveEvenBound

/-! The ceiling-half bound when exactly four even vertices do not form a clique. -/
namespace Erdos583FourEvenNoncliqueDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.ComponentDeficit Erdos583Work.PendantCompletion Erdos583Work.BridgeGlue
open Erdos583ThreeEvenNontriangleDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma evenCount_leaf_at_even (r : V) (hr : Even (Nat.card (G.neighborSet r))) :
    evenCount (leafCompletion G {r})+1=evenCount G := by
  classical
  let S := {x | Even (Nat.card (G.neighborSet x))}
  have heq : {x | Even (Nat.card ((leafCompletion G {r}).neighborSet x))}=
      Sum.inl '' (S \ {r}) := by
    ext x
    cases x with
    | inl v =>
      simp only [Set.mem_setOf_eq,original_neighbor_ncard,Set.mem_singleton_iff,
        Set.mem_image,Set.mem_diff,Sum.inl.injEq]
      by_cases hvr : v=r
      · subst v
        simp only [exists_eq_right,and_false,not_true_eq_false]
        exact iff_false_intro (Nat.not_even_iff_odd.mpr (hr.add_odd odd_one))
      · simp only [exists_eq_right,hvr,↓reduceIte,not_false_eq_true,and_true,S,
          Set.mem_setOf_eq,add_zero]
    | inr v =>
      simp only [Set.mem_setOf_eq,leaf_neighbor_ncard,Set.mem_image,Sum.inl_ne_inr,and_false,
        exists_false,Nat.not_even_one]
  have hc := Set.ncard_diff_add_ncard_of_subset (show ({r} : Set V) ⊆ S from
    Set.singleton_subset_iff.mpr hr)
  rw [Set.ncard_singleton] at hc
  simpa only [evenCount,heq,Set.ncard_image_of_injective _ Sum.inl_injective,S] using hc

lemma four_even_nonclique (he : evenCount G=4) {c d : V} (hcd : c ≠ d)
    (hc : Even (Nat.card (G.neighborSet c))) (hd : Even (Nat.card (G.neighborSet d)))
    (hmissing : ¬G.Adj c d) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  let S := {x | Even (Nat.card (G.neighborSet x))} \ {c,d}
  have hcard : S.ncard=2 := by
    have hsub : ({c,d} : Set V) ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
      rintro x (rfl|rfl) <;> assumption
    have hh := Set.ncard_diff_add_ncard_of_subset hsub
    rw [Set.ncard_pair hcd] at hh
    change S.ncard+2=evenCount G at hh
    omega
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite S)).mp (by omega : 0 < S.ncard)
  have hcr : c ≠ r := fun h ↦ hr.2 (Or.inl h.symm)
  have hdr : d ≠ r := fun h ↦ hr.2 (Or.inr h.symm)
  let H := leafCompletion G {r}
  have hcount : evenCount H=3 := by
    have hh := evenCount_leaf_at_even (G := G) r hr.1
    change evenCount H+1=evenCount G at hh
    omega
  have hce : Even (Nat.card (H.neighborSet (.inl c))) := by
    rw [original_neighbor_ncard]
    simpa only [Set.mem_singleton_iff,if_neg hcr,add_zero] using hc
  have hde : Even (Nat.card (H.neighborSet (.inl d))) := by
    rw [original_neighbor_ncard]
    simpa only [Set.mem_singleton_iff,if_neg hdr,add_zero] using hd
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_not_clique H hcount (Sum.inl_injective.ne hcd)
    hce hde hmissing
  obtain ⟨E,a,P,hE,_,_,hEc⟩ := CutVertexReduction.project_single_leaf_marked r D hD
  have hn : Fintype.card (V ⊕ ({r} : Set V))=Fintype.card V+1 := by simp
  rw [hn] at hDc
  exact ⟨E,hE,by rw [ceil_half]; omega⟩

lemma four_even_failure_clique (he : evenCount G=4)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∀ a b, Even (Nat.card (G.neighborSet a)) →
      Even (Nat.card (G.neighborSet b)) → a ≠ b → G.Adj a b := by
  intro a b ha hb hab
  by_contra hm
  exact hf (four_even_nonclique he hab ha hb hm)

end Erdos583FourEvenNoncliqueDevelopment
