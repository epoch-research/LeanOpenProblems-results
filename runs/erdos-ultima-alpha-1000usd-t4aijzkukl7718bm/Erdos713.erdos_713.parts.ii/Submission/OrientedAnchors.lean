import FormalConjecturesUtil
import Submission.CompactAssemblyAudit

/-! One-sided dependent random choice with two anchors, preserving the
bipartition placement of every vertex in the embedded forbidden graph. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713OrientedAnchors
open Erdos713C6 Erdos713DRC Erdos713Anchors

noncomputable def copyOfMaps {A B V : Type*} (R : A → B → Prop) (G : SimpleGraph V)
    (f : A → V) (g : B → V) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : ∀ a b, f a ≠ g b) (hadj : ∀ a b, R a b → G.Adj (f a) (g b)) :
    (bipGraph R).Copy G := by
  refine ⟨⟨Sum.elim f g,?_⟩,?_⟩
  · rintro (a | b) (a' | b') h
    · exact h.elim
    · exact hadj a b' h
    · exact (hadj a' b h).symm
    · exact h.elim
  · rintro (a | b) (a' | b') h
    · exact congrArg Sum.inl (hf h)
    · exact (hdis a b' h).elim
    · exact (hdis a' b h.symm).elim
    · exact congrArg Sum.inr (hg h)

open scoped Classical in
lemma oriented_copy_of_heavy_set {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Set V) (hB : G.IsBipartiteWith T Tᶜ)
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (z : Fin 2 ↪ V) (hz : ∀ i, z i ∉ T)
    (S : Finset V) (hS : Fintype.card A ≤ S.card) (hST : ∀ a ∈ S, a ∈ T)
    (hSz : ∀ a ∈ S, ∀ i, G.Adj a (z i))
    (hgood : ∀ x ∈ S, ∀ y ∈ S,
      Fintype.card A+Fintype.card B+2 ≤ Fintype.card (G.commonNeighbors x y)) :
    ∃ f : (bipGraph (augmented R)).Copy G,
      (∀ a, f (Sum.inl a) ∈ T) ∧ (∀ b, f (Sum.inr b) ∉ T) := by
  classical
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset hS
  choose u v huv using hR
  let L := (univ : Finset A).image f ∪ (univ : Finset (Fin 2)).image z
  let t : B → Finset V := fun b => (G.commonNeighbors (f (u b)) (f (v b))).toFinset \ L
  have hL : L.card ≤ Fintype.card A+2 := by
    apply (card_union_le _ _).trans
    exact Nat.add_le_add ((card_image_le).trans (by simp)) ((card_image_le).trans (by simp))
  have ht (b : B) : Fintype.card B ≤ (t b).card := by
    have hg := hgood (f (u b)) (hf ⟨u b,rfl⟩) (f (v b)) (hf ⟨v b,rfl⟩)
    have hh := card_le_card_sdiff_add_card (s := (G.commonNeighbors (f (u b)) (f (v b))).toFinset)
      (t := L)
    rw [Set.toFinset_card] at hh
    dsimp only [t]
    omega
  have hHall (U : Finset B) : U.card ≤ (U.biUnion t).card := by
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp
    obtain ⟨b,hb⟩ := hU
    exact (card_le_univ U).trans ((ht b).trans (card_le_card (subset_biUnion_of_mem t hb)))
  obtain ⟨g,hginj,hg⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hdis (a : A) (b : B) : f a ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_left _ (mem_image_of_mem f (mem_univ a)))
  have hdisz (i : Fin 2) (b : B) : z i ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_right _ (mem_image_of_mem z (mem_univ i)))
  have hgCommon (b : B) : g b ∈ G.commonNeighbors (f (u b)) (f (v b)) := by
    simpa only [Set.mem_toFinset] using (mem_sdiff.mp (hg b)).1
  have hAdj (a : A) (b : B) (hab : R a b) : G.Adj (f a) (g b) := by
    rcases huv b a hab with rfl | rfl
    · exact (hgCommon b).1
    · exact (hgCommon b).2
  have hinj : Function.Injective (Sum.elim z g) := by
    rintro (i | b) (j | b') hij
    · exact congrArg Sum.inl (z.injective hij)
    · exact (hdisz i b' hij).elim
    · exact (hdisz j b hij.symm).elim
    · exact congrArg Sum.inr (hginj hij)
  have hdis' : ∀ a b, f a ≠ Sum.elim z g b := by
    intro a b
    cases b with
    | inl i => exact (hSz (f a) (hf ⟨a,rfl⟩) i).ne
    | inr b => exact hdis a b
  have hAdj' : ∀ a b, augmented R a b → G.Adj (f a) (Sum.elim z g b) := by
    intro a b hab
    cases b with
    | inl i => exact hSz (f a) (hf ⟨a,rfl⟩) i
    | inr b => exact hAdj a b hab
  refine ⟨copyOfMaps (augmented R) G f (Sum.elim z g) f.injective hinj hdis' hAdj',?_,?_⟩
  · intro a
    exact hST (f a) (hf ⟨a,rfl⟩)
  · rintro (i | b)
    · exact hz i
    · exact hB.mem_of_mem_adj (hST (f (u b)) (hf ⟨u b,rfl⟩)) (hgCommon b).1

open scoped Classical in
lemma sum_degree_sq_eq_common_shore {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Set V) (hB : G.IsBipartiteWith T Tᶜ) :
    (∑ v ∈ T.toFinset, G.degree v^2) =
      ∑ p ∈ Tᶜ.toFinset ×ˢ Tᶜ.toFinset, Fintype.card (G.commonNeighbors p.1 p.2) := by
  classical
  let U := Tᶜ.toFinset ×ˢ Tᶜ.toFinset
  let r : V → V × V → Prop := fun x p => G.Adj x p.1 ∧ G.Adj x p.2
  have hAbove (v : V) (hv : v ∈ T.toFinset) : (U.bipartiteAbove r v).card = G.degree v^2 := by
    have hs : U.bipartiteAbove r v = G.neighborFinset v ×ˢ G.neighborFinset v := by
      ext p
      simp only [mem_bipartiteAbove,U,mem_product,mem_neighborFinset,r]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨⟨Set.mem_toFinset.mpr (hB.mem_of_mem_adj (Set.mem_toFinset.mp hv) h.1),
          Set.mem_toFinset.mpr (hB.mem_of_mem_adj (Set.mem_toFinset.mp hv) h.2)⟩,h⟩
    rw [hs,card_product,card_neighborFinset_eq_degree,pow_two]
  have hBelow (p : V × V) (hp : p ∈ U) : (T.toFinset.bipartiteBelow r p).card =
      Fintype.card (G.commonNeighbors p.1 p.2) := by
    have hp1 : p.1 ∈ Tᶜ := Set.mem_toFinset.mp (mem_product.mp hp).1
    have hs : T.toFinset.bipartiteBelow r p = (G.commonNeighbors p.1 p.2).toFinset := by
      ext v
      simp only [mem_bipartiteBelow,Set.mem_toFinset,mem_commonNeighbors,r]
      constructor
      · exact fun h => ⟨h.2.1.symm,h.2.2.symm⟩
      · exact fun h => ⟨hB.symm.mem_of_mem_adj hp1 h.1,h.1.symm,h.2.symm⟩
    rw [hs,Set.toFinset_card]
  calc
    _ = ∑ v ∈ T.toFinset, (U.bipartiteAbove r v).card :=
      sum_congr rfl (fun v hv => (hAbove v hv).symm)
    _ = ∑ p ∈ U, (T.toFinset.bipartiteBelow r p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ = _ := sum_congr rfl hBelow

open scoped Classical in
lemma degree_sq_le_of_no_heavy_shore {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Set V) (hB : G.IsBipartiteWith T Tᶜ)
    (s k : ℕ)
    (h : ∀ x ∈ Tᶜ, ∀ y ∈ Tᶜ, x ≠ y → ∀ S : Finset V,
      S ⊆ (G.commonNeighbors x y).toFinset →
      (∀ u ∈ S, ∀ v ∈ S, k ≤ Fintype.card (G.commonNeighbors u v)) → S.card ≤ s) :
    ∑ v ∈ T.toFinset, G.degree v^2 ≤ (s+k^2+1)*Fintype.card V^2 := by
  classical
  let U := Tᶜ.toFinset ×ˢ Tᶜ.toFinset
  let bad (p : V × V) := (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
      (G.commonNeighbors p.1 p.2).toFinset).filter
        (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card
  have hrow (p : V × V) (hp : p ∈ U) : Fintype.card (G.commonNeighbors p.1 p.2) ≤
      s+bad p+(if p.1 = p.2 then Fintype.card V else 0) := by
    by_cases he : p.1 = p.2
    · have hc : Fintype.card (G.commonNeighbors p.1 p.2) ≤ Fintype.card V :=
        Fintype.card_le_of_injective _ Subtype.val_injective
      simp only [if_pos he]
      omega
    · simp only [if_neg he,add_zero]
      obtain ⟨S,hS,hcard,hgood⟩ := clean_set G (G.commonNeighbors p.1 p.2).toFinset k
      rw [Set.toFinset_card] at hcard
      exact hcard.trans (Nat.add_le_add_right (h p.1 (Set.mem_toFinset.mp (mem_product.mp hp).1)
        p.2 (Set.mem_toFinset.mp (mem_product.mp hp).2) he S hS hgood) _)
  have hbad : ∑ p ∈ U, bad p ≤ k^2*Fintype.card V^2 := by
    exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)).trans (sum_bad_pairs_le G k)
  have hdiag : (∑ p ∈ U, if p.1 = p.2 then Fintype.card V else 0) ≤ Fintype.card V^2 := by
    have hh : (∑ p : V × V, if p.1 = p.2 then Fintype.card V else 0) = Fintype.card V^2 := by
      simp [Fintype.sum_prod_type,pow_two]
    rw [← hh]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hconst : (∑ _p ∈ U, s) ≤ s*Fintype.card V^2 := by
    have hc : U.card ≤ Fintype.card V^2 := by simpa [Fintype.card_prod,pow_two] using card_le_univ U
    simpa [mul_comm] using Nat.mul_le_mul_left s hc
  rw [sum_degree_sq_eq_common_shore G T hB]
  calc
    _ ≤ ∑ p ∈ U, (s+bad p+(if p.1 = p.2 then Fintype.card V else 0)) := sum_le_sum hrow
    _ ≤ s*Fintype.card V^2+k^2*Fintype.card V^2+Fintype.card V^2 := by
      simp only [sum_add_distrib]
      exact Nat.add_le_add (Nat.add_le_add hconst hbad) hdiag
    _ = _ := by ring

open scoped Classical in
lemma edge_sq_le_of_no_oriented_copy {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Set V) (hB : G.IsBipartiteWith T Tᶜ)
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (hno : ∀ f : (bipGraph (augmented R)).Copy G,
      (∀ a, f (Sum.inl a) ∈ T) → (∀ b, f (Sum.inr b) ∉ T) → False) :
    G.edgeFinset.card^2 ≤
      (Fintype.card A+(Fintype.card A+Fintype.card B+2)^2+1)*Fintype.card V^3 := by
  classical
  have hb := degree_sq_le_of_no_heavy_shore G T hB (Fintype.card A)
    (Fintype.card A+Fintype.card B+2) (by
      intro x hx y hy hxy S hS hgood
      by_contra hcard
      let z : Fin 2 ↪ V := ⟨![x,y],by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
      have hz : ∀ i, z i ∉ T := by intro i; fin_cases i <;> assumption
      have hST : ∀ v ∈ S, v ∈ T := by
        intro v hv
        have hh : v ∈ G.commonNeighbors x y := Set.mem_toFinset.mp (hS hv)
        exact hB.symm.mem_of_mem_adj hx hh.1
      have hSz : ∀ v ∈ S, ∀ i, G.Adj v (z i) := by
        intro v hv i
        have hh : v ∈ G.commonNeighbors x y := Set.mem_toFinset.mp (hS hv)
        fin_cases i
        · exact hh.1.symm
        · exact hh.2.symm
      obtain ⟨f,hf,hf'⟩ := oriented_copy_of_heavy_set R G T hB hR z hz S (by omega) hST hSz hgood
      exact hno f hf hf')
  have hc := sq_sum_le_card_mul_sum_sq (s := T.toFinset) (f := fun v => G.degree v)
  have hE : ∑ v ∈ T.toFinset, G.degree v = G.edgeFinset.card :=
    isBipartiteWith_sum_degrees_eq_card_edges (s := T.toFinset) (t := Tᶜ.toFinset) (by simpa using hB)
  rw [hE] at hc
  have hmult := Nat.mul_le_mul (card_le_univ T.toFinset) hb
  exact hc.trans (by convert hmult using 1 <;> ring)

open scoped Classical in
lemma edge_sq_le_of_root_excluded {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (hB : G.IsBipartiteWith S Sᶜ)
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (x : A ⊕ (Fin 2 ⊕ B))
    (hroot : ∀ f : (bipGraph (augmented R)).Copy G, f x ∉ S) :
    G.edgeFinset.card^2 ≤
      (Fintype.card A+(Fintype.card A+Fintype.card B+2)^2+1)*Fintype.card V^3 := by
  classical
  cases x with
  | inl a =>
    exact edge_sq_le_of_no_oriented_copy R G S hB hR (fun f hf _ => hroot f (hf a))
  | inr b =>
    apply edge_sq_le_of_no_oriented_copy R G Sᶜ (by simpa using hB.symm) hR
    intro f _ hf
    exact hroot f (not_not.mp (hf b))

#print axioms oriented_copy_of_heavy_set
#print axioms edge_sq_le_of_root_excluded
end Erdos713OrientedAnchors
