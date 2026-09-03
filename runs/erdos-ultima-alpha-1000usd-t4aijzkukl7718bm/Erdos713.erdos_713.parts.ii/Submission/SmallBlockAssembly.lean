import FormalConjecturesUtil
import Submission.CompactRootAssemblyAudit
import Submission.BlockDecomposition

/-! Graph-theoretic assembly from a condition on all connected no-cut
subgraphs, rather than from a supplied gluing certificate. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713Blocks
open Erdos713RootAssembly Erdos713Gluing
universe u

/-- Every finite connected no-cut subgraph has a bipartition shore of size
at most three. This is a structural hypothesis, not a claim about all graphs. -/
def SmallPieces {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ {T : Type u} [Fintype T] (H : SimpleGraph T), H ⊑ G → H.Connected → NoCut H →
    ∃ S : Set T, H.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3

lemma SmallPieces.of_contained {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
    (h : SmallPieces G) (hHG : H ⊑ G) : SmallPieces H := by
  intro A _ J hJ hConn hNC
  exact h J (hJ.trans hHG) hConn hNC


/-- The same small-shore condition, stated just for induced no-cut pieces. -/
def InducedSmallPieces {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, (G.induce S).Connected → NoCut (G.induce S) →
    ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3

lemma small_shore_of_copy {W T : Type u} [Fintype W] [Fintype T]
    {G : SimpleGraph W} {H : SimpleGraph T} (f : H.Copy G) (S : Set W)
    (hS : G.IsBipartiteWith S Sᶜ) (hc : Nat.card S ≤ 3) :
    ∃ A : Set T, H.IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 := by
  classical
  refine ⟨f ⁻¹' S,⟨disjoint_compl_right,fun _ _ hab => hS.2 (f.toHom.map_adj hab)⟩,?_⟩
  let e : ↥(f ⁻¹' S) ↪ S :=
    ⟨fun a => ⟨f a.val,a.prop⟩,fun a b he => Subtype.ext (f.injective (congrArg Subtype.val he))⟩
  have he := Fintype.card_le_of_embedding e
  simp only [Fintype.card_eq_nat_card] at he
  exact he.trans hc

lemma induced_small_pieces_iff {W : Type u} [Fintype W] {G : SimpleGraph W} :
    InducedSmallPieces G ↔ SmallPieces G := by
  classical
  constructor
  · intro h T _ H hHG hH hNC
    obtain ⟨f⟩ := hHG
    let g : H.Copy (G.induce (Set.range f)) :=
      ⟨⟨fun a => ⟨f a,⟨a,rfl⟩⟩,fun hab => f.toHom.map_adj hab⟩,
        fun a b he => f.injective (congrArg Subtype.val he)⟩
    have hg : Function.Surjective g := by
      rintro ⟨v,⟨a,rfl⟩⟩
      exact ⟨a,rfl⟩
    obtain ⟨A,hA,hcard⟩ := h (Set.range f) (hH.map g.toHom hg)
      (hNC.map g.toHom ⟨g.injective,hg⟩)
    exact small_shore_of_copy g A hA hcard
  · intro h S hS hNC
    exact h (G.induce S) ⟨Copy.induce G S⟩ hS hNC


/-- Every block has a bipartition shore of size at most three. -/
def SmallBlocks {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, IsBlock G S →
    ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3

lemma small_blocks_iff_induced {W : Type u} [Fintype W] {G : SimpleGraph W} :
    SmallBlocks G ↔ InducedSmallPieces G := by
  classical
  constructor
  · intro h S hConn hNC
    obtain ⟨T,hST,hT⟩ := exists_block_superset S hConn hNC
    obtain ⟨A,hA,hcard⟩ := h T hT
    exact small_shore_of_copy (induceHomOfLE G hST).toCopy A hA hcard
  · intro h S hS
    exact h S hS.connected hS.noCut

noncomputable def lobeWedgeIso {W : Type u} {G : SimpleGraph W} {S : Set W} {x : W}
    (h : Lobe G S x) :
    wedge (G.induce S) ⟨x,h.root_mem⟩ (G.induce (insert x Sᶜ)) ⟨x,Or.inl rfl⟩ ≃g G := by
  classical
  let y : ↥(insert x Sᶜ) := ⟨x,Or.inl rfl⟩
  let f : S ⊕ {b : ↥(insert x Sᶜ) // b ≠ y} → W :=
    Sum.elim Subtype.val (fun b => b.val.val)
  have hright (b : {b : ↥(insert x Sᶜ) // b ≠ y}) : b.val.val ∉ S := by
    exact (Set.mem_insert_iff.mp b.val.prop).resolve_left (fun he => b.prop (Subtype.ext he))
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) he <;> dsimp [f] at he
    · exact congrArg Sum.inl (Subtype.ext he)
    · exact (hright b (he ▸ a.prop)).elim
    · exact (hright a (he.symm ▸ b.prop)).elim
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext he))
  have hsurj : Function.Surjective f := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
    · refine ⟨Sum.inr ⟨⟨v,Or.inr hv⟩,?_⟩,rfl⟩
      intro he
      have hvx : v = x := congrArg (fun q : ↥(insert x Sᶜ) => q.val) he
      exact hv (hvx.symm ▸ h.root_mem)
  refine ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,?_⟩
  rintro (a | a) (b | b)
  · exact Iff.rfl
  · change G.Adj a.val b.val.val ↔ a = ⟨x,h.root_mem⟩ ∧ G.Adj x b.val.val
    constructor
    · intro hab
      have he : a.val = x := by
        by_contra he
        exact hright b (h.closed a.val a.prop he b.val.val hab)
      exact ⟨Subtype.ext he,he ▸ hab⟩
    · rintro ⟨rfl,hab⟩; exact hab
  · change G.Adj a.val.val b.val ↔ b = ⟨x,h.root_mem⟩ ∧ G.Adj a.val.val x
    constructor
    · intro hab
      have he : b.val = x := by
        by_contra he
        exact hright a (h.closed b.val b.prop he a.val.val hab.symm)
      exact ⟨Subtype.ext he,he ▸ hab⟩
    · rintro ⟨rfl,hab⟩; exact hab
  · exact Iff.rfl

lemma small_pieces_assembly {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : SmallPieces G) : Assembly G := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → SmallPieces G → Assembly G from
    hh _ W G rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ G hcard h
    by_cases hConn : G.Connected
    · by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
      · obtain ⟨S,x,hL,hHConn,hHNC,hHd⟩ := exists_end_piece hConn hd
        obtain ⟨A,hA,hAs⟩ := h (G.induce S) ⟨Copy.induce G S⟩ hHConn hHNC
        by_cases hS : S = Set.univ
        · subst S
          exact .iso (induceUnivIso G).symm (.side _ A hA hAs)
        let T : Set W := insert x Sᶜ
        have hT := hL.complement hS
        have hsmall : Fintype.card T < n := by
          obtain ⟨v,hv,hvx⟩ := hL.other
          have hn : v ∉ T := by simpa only [T,Set.mem_insert_iff,Set.mem_compl_iff,not_or,not_not] using ⟨hvx,hv⟩
          exact (Fintype.card_subtype_lt (x := v) hn).trans_eq hcard
        have hJ : Assembly (G.induce T) := ih _ hsmall T (G.induce T) rfl
          (h.of_contained ⟨Copy.induce G T⟩)
        have hroot := hT.root_adj hConn
        exact .iso (lobeWedgeIso hL).symm
          (.wedgeSmallCore (G.induce S) ⟨x,hL.root_mem⟩ A hA hAs hHd
            (G.induce T) ⟨x,hT.root_mem⟩ hroot hJ)
      · push_neg at hd
        obtain ⟨x,hx⟩ := hd
        have hsmall : Fintype.card ↥({x}ᶜ : Set W) < n :=
          (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hcard
        have hJ : Assembly (G.induce {x}ᶜ) := ih _ hsmall _ _ rfl
          (h.of_contained ⟨Copy.induce G {x}ᶜ⟩)
        have hx' : Nat.card ((G.induce Set.univ).neighborSet ⟨x,Set.mem_univ x⟩) ≤ 1 := by
          rw [Nat.card_congr ((induceUnivIso G).mapNeighborSet ⟨x,Set.mem_univ x⟩)]
          exact Nat.le_of_lt_succ hx
        have hp : Erdos713Pruning.PrunesTo G {x}ᶜ := by
          convert Erdos713Pruning.PrunesTo.delete (.start (G := G)) ⟨x,Set.mem_univ x⟩ hx' using 1
          ext v
          simp
        exact .prunes G _ hp hJ
    · apply Assembly.components G
      intro C
      let f : C.toSimpleGraph.Copy G := ⟨C.toSimpleGraph_hom,Subtype.val_injective⟩
      have hns : ¬ Function.Surjective (fun v : C => v.val) := by
        intro hs
        exact hConn (C.connected_toSimpleGraph.map C.toSimpleGraph_hom hs)
      have hsmall := (Fintype.card_lt_of_injective_not_surjective
        (fun v : C => v.val) Subtype.val_injective hns).trans_eq hcard
      exact ih _ hsmall C C.toSimpleGraph rfl (h.of_contained ⟨f⟩)

lemma rational_of_small_pieces {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : SmallPieces G) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) :=
  (small_pieces_assembly G h).rational hα hc hAsymptotic


lemma induced_small_pieces_assembly {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : InducedSmallPieces G) : Assembly G :=
  small_pieces_assembly G (induced_small_pieces_iff.mp h)

lemma exists_large_noCut_of_not_assembly {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite) (hG : ¬ Assembly G) :
    ∃ S : Set W, (G.induce S).Connected ∧ NoCut (G.induce S) ∧
      (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      ∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A := by
  classical
  have hn : ¬ InducedSmallPieces G := fun h => hG (induced_small_pieces_assembly G h)
  unfold InducedSmallPieces at hn
  push_neg at hn
  obtain ⟨S,hConn,hNC,hS⟩ := hn
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc : 8 ≤ Nat.card S := by
    by_contra hc
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hS A hA)
  refine ⟨S,hConn,hNC,hSB,hc,hNC.min_degree hConn ?_,?_⟩
  · simpa only [Fintype.card_eq_nat_card] using (show 3 ≤ Nat.card S by omega)
  · intro A hA
    exact hS A hA


lemma small_blocks_assembly {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : SmallBlocks G) : Assembly G :=
  induced_small_pieces_assembly G (small_blocks_iff_induced.mp h)

lemma rational_of_small_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : SmallBlocks G) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) :=
  (small_blocks_assembly G h).rational hα hc hAsymptotic

lemma assembly_of_block_card_le_seven {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite)
    (hcard : ∀ S : Set W, IsBlock G S → Nat.card S ≤ 7) : Assembly G := by
  classical
  apply small_blocks_assembly G
  intro S hS
  exact Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S)
    (Colorable.of_hom (Copy.induce G S).toHom hB)
    (by simpa only [Fintype.card_eq_nat_card] using hcard S hS)

lemma exists_large_block_of_not_assembly {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite) (hG : ¬ Assembly G) :
    ∃ S : Set W, IsBlock G S ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      ∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A := by
  classical
  have hn : ¬ SmallBlocks G := fun h => hG (small_blocks_assembly G h)
  unfold SmallBlocks at hn
  push_neg at hn
  obtain ⟨S,hBlock,hS⟩ := hn
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc : 8 ≤ Nat.card S := by
    by_contra hc
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hS A hA)
  refine ⟨S,hBlock,hSB,hc,hBlock.noCut.min_degree hBlock.connected ?_,?_⟩
  · simpa only [Fintype.card_eq_nat_card] using (show 3 ≤ Nat.card S by omega)
  · intro A hA
    exact hS A hA

#print axioms lobeWedgeIso
#print axioms small_pieces_assembly
#print axioms rational_of_small_pieces
#print axioms induced_small_pieces_iff
#print axioms exists_large_noCut_of_not_assembly
#print axioms small_blocks_assembly
#print axioms rational_of_small_blocks
#print axioms assembly_of_block_card_le_seven
#print axioms exists_large_block_of_not_assembly
end Erdos713Blocks
