import FormalConjecturesUtil
import Submission.RootSymmetry

/-! Rational-rate assembly allowing ten-cycle pieces and arbitrary pieces
with a proved matching rational rooted power bound. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713CycleAssembly
open Erdos713Rate Erdos713Gluing Erdos713RootPower Erdos713Blocks
universe u

inductive Assembly : {W : Type u} → SimpleGraph W → Prop where
  | old {W : Type u} {G : SimpleGraph W} (h : Erdos713RootAssembly.Assembly G) : Assembly G
  | iso {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
      (e : G ≃g H) (h : Assembly H) : Assembly G
  | components {W : Type u} [Fintype W] (G : SimpleGraph W)
      (h : ∀ C : G.ConnectedComponent, Assembly C.toSimpleGraph) : Assembly G
  | prunes {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
      (hp : Erdos713Pruning.PrunesTo G S) (h : Assembly (G.induce S)) : Assembly G
  | ten {W : Type u} (G : SimpleGraph W)
      (hlo : Erdos713C10.C10 ⊑ G) (hhi : G ⊑ Erdos713C10.C10) : Assembly G
  | wedgeRooted {W T : Type u} [Fintype W] [Fintype T]
      (H : SimpleGraph W) (x : W) (hNoIso : ∀ v, ∃ w, H.Adj v w)
      (a : ℚ) (hH : HasRate H (a : ℝ)) (hRoot : RootPowerBound H x (a : ℝ))
      (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z) (hJ : Assembly J) :
      Assembly (wedge H x J y)

lemma Assembly.side {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
    (hB : G.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3) : Assembly G :=
  .old (.side G S hB hS)

lemma Assembly.rate {W : Type u} {G : SimpleGraph W} (h : Assembly G) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  induction h with
  | old h => exact h.rate
  | iso e h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,iso_rate e hr⟩
  | components G h ih => exact Erdos713ComponentRates.rate_of_components G ih
  | prunes G S hp h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,hp.rate hr⟩
  | ten G hlo hhi => exact ⟨6/5,by simpa using Erdos713C10.rate_of_containment hlo hhi⟩
  | wedgeRooted H x hNoIso a hH hRoot J y hy hJ ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨max a b,?_⟩
    simpa only [Rat.cast_max] using wedge_rate H x hNoIso J y hy hH hb hRoot

lemma Assembly.rational {W : Type u} {G : SimpleGraph W} (hG : Assembly G)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hG.rate
  exact ⟨r,(exponent_eq hr hα hc h).symm⟩

/-- The atom condition is hereditary under (not necessarily induced) copies. -/
def Piece {W : Type u} (G : SimpleGraph W) : Prop :=
  (∃ S : Set W, G.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3) ∨ G ⊑ Erdos713C10.C10

lemma Piece.of_contained {W T : Type u} [Fintype W] [Fintype T]
    {G : SimpleGraph W} {H : SimpleGraph T} (h : Piece G) (hHG : H ⊑ G) : Piece H := by
  rcases h with ⟨S,hS,hc⟩ | h
  · obtain ⟨f⟩ := hHG
    exact Or.inl (small_shore_of_copy f S hS hc)
  · exact Or.inr (hHG.trans h)

lemma Piece.assembly {W : Type u} [Fintype W] [Nonempty W] {G : SimpleGraph W}
    (h : Piece G) (hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)) : Assembly G := by
  rcases h with ⟨S,hS,hc⟩ | h
  · exact .side G S hS hc
  · obtain ⟨e⟩ := Erdos713CycleCore.contained_c10 G hd h
    exact .ten G ⟨e.symm.toCopy⟩ h

lemma Piece.rooted_rate {W : Type u} [Fintype W] [Nonempty W] {G : SimpleGraph W}
    (h : Piece G) (hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)) :
    ∃ r : ℚ, HasRate G (r : ℝ) ∧ ∀ x, RootPowerBound G x (r : ℝ) := by
  rcases h with ⟨S,hS,hc⟩ | h
  · exact small_core G S hS hc hd
  · obtain ⟨e⟩ := Erdos713CycleCore.contained_c10 G hd h
    refine ⟨6/5,by simpa using iso_rate e Erdos713C10.rate,?_⟩
    intro x
    simpa using (c10 (e x)).of_copy e.toCopy x

def Pieces {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ {T : Type u} [Fintype T] (H : SimpleGraph T), H ⊑ G → H.Connected → NoCut H → Piece H

lemma Pieces.of_contained {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
    (h : Pieces G) (hHG : H ⊑ G) : Pieces H := by
  intro A _ J hJ hConn hNC
  exact h J (hJ.trans hHG) hConn hNC

/-- Every block either has a shore of size at most three or is contained in C10. -/
def Blocks {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, IsBlock G S → Piece (G.induce S)

lemma blocks_iff_pieces {W : Type u} [Fintype W] {G : SimpleGraph W} :
    Blocks G ↔ Pieces G := by
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
    obtain ⟨S,hRS,hS⟩ := exists_block_superset (Set.range f)
      (hH.map g.toHom hg) (hNC.map g.toHom ⟨g.injective,hg⟩)
    exact (h S hS).of_contained ⟨((induceHomOfLE G hRS).toCopy).comp g⟩
  · intro h S hS
    exact h (G.induce S) ⟨Copy.induce G S⟩ hS.connected hS.noCut

lemma pieces_assembly {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : Pieces G) : Assembly G := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → Pieces G → Assembly G from
    hh _ W G rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ G hcard h
    by_cases hConn : G.Connected
    · by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
      · obtain ⟨S,x,hL,hHConn,hHNC,hHd⟩ := exists_end_piece hConn hd
        haveI : Nonempty S := hHConn.nonempty
        have hPiece := h (G.induce S) ⟨Copy.induce G S⟩ hHConn hHNC
        by_cases hS : S = Set.univ
        · subst S
          exact .iso (induceUnivIso G).symm (hPiece.assembly hHd)
        let T : Set W := insert x Sᶜ
        have hT := hL.complement hS
        have hsmall : Fintype.card T < n := by
          obtain ⟨v,hv,hvx⟩ := hL.other
          have hn : v ∉ T := by simpa only [T,Set.mem_insert_iff,Set.mem_compl_iff,not_or,not_not] using ⟨hvx,hv⟩
          exact (Fintype.card_subtype_lt (x := v) hn).trans_eq hcard
        have hJ : Assembly (G.induce T) := ih _ hsmall T (G.induce T) rfl
          (h.of_contained ⟨Copy.induce G T⟩)
        have hroot := hT.root_adj hConn
        obtain ⟨a,ha,hRoot⟩ := hPiece.rooted_rate hHd
        have hNoIso : ∀ v, ∃ w, (G.induce S).Adj v w := by
          intro v
          apply ((G.induce S).degree_pos_iff_exists_adj v).mp
          have hdv := hHd v
          simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hdv
          omega
        exact .iso (lobeWedgeIso hL).symm
          (.wedgeRooted (G.induce S) ⟨x,hL.root_mem⟩ hNoIso a ha (hRoot _)
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


lemma blocks_assembly {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : Blocks G) : Assembly G := pieces_assembly G (blocks_iff_pieces.mp h)

lemma rational_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : Blocks G) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) :=
  (blocks_assembly G h).rational hα hc hAsymptotic


lemma assembly_of_blocks_small_or_c10 {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite)
    (hblocks : ∀ S : Set W, IsBlock G S → Nat.card S ≤ 7 ∨ G.induce S ⊑ Erdos713C10.C10) :
    Assembly G := by
  classical
  apply blocks_assembly G
  intro S hS
  rcases hblocks S hS with hcard | hTen
  · exact Or.inl (Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S)
      (Colorable.of_hom (Copy.induce G S).toHom hB)
      (by simpa only [Fintype.card_eq_nat_card] using hcard))
  · exact Or.inr hTen

lemma exists_remaining_block {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite) (hG : ¬ Assembly G) :
    ∃ S : Set W, IsBlock G S ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      (∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A) ∧
      ¬ G.induce S ⊑ Erdos713C10.C10 := by
  classical
  have hn : ¬ Blocks G := fun h => hG (blocks_assembly G h)
  unfold Blocks at hn
  push_neg at hn
  obtain ⟨S,hBlock,hS⟩ := hn
  have hSmall : ¬ ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 :=
    fun h => hS (Or.inl h)
  push_neg at hSmall
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc : 8 ≤ Nat.card S := by
    by_contra hc
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hSmall A hA)
  refine ⟨S,hBlock,hSB,hc,hBlock.noCut.min_degree hBlock.connected ?_,?_,?_⟩
  · simpa only [Fintype.card_eq_nat_card] using (show 3 ≤ Nat.card S by omega)
  · intro A hA
    exact hSmall A hA
  · exact fun h => hS (Or.inr h)

#print axioms Assembly.rate
#print axioms Piece.rooted_rate
#print axioms blocks_assembly
#print axioms rational_of_blocks
#print axioms exists_remaining_block
#print axioms assembly_of_blocks_small_or_c10
end Erdos713CycleAssembly
