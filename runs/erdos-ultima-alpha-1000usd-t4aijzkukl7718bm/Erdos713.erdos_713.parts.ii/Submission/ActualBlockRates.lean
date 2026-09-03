import FormalConjecturesUtil
import Submission.CompactCycleAssemblyAudit

/-! Conditional rate reduction using actual maximal blocks, with no hereditary
assumption on the class of blocks. This does not assert the rate hypothesis for
arbitrary blocks. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713Blocks
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Flatten a twice-induced graph. -/
noncomputable def induceImageIso (G : SimpleGraph V) (T : Set V) (U : Set T) :
    ((G.induce T).induce U) ≃g G.induce (Subtype.val '' U) := by
  let f : U → ↥(Subtype.val '' U) := fun v => ⟨v.val.val,⟨v.val,v.prop,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(Subtype.val '' U) => z.val) he
    · rintro ⟨v,⟨w,hw,rfl⟩⟩
      exact ⟨⟨w,hw⟩,rfl⟩
  exact ⟨Equiv.ofBijective f hf,Iff.rfl⟩

/-- A connected no-cut piece meeting a lobe away from the root stays inside
that lobe. The root need not belong to the piece. -/
lemma Lobe.subset_of_inter {S A : Set V} {x : V} (h : Lobe G S x)
    (hA : (G.induce A).Connected) (hNC : NoCut (G.induce A))
    (hi : ∃ u ∈ A, u ∈ S ∧ u ≠ x) : A ⊆ S := by
  classical
  obtain ⟨u,huA,huS,hux⟩ := hi
  intro v hvA
  by_cases hvx : v = x
  · exact hvx ▸ h.root_mem
  by_cases hxA : x ∈ A
  · let z : A := ⟨x,hxA⟩
    let B := (G.induce A).induce {z}ᶜ
    let a : ↥({z}ᶜ : Set A) := ⟨⟨u,huA⟩,fun he => hux (congrArg Subtype.val he)⟩
    let b : ↥({z}ᶜ : Set A) := ⟨⟨v,hvA⟩,fun he => hvx (congrArg Subtype.val he)⟩
    have hclosed : ∀ p ∈ {p : ↥({z}ᶜ : Set A) | p.val.val ∈ S}, ∀ q,
        B.Adj p q → q ∈ {p : ↥({z}ᶜ : Set A) | p.val.val ∈ S} := by
      intro p hp q hpq
      exact h.closed p.val.val hp (fun he => p.prop (Subtype.ext he)) q.val.val hpq
    exact mem_of_reachable_closed hclosed (u := a) huS (hNC z a b)
  · have hclosed : ∀ p ∈ {p : A | p.val ∈ S}, ∀ q,
        (G.induce A).Adj p q → q ∈ {p : A | p.val ∈ S} := by
      intro p hp q hpq
      exact h.closed p.val hp (fun he => hxA (he ▸ p.prop)) q.val hpq
    exact mem_of_reachable_closed hclosed (u := ⟨u,huA⟩) huS (hA _ ⟨v,hvA⟩)

lemma Lobe.isBlock {S : Set V} {x : V} (h : Lobe G S x)
    (hS : (G.induce S).Connected) (hNC : NoCut (G.induce S)) : IsBlock G S := by
  refine ⟨hS,hNC,?_⟩
  intro T hST hT hTNC
  obtain ⟨u,hu,hux⟩ := h.other
  exact Set.Subset.antisymm (h.subset_of_inter hT hTNC ⟨u,hST hu,hu,hux⟩) hST

/-- An abstract lifting criterion for an actual induced block: no connected
no-cut extension of its image is allowed to leave the induction set. -/
lemma IsBlock.lift {T : Set V} {U : Set T} (h : IsBlock (G.induce T) U)
    (hclosed : ∀ A : Set V, Subtype.val '' U ⊆ A → (G.induce A).Connected →
      NoCut (G.induce A) → A ⊆ T) : IsBlock G (Subtype.val '' U) := by
  classical
  let e := induceImageIso G T U
  refine ⟨h.connected.map e.toHom e.surjective,
    h.noCut.map e.toHom e.bijective,?_⟩
  intro A hUA hA hANC
  have hAT := hclosed A hUA hA hANC
  let B : Set T := Subtype.val ⁻¹' A
  have hIB : Subtype.val '' B = A := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩; exact hw
    · intro hv; exact ⟨⟨v,hAT hv⟩,hv,rfl⟩
  have hUB : U ⊆ B := by intro v hv; exact hUA ⟨v,hv,rfl⟩
  have hBConn : ((G.induce T).induce B).Connected := by
    apply (induceImageIso G T B).connected_iff.mpr
    rw [hIB]
    exact hA
  have hBNC : NoCut ((G.induce T).induce B) := by
    have hh : NoCut (G.induce (Subtype.val '' B)) := by
      rw [hIB]
      exact hANC
    exact hh.map (induceImageIso G T B).symm.toHom (induceImageIso G T B).symm.bijective
  exact hIB.symm.trans (congrArg (fun U => Subtype.val '' U) (h.maximal B hUB hBConn hBNC))

lemma IsBlock.lift_lobe [Fintype V] {T : Set V} {U : Set T} {x : V}
    (h : IsBlock (G.induce T) U) (hL : Lobe G T x) (hc : 2 ≤ Nat.card U) :
    IsBlock G (Subtype.val '' U) := by
  classical
  apply h.lift
  intro A hUA hA hANC
  have hi : ∃ u ∈ U, u.val ≠ x := by
    by_contra hn
    push_neg at hn
    have hsub : Subsingleton U := ⟨by
      intro a b
      exact Subtype.ext (Subtype.ext ((hn a.val a.prop).trans (hn b.val b.prop).symm))⟩
    haveI := hsub
    have hc' : Nat.card U = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub,h.connected.nonempty⟩
    omega
  obtain ⟨u,hu,hux⟩ := hi
  exact hL.subset_of_inter hA hANC ⟨u.val,hUA ⟨u,hu,rfl⟩,u.prop,hux⟩

lemma IsBlock.lift_prunes [Fintype V] {T : Set V} {U : Set T}
    (h : IsBlock (G.induce T) U) (hp : Erdos713Pruning.PrunesTo G T)
    (hc : 3 ≤ Nat.card U) : IsBlock G (Subtype.val '' U) := by
  classical
  apply h.lift
  intro A hUA hA hANC
  have hcard : 3 ≤ Fintype.card A := by
    let f : U ↪ A := ⟨fun v => ⟨v.val.val,hUA ⟨v.val,v.prop,rfl⟩⟩,by
      intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : A => z.val) he⟩
    have hc' : 3 ≤ Fintype.card U := by simpa only [Fintype.card_eq_nat_card] using hc
    exact hc'.trans (Fintype.card_le_of_embedding f)
  exact hp.retains (hANC.min_degree hA hcard)

lemma IsBlock.lift_component (C : G.ConnectedComponent) {U : Set C}
    (h : IsBlock C.toSimpleGraph U) : IsBlock G (Subtype.val '' U) := by
  apply h.lift
  intro A hUA hA hANC
  obtain ⟨u⟩ := h.connected.nonempty
  have hclosed : ∀ p ∈ {p : A | p.val ∈ C.supp}, ∀ q,
      (G.induce A).Adj p q → q ∈ {p : A | p.val ∈ C.supp} := by
    intro p hp q hpq
    exact C.mem_supp_of_adj_mem_supp hp hpq
  intro v hv
  exact mem_of_reachable_closed hclosed
    (u := ⟨u.val.val,hUA ⟨u.val,u.prop,rfl⟩⟩) u.val.prop (hA _ ⟨v,hv⟩)

#print axioms Lobe.isBlock
#print axioms IsBlock.lift_lobe
#print axioms IsBlock.lift_prunes
#print axioms IsBlock.lift_component
end Erdos713Blocks

namespace Erdos713ActualBlocks
open Erdos713Blocks Erdos713Rate Erdos713RootPower Erdos713Gluing
universe u

/-- An ordinary rational threshold together with the matching bound at every
possible attachment root. This is data to be proved, not a universal axiom. -/
def RootedRate {W : Type u} (G : SimpleGraph W) : Prop :=
  ∃ r : ℚ, HasRate G (r : ℝ) ∧ ∀ x, RootPowerBound G x (r : ℝ)

lemma RootedRate.of_iso {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
    (e : G ≃g H) (h : RootedRate H) : RootedRate G := by
  obtain ⟨r,hr,hroot⟩ := h
  exact ⟨r,iso_rate e hr,fun x => (hroot (e x)).of_copy e.toCopy x⟩

/-- Rate data is requested only for actual maximal blocks of order at least
three. Bridge edges and isolated vertices need no separate hypothesis. -/
def BlockRates {W : Type u} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S → RootedRate (G.induce S)

lemma BlockRates.induce {W : Type u} [Fintype W] {G : SimpleGraph W}
    (h : BlockRates G) (T : Set W)
    (hlift : ∀ U : Set T, IsBlock (G.induce T) U → 3 ≤ Nat.card U →
      IsBlock G (Subtype.val '' U)) : BlockRates (G.induce T) := by
  intro U hU hc
  let e := induceImageIso G T U
  have hc' : 3 ≤ Nat.card ↥(Subtype.val '' U) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc
  exact (h _ (hlift U hU hc) hc').of_iso e

lemma BlockRates.lobe {W : Type u} [Fintype W] {G : SimpleGraph W}
    (h : BlockRates G) {T : Set W} {x : W} (hL : Lobe G T x) :
    BlockRates (G.induce T) :=
  h.induce T (fun _ hU hc => hU.lift_lobe hL (by omega))

lemma BlockRates.prunes {W : Type u} [Fintype W] {G : SimpleGraph W}
    (h : BlockRates G) {T : Set W} (hp : Erdos713Pruning.PrunesTo G T) :
    BlockRates (G.induce T) :=
  h.induce T (fun _ hU hc => hU.lift_prunes hp hc)

lemma BlockRates.component {W : Type u} [Fintype W] {G : SimpleGraph W}
    (h : BlockRates G) (C : G.ConnectedComponent) : BlockRates C.toSimpleGraph :=
  h.induce C.supp (fun _ hU _ => hU.lift_component C)

/-- Matched rational rate bounds on actual cyclic blocks imply a rational
attained growth threshold for the whole graph. No rate hypothesis is made on
proper subgraphs of a block. -/
lemma rate_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : BlockRates G) : ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → BlockRates G → ∃ r : ℚ, HasRate G (r : ℝ) from
    hh _ W G rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ G hcard h
    by_cases hConn : G.Connected
    · by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
      · obtain ⟨S,x,hL,hSConn,hSNC,hSd⟩ := exists_end_piece hConn hd
        obtain ⟨a,ha,hRoot⟩ := h S (hL.isBlock hSConn hSNC) (hL.card_ge_three hd)
        by_cases hS : S = Set.univ
        · subst S
          exact ⟨a,iso_rate (induceUnivIso G).symm ha⟩
        let T : Set W := insert x Sᶜ
        have hT := hL.complement hS
        have hsmall : Fintype.card T < n := by
          obtain ⟨v,hv,hvx⟩ := hL.other
          have hn : v ∉ T := by
            simpa only [T,Set.mem_insert_iff,Set.mem_compl_iff,not_or,not_not] using ⟨hvx,hv⟩
          exact (Fintype.card_subtype_lt (x := v) hn).trans_eq hcard
        obtain ⟨b,hb⟩ := ih _ hsmall T (G.induce T) rfl (h.lobe hT)
        have hNoIso : ∀ v, ∃ w, (G.induce S).Adj v w := by
          intro v
          apply ((G.induce S).degree_pos_iff_exists_adj v).mp
          have hdv := hSd v
          simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hdv
          omega
        refine ⟨max a b,iso_rate (lobeWedgeIso hL).symm ?_⟩
        simpa only [Rat.cast_max] using wedge_rate (G.induce S) ⟨x,hL.root_mem⟩ hNoIso
          (G.induce T) ⟨x,hT.root_mem⟩ (hT.root_adj hConn) ha hb (hRoot _)
      · push_neg at hd
        obtain ⟨x,hx⟩ := hd
        have hsmall : Fintype.card ↥({x}ᶜ : Set W) < n :=
          (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hcard
        have hx' : Nat.card ((G.induce Set.univ).neighborSet ⟨x,Set.mem_univ x⟩) ≤ 1 := by
          rw [Nat.card_congr ((induceUnivIso G).mapNeighborSet ⟨x,Set.mem_univ x⟩)]
          exact Nat.le_of_lt_succ hx
        have hp : Erdos713Pruning.PrunesTo G {x}ᶜ := by
          convert Erdos713Pruning.PrunesTo.delete (.start (G := G)) ⟨x,Set.mem_univ x⟩ hx' using 1
          ext v
          simp
        obtain ⟨r,hr⟩ := ih _ hsmall _ _ rfl (h.prunes hp)
        exact ⟨r,hp.rate hr⟩
    · apply Erdos713ComponentRates.rate_of_components G
      intro C
      have hns : ¬ Function.Surjective (fun v : C => v.val) := by
        intro hs
        exact hConn (C.connected_toSimpleGraph.map C.toSimpleGraph_hom hs)
      have hsmall := (Fintype.card_lt_of_injective_not_surjective
        (fun v : C => v.val) Subtype.val_injective hns).trans_eq hcard
      exact ih _ hsmall C C.toSimpleGraph rfl (h.component C)

lemma rational_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : BlockRates G) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := rate_of_blocks G h
  exact ⟨r,(exponent_eq hr hα hc hAsymptotic).symm⟩

lemma exists_unmatched_block {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : ¬ BlockRates G) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧ ¬ RootedRate (G.induce S) := by
  classical
  unfold BlockRates at h
  push_neg at h
  obtain ⟨S,hS,hc,hn⟩ := h
  exact ⟨S,hS,hc,hS.noCut.min_degree hS.connected
    (by simpa only [Fintype.card_eq_nat_card] using hc),hn⟩

/-- The earlier small-shore/C10 block class satisfies the new analytic data. -/
lemma BlockRates.of_cycle_blocks {W : Type u} [Fintype W] {G : SimpleGraph W}
    (h : Erdos713CycleAssembly.Blocks G) : BlockRates G := by
  classical
  intro S hS hc
  haveI : Nonempty S := hS.connected.nonempty
  exact (h S hS).rooted_rate (hS.noCut.min_degree hS.connected
    (by simpa only [Fintype.card_eq_nat_card] using hc))

/-- Root-shifting symmetry makes an ordinary rational rate sufficient. -/
lemma RootedRate.of_root_shift {W : Type u} {G : SimpleGraph W}
    (hr : ∃ r : ℚ, HasRate G (r : ℝ))
    (hshift : ∀ x, ∃ e : G.Copy G, G.Adj x (e x)) : RootedRate G := by
  obtain ⟨r,hr⟩ := hr
  refine ⟨r,hr,?_⟩
  intro x
  obtain ⟨e,he⟩ := hshift x
  exact Erdos713RootPower.of_root_shift G x e he (by linarith [hr.one_le]) hr.upper

/-- Failure of the actual-block hypothesis produces one block outside all
completed small-shore and C10 cases, and without matching rational rooted data.
This asserts no exact asymptotic for the selected block. -/
lemma exists_remaining_block {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hB : G.IsBipartite) (h : ¬ BlockRates G) :
    ∃ S : Set W, IsBlock G S ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      (∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A) ∧
      ¬ G.induce S ⊑ Erdos713C10.C10 ∧ ¬ RootedRate (G.induce S) := by
  classical
  obtain ⟨S,hS,hc,hd,hn⟩ := exists_unmatched_block G h
  haveI : Nonempty S := hS.connected.nonempty
  have hNP : ¬ Erdos713CycleAssembly.Piece (G.induce S) :=
    fun hp => hn (hp.rooted_rate hd)
  have hSmall : ¬ ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 :=
    fun hh => hNP (Or.inl hh)
  push_neg at hSmall
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc' : 8 ≤ Nat.card S := by
    by_contra hc'
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hSmall A hA)
  exact ⟨S,hS,hSB,hc',hd,fun A hA => hSmall A hA,fun hh => hNP (Or.inr hh),hn⟩

#print axioms rate_of_blocks
#print axioms rational_of_blocks
#print axioms exists_remaining_block
#print axioms BlockRates.of_cycle_blocks
#print axioms RootedRate.of_root_shift
#print axioms exists_unmatched_block
end Erdos713ActualBlocks
