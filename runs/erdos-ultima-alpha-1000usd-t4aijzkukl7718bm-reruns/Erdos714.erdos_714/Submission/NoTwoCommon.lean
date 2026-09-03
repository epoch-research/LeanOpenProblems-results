import Submission.PureFourStructure

/-!
A local restriction when four-point coverage never equals two. This does
not improve the critical K44 exponent: its square-root intersection bound
is consistent with pair codegrees at critical density.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 5000000
namespace Erdos714NoTwoCommon
open Erdos714Packing Erdos714NonuniformFourthDesign
variable {B V : Type*} [Fintype B] [Fintype V]

/-- The local design argument only needs constant coverage on the
four-subsets of U, not on every four-subset of the whole point set. -/
theorem local_container_alternative (S : B → Finset V) (U : Finset V)
    (hU : 4 ≤ U.card) (hex : (blocksContaining S U).Nonempty)
    (hfour : ∀ T : Finset V, T ⊆ U → T.card=4 → (blocksContaining S T).card=3) :
    (U.card-2)^2 ≤ 4*Fintype.card B ∨ (blocksContaining S U).card=3 := by
  let X := blocksContaining S U
  have hXle : X.card ≤ 3 := by
    obtain ⟨T,hTU,hT⟩ := exists_subset_card_eq hU
    rw [← hfour T hTU hT]
    apply card_le_card
    intro c hc
    exact (mem_blocksContaining S T c).mpr
      (hTU.trans ((mem_blocksContaining S U c).mp hc))
  by_cases hX : X.card=3
  · exact Or.inr hX
  left
  have hXpos : 0 < X.card := card_pos.mpr hex
  let J := {c : B // ¬ U ⊆ S c}
  let W := U
  let R : J → Finset W := fun c => univ.filter (fun v => v.val ∈ S c.val)
  let e : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hiff (T : Finset W) (c : J) : T ⊆ R c ↔ T.map e ⊆ S c.val := by
    constructor
    · intro h v hv
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp (h hw)).2
    · intro h v hv
      exact mem_filter.mpr ⟨mem_univ _, h (mem_map.mpr ⟨v,hv,rfl⟩)⟩
  have hproper (c : J) : R c ≠ univ := by
    intro he
    apply c.property
    intro v hv
    have hmem : (⟨v,hv⟩ : W) ∈ R c := by rw [he]; exact mem_univ _
    exact (mem_filter.mp hmem).2
  have hfourR (T : Finset W) (hT : T.card=4) :
      (blocksContaining R T).card=3-X.card := by
    have hTU : T.map e ⊆ U := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
      exact w.property
    have hTcard : (T.map e).card=4 := by simpa only [card_map] using hT
    have hcover : (blocksContaining S (T.map e)).card=3 := hfour _ hTU hTcard
    have hsub : X ⊆ blocksContaining S (T.map e) := by
      intro c hc
      exact (mem_blocksContaining S _ c).mpr
        (hTU.trans ((mem_blocksContaining S U c).mp hc))
    have heq : (blocksContaining R T).card = (blocksContaining S (T.map e) \ X).card := by
      apply card_bij (fun c _ => c.val)
      · intro c hc
        apply mem_sdiff.mpr
        refine ⟨(mem_blocksContaining S _ c.val).mpr
          ((hiff T c).mp ((mem_blocksContaining R T c).mp hc)), ?_⟩
        intro hc'
        exact c.property ((mem_blocksContaining S U c.val).mp hc')
      · intro c hc d hd he
        exact Subtype.ext he
      · intro c hc
        obtain ⟨hcover,hnot⟩ := mem_sdiff.mp hc
        have hnot' : ¬ U ⊆ S c := by
          intro h
          exact hnot ((mem_blocksContaining S U c).mpr h)
        refine ⟨⟨c,hnot'⟩, ?_, rfl⟩
        exact (mem_blocksContaining R T _).mpr
          ((hiff T _).mpr ((mem_blocksContaining S _ c).mp hcover))
    rw [heq, card_sdiff_of_subset hsub, hcover]
  have hh := fourth_design_bound R (3-X.card) (by omega) (by omega)
    (by simpa only [W, Fintype.card_coe] using hU) hproper (by
      intro T hT
      convert hfourR T hT using 2)
  have hJ : Fintype.card J ≤ Fintype.card B := Fintype.card_subtype_le _
  simp only [W, Fintype.card_coe] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hJ)

/-- If the local alternative gives three containers, every outside block
meets U in at most three points. -/
theorem local_container_isolation (S : B → Finset V) (U : Finset V)
    (hthree : (blocksContaining S U).card=3)
    (hfour : ∀ T : Finset V, T ⊆ U → T.card=4 → (blocksContaining S T).card=3) :
    ∀ c, ¬ U ⊆ S c → (U ∩ S c).card ≤ 3 := by
  intro c hc
  by_contra hn
  obtain ⟨T,hTi,hT⟩ := exists_subset_card_eq (by omega : 4 ≤ (U ∩ S c).card)
  have hTU : T ⊆ U := hTi.trans inter_subset_left
  have hTc : T ⊆ S c := hTi.trans inter_subset_right
  have hcov := hfour T hTU hT
  have hsub : blocksContaining S U ⊆ blocksContaining S T := by
    intro d hd
    exact (mem_blocksContaining S T d).mpr
      (hTU.trans ((mem_blocksContaining S U d).mp hd))
  have he := eq_of_subset_of_card_le hsub (by omega)
  apply hc
  apply (mem_blocksContaining S U c).mp
  rw [he]
  exact (mem_blocksContaining S T c).mpr hTc

/-- In a packing with coverage at most three and never two, every
four-subset of an intersection of two distinct indexed blocks has coverage
exactly three. -/
lemma pair_four_coverage (S : B → Finset V)
    (hbound : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card ≤ 3)
    (hnotwo : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card ≠ 2)
    (b c : B) (hbc : b ≠ c) (T : Finset V) (hT : T.card=4)
    (hTi : T ⊆ S b ∩ S c) : (blocksContaining S T).card=3 := by
  have hsub : {b,c} ⊆ blocksContaining S T := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_blocksContaining]
    exact ⟨hTi.trans inter_subset_left,hTi.trans inter_subset_right⟩
  have hlo := card_le_card hsub
  rw [card_pair hbc] at hlo
  have hhi := hbound T hT
  have hn := hnotwo T hT
  omega

/-- An oversized pair intersection in the no-two model is contained in
exactly three blocks, and all other blocks meet it in at most three points.
This is a local structural statement, not a subcritical global edge bound. -/
theorem pair_intersection_alternative (S : B → Finset V)
    (hbound : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card ≤ 3)
    (hnotwo : ∀ T : Finset V, T.card=4 → (blocksContaining S T).card ≠ 2)
    (b c : B) (hbc : b ≠ c) :
    ((S b ∩ S c).card-2)^2 ≤ 4*Fintype.card B ∨
      ((blocksContaining S (S b ∩ S c)).card=3 ∧
        ∃ d : B, d ≠ b ∧ d ≠ c ∧ S b ∩ S c ⊆ S d ∧
          ∀ a, ¬ S b ∩ S c ⊆ S a → ((S b ∩ S c) ∩ S a).card ≤ 3) := by
  let U := S b ∩ S c
  have hfour (T : Finset V) (hTU : T ⊆ U) (hT : T.card=4) :
      (blocksContaining S T).card=3 := pair_four_coverage S hbound hnotwo b c hbc T hT hTU
  by_cases hU : 4 ≤ U.card
  · have hex : (blocksContaining S U).Nonempty :=
      ⟨b,(mem_blocksContaining S U b).mpr inter_subset_left⟩
    rcases local_container_alternative S U hU hex hfour with hsmall | hthree
    · exact Or.inl hsmall
    · right
      refine ⟨hthree, ?_⟩
      have hn : ¬ blocksContaining S U ⊆ {b,c} := by
        intro h
        have hh := card_le_card h
        rw [hthree,card_pair hbc] at hh
        omega
      obtain ⟨d,hd,hdnot⟩ := not_subset.mp hn
      have hdb : d ≠ b := by intro he; apply hdnot; simp [he]
      have hdc : d ≠ c := by intro he; apply hdnot; simp [he]
      exact ⟨d,hdb,hdc,(mem_blocksContaining S U d).mp hd,
        local_container_isolation S U hthree hfour⟩
  · left
    have hs : U.card-2 ≤ 1 := by omega
    have hp := Nat.pow_le_pow_left hs 2
    have hB : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
    change (U.card-2)^2 ≤ _
    norm_num only at hp
    omega

#print axioms local_container_alternative
#print axioms local_container_isolation
#print axioms pair_four_coverage
#print axioms pair_intersection_alternative
end Erdos714NoTwoCommon
