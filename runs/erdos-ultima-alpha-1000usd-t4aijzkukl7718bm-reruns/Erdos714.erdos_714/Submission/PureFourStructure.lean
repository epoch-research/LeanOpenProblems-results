import Submission.NonuniformFourthDesign

/-!
Structural consequences of the exact zero-or-three four-point coverage
condition. General K44-free set systems may also have coverages one and two,
so the condition here is stronger than the conjecture's freeness condition.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 5000000
namespace Erdos714PureFourStructure
open Erdos714Packing Erdos714NonuniformFourthDesign
variable {B V : Type*} [Fintype B] [Fintype V]

/-- A four-subset of one block has coverage three in a pure system. -/
lemma covered_four (S : B → Finset V)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3)
    (b : B) (T : Finset V) (hT : T.card=4) (hTb : T ⊆ S b) :
    (blocksContaining S T).card=3 := by
  have hpos := card_pos.mpr (show (blocksContaining S T).Nonempty from
    ⟨b,(mem_blocksContaining S T b).mpr hTb⟩)
  rcases hpure T hT with h | h
  · omega
  · exact h

lemma full_cover_le (S : B → Finset V)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3)
    (b : B) (hb : 4 ≤ (S b).card) : (blocksContaining S (S b)).card ≤ 3 := by
  obtain ⟨T,hTb,hT⟩ := exists_subset_card_eq hb
  rw [← covered_four S hpure b T hT hTb]
  apply card_le_card
  intro c hc
  exact (mem_blocksContaining S T c).mpr
    (hTb.trans ((mem_blocksContaining S (S b) c).mp hc))

/-- Unless a block is fully contained in three indexed blocks, its size
obeys the local nonuniform fourth-design bound. -/
theorem block_size_or_three_containers (S : B → Finset V)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3)
    (b : B) (hb : 4 ≤ (S b).card) :
    ((S b).card-2)^2 ≤ 4*Fintype.card B ∨ (blocksContaining S (S b)).card=3 := by
  let X := blocksContaining S (S b)
  have hXle : X.card ≤ 3 := full_cover_le S hpure b hb
  by_cases hX : X.card=3
  · exact Or.inr hX
  left
  have hXpos : 0 < X.card := card_pos.mpr ⟨b,(mem_blocksContaining S (S b) b).mpr subset_rfl⟩
  let J := {c : B // ¬ S b ⊆ S c}
  let W := (S b : Finset V)
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
  have hfour (T : Finset W) (hT : T.card=4) :
      (blocksContaining R T).card=3-X.card := by
    have hTb : T.map e ⊆ S b := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
      exact w.property
    have hTcard : (T.map e).card=4 := by simpa only [card_map] using hT
    have hcover : (blocksContaining S (T.map e)).card=3 := covered_four S hpure b _ hTcard hTb
    have hsub : X ⊆ blocksContaining S (T.map e) := by
      intro c hc
      exact (mem_blocksContaining S _ c).mpr
        (hTb.trans ((mem_blocksContaining S (S b) c).mp hc))
    have heq : (blocksContaining R T).card = (blocksContaining S (T.map e) \ X).card := by
      apply card_bij (fun c _ => c.val)
      · intro c hc
        apply mem_sdiff.mpr
        refine ⟨(mem_blocksContaining S _ c.val).mpr
          ((hiff T c).mp ((mem_blocksContaining R T c).mp hc)), ?_⟩
        intro hc'
        exact c.property ((mem_blocksContaining S (S b) c.val).mp hc')
      · intro c hc d hd he
        exact Subtype.ext he
      · intro c hc
        obtain ⟨hcover,hnot⟩ := mem_sdiff.mp hc
        have hnot' : ¬ S b ⊆ S c := by
          intro h
          exact hnot ((mem_blocksContaining S (S b) c).mpr h)
        refine ⟨⟨c,hnot'⟩, ?_, rfl⟩
        exact (mem_blocksContaining R T _).mpr
          ((hiff T _).mpr ((mem_blocksContaining S _ c).mp hcover))
    rw [heq, card_sdiff_of_subset hsub, hcover]
  have hh := fourth_design_bound R (3-X.card) (by omega) (by omega)
    (by simpa only [W, Fintype.card_coe] using hb) hproper (by
      intro T hT
      convert hfour T hT using 2)
  have hJ : Fintype.card J ≤ Fintype.card B := Fintype.card_subtype_le _
  simp only [W, Fintype.card_coe] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hJ)

/-- Any block larger than the local quadratic bound has exactly three
containers and meets every other block outside those containers in at most
three points. -/
theorem large_block_isolated (S : B → Finset V)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3)
    (b : B) (hb : 4 ≤ (S b).card)
    (hlarge : 4*Fintype.card B < ((S b).card-2)^2) :
    (blocksContaining S (S b)).card=3 ∧
      ∀ c, ¬ S b ⊆ S c → (S b ∩ S c).card ≤ 3 := by
  have hthree : (blocksContaining S (S b)).card=3 :=
    (block_size_or_three_containers S hpure b hb).resolve_left (by omega)
  refine ⟨hthree, ?_⟩
  intro c hc
  by_contra hn
  obtain ⟨T,hTi,hT⟩ := exists_subset_card_eq (by omega : 4 ≤ (S b ∩ S c).card)
  have hTb : T ⊆ S b := hTi.trans inter_subset_left
  have hTc : T ⊆ S c := hTi.trans inter_subset_right
  have hfour := covered_four S hpure b T hT hTb
  have hsub : blocksContaining S (S b) ⊆ blocksContaining S T := by
    intro d hd
    exact (mem_blocksContaining S T d).mpr
      (hTb.trans ((mem_blocksContaining S (S b) d).mp hd))
  have he := eq_of_subset_of_card_le hsub (by omega)
  apply hc
  apply (mem_blocksContaining S (S b) c).mp
  rw [he]
  exact (mem_blocksContaining S T c).mpr hTc

/-- The three containers of a large block are in fact three identical
indexed copies of that block. -/
theorem large_block_twins (S : B → Finset V)
    (hpure : ∀ T : Finset V, T.card=4 →
      (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=3)
    (b : B) (hb : 4 ≤ (S b).card)
    (hlarge : 4*Fintype.card B < ((S b).card-2)^2) :
    ∀ c, S b ⊆ S c → S c=S b := by
  intro c hbc
  have hcard : (S b).card ≤ (S c).card := card_le_card hbc
  have hc : 4 ≤ (S c).card := hb.trans hcard
  have hlargec : 4*Fintype.card B < ((S c).card-2)^2 :=
    hlarge.trans_le (Nat.pow_le_pow_left (Nat.sub_le_sub_right hcard 2) 2)
  have hthreeb := (large_block_isolated S hpure b hb hlarge).1
  have hthreec := (large_block_isolated S hpure c hc hlargec).1
  have hsub : blocksContaining S (S c) ⊆ blocksContaining S (S b) := by
    intro d hd
    exact (mem_blocksContaining S _ d).mpr
      (hbc.trans ((mem_blocksContaining S _ d).mp hd))
  have he := eq_of_subset_of_card_le hsub (by omega)
  apply subset_antisymm _ hbc
  apply (mem_blocksContaining S (S c) b).mp
  rw [he]
  exact (mem_blocksContaining S (S b) b).mpr subset_rfl

#print axioms covered_four
#print axioms full_cover_le
#print axioms block_size_or_three_containers
#print axioms large_block_isolated
#print axioms large_block_twins
end Erdos714PureFourStructure
