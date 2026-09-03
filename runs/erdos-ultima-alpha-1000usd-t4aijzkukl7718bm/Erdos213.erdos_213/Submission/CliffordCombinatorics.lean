import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

/-! The combinatorial obstruction for using only the local edges of a
Clifford cube. This does not bound all rational-distance configurations. -/
namespace Erdos213.CliffordCombinatorics

private lemma pair_eq_of_mem {α : Type*} [DecidableEq α] {A : Finset α}
    (hA : A.card=2) {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    A = {a,b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp [hab,hA]

/-- Four or more distinct, pairwise-intersecting two-element sets have a
common element. Thus the non-star local clique has size at most four after
adjoining the origin of a binary cube. -/
lemma intersecting_pairs_have_common {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (hT : 4 ≤ T.card)
    (hcard : ∀ A ∈ T, A.card=2)
    (hint : ∀ A ∈ T, ∀ B ∈ T, ∃ x, x ∈ A ∧ x ∈ B) :
    ∃ x, ∀ A ∈ T, x ∈ A := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨A,hAT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨a,b,hab,hA⟩ := Finset.card_eq_two.mp (hcard A hAT)
  obtain ⟨B,hBT,haB⟩ := hno a
  obtain ⟨x,hxA,hxB⟩ := hint A hAT B hBT
  have hbB : b ∈ B := by
    rw [hA] at hxA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxA
    rcases hxA with rfl | rfl
    · exact False.elim (haB hxB)
    · exact hxB
  obtain ⟨c,hbc,hB⟩ : ∃ c, b ≠ c ∧ B={b,c} := by
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (hcard B hBT)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hbB
    rcases hbB with rfl | rfl
    · exact ⟨v,huv,rfl⟩
    · exact ⟨u,huv.symm,by simp [Finset.pair_comm]⟩
  have hac : a ≠ c := by
    intro he
    apply haB
    simp [hB,he]
  obtain ⟨C,hCT,hbC⟩ := hno b
  obtain ⟨y,hyA,hyC⟩ := hint A hAT C hCT
  have haC : a ∈ C := by
    rw [hA] at hyA
    simp only [Finset.mem_insert,Finset.mem_singleton] at hyA
    rcases hyA with rfl | rfl
    · exact hyC
    · exact False.elim (hbC hyC)
  obtain ⟨y,hyB,hyC⟩ := hint B hBT C hCT
  have hcC : c ∈ C := by
    rw [hB] at hyB
    simp only [Finset.mem_insert,Finset.mem_singleton] at hyB
    rcases hyB with rfl | rfl
    · exact False.elim (hbC hyC)
    · exact hyC
  have hC := pair_eq_of_mem (hcard C hCT) haC hcC hac
  have hsub : T ⊆ {A,B,C} := by
    intro D hDT
    obtain ⟨x,hxA,hxD⟩ := hint A hAT D hDT
    rw [hA] at hxA
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxA
    by_cases haD : a ∈ D
    · obtain ⟨y,hyB,hyD⟩ := hint B hBT D hDT
      rw [hB] at hyB
      simp only [Finset.mem_insert,Finset.mem_singleton] at hyB
      rcases hyB with rfl | rfl
      · have he := pair_eq_of_mem (hcard D hDT) haD hyD hab
        have : D=A := he.trans hA.symm
        simp [this]
      · have he := pair_eq_of_mem (hcard D hDT) haD hyD hac
        have : D=C := he.trans hC.symm
        simp [this]
    · have hbD : b ∈ D := by
        rcases hxA with rfl | rfl
        · exact False.elim (haD hxD)
        · exact hxD
      obtain ⟨y,hyC,hyD⟩ := hint C hCT D hDT
      rw [hC] at hyC
      simp only [Finset.mem_insert,Finset.mem_singleton] at hyC
      have hcD : c ∈ D := by
        rcases hyC with rfl | rfl
        · exact False.elim (haD hyD)
        · exact hyD
      have he := pair_eq_of_mem (hcard D hDT) hbD hcD hbc
      have : D=B := he.trans hB.symm
      simp [this]
  have hle := Finset.card_le_card hsub
  have hthree : ({A,B,C} : Finset (Finset α)).card ≤ 3 := by
    calc
      _ ≤ ({B,C} : Finset (Finset α)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({C} : Finset (Finset α)).card + 1) + 1 := by
        gcongr
        exact Finset.card_insert_le _ _
      _ = 3 := by simp
  omega


open scoped symmDiff

/-- Every local clique with at least five vertices in a binary cube lies
in the neighborhood of one vertex of the opposite parity. -/
lemma large_local_clique_has_center {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (hS : 5 ≤ S.card)
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∆ B).card=2) :
    ∃ B : Finset α, ∀ A ∈ S, (A ∆ B).card=1 := by
  classical
  obtain ⟨O,hOS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  let T := (S.erase O).image (fun A => A ∆ O)
  have hT : 4 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (symmDiff_left_injective O),
      Finset.card_erase_of_mem hOS]
    omega
  have hcard : ∀ X ∈ T, X.card=2 := by
    intro X hX
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hX
    exact hpair A (Finset.mem_of_mem_erase hA) O hOS (Finset.ne_of_mem_erase hA)
  have hint : ∀ X ∈ T, ∀ Y ∈ T, ∃ x, x ∈ X ∧ x ∈ Y := by
    intro X hX Y hY
    by_cases hXY : X=Y
    · subst Y
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [hcard X hX]; omega)
      exact ⟨x,hx,hx⟩
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hY
    have hAB : A ≠ B := by intro he; exact hXY (he ▸ rfl)
    have hdiff := hpair A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB) hAB
    have hid : (A ∆ O) ∆ (B ∆ O) = A ∆ B := by
      rw [symmDiff_comm B O, ← symmDiff_assoc, symmDiff_symmDiff_cancel_right]
    by_contra hn
    have hdis : Disjoint (A ∆ O) (B ∆ O) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact hn ⟨x,hx,hy⟩
    have hc := Finset.card_union_of_disjoint hdis
    rw [← Finset.symmDiff_eq_union hdis, hid, hdiff,
      hcard _ (Finset.mem_image.mpr ⟨A,hA,rfl⟩),
      hcard _ (Finset.mem_image.mpr ⟨B,hB,rfl⟩)] at hc
    omega
  obtain ⟨x,hx⟩ := intersecting_pairs_have_common T hT hcard hint
  refine ⟨O ∆ {x}, ?_⟩
  intro A hAS
  by_cases hAO : A=O
  · subst A
    simp
  have hAT : A ∆ O ∈ T := Finset.mem_image.mpr
    ⟨A,Finset.mem_erase.mpr ⟨hAO,hAS⟩,rfl⟩
  obtain ⟨y,hxy,he⟩ : ∃ y, x ≠ y ∧ A ∆ O={x,y} := by
    obtain ⟨u,v,huv,hev⟩ := Finset.card_eq_two.mp (hcard _ hAT)
    have hm := hx _ hAT
    rw [hev] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨v,huv,hev⟩
    · exact ⟨u,huv.symm,by simpa [Finset.pair_comm] using hev⟩
  have hremove : ({x,y} : Finset α) ∆ {x} = {y} := by
    ext z
    simp only [Finset.mem_symmDiff,Finset.mem_insert,Finset.mem_singleton]
    aesop
  rw [← symmDiff_assoc,he,hremove]
  simp

#print axioms large_local_clique_has_center

#print axioms intersecting_pairs_have_common
end Erdos213.CliffordCombinatorics
