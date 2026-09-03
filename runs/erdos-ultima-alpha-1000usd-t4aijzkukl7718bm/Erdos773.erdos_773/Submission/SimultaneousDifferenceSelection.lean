import Submission.Hypergraph

/-!
Simultaneous bounded-difference selection for a finite family of increasing
integer-valued maps. The multiplicity bound is not asserted to be one.
-/
namespace Erdos773.SimultaneousDifferenceSelection
open Finset
set_option maxHeartbeats 1000000

/-- Positive difference representations on an ordered finite index set. -/
def reps {N : ℕ} (f : Fin N → ℕ) (D : ℕ) : Finset (Fin N × Fin N) :=
  univ.filter (fun ab => ab.1 < ab.2 ∧ f ab.2 = f ab.1 + D)

private def support {N : ℕ} (E : Finset (Fin N × Fin N)) : Finset (Fin N) :=
  E.image Prod.fst ∪ E.image Prod.snd

private lemma mem_reps {N D : ℕ} {f : Fin N → ℕ} {ab : Fin N × Fin N} :
    ab ∈ reps f D ↔ ab.1 < ab.2 ∧ f ab.2 = f ab.1 + D := by simp [reps]

private lemma snd_injective {N D : ℕ} {f : Fin N → ℕ} (hf : Function.Injective f) :
    Set.InjOn Prod.snd (reps f D : Set (Fin N × Fin N)) := by
  intro ab hab cd hcd he
  obtain ⟨_, hab⟩ := mem_reps.mp hab
  obtain ⟨_, hcd⟩ := mem_reps.mp hcd
  apply Prod.ext
  · apply hf
    rw [he] at hab
    omega
  · exact he

private lemma support_card {N D : ℕ} {f : Fin N → ℕ} (hf : Function.Injective f)
    {E : Finset (Fin N × Fin N)} (hE : E ⊆ reps f D) (hne : E.Nonempty) :
    E.card + 1 ≤ (support E).card := by
  let T := E.image Prod.fst
  have hT : T.Nonempty := hne.image Prod.fst
  let a := T.min' hT
  have ha : a ∈ T := min'_mem T hT
  have hnot : a ∉ E.image Prod.snd := by
    intro h
    obtain ⟨ab, hab, he⟩ := mem_image.mp h
    have hle : a ≤ ab.1 := min'_le T _ (mem_image.mpr ⟨ab, hab, rfl⟩)
    have hlt := (mem_reps.mp (hE hab)).1
    rw [he] at hlt
    exact (not_lt_of_ge hle) hlt
  have hi : insert a (E.image Prod.snd) ⊆ support E := by
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact mem_union_left _ ha
    · exact mem_union_right _ hb
  have hc : (E.image Prod.snd).card = E.card :=
    card_image_of_injOn (fun p hp q hq he => snd_injective hf (hE hp) (hE hq) he)
  have hh := card_le_card hi
  rw [card_insert_of_notMem hnot, hc] at hh
  exact hh

section Family
variable {κ : Type*} {N : ℕ}

private def badSupports (J : Finset κ) (f : κ → Fin N → ℕ) (R g : ℕ) :
    Finset (Finset (Fin N)) :=
  J.biUnion (fun j => (Icc 1 R).biUnion (fun D =>
    ((reps (f j) D).powersetCard (g+1)).image support))

private lemma badSupports_size {J : Finset κ} {f : κ → Fin N → ℕ} {R g : ℕ}
    (hf : ∀ j ∈ J, Function.Injective (f j)) {e : Finset (Fin N)}
    (he : e ∈ badSupports J f R g) : g+2 ≤ e.card := by
  obtain ⟨j, hj, he⟩ := mem_biUnion.mp he
  obtain ⟨D, hD, he⟩ := mem_biUnion.mp he
  obtain ⟨E, hE, rfl⟩ := mem_image.mp he
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hE
  have hn : E.Nonempty := card_pos.mp (by omega)
  have hh := support_card (hf j hj) hsub hn
  omega

private lemma badSupports_count (J : Finset κ) (f : κ → Fin N → ℕ) (R g : ℕ) :
    (badSupports J f R g).card ≤ ∑ j ∈ J, ∑ D ∈ Icc 1 R, (reps (f j) D).card ^ (g+1) := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro j hj
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro D hD
  exact card_image_le.trans (by rw [card_powersetCard]; exact Nat.choose_le_pow _ _)

private lemma avoids_bounded {J : Finset κ} {f : κ → Fin N → ℕ} {R g : ℕ}
    (hR : ∀ j ∈ J, ∀ a, f j a ≤ R) {B : Finset (Fin N)}
    (hB : ∀ e ∈ badSupports J f R g, ¬e ⊆ B) :
    ∀ j ∈ J, ∀ D : ℕ, 0 < D →
      ((reps (f j) D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g := by
  intro j hj D hD
  by_cases hDR : D ≤ R
  · by_contra! hlarge
    obtain ⟨E, hE, hcard⟩ := exists_subset_card_eq (show g+1 ≤
      ((reps (f j) D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card by omega)
    have hsub : E ⊆ reps (f j) D := hE.trans (filter_subset _ _)
    apply hB (support E)
    · exact mem_biUnion.mpr ⟨j, hj, mem_biUnion.mpr ⟨D, mem_Icc.mpr ⟨hD,hDR⟩,
        mem_image.mpr ⟨E, mem_powersetCard.mpr ⟨hsub,hcard⟩, rfl⟩⟩⟩
    · intro a ha
      rcases mem_union.mp ha with ha | ha
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.1
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.2
  · have he : reps (f j) D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ab hab
      have hh := (mem_reps.mp hab).2
      have hb := hR j hj ab.2
      omega
    simp [he]

/-- One subset simultaneously controls all maps in the family. The number
of constraints appears only in the deletion cost. No AP-free hypothesis is
needed, because g+1 equal differences use at least g+2 vertices. -/
theorem finite_selection (J : Finset κ) (f : κ → Fin N → ℕ) (R g : ℕ)
    (hf : ∀ j ∈ J, Function.Injective (f j)) (hR : ∀ j ∈ J, ∀ a, f j a ≤ R)
    (p K : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hrep : ∀ j ∈ J, ∀ D ∈ Icc 1 R, ((reps (f j) D).card : ℝ) ≤ K) :
    ∃ B : Finset (Fin N),
      (∀ j ∈ J, ∀ D : ℕ, 0 < D →
        ((reps (f j) D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g) ∧
      p * N - (J.card : ℝ) * R * K ^ (g+1) * p ^ (g+2) ≤ B.card := by
  have hn : ∀ e ∈ badSupports J f R g, e.Nonempty := by
    intro e he
    exact card_pos.mp (by have := badSupports_size hf he; omega)
  obtain ⟨B, hB, hcard⟩ := alteration_bound (badSupports J f R g) hn p hp hp1
  have hcount : ((badSupports J f R g).card : ℝ) ≤ (J.card : ℝ) * R * K ^ (g+1) := by
    calc
      _ ≤ ∑ j ∈ J, ∑ D ∈ Icc 1 R, ((reps (f j) D).card : ℝ) ^ (g+1) := by
        exact_mod_cast badSupports_count J f R g
      _ ≤ ∑ j ∈ J, ∑ _D ∈ Icc 1 R, K ^ (g+1) := by
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro D hD
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hrep j hj D hD) _
      _ = _ := by simp [mul_assoc]
  have hcost : (∑ e ∈ badSupports J f R g, p ^ e.card) ≤
      (J.card : ℝ) * R * K ^ (g+1) * p ^ (g+2) := by
    calc
      _ ≤ ∑ _e ∈ badSupports J f R g, p ^ (g+2) := by
        apply sum_le_sum
        intro e he
        exact pow_le_pow_of_le_one hp hp1 (badSupports_size hf he)
      _ = ((badSupports J f R g).card : ℝ) * p ^ (g+2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp _)
  refine ⟨B, avoids_bounded hR hB, ?_⟩
  simp only [Fintype.card_fin] at hcard
  linarith
end Family

#print axioms finite_selection
end Erdos773.SimultaneousDifferenceSelection
