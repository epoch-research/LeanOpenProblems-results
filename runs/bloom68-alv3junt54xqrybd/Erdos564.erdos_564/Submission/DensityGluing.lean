import Submission.SmallRamsey

/-!
# The four omitted-pair covering and its colour coherence

All four monochromatic facets force a monochromatic union. This is a
combinatorial equivalence, not a lower bound on the joint event's density.
-/
namespace Combinatorics.DensityRoute.Gluing

open Finset
universe u
variable {α : Type u} [DecidableEq α]

def Mono (c : Finset α → Bool) (S : Finset α) (b : Bool) : Prop :=
  ∀ e ∈ S.powersetCard 3, c e = b

lemma color_coherence (c : Finset α → Bool) {S T : Finset α} {b d : Bool}
    (hS : Mono c S b) (hT : Mono c T d) (hcard : 3 ≤ (S ∩ T).card) : b = d := by
  obtain ⟨e, he, hecard⟩ := exists_subset_card_eq hcard
  have hSe := hS e (mem_powersetCard.mpr ⟨he.trans inter_subset_left, hecard⟩)
  have hTe := hT e (mem_powersetCard.mpr ⟨he.trans inter_subset_right, hecard⟩)
  exact hSe.symm.trans hTe

/-- A triple cannot meet all four pairwise-disjoint omitted sets. -/
theorem cover_triples (V : Finset α) (P : Fin 4 → Finset α)
    (hdis : ∀ i j : Fin 4, i ≠ j → Disjoint (P i) (P j))
    (e : Finset α) (heV : e ⊆ V) (hecard : e.card ≤ 3) :
    ∃ i : Fin 4, e ⊆ V \ P i := by
  classical
  by_contra h
  have hx : ∀ i : Fin 4, ∃ x : α, x ∈ e ∧ x ∈ P i := by
    intro i
    have hi : ¬ e ⊆ V \ P i := fun hi => h ⟨i, hi⟩
    obtain ⟨x, hxe, hxnot⟩ := not_subset.mp hi
    refine ⟨x, hxe, ?_⟩
    by_contra hp
    exact hxnot (mem_sdiff.mpr ⟨heV hxe, hp⟩)
  choose x hxe hxP using hx
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    exact (disjoint_left.mp (hdis i j hne) (hxP i)) (hij.symm ▸ hxP j)
  have hsub : (univ.image x : Finset α) ⊆ e := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact hxe i
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj] at hcard
  simp only [card_univ, Fintype.card_fin] at hcard
  omega

/-- The four-facet event with a common colour equals the full monochromatic event. -/
theorem four_facet_same_color_iff (c : Finset α → Bool) (V : Finset α)
    (P : Fin 4 → Finset α)
    (hdis : ∀ i j : Fin 4, i ≠ j → Disjoint (P i) (P j)) (b : Bool) :
    (∀ i : Fin 4, Mono c (V \ P i) b) ↔ Mono c V b := by
  constructor
  · intro h e he
    obtain ⟨heV, hecard⟩ := mem_powersetCard.mp he
    obtain ⟨i, hi⟩ := cover_triples V P hdis e heV hecard.le
    exact h i e (mem_powersetCard.mpr ⟨hi, hecard⟩)
  · intro h i e he
    exact h e (powersetCard_mono sdiff_subset he)

/-- With at least seven union vertices and omitted sets of size at most two,
any two facets share a triple, so separate colour choices must agree. -/
theorem four_facet_mono_iff (c : Finset α → Bool) (V : Finset α)
    (P : Fin 4 → Finset α) (hV : 7 ≤ V.card)
    (hP : ∀ i : Fin 4, (P i).card ≤ 2)
    (hdis : ∀ i j : Fin 4, i ≠ j → Disjoint (P i) (P j)) :
    (∀ i : Fin 4, ∃ b : Bool, Mono c (V \ P i) b) ↔ ∃ b : Bool, Mono c V b := by
  classical
  constructor
  · intro h
    choose b hb using h
    have hcol : ∀ i : Fin 4, b i = b 0 := by
      intro i
      have hunion := card_union_le (P i) (P 0)
      have hdiff := le_card_sdiff (P i ∪ P 0) V
      rw [sdiff_union_distrib] at hdiff
      have hcard : 3 ≤ ((V \ P i) ∩ (V \ P 0)).card := by
        have hi := hP i
        have h0 := hP 0
        omega
      exact color_coherence c (hb i) (hb 0) hcard
    refine ⟨b 0, (four_facet_same_color_iff c V P hdis (b 0)).mp ?_⟩
    intro i
    rw [← hcol i]
    exact hb i
  · rintro ⟨b, hb⟩ i
    exact ⟨b, (four_facet_same_color_iff c V P hdis b).mpr hb i⟩

end Combinatorics.DensityRoute.Gluing
