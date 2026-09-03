import Submission.IntegerDifferenceCapacity

/-!
Forbidden supports for bounded multiplicity of sums of distinct entries.
This is a generic integer-set construction, not a claim about squares.
-/
namespace Erdos773.IntegerSumCapacity
open Finset IntegerDifferenceCapacity
set_option maxHeartbeats 1000000

def sumReps (B : Finset ℕ) (S : ℕ) : Finset (ℕ × ℕ) :=
  (B ×ˢ B).filter (fun ab => ab.1 < ab.2 ∧ ab.1+ab.2=S)

def obstructions (m g : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 (2*m)).biUnion (fun S =>
    ((sumReps (Icc 1 m) S).powersetCard (g+1)).image support)).filter
      (fun e => e.card=2*(g+1))

lemma fst_injective {B : Finset ℕ} {S : ℕ} :
    Set.InjOn Prod.fst (sumReps B S : Set (ℕ × ℕ)) := by
  intro ab hab cd hcd he
  have hp := (mem_filter.mp hab).2.2
  have hq := (mem_filter.mp hcd).2.2
  exact Prod.ext he (by omega)

lemma snd_injective {B : Finset ℕ} {S : ℕ} :
    Set.InjOn Prod.snd (sumReps B S : Set (ℕ × ℕ)) := by
  intro ab hab cd hcd he
  have hp := (mem_filter.mp hab).2.2
  have hq := (mem_filter.mp hcd).2.2
  exact Prod.ext (by omega) he

lemma sumReps_card (B : Finset ℕ) (S : ℕ) : (sumReps B S).card ≤ B.card := by
  exact card_le_card_of_injOn Prod.fst
    (fun ab hab => (mem_product.mp (mem_filter.mp hab).1).1) fst_injective

lemma support_subset {B : Finset ℕ} {S : ℕ} {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ sumReps B S) : support E ⊆ B := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (mem_filter.mp (hE hab)).1).1
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (mem_filter.mp (hE hab)).1).2

/-- Distinct ordered sum representations are disjoint pairs, without an
additional AP-free hypothesis. -/
lemma support_card {B : Finset ℕ} {S : ℕ} {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ sumReps B S) : (support E).card=2*E.card := by
  have hdis : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨ab,hab,hea⟩ := mem_image.mp ha
    obtain ⟨cd,hcd,heb⟩ := mem_image.mp hb
    have hp := (mem_filter.mp (hE hab)).2
    have hq := (mem_filter.mp (hE hcd)).2
    omega
  unfold support
  rw [card_union_of_disjoint hdis,
    card_image_of_injOn (fun p hp q hq he => fst_injective (hE hp) (hE hq) he),
    card_image_of_injOn (fun p hp q hq he => snd_injective (hE hp) (hE hq) he)]
  omega

lemma obstructions_card (m g : ℕ) : (obstructions m g).card ≤ 2*m^(g+2) := by
  calc
    _ ≤ ((Icc 1 (2*m)).biUnion (fun S =>
        ((sumReps (Icc 1 m) S).powersetCard (g+1)).image support)).card := card_filter_le _ _
    _ ≤ ∑ S ∈ Icc 1 (2*m),
        (((sumReps (Icc 1 m) S).powersetCard (g+1)).image support).card := card_biUnion_le
    _ ≤ ∑ _S ∈ Icc 1 (2*m), m^(g+1) := by
      apply sum_le_sum
      intro S hS
      apply card_image_le.trans
      rw [card_powersetCard]
      apply (Nat.choose_le_pow _ _).trans
      apply Nat.pow_le_pow_left
      simpa using sumReps_card (Icc 1 m) S
    _ = _ := by simp [pow_succ]; ring

lemma obstructions_size {m g : ℕ} {e : Finset ℕ} (he : e ∈ obstructions m g) :
    e.card=2*(g+1) := (mem_filter.mp he).2

lemma obstructions_subset {m g : ℕ} {e : Finset ℕ} (he : e ∈ obstructions m g) :
    e ⊆ Icc 1 m := by
  obtain ⟨S,hS,he⟩ := mem_biUnion.mp (mem_filter.mp he).1
  obtain ⟨E,hE,rfl⟩ := mem_image.mp he
  exact support_subset (mem_powersetCard.mp hE).1

lemma capacity_of_avoids {m g : ℕ} {B : Finset ℕ} (hB : B ⊆ Icc 1 m)
    (havoid : ∀ e ∈ obstructions m g, ¬e ⊆ B) :
    ∀ S, (sumReps B S).card ≤ g := by
  intro S
  by_contra! hlarge
  obtain ⟨E,hE,hcard⟩ := exists_subset_card_eq (show g+1 ≤ (sumReps B S).card by omega)
  have hE' : E ⊆ sumReps (Icc 1 m) S := by
    intro ab hab
    obtain ⟨habB,habS⟩ := mem_filter.mp (hE hab)
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨hB (mem_product.mp habB).1,hB (mem_product.mp habB).2⟩,habS⟩
  have hSm : 1 ≤ S ∧ S ≤ 2*m := by
    obtain ⟨ab,hab⟩ := card_pos.mp (show 0<E.card by omega)
    obtain ⟨hp,hq⟩ := mem_filter.mp (hE' hab)
    have ha := mem_Icc.mp (mem_product.mp hp).1
    have hb := mem_Icc.mp (mem_product.mp hp).2
    omega
  apply havoid (support E) _ (support_subset hE)
  apply mem_filter.mpr
  refine ⟨mem_biUnion.mpr ⟨S,mem_Icc.mpr hSm,
    mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hE',hcard⟩,rfl⟩⟩,?_⟩
  rw [support_card hE,hcard]

/-- The non-strict convention also counts a possible diagonal pair. -/
def unorderedSumReps (B : Finset ℕ) (S : ℕ) : Finset (ℕ × ℕ) :=
  (B ×ˢ B).filter (fun ab => ab.1 ≤ ab.2 ∧ ab.1+ab.2=S)

lemma unordered_capacity {B : Finset ℕ} {g : ℕ} (hg : 1 ≤ g)
    (hAP : ThreeAPFree (B:Set ℕ)) (hc : ∀ S, (sumReps B S).card ≤ g) :
    ∀ S, (unorderedSumReps B S).card ≤ g := by
  intro S
  by_cases hd : ∃ a ∈ B, a+a=S
  · obtain ⟨a,ha,he⟩ := hd
    have hsub : unorderedSumReps B S ⊆ {(a,a)} := by
      intro ab hab
      obtain ⟨hp,hq⟩ := mem_filter.mp hab
      have hx := hAP (mem_product.mp hp).1 ha (mem_product.mp hp).2 (by omega)
      have hy : ab.2=a := by omega
      exact mem_singleton.mpr (Prod.ext hx hy)
    exact (card_le_card hsub).trans (by simpa using hg)
  · have heq : unorderedSumReps B S = sumReps B S := by
      ext ab
      simp only [unorderedSumReps,sumReps,mem_filter]
      constructor
      · rintro ⟨hp,hle,he⟩
        refine ⟨hp,?_,he⟩
        have hne : ab.1 ≠ ab.2 := by
          intro heq
          exact hd ⟨ab.1,(mem_product.mp hp).1,by omega⟩
        omega
      · rintro ⟨hp,hlt,he⟩
        exact ⟨hp,hlt.le,he⟩
    rw [heq]
    exact hc S

#print axioms support_card
#print axioms obstructions_card
#print axioms capacity_of_avoids
#print axioms unordered_capacity
end Erdos773.IntegerSumCapacity
