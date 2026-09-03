import FormalConjecturesUtil

/-!
A translated-intersection reduction for square-Sidon sets.  This does not
supply a bound on simultaneous Sidon sets, and does not settle Erdős 773.
-/
namespace Erdos773.TranslatedIntersectionSelection
open Finset
set_option maxHeartbeats 1000000

/-- Roots which remain in `A` after the positive translation `h`. -/
def overlap (A : Finset ℕ) (h : ℕ) : Finset ℕ :=
  A.filter (fun a => a + h ∈ A)

lemma overlap_subset (A : Finset ℕ) (h : ℕ) : overlap A h ⊆ A :=
  filter_subset _ _

lemma translate_overlap_subset (A : Finset ℕ) (h : ℕ) :
    (overlap A h).image (fun a => a + h) ⊆ A := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  exact (mem_filter.mp hb).2

/-- Bounding every positive translate intersection bounds the pair count. -/
theorem pair_count_bound (N K : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hK : ∀ h ∈ Icc 1 N, (overlap A h).card ≤ K) :
    A.card * (A.card - 1) ≤ 2 * N * K := by
  let P := (A ×ˢ A).filter (fun p => p.1 < p.2)
  have hcover : A.offDiag ⊆ P ∪ P.image Prod.swap := by
    intro p hp
    obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp hp
    rcases lt_or_gt_of_ne hab with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, h⟩)
    · apply mem_union_right
      exact mem_image.mpr ⟨p.swap,
        mem_filter.mpr ⟨mem_product.mpr ⟨hb, ha⟩, h⟩, Prod.swap_swap p⟩
  have hpair : A.card * (A.card - 1) ≤ 2 * P.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le P (P.image Prod.swap)
    have h3 := card_image_le (s := P) (f := Prod.swap)
    rw [offDiag_card] at h1
    rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  have hgap {p : ℕ × ℕ} (hp : p ∈ P) : p.2 - p.1 ∈ Icc 1 N := by
    obtain ⟨hp, hlt⟩ := mem_filter.mp hp
    obtain ⟨ha, hb⟩ := mem_product.mp hp
    have hbN := (mem_Icc.mp (hA hb)).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : P.card = ∑ h ∈ Icc 1 N,
      (P.filter (fun p => p.2 - p.1 = h)).card :=
    card_eq_sum_card_fiberwise (fun _ hp => hgap hp)
  have hfiber (h : ℕ) (hh : h ∈ Icc 1 N) :
      (P.filter (fun p => p.2 - p.1 = h)).card ≤ K := by
    apply le_trans ?_ (hK h hh)
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨hp, hlt⟩ := mem_filter.mp hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      apply mem_filter.mpr
      exact ⟨ha, by convert hb using 1; omega⟩
    · intro p hp q hq he
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have hp'' := (mem_filter.mp (mem_filter.mp hp).1).2
      have hq'' := (mem_filter.mp (mem_filter.mp hq).1).2
      apply Prod.ext he
      omega
  have hP : P.card ≤ N * K := by
    rw [hsum]
    calc
      _ ≤ ∑ h ∈ Icc 1 N, K := sum_le_sum hfiber
      _ = N * K := by simp
  calc
    _ ≤ 2 * P.card := hpair
    _ ≤ 2 * (N * K) := Nat.mul_le_mul_left 2 hP
    _ = _ := by ring

/-- A large root set has a large intersection with some nonzero translate.
The shift is selected existentially, not prescribed in advance. -/
theorem exists_large_overlap (N : ℕ) (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N) :
    ∃ h ∈ Icc 1 N,
      A.card * (A.card - 1) ≤ 2 * N * (overlap A h).card := by
  obtain ⟨h, hh, hmax⟩ := exists_max_image (Icc 1 N)
    (fun h => (overlap A h).card) (nonempty_Icc.mpr hN)
  exact ⟨h, hh, pair_count_bound N _ A hA hmax⟩

/-- Both square maps on the extracted roots are Sidon because their images
are subsets of the original Sidon square set. -/
theorem extract_two_shifts (N : ℕ) (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ h ∈ Icc 1 N, ∃ B : Finset ℕ,
      B ⊆ A ∧ B.image (fun a => a + h) ⊆ A ∧
      A.card * (A.card - 1) ≤ 2 * N * B.card ∧
      IsSidon ((B.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ) ∧
      IsSidon ((B.image (fun a => (a + h) ^ 2) : Finset ℕ) : Set ℕ) := by
  obtain ⟨h, hh, hcard⟩ := exists_large_overlap N hN A hA
  refine ⟨h, hh, overlap A h, overlap_subset A h,
    translate_overlap_subset A h, hcard, ?_, ?_⟩
  · apply Set.IsSidon.subset hSidon
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨a, overlap_subset A h ha, rfl⟩
  · apply Set.IsSidon.subset hSidon
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨a + h, (mem_filter.mp ha).2, rfl⟩

/-- The whole union of the two translated copies is Sidon in squares.
This is stronger than merely requiring each copy separately to be Sidon. -/
theorem extract_sidon_union (N : ℕ) (hN : 0 < N) (A : Finset ℕ)
    (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    ∃ h ∈ Icc 1 N, ∃ B : Finset ℕ,
      B ∪ B.image (fun a => a + h) ⊆ A ∧
      A.card * (A.card - 1) ≤ 2 * N * B.card ∧
      IsSidon ((((B ∪ B.image (fun a => a + h)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) := by
  obtain ⟨h, hh, hcard⟩ := exists_large_overlap N hN A hA
  have hsub : overlap A h ∪ (overlap A h).image (fun a => a + h) ⊆ A :=
    union_subset (overlap_subset A h) (translate_overlap_subset A h)
  refine ⟨h, hh, overlap A h, hsub, hcard, ?_⟩
  apply Set.IsSidon.subset hSidon
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨a, hsub ha, rfl⟩

/-- A *uniform* two-shift upper bound would transfer to the original problem.
No such upper bound is asserted here. -/
theorem uniform_two_shift_bound_transfers (N K : ℕ) (hN : 0 < N)
    (hK : ∀ h ∈ Icc 1 N, ∀ B : Finset ℕ,
      B ⊆ Icc 1 N → B.image (fun a => a + h) ⊆ Icc 1 N →
      IsSidon ((B.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ) →
      IsSidon ((B.image (fun a => (a + h) ^ 2) : Finset ℕ) : Set ℕ) →
      B.card ≤ K)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    A.card * (A.card - 1) ≤ 2 * N * K := by
  obtain ⟨h, hh, B, hBA, hBtA, hcard, hs0, hsh⟩ :=
    extract_two_shifts N hN A hA hSidon
  exact hcard.trans (Nat.mul_le_mul_left (2 * N)
    (hK h hh B (hBA.trans hA) (hBtA.trans hA) hs0 hsh))

/-- Even an upper bound restricted to Sidon *unions* would suffice for this
transfer. The missing upper bound remains an explicit hypothesis. -/
theorem uniform_union_bound_transfers (N K : ℕ) (hN : 0 < N)
    (hK : ∀ h ∈ Icc 1 N, ∀ B : Finset ℕ,
      B ∪ B.image (fun a => a + h) ⊆ Icc 1 N →
      IsSidon ((((B ∪ B.image (fun a => a + h)).image
        (fun a => a ^ 2)) : Finset ℕ) : Set ℕ) → B.card ≤ K)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hSidon : IsSidon ((A.image (fun a => a ^ 2) : Finset ℕ) : Set ℕ)) :
    A.card * (A.card - 1) ≤ 2 * N * K := by
  obtain ⟨h, hh, B, hBA, hcard, hs⟩ := extract_sidon_union N hN A hA hSidon
  exact hcard.trans (Nat.mul_le_mul_left (2 * N) (hK h hh B (hBA.trans hA) hs))

#print axioms pair_count_bound
#print axioms exists_large_overlap
#print axioms extract_two_shifts
#print axioms extract_sidon_union
#print axioms uniform_two_shift_bound_transfers
#print axioms uniform_union_bound_transfers
end Erdos773.TranslatedIntersectionSelection
