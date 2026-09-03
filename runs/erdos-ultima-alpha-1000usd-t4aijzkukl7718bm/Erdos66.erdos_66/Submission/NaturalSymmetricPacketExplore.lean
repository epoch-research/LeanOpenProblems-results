import Submission.FiniteSwapAlgebraExplore

/-! Natural-number symmetric Sidon packets. The packet has a prescribed
central peak, and at most six ordered representations away from its center. -/
namespace Erdos66NaturalSymmetricPacket
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66NaturalSidonExtraction
  Erdos66FiniteSwapAlgebra
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def natPacket (n : ℕ) (E : Finset ℕ) : Finset ℕ := E ∪ natReflect n E

lemma natReflect_mem_iff (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, a ≤ n) (a : ℕ) :
    a ∈ natReflect n E ↔ a ≤ n ∧ n-a ∈ E := by
  simp only [natReflect, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hh := hE b hb
    exact ⟨by omega, by simpa only [Nat.sub_sub_self hh] using hb⟩
  · rintro ⟨han, ha⟩
    exact ⟨n-a, ha, by omega⟩

lemma natPacket_le (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, a ≤ n) :
    ∀ a ∈ natPacket n E, a ≤ n := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact hE a ha
  · exact (natReflect_mem_iff n E hE a).mp ha |>.1

lemma natPacket_symmetric (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, a ≤ n)
    {a : ℕ} (ha : a ∈ natPacket n E) : n-a ∈ natPacket n E := by
  rcases Finset.mem_union.mp ha with ha | ha
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · exact Finset.mem_union_left _ ((natReflect_mem_iff n E hE a).mp ha).2

lemma nat_lower_half_disjoint (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, 2*a < n) :
    Disjoint E (natReflect n E) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hb
  have hh := hE a ha
  have hh' := hE b hb
  omega

lemma natPacket_card (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, 2*a < n) :
    (natPacket n E).card = 2*E.card := by
  have hinj : Set.InjOn (fun a ↦ n-a) (E : Set ℕ) := by
    intro a ha b hb he
    dsimp only at he
    have hh := hE a ha
    have hh' := hE b hb
    omega
  rw [natPacket, Finset.card_union_of_disjoint (nat_lower_half_disjoint n E hE),
    natReflect, Finset.card_image_of_injOn hinj]
  omega

lemma natPacket_center (n : ℕ) (E : Finset ℕ) (hE : ∀ a ∈ E, a ≤ n) :
    sumRep (natPacket n E : Set ℕ) n = (natPacket n E).card := by
  rw [← pairs_self]
  exact pairs_eq_card_of_partner _ _ _ (fun a ha ↦
    ⟨natPacket_le n E hE a ha, natPacket_symmetric n E hE ha⟩)

lemma natPacket_mixed_center_zero (A E : Finset ℕ) (n : ℕ)
    (hE : ∀ a ∈ E, a ≤ n) (hdis : Disjoint A (natPacket n E)) :
    pairs (natPacket n E) A n = 0 := by
  apply pairs_eq_zero_of_no_partner
  intro a ha han hb
  exact Finset.disjoint_left.mp hdis hb (natPacket_symmetric n E hE ha)

lemma natSidon_reflected_mixed_le_one (E : Finset ℕ) (hE : NatSidon E) (n z : ℕ)
    (hn : ∀ a ∈ E, a ≤ n) (hz : z ≠ n) : pairs E (natReflect n E) z ≤ 1 := by
  rw [pairs_eq_filter, Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haE, haz, haR⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbE, hbz, hbR⟩ := Finset.mem_filter.mp hb
  obtain ⟨haN, ha'⟩ := (natReflect_mem_iff n E hn (z-a)).mp haR
  obtain ⟨hbN, hb'⟩ := (natReflect_mem_iff n E hn (z-b)).mp hbR
  have hh := hE a haE (n-(z-b)) hb' b hbE (n-(z-a)) ha' (by omega)
  rcases hh with ⟨hab, _⟩ | ⟨he, _⟩
  · exact hab
  · omega

lemma natPacket_off_center (E : Finset ℕ) (hE : NatSidon E) (n : ℕ)
    (hhalf : ∀ a ∈ E, 2*a < n) (z : ℕ) (hz : z ≠ n) :
    sumRep (natPacket n E : Set ℕ) z ≤ 6 := by
  have hn : ∀ a ∈ E, a ≤ n := fun a ha ↦ by have := hhalf a ha; omega
  rw [natPacket, sumRep_union_self _ _ _ (nat_lower_half_disjoint n E hhalf)]
  have h1 := natSidon_rep_le_two hE z
  have h2 := natSidon_reflected_mixed_le_one E hE n z hn hz
  have h3 := natSidon_rep_le_two (natReflect_sidon hE n hn) z
  omega

/-- Target accounting for a symmetric packet differs from anchored insertion:
all new target representations are new/new, not new/old. -/
lemma swapped_symmetric_target (A D E : Finset ℕ) (n : ℕ) (hD : D ⊆ A)
    (hE : ∀ a ∈ E, a ≤ n) (hdis : Disjoint A (natPacket n E))
    (hDA : pairs D A n = 0) :
    sumRep (swapped A D (natPacket n E) : Set ℕ) n =
      sumRep (A : Set ℕ) n + (natPacket n E).card := by
  have hcore : Disjoint (A\D) D := Finset.sdiff_disjoint
  have he : (A\D)∪D = A := Finset.sdiff_union_of_subset hD
  have hdd : sumRep (D : Set ℕ) n = 0 := by
    have hh := pairs_mono_right hD (A := D) n
    rw [pairs_self, hDA] at hh
    omega
  have hdc : pairs (A\D) D n = 0 := by
    have hh := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := D) n
    rw [pairs_comm D (A\D), hDA] at hh
    omega
  have hrep := sumRep_union_self (A\D) D n hcore
  rw [he, hdc, hdd] at hrep
  have hmix : pairs (A\D) (natPacket n E) n = 0 := by
    have hh := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := natPacket n E) n
    rw [natPacket_mixed_center_zero A E n hE hdis, pairs_comm] at hh
    omega
  change sumRep (((A\D)∪natPacket n E : Finset ℕ) : Set ℕ) n = _
  rw [sumRep_union_self _ _ _ (hdis.mono_left Finset.sdiff_subset), hmix,
    natPacket_center n E hE]
  omega

end Erdos66NaturalSymmetricPacket
