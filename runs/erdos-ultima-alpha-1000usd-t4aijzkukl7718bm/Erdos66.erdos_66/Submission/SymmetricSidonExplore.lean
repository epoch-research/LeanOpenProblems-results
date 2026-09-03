import Submission.OriginRepairExplore
import Submission.CarryExplore

/-! A symmetric Sidon packet creates many representations at one target and
at most six self-representations at every other target. -/
namespace Erdos66SymmetricSidon
open Erdos66OriginRepair AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1000000

def IsSidon (D : Finset ℤ) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D, a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

noncomputable def reflected (n : ℤ) (D : Finset ℤ) : Finset ℤ :=
  D.image (fun a ↦ n - a)

noncomputable def packet (n : ℤ) (D : Finset ℤ) : Finset ℤ := D ∪ reflected n D

lemma mem_reflected {n a : ℤ} {D : Finset ℤ} :
    a ∈ reflected n D ↔ n - a ∈ D := by
  simp only [reflected, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro h
    exact ⟨n - a, h, by omega⟩

lemma sidon_self_le_two {D : Finset ℤ} (hD : IsSidon D) (z : ℤ) :
    pairCount D D z ≤ 2 := by
  let F := D.filter (fun a ↦ z - a ∈ D)
  by_cases hF : F.Nonempty
  · obtain ⟨a, ha⟩ := hF
    obtain ⟨haD, ha'⟩ := Finset.mem_filter.mp ha
    have hsub : F ⊆ {a, z - a} := by
      intro b hb
      obtain ⟨hbD, hb'⟩ := Finset.mem_filter.mp hb
      have hh := hD b hbD (z - b) hb' a haD (z - a) ha' (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 2
    simp [he]

lemma sidon_reflected {D : Finset ℤ} (hD : IsSidon D) (n : ℤ) : IsSidon (reflected n D) := by
  intro a ha b hb c hc d hd he
  have hh := hD (n - a) (mem_reflected.mp ha) (n - b) (mem_reflected.mp hb)
    (n - c) (mem_reflected.mp hc) (n - d) (mem_reflected.mp hd) (by omega)
  rcases hh with ⟨hh, hh'⟩ | ⟨hh, hh'⟩ <;> omega

lemma sidon_reflected_mixed_le_one {D : Finset ℤ} (hD : IsSidon D) (n z : ℤ) (hz : z ≠ n) :
    pairCount D (reflected n D) z ≤ 1 := by
  rw [pairCount, Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haD, ha'⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbD, hb'⟩ := Finset.mem_filter.mp hb
  have ha'' := mem_reflected.mp ha'
  have hb'' := mem_reflected.mp hb'
  have hh := hD a haD (n - (z - b)) hb'' b hbD (n - (z - a)) ha'' (by omega)
  rcases hh with ⟨hab, _⟩ | ⟨he, _⟩
  · exact hab
  · omega

lemma reflected_mixed_center (n : ℤ) (D : Finset ℤ) :
    pairCount D (reflected n D) n = D.card := by
  rw [pairCount]
  have he : D.filter (fun a ↦ n - a ∈ reflected n D) = D := by
    ext a
    simp only [Finset.mem_filter, mem_reflected]
    simp
  rw [he]

lemma lower_half_disjoint {n : ℤ} {D : Finset ℤ} (hD : ∀ a ∈ D, 2 * a < n) :
    Disjoint D (reflected n D) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hb' := mem_reflected.mp hb
  have hh := hD a ha
  have hh' := hD (n - a) hb'
  omega

lemma lower_half_center_zero {n : ℤ} {D : Finset ℤ} (hD : ∀ a ∈ D, 2 * a < n) :
    pairCount D D n = 0 ∧ pairCount (reflected n D) (reflected n D) n = 0 := by
  constructor
  · rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hb
    have hh := hD a ha
    have hh' := hD (n - a) hb
    omega
  · rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hb
    have ha' := mem_reflected.mp ha
    have hb' := mem_reflected.mp hb
    have hh := hD (n - a) ha'
    have hh' := hD (n - (n - a)) hb'
    omega

lemma packet_center {n : ℤ} {D : Finset ℤ} (hD : ∀ a ∈ D, 2 * a < n) :
    pairCount (packet n D) (packet n D) n = 2 * D.card := by
  rw [packet, pairCount_union_self _ _ _ (lower_half_disjoint hD),
    (lower_half_center_zero hD).1, (lower_half_center_zero hD).2,
    pairCount_comm (reflected n D), reflected_mixed_center]
  omega

lemma packet_off_center {n : ℤ} {D : Finset ℤ} (hD : IsSidon D)
    (hhalf : ∀ a ∈ D, 2 * a < n) (z : ℤ) (hz : z ≠ n) :
    pairCount (packet n D) (packet n D) z ≤ 6 := by
  rw [packet, pairCount_union_self _ _ _ (lower_half_disjoint hhalf),
    pairCount_comm (reflected n D)]
  have h₁ := sidon_self_le_two hD z
  have h₂ := sidon_reflected_mixed_le_one hD n z hz
  have h₃ := sidon_self_le_two (sidon_reflected hD n) z
  omega

lemma packet_card {n : ℤ} {D : Finset ℤ} (hD : ∀ a ∈ D, 2 * a < n) :
    (packet n D).card = 2 * D.card := by
  rw [packet, Finset.card_union_of_disjoint (lower_half_disjoint hD), reflected,
    Finset.card_image_of_injective _ (fun a b h ↦ by omega)]
  omega

lemma packet_symmetric {n a : ℤ} {D : Finset ℤ} :
    n - a ∈ packet n D ↔ a ∈ packet n D := by
  simp only [packet, Finset.mem_union, mem_reflected]
  simp [or_comm]

/-- Convert the finite integer pair count to the ordinary natural-number
representation count whenever all packet points are nonnegative. -/
lemma pairCount_eq_sumRep_toNat (C : Finset ℤ) (hC : ∀ a ∈ C, 0 ≤ a) (z : ℕ) :
    pairCount C C (z : ℤ) = sumRep ((C.image Int.toNat : Finset ℕ) : Set ℕ) z := by
  have hinj : Set.InjOn Int.toNat (C : Set ℤ) := by
    intro a ha b hb he
    have he' := congrArg (fun x : ℕ ↦ (x : ℤ)) he
    simpa only [Int.toNat_of_nonneg (hC a ha), Int.toNat_of_nonneg (hC b hb)] using he'
  rw [sumRep_def]
  let F := C.filter (fun a ↦ (z : ℤ) - a ∈ C)
  let Q := (Finset.antidiagonal z).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ (C.image Int.toNat : Finset ℕ) ∧ p.2 ∈ (C.image Int.toNat : Finset ℕ))
  let f : ℤ → ℕ × ℕ := fun a ↦ (a.toNat, ((z : ℤ) - a).toNat)
  have himage : F.image f = Q := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_antidiagonal, F, Q, f]
    constructor
    · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
      refine ⟨?_, ⟨a, ha, rfl⟩, ⟨(z : ℤ) - a, ha', rfl⟩⟩
      have he : (a.toNat : ℤ) + (((z : ℤ) - a).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg (hC a ha), Int.toNat_of_nonneg (hC _ ha')]
        omega
      exact_mod_cast he
    · rintro ⟨hs, ⟨a, ha, haeq⟩, ⟨b, hb, hbeq⟩⟩
      have he : a + b = (z : ℤ) := by
        have hh : (a.toNat : ℤ) + (b.toNat : ℤ) = z := by exact_mod_cast (show a.toNat + b.toNat = z by omega)
        simpa only [Int.toNat_of_nonneg (hC a ha), Int.toNat_of_nonneg (hC b hb)] using hh
      have hb' : (z : ℤ) - a = b := by omega
      exact ⟨a, ⟨ha, hb' ▸ hb⟩, Prod.ext haeq (by rw [hb']; exact hbeq)⟩
  have hfinj : Set.InjOn f (F : Set ℤ) := by
    intro a ha b hb he
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 (congrArg Prod.fst he)
  have he : F.card = Q.card := by
    rw [← Finset.card_image_of_injOn hfinj, himage]
  calc
    _ = F.card := rfl
    _ = Q.card := he
    _ = _ := by congr 1; ext p; simp [Q]

end Erdos66SymmetricSidon
