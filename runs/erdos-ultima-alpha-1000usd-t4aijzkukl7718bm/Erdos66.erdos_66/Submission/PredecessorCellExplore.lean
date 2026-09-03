import Submission.ProfileLowerGapExplore
import Submission.OrderedPartialReplacementExplore

/-! Predecessor cells and finite count-preserving repairs. No global repair
or representation-limit assertion is made in this file. -/
namespace Erdos66PredecessorCell
open Erdos66ProfileLowerGap Erdos66ReflectionRoundingPatch Erdos66Fractional
  Erdos66Counting Erdos66Generating Erdos66Rounding Erdos66OrderedPartialReplacement
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def predecessor (A : Set ℕ) (u : ℕ) : ℕ :=
  Nat.findGreatest (fun a ↦ a ∈ A) u

lemma predecessor_le (A : Set ℕ) (u : ℕ) : predecessor A u ≤ u :=
  Nat.findGreatest_le _

lemma le_predecessor (A : Set ℕ) {a u : ℕ} (ha : a ∈ A) (hau : a ≤ u) :
    a ≤ predecessor A u := Nat.le_findGreatest hau ha

lemma predecessor_mem (A : Set ℕ) {u : ℕ} (h : ∃ a ≤ u, a ∈ A) :
    predecessor A u ∈ A := by
  obtain ⟨a, hau, ha⟩ := h
  exact Nat.findGreatest_spec hau ha

lemma predecessor_mono (A : Set ℕ) : Monotone (predecessor A) :=
  fun _ _ h ↦ Nat.findGreatest_mono_right (fun a ↦ a ∈ A) h

lemma predecessor_lt_of_not_mem (A : Set ℕ) {u : ℕ}
    (h : ∃ a ≤ u, a ∈ A) (hu : u ∉ A) : predecessor A u < u := by
  have hm := predecessor_mem A h
  have hl := predecessor_le A u
  by_contra hn
  have he : predecessor A u = u := by omega
  exact hu (he ▸ hm)

lemma no_old_point_in_cell (A : Set ℕ) {u a : ℕ}
    (hlo : predecessor A u < a) (hhi : a ≤ u) : a ∉ A :=
  Nat.findGreatest_is_greatest hlo hhi

lemma disjoint_cell_order (A : Set ℕ) {u v : ℕ}
    (hv : predecessor A v ∈ A) (huv : predecessor A u < predecessor A v) :
    u < predecessor A v := by
  by_contra hn
  exact no_old_point_in_cell A huv (by omega) hv

/-- The exact harmonic profile gives a square-root bound on the distance to
an old point to the left, without requiring profile regular variation. -/
lemma predecessor_gap_of_profile (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hA : ∀ N, |(count A N : ℝ) - cumulative profile N| ≤ D)
    (u H : ℕ) (hH : H ≤ u + 1)
    (hlen : 2 * D * Real.sqrt ((u + 1 : ℕ) : ℝ) < H) :
    predecessor A u ∈ A ∧ u < predecessor A u + H := by
  have he : u + 1 - H + H = u + 1 := by omega
  have hn := interval_nonempty_of_length A D hD hA (u + 1 - H) H
    (by simpa only [he] using hlen)
  obtain ⟨a, ha⟩ := hn
  obtain ⟨hai, haA⟩ := Finset.mem_filter.mp ha
  obtain ⟨hal, hau⟩ := Finset.mem_Ico.mp hai
  rw [he] at hau
  have hau' : a ≤ u := by omega
  have hp := le_predecessor A haA hau'
  exact ⟨predecessor_mem A ⟨a, hau', haA⟩, by omega⟩

lemma fiber_card_le (A : Set ℕ) (C : Finset ℕ) (H : ℕ)
    (hgap : ∀ u ∈ C, u < predecessor A u + H) (r : ℕ) :
    (C.filter (fun u ↦ predecessor A u = r)).card ≤ H := by
  have hsub : C.filter (fun u ↦ predecessor A u = r) ⊆ Finset.Ico r (r + H) := by
    intro u hu
    obtain ⟨huC, hu⟩ := Finset.mem_filter.mp hu
    have hl := predecessor_le A u
    have hh := hgap u huC
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hh := Finset.card_le_card hsub
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hh

/-- At most one of a family of moves from distinct predecessor cells can
cross a given prefix cutoff. -/
lemma crossing_card_le_one (A : Set ℕ) (F : Finset ℕ)
    (hmem : ∀ u ∈ F, predecessor A u ∈ A)
    (hinj : Set.InjOn (predecessor A) (F : Set ℕ)) (N : ℕ) :
    (F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  obtain ⟨huF, huN, hNu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvF, hvN, hNv⟩ := Finset.mem_filter.mp hv
  apply hinj huF hvF
  rcases lt_trichotomy (predecessor A u) (predecessor A v) with h | h | h
  · have hh := disjoint_cell_order A (hmem v hvF) h
    omega
  · exact h
  · have hh := disjoint_cell_order A (hmem u huF) h
    omega

lemma predecessor_prefix_card (A : Set ℕ) (F : Finset ℕ)
    (hinj : Set.InjOn (predecessor A) (F : Set ℕ)) (N : ℕ) :
    ((F.image (predecessor A)) ∩ Finset.range N).card =
      (F.filter (fun u ↦ predecessor A u < N)).card := by
  have he : (F.image (predecessor A)) ∩ Finset.range N =
      (F.filter (fun u ↦ predecessor A u < N)).image (predecessor A) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hN⟩
      exact ⟨u, ⟨hu, hN⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hN⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, hN⟩
  rw [he, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]

lemma predecessor_prefix_split (A : Set ℕ) (F : Finset ℕ) (N : ℕ) :
    (F.filter (fun u ↦ predecessor A u < N)).card =
      (F ∩ Finset.range N).card +
        (F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)).card := by
  have he : F.filter (fun u ↦ predecessor A u < N) = (F ∩ Finset.range N) ∪
      (F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Finset.mem_range]
    have hh := predecessor_le A u
    by_cases huF : u ∈ F <;> simp only [huF, true_and, false_and, false_or] <;> omega
  have hd : Disjoint (F ∩ Finset.range N)
      (F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hh := Finset.mem_range.mp (Finset.mem_inter.mp hu).2
    have hh' := (Finset.mem_filter.mp hv).2.2
    omega
  rw [he, Finset.card_union_of_disjoint hd]

/-- Replacing any finite selection of distinct predecessor cells changes
every prefix count by zero or minus one, regardless of the number of moves. -/
theorem predecessor_swap_prefix (A : Set ℕ) (F : Finset ℕ)
    (hmem : ∀ u ∈ F, predecessor A u ∈ A) (hnew : ∀ u ∈ F, u ∉ A)
    (hinj : Set.InjOn (predecessor A) (F : Set ℕ)) (N : ℕ) :
    -1 ≤ (count (swap A (F.image (predecessor A)) F) N : ℝ) - count A N ∧
      (count (swap A (F.image (predecessor A)) F) N : ℝ) - count A N ≤ 0 := by
  have hD : (F.image (predecessor A) : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    exact hmem u hu
  have hF : Disjoint (F : Set ℕ) A := Set.disjoint_left.mpr (fun u hu ↦ hnew u hu)
  rw [swap_count_difference A _ _ hD hF, predecessor_prefix_card A F hinj N,
    predecessor_prefix_split A F N, Nat.cast_add]
  have hh : ((F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)).card : ℝ) ≤ 1 :=
    by exact_mod_cast crossing_card_le_one A F hmem hinj N
  have h0 := Nat.cast_nonneg (α := ℝ) (F.filter (fun u ↦ predecessor A u < N ∧ N ≤ u)).card
  constructor <;> linarith

lemma predecessor_swap_card (A : Set ℕ) (F : Finset ℕ)
    (hinj : Set.InjOn (predecessor A) (F : Set ℕ)) :
    (F.image (predecessor A)).card = F.card := Finset.card_image_of_injOn hinj

end Erdos66PredecessorCell
