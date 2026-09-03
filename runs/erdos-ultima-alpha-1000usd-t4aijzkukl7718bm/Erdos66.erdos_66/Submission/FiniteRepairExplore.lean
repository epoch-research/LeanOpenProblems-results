import Submission.SidonSelectionExplore
import Submission.SymmetricSidonExplore

/-! A finite one-target repair, with an explicit uniform-selection criterion.
The collateral bounds are simultaneous, not target-by-target choices. -/
namespace Erdos66FiniteRepair
open Erdos66UniformSelection Erdos66SidonSelection Erdos66SymmetricSidon Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1200000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

noncomputable def forbidden (A : Finset ℤ) (n : ℤ) (x : α → ℤ) : Finset α :=
  Finset.univ.filter (fun a ↦ x a ∈ A ∨ n - x a ∈ A)

noncomputable def hitChoices (A : Finset ℤ) (n : ℤ) (x : α → ℤ) (z : ℤ) : Finset α :=
  Finset.univ.filter (fun a ↦ z - x a ∈ A ∨ z - (n - x a) ∈ A)

lemma pairCount_image_le {ι : Type*} [Fintype ι] (f : ι → ℤ) (A : Finset ℤ) (z : ℤ) :
    pairCount (Finset.univ.image f) A z ≤ (Finset.univ.filter (fun i ↦ z - f i ∈ A)).card := by
  rw [pairCount, Finset.filter_image]
  exact Finset.card_image_le

lemma packet_mixed_le_hits {ι : Type*} [Fintype ι]
    (A : Finset ℤ) (n : ℤ) (x : α → ℤ) (ω : ι → α)
    (hhalf : ∀ a : α, 2 * x a < n) (z : ℤ) :
    (pairCount (packet n (Finset.univ.image (x ∘ ω))) A z : ℝ) ≤
      2 * hits (hitChoices A n x z) ω := by
  let D := Finset.univ.image (x ∘ ω)
  have hD : ∀ a ∈ D, 2 * a < n := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hhalf _
  have href : reflected n D = Finset.univ.image (fun i ↦ n - x (ω i)) := by
    simp [reflected, D, Finset.image_image, Function.comp_def]
  have h₁ := pairCount_image_le (x ∘ ω) A z
  have h₂ := pairCount_image_le (fun i ↦ n - x (ω i)) A z
  let H := Finset.univ.filter (fun i : ι ↦ ω i ∈ hitChoices A n x z)
  have hsub₁ : Finset.univ.filter (fun i : ι ↦ z - (x ∘ ω) i ∈ A) ⊆ H := by
    intro i hi
    simp only [H, hitChoices, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
    exact Or.inl hi
  have hsub₂ : Finset.univ.filter (fun i : ι ↦ z - (n - x (ω i)) ∈ A) ⊆ H := by
    intro i hi
    simp only [H, hitChoices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inr hi
  have hh₁ := h₁.trans (Finset.card_le_card hsub₁)
  have hh₂ := h₂.trans (Finset.card_le_card hsub₂)
  have hhit : (H.card : ℝ) = hits (hitChoices A n x z) ω := by
    simp only [H, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hits]
  change (pairCount (packet n D) A z : ℝ) ≤ _
  rw [packet, pairCount_union_left _ _ _ _ (lower_half_disjoint hD), href, Nat.cast_add]
  have hh₁' : (pairCount D A z : ℝ) ≤ H.card := by exact_mod_cast hh₁
  have hh₂' : (pairCount (Finset.univ.image (fun i ↦ n - x (ω i))) A z : ℝ) ≤ H.card := by exact_mod_cast hh₂
  rw [hhit] at hh₁' hh₂'
  linarith

lemma packet_avoids (A : Finset ℤ) (n : ℤ) (x : α → ℤ)
    {ι : Type*} [Fintype ι] (ω : ι → α) (hω : ∀ i, ω i ∉ forbidden A n x) :
    Disjoint A (packet n (Finset.univ.image (x ∘ ω))) := by
  apply Finset.disjoint_left.mpr
  intro a ha hp
  rcases Finset.mem_union.mp hp with hD | hR
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
    exact hω i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ha⟩)
  · obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hR
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact hω i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (he ▸ ha)⟩)

lemma disjoint_packet_mixed_center (A D : Finset ℤ) (n : ℤ)
    (h : Disjoint A (packet n D)) : pairCount (packet n D) A n = 0 := by
  rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha hb
  exact Finset.disjoint_left.mp h hb (packet_symmetric.mpr ha)

/-- A single packet can repair one representation count exactly. Its choices
avoid the existing set and are uniformly spread relative to all target tests. -/
theorem exists_finite_repair (A : Finset ℤ) (n : ℤ) (x : α → ℤ)
    (hx : Function.Injective x) (hhalf : ∀ a, 2 * x a < n)
    (m : ℕ) (T : Finset ℤ) (K₀ K R t : ℝ)
    (hB : (forbidden A n x).card ≤ K₀)
    (hS : ∀ z ∈ T, (hitChoices A n x z).card ≤ K) (ht : 0 < t)
    (hsmall : ((m : ℝ) ^ 4 + m * K₀) / Fintype.card α +
      T.card * Real.exp ((m : ℝ) * Real.exp t * K / Fintype.card α - t * R) < 1) :
    ∃ C : Finset ℤ, C.card = 2 * m ∧ Disjoint A C ∧
      C ⊆ (Finset.univ.image x) ∪ reflected n (Finset.univ.image x) ∧
      (∀ a : ℤ, n - a ∈ C ↔ a ∈ C) ∧
      pairCount (A ∪ C) (A ∪ C) n = pairCount A A n + 2 * m ∧
      (∀ z : ℤ, z ≠ n → pairCount C C z ≤ 6) ∧
      ∀ z ∈ T, z ≠ n →
        (pairCount (A ∪ C) (A ∪ C) z : ℝ) - pairCount A A z < 4 * R + 6 := by
  have hsmall' : ((Fintype.card (Fin m) : ℝ) ^ 4 + Fintype.card (Fin m) * (forbidden A n x).card) /
      Fintype.card α + T.card * Real.exp ((Fintype.card (Fin m) : ℝ) * Real.exp t * K /
        Fintype.card α - t * R) < 1 := by
    simp only [Fintype.card_fin]
    have hh := div_le_div_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (α := ℝ) m)) ((m : ℝ) ^ 4))
      (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    simp only [add_div] at hh hsmall ⊢
    linarith
  obtain ⟨ω, hωinj, hωavoid, hsidon, hhits⟩ :=
    exists_sidon_avoid_and_hits (ι := Fin m) x hx (forbidden A n x) T
      (hitChoices A n x) K R t hS ht hsmall'
  let D : Finset ℤ := Finset.univ.image (x ∘ ω)
  have hDhalf : ∀ a ∈ D, 2 * a < n := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hhalf _
  have hDsidon : IsSidon D := by
    intro a ha b hb c hc d hd he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
    rcases hsidon i j k l he with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
    · exact Or.inl ⟨by rw [hik], by rw [hjl]⟩
    · exact Or.inr ⟨by rw [hil], by rw [hjk]⟩
  have hDcard : D.card = m := by
    dsimp only [D]
    rw [Finset.card_image_of_injective _ (hx.comp hωinj), Finset.card_univ, Fintype.card_fin]
  have hdis : Disjoint A (packet n D) := packet_avoids A n x ω hωavoid
  refine ⟨packet n D, by rw [packet_card hDhalf, hDcard], hdis, ?_,
    fun a ↦ packet_symmetric, ?_, packet_off_center hDsidon hDhalf, ?_⟩
  · have hsub : D ⊆ Finset.univ.image x := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨ω i, Finset.mem_univ _, rfl⟩
    exact Finset.union_subset_union hsub (Finset.image_subset_image hsub)
  · rw [pairCount_union_self _ _ _ hdis, disjoint_packet_mixed_center A D n hdis,
      packet_center hDhalf, hDcard]
    omega
  · intro z hz hzn
    have hcross := packet_mixed_le_hits A n x ω hhalf z
    have hself := packet_off_center hDsidon hDhalf z hzn
    have hself' : (pairCount (packet n D) (packet n D) z : ℝ) ≤ 6 := by exact_mod_cast hself
    have hh := hhits z hz
    rw [pairCount_union_self _ _ _ hdis]
    push_cast
    change (pairCount (packet n D) A z : ℝ) ≤ _ at hcross
    linarith

end Erdos66FiniteRepair
