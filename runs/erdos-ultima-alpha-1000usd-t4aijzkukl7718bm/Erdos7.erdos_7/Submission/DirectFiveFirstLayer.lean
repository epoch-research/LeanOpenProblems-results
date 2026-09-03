import Submission.DirectFiveLayers

/-! Pointwise control of the first prime layer and of an extra pure class. -/
namespace Erdos7DirectFiveFirstLayer
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

lemma first_layer_fraction {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i₀ : Fin n) (hi₀ : i₀.val=0) (p E : ℕ) (hp : 1 < p)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e) (he : ∀ k, e k i₀ ≤ E)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k, fraction (X k i₀) ≤ ((p : ℚ)⁻¹)^(e k i₀))
    (σ : κ → Fin n) (hσ : ∀ k, σ k∈expSupport (e k))
    (hS : ∀ k j, j∈expSupport (e k) → j≤σ k) (x : ∀ i, A i) :
    coordinateFraction A i₀ (layeredBad A (fun k => expSupport (e k)) X σ i₀) x ≤ 1/(p-1 : ℚ) := by
  classical
  let K := layerFamily σ i₀
  have hpos (k : κ) (hk : k∈K) : 0 < e k i₀ := by
    have hs := hσ k
    rw [(Finset.mem_filter.mp hk).2] at hs
    have hh := (mem_expSupport _ _).mp hs
    omega
  have hzero (k : κ) (hk : k∈K) (j : Fin n) (hj : j≠i₀) : e k j=0 := by
    by_contra h
    have hh := hS k j ((mem_expSupport _ _).mpr h)
    rw [(Finset.mem_filter.mp hk).2] at hh
    apply hj
    apply Fin.ext
    have hh' : j.val ≤ i₀.val := hh
    omega
  have hin : Set.InjOn (fun k : κ => e k i₀-1) (K : Set κ) := by
    intro k hk l hl hkl
    change e k i₀-1=e l i₀-1 at hkl
    apply hei
    funext j
    by_cases hj : j=i₀
    · subst j
      have hp := hpos k hk
      have hq := hpos l hl
      omega
    · rw [hzero k hk j hj,hzero l hl j hj]
  have hsub : K.image (fun k => e k i₀-1) ⊆ Finset.range E := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hg
    apply Finset.mem_range.mpr
    have hp := hpos k hk
    have hle := he k
    omega
  have himage : (∑ k∈K, ((p : ℚ)⁻¹)^(e k i₀)) =
      ∑ g∈K.image (fun k => e k i₀-1), ((p : ℚ)⁻¹)^(g+1) := by
    rw [Finset.sum_image hin]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.sub_add_cancel (hpos k hk)]
  calc
    _ ≤ ∑ k∈K, fraction (X k i₀)*boxIndicator A ((expSupport (e k)).erase i₀) (X k) x :=
      layered_fraction_bound A (fun k => expSupport (e k)) X σ hσ i₀ x
    _ ≤ ∑ k∈K, ((p : ℚ)⁻¹)^(e k i₀) := by
      apply Finset.sum_le_sum
      intro k hk
      have hb : boxIndicator A ((expSupport (e k)).erase i₀) (X k) x ≤ 1 := by
        unfold boxIndicator
        split_ifs <;> norm_num
      exact (mul_le_mul_of_nonneg_left hb (fraction_nonneg _)).trans (by simpa using hX k)
    _ = _ := himage
    _ ≤ ∑ g∈Finset.range E, ((p : ℚ)⁻¹)^(g+1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := positive_power_sum_le p hp E

lemma fraction_union {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (S T : Finset α) : fraction (S∪T) ≤ fraction S+fraction T := by
  unfold fraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ card_pos_rat.le
  exact_mod_cast Finset.card_union_le S T

lemma coordinate_union {n : ℕ}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i : Fin n) (B C : Finset (∀ j, A j)) (x : ∀ j, A j) :
    coordinateFraction A i (B∪C) x ≤ coordinateFraction A i B x+coordinateFraction A i C x := by
  classical
  have he : coordinateFibre A i (B∪C) (splitCoordinate A i x).1 =
      coordinateFibre A i B (splitCoordinate A i x).1 ∪ coordinateFibre A i C (splitCoordinate A i x).1 := by
    ext v
    simp [coordinateFibre]
  unfold coordinateFraction
  rw [he]
  exact fraction_union _ _

lemma coordinate_pure {n : ℕ}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i : Fin n) (Y : Finset (A i)) (x : ∀ j, A j) :
    coordinateFraction A i (Finset.univ.filter (fun x => x i∈Y)) x = fraction Y := by
  classical
  unfold coordinateFraction
  congr 1
  ext v
  simp [coordinateFibre,joinCoordinate_self]

#print axioms first_layer_fraction
end Erdos7DirectFiveFirstLayer
