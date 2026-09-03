import Submission.PairedRetentionKernel
import Submission.KernelFamilyCompression

/-! Shared-capacity compression for two live states. Both states use the
SAME scalar count family. The expensive state's increments dominate the
other state's increments. These hypotheses are essential; no paired covering
budget or unrestricted covering-system obstruction is asserted. -/
namespace Erdos7StateSharedCompression
open scoped BigOperators
open Erdos7RealChain
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Two-state fractional allocation, with the larger coefficient served first. -/
lemma two_capacity_bound (h₁ h₂ q u v d₁ d₂ : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hu₁ : u ≤ h₁) (hv₂ : v ≤ h₂)
    (huv : u+v ≤ q) (hd₂ : 0 ≤ d₂) (hd : d₂ ≤ d₁) :
    d₁*u+d₂*v ≤ min h₁ q*d₁ + min h₂ (max (q-h₁) 0)*d₂ := by
  have hd₁ : 0 ≤ d₁ := hd₂.trans hd
  by_cases hq : q ≤ h₁
  · rw [min_eq_right hq, max_eq_right (by linarith : q-h₁ ≤ 0),
      min_eq_right (hv.trans hv₂), zero_mul, add_zero]
    nlinarith [mul_le_mul_of_nonneg_left huv hd₁,
      mul_le_mul_of_nonneg_right hd hv]
  · have hq' : h₁ ≤ q := le_of_not_ge hq
    rw [min_eq_left hq', max_eq_left (by linarith : 0 ≤ q-h₁)]
    by_cases hh : h₂ ≤ q-h₁
    · rw [min_eq_left hh]
      nlinarith [mul_le_mul_of_nonneg_left hu₁ hd₁,
        mul_le_mul_of_nonneg_left hv₂ hd₂]
    · rw [min_eq_right (le_of_not_ge hh)]
      nlinarith [mul_le_mul_of_nonneg_left hu₁ (sub_nonneg.mpr hd),
        mul_le_mul_of_nonneg_left huv hd₂]

/-- A common event consumes the total cap only once across the two states. -/
lemma common_group_marginal {A : Type*} [Fintype A]
    (ν₁ ν₂ ρ s : A → ℝ) (c r W : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ y, ν₁ y+ν₂ y ≤ c*ρ y) (hs : ∀ y, 0 ≤ s y)
    (hd : (∑ y, ρ y*s y) ≤ r*W) :
    (∑ y, (ν₁ y+ν₂ y)*s y) ≤ (c*r)*W := by
  calc
    _ ≤ ∑ y, c*(ρ y*s y) := Finset.sum_le_sum (fun y _ => by
      nlinarith [mul_le_mul_of_nonneg_right (hcap y) (hs y)])
    _ = c*(∑ y, ρ y*s y) := (Finset.mul_sum ..).symm
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd hc]

lemma normalized_group_bounds {A : Type*} [Fintype A]
    (ν₁ ν₂ s : A → ℝ) (h₁ h₂ q W : ℝ)
    (hn₁ : ∀ y, 0 ≤ ν₁ y) (hn₂ : ∀ y, 0 ≤ ν₂ y)
    (hm₁ : (∑ y, ν₁ y) = h₁) (hm₂ : (∑ y, ν₂ y) = h₂)
    (hq : 0 ≤ q) (hW : 0 ≤ W) (hs : ∀ y, s y ∈ Set.Icc (0:ℝ) W)
    (hmarg : (∑ y, (ν₁ y+ν₂ y)*s y) ≤ q*W) :
    let u := ∑ y, ν₁ y*(s y/W)
    let v := ∑ y, ν₂ y*(s y/W)
    0 ≤ u ∧ 0 ≤ v ∧ u ≤ h₁ ∧ v ≤ h₂ ∧ u+v ≤ q := by
  dsimp only
  have hg (y : A) : s y/W ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (hs y).1 hW, ?_⟩
    by_cases hz : W = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hW (Ne.symm hz))).mpr (hs y).2
  refine ⟨Finset.sum_nonneg (fun y _ => mul_nonneg (hn₁ y) (hg y).1),
    Finset.sum_nonneg (fun y _ => mul_nonneg (hn₂ y) (hg y).1), ?_, ?_, ?_⟩
  · rw [← hm₁]
    exact Finset.sum_le_sum (fun y _ => by simpa using mul_le_mul_of_nonneg_left (hg y).2 (hn₁ y))
  · rw [← hm₂]
    exact Finset.sum_le_sum (fun y _ => by simpa using mul_le_mul_of_nonneg_left (hg y).2 (hn₂ y))
  · by_cases hz : W = 0
    · simpa [hz] using hq
    · have hp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
      calc
        _ = (∑ y, (ν₁ y+ν₂ y)*s y)/W := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ ≤ q := (div_le_iff₀ hp).mpr hmarg

/-- A genuine fiber-varying convex comparison. The cost functions may be
signed, but are monotone and convex, and their difference is monotone.
The same count function occurs in both states. -/
theorem shared_group_compression {A : Type*} [Fintype A]
    (ν₁ ν₂ : A → ℝ) (hn₁ : ∀ y, 0 ≤ ν₁ y) (hn₂ : ∀ y, 0 ≤ ν₂ y)
    (h₁ h₂ : ℝ) (hm₁ : (∑ y, ν₁ y) = h₁) (hm₂ : (∑ y, ν₂ y) = h₂)
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : ConvexOn ℝ Set.univ φ₁)
    (hφ₂ : ConvexOn ℝ Set.univ φ₂) (hmφ₁ : Monotone φ₁) (hmφ₂ : Monotone φ₂)
    (horder : Monotone (fun t => φ₁ t-φ₂ t))
    (a : ℝ) (W : ℕ → ℝ) (s : ℕ → A → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hW : ∀ j < R, 0 ≤ W j) (hq : ∀ j < R, 0 ≤ q j)
    (hs : ∀ j < R, ∀ y, s j y ∈ Set.Icc (0:ℝ) (W j))
    (hmarg : ∀ j < R, (∑ y, (ν₁ y+ν₂ y)*s j y) ≤ q j*W j) :
    (∑ y, (ν₁ y*φ₁ (a+prefixWeight (fun j => s j y) R) +
      ν₂ y*φ₂ (a+prefixWeight (fun j => s j y) R))) ≤
      h₁*φ₁ a+h₂*φ₂ a + ∑ j ∈ Finset.range R,
        (min h₁ (q j)*chainIncrement φ₁ a W j +
          min h₂ (max (q j-h₁) 0)*chainIncrement φ₂ a W j) := by
  let d₁ (j : ℕ) := chainIncrement φ₁ a W j
  let d₂ (j : ℕ) := chainIncrement φ₂ a W j
  have hstep (j : ℕ) (hj : j < R) : a+prefixWeight W j ≤ a+prefixWeight W (j+1) := by
    simp only [prefixWeight, Finset.sum_range_succ]
    linarith [hW j hj]
  have hds (j : ℕ) (hj : j < R) : 0 ≤ d₂ j ∧ d₂ j ≤ d₁ j := by
    have hp := hmφ₂ (hstep j hj)
    have ho := horder (hstep j hj)
    dsimp only [d₁, d₂, chainIncrement]
    constructor <;> linarith
  have hb (j : ℕ) (hj : j < R) :
      d₁ j*(∑ y, ν₁ y*(s j y/W j)) + d₂ j*(∑ y, ν₂ y*(s j y/W j)) ≤
        min h₁ (q j)*d₁ j + min h₂ (max (q j-h₁) 0)*d₂ j := by
    obtain ⟨hu,hv,hu₁,hv₂,huv⟩ := normalized_group_bounds ν₁ ν₂ (s j)
      h₁ h₂ (q j) (W j) hn₁ hn₂ hm₁ hm₂ (hq j hj) (hW j hj) (hs j hj) (hmarg j hj)
    exact two_capacity_bound _ _ _ _ _ _ _ hu hv hu₁ hv₂ huv (hds j hj).1 (hds j hj).2
  have he (ν : A → ℝ) (φ : ℝ → ℝ) (d : ℕ → ℝ) :
      (∑ y, ν y*(φ a+∑ j ∈ Finset.range R, d j/W j*s j y)) =
        (∑ y, ν y)*φ a+∑ j ∈ Finset.range R, d j*(∑ y, ν y*(s j y/W j)) := by
    simp_rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro y _
    ring
  calc
    _ ≤ ∑ y, (ν₁ y*(φ₁ a+∑ j ∈ Finset.range R, d₁ j/W j*s j y) +
        ν₂ y*(φ₂ a+∑ j ∈ Finset.range R, d₂ j/W j*s j y)) := by
      apply Finset.sum_le_sum
      intro y _
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (bounded_chain_majorant φ₁ hφ₁ a W
          (fun j => s j y) R (fun j hj => (hs j hj y).1) (fun j hj => (hs j hj y).2)) (hn₁ y)
      · exact mul_le_mul_of_nonneg_left (bounded_chain_majorant φ₂ hφ₂ a W
          (fun j => s j y) R (fun j hj => (hs j hj y).1) (fun j hj => (hs j hj y).2)) (hn₂ y)
    _ = h₁*φ₁ a+h₂*φ₂ a + ∑ j ∈ Finset.range R,
        (d₁ j*(∑ y, ν₁ y*(s j y/W j)) + d₂ j*(∑ y, ν₂ y*(s j y/W j))) := by
      rw [Finset.sum_add_distrib, he, he, hm₁, hm₂, Finset.sum_add_distrib]
      ring
    _ ≤ _ := by
      have hh := Finset.sum_le_sum (fun j hj => hb j (Finset.mem_range.mp hj))
      dsimp only [d₁, d₂] at hh
      linarith

/-- A small exact allocation control exhibits the gain over independent caps.
This is not an arithmetic covering family. -/
lemma shared_allocation_gain :
    min (3/10 : ℝ) (1/5)*2 + min (1/2 : ℝ) (max ((1/5 : ℝ)-3/10) 0)*1 = 2/5 ∧
    min (3/10 : ℝ) (1/5)*2 + min (1/2 : ℝ) (1/5)*1 = 3/5 := by
  norm_num

#print axioms two_capacity_bound
#print axioms shared_group_compression
#print axioms shared_allocation_gain


noncomputable def firstCap (h q : ℝ) : ℝ := min h q
noncomputable def secondCap (h₁ h₂ q : ℝ) : ℝ := min h₂ (max (q-h₁) 0)

lemma cap_properties (h₁ h₂ q : ℝ) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hq : 0 ≤ q) :
    0 ≤ firstCap h₁ q ∧ firstCap h₁ q ≤ h₁ ∧
    0 ≤ secondCap h₁ h₂ q ∧ secondCap h₁ h₂ q ≤ h₂ ∧
    firstCap h₁ q + secondCap h₁ h₂ q = min (h₁+h₂) q := by
  refine ⟨le_min hh₁ hq, min_le_left _ _,
    le_min hh₂ (le_max_right _ _), min_le_left _ _, ?_⟩
  dsimp only [firstCap, secondCap]
  by_cases hq₁ : q ≤ h₁
  · rw [min_eq_right hq₁, max_eq_right (by linarith : q-h₁ ≤ 0),
      min_eq_right hh₂, add_zero, min_eq_right (by linarith : q ≤ h₁+h₂)]
  · have h₁q : h₁ ≤ q := le_of_not_ge hq₁
    rw [min_eq_left h₁q, max_eq_left (by linarith : 0 ≤ q-h₁)]
    by_cases hh : h₂ ≤ q-h₁
    · rw [min_eq_left hh, min_eq_left (by linarith : h₁+h₂ ≤ q)]
    · rw [min_eq_right (le_of_not_ge hh), min_eq_right (by linarith : q ≤ h₁+h₂)]
      ring

lemma firstCap_mono (h : ℝ) : Monotone (firstCap h) := by
  intro q r hqr
  exact min_le_min le_rfl hqr

lemma secondCap_mono (h₁ h₂ : ℝ) : Monotone (secondCap h₁ h₂) := by
  intro q r hqr
  exact min_le_min le_rfl (max_le_max (by linarith) le_rfl)

lemma caps_zero (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) :
    firstCap h₁ 0 = 0 ∧ secondCap h₁ h₂ 0 = 0 := by
  simp [firstCap, secondCap, hh₁, hh₂, max_eq_right (by linarith : (0:ℝ)-h₁ ≤ 0)]

noncomputable def mixValue (h : ℝ) (β : ℕ → ℝ) (R : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (h-β 0)*φ 1 + ∑ j ∈ Finset.range R, (β j-β (j+1))*φ ((j:ℝ)+2)

lemma mixValue_increment (h : ℝ) (β : ℕ → ℝ) (R : ℕ) (hβ : β R = 0)
    (φ : ℝ → ℝ) :
    h*φ 1 + (∑ j ∈ Finset.range R, β j*chainIncrement φ 1 (fun _ => 1) j) =
      mixValue h β R φ := by
  have ht := chain_summation_by_parts (fun j : ℕ => φ (1+(j:ℝ))) β R
  simp only [hβ, zero_mul, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at ht
  simp only [chainIncrement, prefixWeight, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  have he (j : ℕ) : (1 : ℝ)+((j:ℝ)+1) = (j:ℝ)+2 := by ring
  simp_rw [he] at ht ⊢
  unfold mixValue
  linarith

lemma mixValue_mono (h : ℝ) (β : ℕ → ℝ) (R : ℕ)
    (hbase : β 0 ≤ h) (hβ : ∀ j < R, β (j+1) ≤ β j)
    (φ ψ : ℝ → ℝ) (hφψ : ∀ x, φ x ≤ ψ x) :
    mixValue h β R φ ≤ mixValue h β R ψ := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hφψ _) (sub_nonneg.mpr hbase)
  · exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (hφψ _) (sub_nonneg.mpr (hβ j (Finset.mem_range.mp hj))))

lemma mixValue_sum {I : Type*} [Fintype I]
    (h : ℝ) (β : ℕ → ℝ) (R : ℕ) (φ : I → ℝ → ℝ) :
    (∑ i, mixValue h β R (φ i)) = mixValue h β R (fun x => ∑ i, φ i x) := by
  simp only [mixValue, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- The allocation gives a positive common finite comparison law for each
state, with no geometric endpoint silently discarded. -/
theorem shared_unit_mixture {A : Type*} [Fintype A]
    (ν₁ ν₂ : A → ℝ) (hn₁ : ∀ y, 0 ≤ ν₁ y) (hn₂ : ∀ y, 0 ≤ ν₂ y)
    (h₁ h₂ : ℝ) (hm₁ : (∑ y, ν₁ y) = h₁) (hm₂ : (∑ y, ν₂ y) = h₂)
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : ConvexOn ℝ Set.univ φ₁)
    (hφ₂ : ConvexOn ℝ Set.univ φ₂) (hmφ₁ : Monotone φ₁) (hmφ₂ : Monotone φ₂)
    (horder : Monotone (fun t => φ₁ t-φ₂ t))
    (s : ℕ → A → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hq : ∀ j < R, 0 ≤ q j) (hqR : q R = 0)
    (hs : ∀ j < R, ∀ y, s j y ∈ Set.Icc (0:ℝ) 1)
    (hmarg : ∀ j < R, (∑ y, (ν₁ y+ν₂ y)*s j y) ≤ q j) :
    (∑ y, (ν₁ y*φ₁ (1+prefixWeight (fun j => s j y) R) +
      ν₂ y*φ₂ (1+prefixWeight (fun j => s j y) R))) ≤
      mixValue h₁ (fun j => firstCap h₁ (q j)) R φ₁ +
        mixValue h₂ (fun j => secondCap h₁ h₂ (q j)) R φ₂ := by
  have hh₁ : 0 ≤ h₁ := hm₁ ▸ Finset.sum_nonneg (fun y _ => hn₁ y)
  have hh₂ : 0 ≤ h₂ := hm₂ ▸ Finset.sum_nonneg (fun y _ => hn₂ y)
  have hb := shared_group_compression ν₁ ν₂ hn₁ hn₂ h₁ h₂ hm₁ hm₂
    φ₁ φ₂ hφ₁ hφ₂ hmφ₁ hmφ₂ horder 1 (fun _ => 1) s q R
    (fun j hj => by norm_num) hq hs (fun j hj => by simpa using hmarg j hj)
  have hzero := caps_zero h₁ h₂ hh₁ hh₂
  rw [← mixValue_increment h₁ _ R (by simpa [hqR] using hzero.1),
    ← mixValue_increment h₂ _ R (by simpa [hqR] using hzero.2)]
  simp only [Finset.sum_add_distrib] at hb ⊢
  dsimp only [firstCap, secondCap]
  linarith

#print axioms shared_unit_mixture

/-- Independent family labels remain independent. Within each label, however,
the two states share the same count. Ordered increments give one comparison
law, so sums of different tests can safely use their diagonal bounds. -/
theorem separate_families {A I : Type*} [Fintype A] [Fintype I]
    (ν₁ ν₂ : A → ℝ) (hn₁ : ∀ y, 0 ≤ ν₁ y) (hn₂ : ∀ y, 0 ≤ ν₂ y)
    (h₁ h₂ : ℝ) (hm₁ : (∑ y, ν₁ y) = h₁) (hm₂ : (∑ y, ν₂ y) = h₂)
    (φ₁ φ₂ : I → ℝ → ℝ)
    (hφ₁ : ∀ i, ConvexOn ℝ Set.univ (φ₁ i))
    (hφ₂ : ∀ i, ConvexOn ℝ Set.univ (φ₂ i))
    (hmφ₁ : ∀ i, Monotone (φ₁ i)) (hmφ₂ : ∀ i, Monotone (φ₂ i))
    (horder : ∀ i, Monotone (fun t => φ₁ i t-φ₂ i t))
    (s : I → ℕ → A → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hq : ∀ j < R, 0 ≤ q j) (hqR : q R = 0)
    (hqdec : ∀ j < R, q (j+1) ≤ q j)
    (hs : ∀ i j, j < R → ∀ y, s i j y ∈ Set.Icc (0:ℝ) 1)
    (hmarg : ∀ i j, j < R → (∑ y, (ν₁ y+ν₂ y)*s i j y) ≤ q j)
    (F₁ F₂ : ℝ → ℝ) (hF₁ : ∀ t, (∑ i, φ₁ i t) ≤ F₁ t)
    (hF₂ : ∀ t, (∑ i, φ₂ i t) ≤ F₂ t) :
    (∑ i, ∑ y, (ν₁ y*φ₁ i (1+prefixWeight (fun j => s i j y) R) +
      ν₂ y*φ₂ i (1+prefixWeight (fun j => s i j y) R))) ≤
      mixValue h₁ (fun j => firstCap h₁ (q j)) R F₁ +
        mixValue h₂ (fun j => secondCap h₁ h₂ (q j)) R F₂ := by
  calc
    _ ≤ ∑ i, (mixValue h₁ (fun j => firstCap h₁ (q j)) R (φ₁ i) +
        mixValue h₂ (fun j => secondCap h₁ h₂ (q j)) R (φ₂ i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact shared_unit_mixture ν₁ ν₂ hn₁ hn₂ h₁ h₂ hm₁ hm₂
        (φ₁ i) (φ₂ i) (hφ₁ i) (hφ₂ i) (hmφ₁ i) (hmφ₂ i) (horder i)
        (s i) q R hq hqR (hs i) (hmarg i)
    _ = mixValue h₁ (fun j => firstCap h₁ (q j)) R (fun t => ∑ i, φ₁ i t) +
        mixValue h₂ (fun j => secondCap h₁ h₂ (q j)) R (fun t => ∑ i, φ₂ i t) := by
      rw [Finset.sum_add_distrib, mixValue_sum, mixValue_sum]
    _ ≤ _ := by
      apply add_le_add
      · exact mixValue_mono _ _ R (min_le_left _ _)
          (fun j hj => firstCap_mono h₁ (hqdec j hj)) _ _ hF₁
      · exact mixValue_mono _ _ R (min_le_left _ _)
          (fun j hj => secondCap_mono h₁ h₂ (hqdec j hj)) _ _ hF₂

/-- A shared density cap does not supply a shared marginal cap when the two
states are permitted to use different events. -/
theorem different_events_control :
    let ν₁ := fun y : Bool => if y = false then (1/2 : ℝ) else 0
    let ν₂ := fun y : Bool => if y = true then (1/2 : ℝ) else 0
    (∀ y, ν₁ y+ν₂ y = 1/2) ∧
    (1/2 : ℝ) < (∑ y, (ν₁ y*(if y = false then 1 else 0) +
      ν₂ y*(if y = true then 1 else 0))) := by
  dsimp only
  constructor
  · intro y
    cases y <;> norm_num
  · norm_num [Fintype.sum_bool]

#print axioms separate_families
#print axioms different_events_control
end Erdos7StateSharedCompression
