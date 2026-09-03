import Submission.MonotoneRegionRectangles

/-! Bounds for a thin band between two antitone integer subgraphs. -/
namespace Erdos371.MonotoneRectangles
open Finset

lemma stairArea_sub_le (p H K r : ℕ) (h k : ℕ → ℕ) (hp : 0 < p)
    (hk : ∀ j, k j ≤ h j + r) :
    stairArea p H K k - stairArea p H K h ≤ (r : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  let w : ℕ → ℝ := fun j => (min (p : ℝ) (j * H)) / p
  have hw (j : ℕ) : 0 ≤ w (j+1) - w j := by
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ hp0.le
    apply min_le_min_left
    have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    push_cast
    nlinarith
  have he : stairArea p H K k - stairArea p H K h =
      ∑ j ∈ range K, (((k j : ℝ) - h j) / p) * (w (j+1) - w j) := by
    unfold stairArea
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    dsimp [w]
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ∑ j ∈ range K, ((r : ℝ) / p) * (w (j+1) - w j) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hw j)
      apply div_le_div_of_nonneg_right _ hp0.le
      have hj' : (k j : ℝ) ≤ h j + r := by exact_mod_cast hk j
      linarith
    _ = ((r : ℝ) / p) * (w K - w 0) := by
      rw [← mul_sum, sum_range_sub]
    _ ≤ ((r : ℝ) / p) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [w]
      simp only [Nat.cast_zero, zero_mul, min_eq_right hp0.le, zero_div, sub_zero]
      exact (div_le_one hp0).mpr (min_le_left _ _)
    _ = _ := mul_one _

/-- The area error for different antitone heights is at most their vertical
separation plus the usual staircase width. -/
lemma stairArea_gap_of_close (p H K r : ℕ) (h k : ℕ → ℕ) (hp : 0 < p)
    (hh : Antitone h) (hzero : h 0 ≤ p) (hk : ∀ y, k y ≤ h y + r) :
    stairArea p H K (fun j => k (j*H)) -
      stairArea p H K (fun j => h ((j+1)*H)) ≤ (H : ℝ)/p + (r : ℝ)/p := by
  have h₁ := stairArea_sub_le p H K r (fun j => h (j*H))
    (fun j => k (j*H)) hp (fun j => hk (j*H))
  have h₂ := stairArea_gap p H K h hp hh hzero
  linarith

lemma regionCount_mono {ι : Type*} [Fintype ι] (a b : ι → ℕ)
    (h k : ℕ → ℕ) (hk : ∀ y, h y ≤ k y) :
    regionCount a b h ≤ regionCount a b k := by
  apply card_le_card
  intro i hi
  obtain ⟨hi,hai⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hi,hai.trans_le (hk _)⟩

/-- A thin antitone band in a rectangle-equidistributed finite point set. -/
theorem thin_monotone_band {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (h k : ℕ → ℕ) (hh : Antitone h) (hk : Antitone k)
    (p H K r : ℕ) (hp : 0 < p) (hH : 0 < H) (hcover : p ≤ K*H)
    (hb : ∀ i, b i < p) (hzero : h 0 ≤ p) (kzero : k 0 ≤ p)
    (hle : ∀ y, h y ≤ k y) (hclose : ∀ y, k y ≤ h y + r) (δ : ℝ)
    (hrect : ∀ U V : ℕ, U ≤ p → V ≤ p →
      |(rectCount a b U V : ℝ)/p - ((U : ℝ)/p)*((V : ℝ)/p)| ≤ δ) :
    |(regionCount a b k : ℝ)/p - (regionCount a b h : ℝ)/p| ≤
      (H : ℝ)/p + (r : ℝ)/p + 4*K*δ := by
  have h₁ := region_area_bounds a b h hh p H K hp hH hcover hb hzero δ hrect
  have h₂ := region_area_bounds a b k hk p H K hp hH hcover hb kzero δ hrect
  have h₃ := stairArea_gap_of_close p H K r h k hp hh hzero hclose
  have h₄ : (regionCount a b h : ℝ)/p ≤ (regionCount a b k : ℝ)/p := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast regionCount_mono a b h k hle
  rw [abs_of_nonneg (sub_nonneg.mpr h₄)]
  linarith

#print axioms stairArea_sub_le
#print axioms thin_monotone_band
end Erdos371.MonotoneRectangles
