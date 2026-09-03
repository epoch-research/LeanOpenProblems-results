import Submission.FiniteRowDual

/-! A family of scalar coefficient rows can be sorted by the coefficient,
not by its external row label. Different coefficient groups may therefore use
different orders. No common extremizer for the component arguments is assumed. -/
namespace Erdos7ScalarCoefficientDual
open scoped BigOperators
open Erdos7FiniteRowDual
set_option maxHeartbeats 1500000

/-- Separable convex lifting for one coefficient group with arbitrary finite
row labels. All members of the group have the same nonnegative row coefficient. -/
theorem scalar_coefficient_dual_split {ι κ : Type*} (S : Finset ι)
    (φ : ι → ℝ → ℝ) (R : Finset κ) (hR : R.Nonempty)
    (c A : κ → ℝ) (V : ℝ → ℝ) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (hc : ∀ r ∈ R, 0 ≤ c r)
    (hV : ∀ x ∈ Set.Icc lo hi, 0 ≤ V x)
    (hdual : ∀ r ∈ R, ∀ x ∈ Set.Icc lo hi,
      (∑ i ∈ S, c r * φ i x) ≤ A r + V x) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) ≤ V x) ∧
      (∀ r ∈ R, ∀ x : ι → ℝ, (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        (∑ i ∈ S, c r * φ i (x i)) ≤ A r + b + ∑ i ∈ S, h i (x i)) := by
  classical
  let T := R.image (fun r => -c r)
  have hT : T.Nonempty := hR.image _
  have hex (t : ℝ) (ht : t ∈ T) :
      ∃ r, r ∈ R ∧ -c r=t ∧ ∀ s ∈ R, -c s=t → A r ≤ A s := by
    have hf : (R.filter (fun r => -c r=t)).Nonempty := by
      obtain ⟨r, hr, he⟩ := Finset.mem_image.mp ht
      exact ⟨r, Finset.mem_filter.mpr ⟨hr, he⟩⟩
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image _ A hf
    obtain ⟨hrR, he⟩ := Finset.mem_filter.mp hr
    exact ⟨r, hrR, he, fun s hs hse => hmin s (Finset.mem_filter.mpr ⟨hs,hse⟩)⟩
  let rep (t : ℝ) (ht : t ∈ T) : κ := Classical.choose (hex t ht)
  have hrep (t : ℝ) (ht : t ∈ T) :
      rep t ht ∈ R ∧ -c (rep t ht)=t ∧
        ∀ s ∈ R, -c s=t → A (rep t ht) ≤ A s := Classical.choose_spec (hex t ht)
  let B (t : ℝ) : ℝ := if ht : t ∈ T then A (rep t ht) else 0
  have hcoeff (t : ℝ) (ht : t ∈ T) : -t=c (rep t ht) := by
    have hh := (hrep t ht).2.1
    linarith
  obtain ⟨b, h, hh, hdiag, hmaj⟩ := antitone_finite_dual_split S φ
    (fun t _ => -t) B (fun _ => 0) V T hT lo hi hlh hφ hmφ
    (by
      intro t ht i hi
      change 0 ≤ -t
      rw [hcoeff t ht]
      exact hc _ (hrep t ht).1)
    (fun _ _ _ _ h => neg_le_neg h) hV
    (by
      intro t ht x hx
      simpa only [zero_add, hcoeff t ht, B, dif_pos ht] using
        hdual (rep t ht) (hrep t ht).1 x hx)
  refine ⟨b, h, hh, hdiag, ?_⟩
  intro r hr x hx
  have ht : -c r ∈ T := Finset.mem_image_of_mem _ hr
  have hB : B (-c r) ≤ A r := by
    dsimp only [B]
    rw [dif_pos ht]
    exact (hrep (-c r) ht).2.2 r hr rfl
  have hm := hmaj (-c r) ht x hx
  simp only [zero_add, neg_neg] at hm
  linarith

/-- Two coefficient groups may be sorted independently. This is useful when
one coefficient decreases and the other increases with the removal count. -/
theorem two_group_dual_split {ι κ ρ : Type*} (S : Finset ι) (T : Finset κ)
    (φ : ι → ℝ → ℝ) (ψ : κ → ℝ → ℝ) (R : Finset ρ) (hR : R.Nonempty)
    (a c A B loss U : ρ → ℝ) (V W : ℝ → ℝ)
    (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (hψ : ∀ i ∈ T, ConvexOn ℝ Set.univ (ψ i))
    (hmψ : ∀ i ∈ T, Monotone (ψ i))
    (ha : ∀ r ∈ R, 0 ≤ a r) (hc : ∀ r ∈ R, 0 ≤ c r)
    (hV : ∀ x ∈ Set.Icc lo hi, 0 ≤ V x)
    (hW : ∀ x ∈ Set.Icc lo hi, 0 ≤ W x)
    (hdualA : ∀ r ∈ R, ∀ x ∈ Set.Icc lo hi,
      (∑ i ∈ S, a r * φ i x) ≤ A r + V x)
    (hdualB : ∀ r ∈ R, ∀ x ∈ Set.Icc lo hi,
      (∑ i ∈ T, c r * ψ i x) ≤ B r + W x)
    (hrow : ∀ r ∈ R, loss r+A r+B r ≤ U r) :
    ∃ (b : ℝ) (f : ι → ℝ → ℝ) (g : κ → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (f i) ∧ Monotone (f i)) ∧
      (∀ i ∈ T, ConvexOn ℝ Set.univ (g i) ∧ Monotone (g i)) ∧
      (∀ x ∈ Set.Icc lo hi,
        b+(∑ i ∈ S, f i x)+(∑ i ∈ T, g i x) ≤ V x+W x) ∧
      (∀ r ∈ R, ∀ x : ι → ℝ, ∀ y : κ → ℝ,
        (∀ i ∈ S, x i ∈ Set.Icc lo hi) →
        (∀ i ∈ T, y i ∈ Set.Icc lo hi) →
        loss r+(∑ i ∈ S, a r*φ i (x i))+(∑ i ∈ T, c r*ψ i (y i)) ≤
          U r+b+(∑ i ∈ S, f i (x i))+(∑ i ∈ T, g i (y i))) := by
  obtain ⟨b, f, hf, hdA, hmA⟩ := scalar_coefficient_dual_split S φ R hR a A V
    lo hi hlh hφ hmφ ha hV hdualA
  obtain ⟨d, g, hg, hdB, hmB⟩ := scalar_coefficient_dual_split T ψ R hR c B W
    lo hi hlh hψ hmψ hc hW hdualB
  refine ⟨b+d, f, g, hf, hg, ?_, ?_⟩
  · intro x hx
    have h₁ := hdA x hx
    have h₂ := hdB x hx
    linarith
  · intro r hr x y hx hy
    have h₁ := hmA r hr x hx
    have h₂ := hmB r hr y hy
    have h₃ := hrow r hr
    linarith

#print axioms scalar_coefficient_dual_split
#print axioms two_group_dual_split
end Erdos7ScalarCoefficientDual
