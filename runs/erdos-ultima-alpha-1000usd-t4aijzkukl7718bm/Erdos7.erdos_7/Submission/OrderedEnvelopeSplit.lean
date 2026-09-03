import FormalConjecturesUtil

/-! Splitting a two-row envelope along a common crossing rank. This is an
auxiliary identity and separable majorant, not a full covering comparison. -/
namespace Erdos7EnvelopeSplit
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Clipping commutes with a sum when all summands change sign at the same
rank. Only monotonicity, not convexity, is needed for this identity. -/
theorem common_crossing_hinge {ι α : Type*} [LinearOrder α]
    (S : Finset ι) (f : ι → α → ℚ) (hf : ∀ i ∈ S, Monotone (f i)) (x t : α) :
    max (∑ i ∈ S, (f i x - f i t)) 0 = ∑ i ∈ S, max (f i x - f i t) 0 := by
  rcases le_total x t with hxt | htx
  · have hh : ∀ i ∈ S, f i x - f i t ≤ 0 := fun i hi => sub_nonpos.mpr (hf i hi hxt)
    rw [max_eq_right (Finset.sum_nonpos hh)]
    simp only [Finset.sum_eq_zero (fun i hi => max_eq_right (hh i hi))]
  · have hh : ∀ i ∈ S, 0 ≤ f i x - f i t := fun i hi => sub_nonneg.mpr (hf i hi htx)
    rw [max_eq_left (Finset.sum_nonneg hh)]
    exact Finset.sum_congr rfl (fun i hi => (max_eq_left (hh i hi)).symm)

lemma max_eq_add_hinge (a b : ℚ) : max a b = a + max (b - a) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Two sums with co-monotone component differences can be split into
componentwise maxima at any rank where the total rows cross. -/
theorem two_row_envelope_identity {ι α : Type*} [LinearOrder α]
    (S : Finset ι) (f g : ι → α → ℚ)
    (hfg : ∀ i ∈ S, Monotone (fun x => g i x - f i x))
    (b d : ℚ) (t x : α)
    (hcross : b + (∑ i ∈ S, f i t) = d + ∑ i ∈ S, g i t) :
    max (b + ∑ i ∈ S, f i x) (d + ∑ i ∈ S, g i x) =
      b + ∑ i ∈ S, max (f i x) (g i x + f i t - g i t) := by
  have hd : (d + ∑ i ∈ S, g i x) - (b + ∑ i ∈ S, f i x) =
      ∑ i ∈ S, ((g i x - f i x) - (g i t - f i t)) := by
    simp only [Finset.sum_sub_distrib]
    linarith
  rw [max_eq_add_hinge, hd, common_crossing_hinge S (fun i y => g i y - f i y) hfg x t]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_add_hinge (f i x) (g i x + f i t - g i t)]
  congr 2
  ring

/-- The same split is a separable majorant even when the components are
subsequently evaluated at different arguments. -/
theorem two_row_separable_majorant {ι α : Type*}
    (S : Finset ι) (f g : ι → α → ℚ) (b d : ℚ) (t : α) (x : ι → α)
    (hcross : b + (∑ i ∈ S, f i t) = d + ∑ i ∈ S, g i t) :
    max (b + ∑ i ∈ S, f i (x i)) (d + ∑ i ∈ S, g i (x i)) ≤
      b + ∑ i ∈ S, max (f i (x i)) (g i (x i) + f i t - g i t) := by
  apply max_le
  · exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ => le_max_left _ _))
  · have hh := Finset.sum_le_sum (s := S) (fun i _ =>
        le_max_right (f i (x i)) (g i (x i) + f i t - g i t))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hh
    linarith

/-- Each split component remains convex. -/
theorem split_component_convex (f g : ℚ → ℚ)
    (hf : ConvexOn ℚ Set.univ f) (hg : ConvexOn ℚ Set.univ g) (t : ℚ) :
    ConvexOn ℚ Set.univ (fun x => max (f x) (g x + f t - g t)) := by
  simpa only [Pi.add_apply, add_sub_assoc] using hf.sup (hg.add_const (f t - g t))

/-- Each split component remains monotone. -/
theorem split_component_monotone {α : Type*} [Preorder α] (f g : α → ℚ)
    (hf : Monotone f) (hg : Monotone g) (t : α) :
    Monotone (fun x => max (f x) (g x + f t - g t)) := by
  intro x y hxy
  exact max_le_max (hf hxy) (by linarith [hg hxy])

#print axioms common_crossing_hinge
#print axioms two_row_envelope_identity
#print axioms two_row_separable_majorant
#print axioms split_component_convex
#print axioms split_component_monotone
end Erdos7EnvelopeSplit
