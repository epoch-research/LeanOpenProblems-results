import Submission.FiniteRetentionKernel

/-! Compression of actual coordinate-event families under an exact retention
kernel. The projected cumulative counts are kept as separate old families. -/
namespace Erdos7KernelFamilyCompression
open scoped BigOperators
open Erdos7RealChain Erdos7CappedFiberMixture Erdos7CappedRetentionRows
set_option maxHeartbeats 1500000

/-- A weighted group of events of coordinate mass at most r. -/
lemma event_group_marginal {A I : Type*} [Fintype A] [Fintype I]
    (ν ρ : A → ℝ) (m c r : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hcap : ∀ y, ν y ≤ c*m*ρ y) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hit : I → A → Prop) [∀ i y, Decidable (hit i y)]
    (hdensity : ∀ i, (∑ y, if hit i y then ρ y else 0) ≤ r) :
    (∑ y, ν y*(∑ i, if hit i y then w i else 0)) ≤ m*(c*r)*(∑ i, w i) := by
  classical
  have hb (i : I) : (∑ y, if hit i y then ν y else 0) ≤ c*m*r := by
    calc
      _ ≤ ∑ y, c*m*(if hit i y then ρ y else 0) := by
        apply Finset.sum_le_sum
        intro y _
        split_ifs
        · exact hcap y
        · simp
      _ = c*m*(∑ y, if hit i y then ρ y else 0) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdensity i) (mul_nonneg hc hm)
  calc
    _ = ∑ i, w i*(∑ y, if hit i y then ν y else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    _ ≤ ∑ i, w i*(c*m*r) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = _ := by rw [← Finset.sum_mul]; ring

noncomputable def multiplier {R : ℕ} : Option (Fin R) → ℝ
  | none => 1
  | some j => (j.val:ℝ)+2

lemma multiplier_nonneg {R : ℕ} (d : Option (Fin R)) : 0 ≤ multiplier d := by
  cases d with
  | none => norm_num [multiplier]
  | some j => simp only [multiplier]; positivity

/-- One-family capped compression. The equation hprefix is the precise
closure property that complete normalized pattern families must supply. -/
theorem normalized_family_compression {Ω A I : Type*}
    [Fintype Ω] [Fintype A] [Fintype I]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν : Ω → A → ℝ)
    (hν : ∀ x y, 0 ≤ ν x y) (h : Ω → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hmass : ∀ x, (∑ y, ν x y)=μ x*h x)
    (ρ : A → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ x y, ν x y ≤ c*μ x*ρ y)
    (R : ℕ) (r : ℕ → ℝ) (hrR : r R=0)
    (w : ℕ → I → Ω → ℝ) (hw : ∀ j<R, ∀ i x, 0 ≤ w j i x)
    (hit : ℕ → I → A → Prop) [∀ j i y, Decidable (hit j i y)]
    (hdensity : ∀ j<R, ∀ i, (∑ y, if hit j i y then ρ y else 0) ≤ r j)
    (Z : Option (Fin R) → Ω → ℝ) (Y : Ω → A → ℝ)
    (hcount : ∀ x y, Y x y = Z none x +
      ∑ j ∈ Finset.range R, ∑ i, if hit j i y then w j i x else 0)
    (hprefix : ∀ (j : Fin R) x,
      Z none x + ∑ g ∈ Finset.range (j.val+1), ∑ i, w g i x =
        multiplier (some j)*Z (some j) x)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, ∑ y, ν x y*φ (Y x y)) ≤
      ∑ x, μ x*(∑ d, coefficient (h x) (fun j => c*r j) R d *
        φ (multiplier d*Z d x)) := by
  classical
  let W (j : ℕ) (x : Ω) := ∑ i, w j i x
  let s (j : ℕ) (x : Ω) (y : A) := ∑ i, if hit j i y then w j i x else 0
  have hW (j : ℕ) (hj : j<R) (x : Ω) : 0 ≤ W j x :=
    Finset.sum_nonneg (fun i _ => hw j hj i x)
  have hs (j : ℕ) (hj : j<R) (x : Ω) (y : A) : 0 ≤ s j x y := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hw j hj i x
    · exact le_rfl
  have hsW (j : ℕ) (hj : j<R) (x : Ω) (y : A) : s j x y ≤ W j x := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact hw j hj i x
  have hmarg (j : ℕ) (hj : j<R) (x : Ω) :
      (∑ y, ν x y*s j x y) ≤ μ x*(c*r j)*W j x :=
    event_group_marginal (ν x) ρ (μ x) c (r j) (hμ x) hc (hcap x)
      (fun i => w j i x) (fun i => hw j hj i x) (hit j) (hdensity j hj)
  apply Finset.sum_le_sum
  intro x _
  have hb := retained_capped_group_mixture (ν x) (hν x) (μ x) (h x) (hh x)
    (hmass x) φ hφ hmφ (Z none x) (fun j => W j x) (fun j y => s j x y)
    (fun j => c*r j) R (fun j hj => hW j hj x) (fun j hj y => hs j hj x y)
    (fun j hj y => hsW j hj x y) (fun j hj => hmarg j hj x) (by simp only [hrR, mul_zero])
  have he : (∑ d, coefficient (h x) (fun j => c*r j) R d *
      φ (multiplier d*Z d x)) =
      (h x-min (h x) (c*r 0))*φ (Z none x) +
      ∑ j ∈ Finset.range R, (min (h x) (c*r j)-min (h x) (c*r (j+1)))*
        φ (Z none x+prefixWeight (fun j => W j x) (j+1)) := by
    rw [Fintype.sum_option]
    simp only [coefficient, multiplier, one_mul]
    congr 1
    have heq : (∑ j : Fin R, (min (h x) (c*r j.val)-min (h x) (c*r (j.val+1)))*
        φ ((j.val+2)*Z (some j) x)) =
      ∑ j : Fin R, (min (h x) (c*r j.val)-min (h x) (c*r (j.val+1)))*
        φ (Z none x+prefixWeight (fun j => W j x) (j.val+1)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show Z none x+prefixWeight (fun j => W j x) (j.val+1) =
        ((j.val:ℝ)+2)*Z (some j) x from hprefix j x]
    rw [heq, Fin.sum_univ_eq_sum_range (fun j =>
      (min (h x) (c*r j)-min (h x) (c*r (j+1)))*
        φ (Z none x+prefixWeight (fun j => W j x) (j+1))) R]
  rw [he]
  simpa only [hcount, prefixWeight, s] using hb

#print axioms normalized_family_compression
#print axioms event_group_marginal
end Erdos7KernelFamilyCompression
