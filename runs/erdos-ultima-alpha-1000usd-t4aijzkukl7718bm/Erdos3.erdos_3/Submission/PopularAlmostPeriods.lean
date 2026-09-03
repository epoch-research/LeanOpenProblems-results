import Submission.CorrelationSifting
import Submission.CrootSisaskSup

/-! Uniform almost-periodicity for a sifted set of popular differences.
This is an auxiliary finite-group step, not a settlement of Erdős Problem 3. -/
namespace Erdos3PopularAlmostPeriods
open Finset Erdos3CorrelationSifting Erdos3CrootSisaskL2 Erdos3CrootSisaskSup
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 1500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def diffSmooth (B : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 b : B, 𝔼 c : B, f (x+(c : G)-(b : G))

lemma expect_indicator_mul (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) :
    (𝔼 x : G, indicator B x * f x) = density B * (𝔼 b : B, f b) := by
  have hBc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_coe]
  simp only [indicator, ite_mul, one_mul, zero_mul, ← sum_filter, filter_mem_eq_inter,
    univ_inter, sum_coe_sort, density]
  field_simp

lemma pairDensity_eq_diffSmooth (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) :
    pairDensity B f = (density B)^2 * diffSmooth B f 0 := by
  unfold pairDensity
  simp_rw [mul_assoc, ← mul_expect, expect_indicator_mul B hB]
  rw [← mul_expect]
  simp only [diffSmooth, zero_add, sq, mul_assoc]

omit [Fintype G] in
lemma smooth_neg (B : Finset G) (f : G → ℝ) (x : G) :
    smooth (-B) f x = 𝔼 b : B, f (x-(b : G)) := by
  let e : B ≃ (↑(-B) : Set G) :=
    { toFun := fun b ↦ ⟨-(b : G), by simpa using b.property⟩
      invFun := fun b ↦ ⟨-(b : G), by simpa using b.property⟩
      left_inv := fun b ↦ by apply Subtype.ext; simp
      right_inv := fun b ↦ by apply Subtype.ext; simp }
  exact (Fintype.expect_equiv e _ _ (fun b ↦ by simp [e, sub_eq_add_neg])).symm

omit [Fintype G] in
lemma smooth_neg_smooth (B : Finset G) (f : G → ℝ) (x : G) :
    smooth (-B) (smooth B f) x = diffSmooth B f x := by
  rw [smooth_neg]
  apply expect_congr rfl
  intro b _
  apply expect_congr rfl
  intro c _
  congr 1
  abel

omit [Fintype G] in
lemma diffSmooth_sub (B : Finset G) (f g : G → ℝ) (x : G) :
    diffSmooth B (fun y ↦ f y-g y) x = diffSmooth B f x - diffSmooth B g x := by
  simp only [diffSmooth, expect_sub_distrib]

omit [Fintype G] in
lemma diffSmooth_const (B : Finset G) (hB : B.Nonempty) (a : ℝ) (x : G) :
    diffSmooth B (fun _ ↦ a) x = a := by
  letI : Nonempty B := hB.to_subtype
  simp only [diffSmooth, Fintype.expect_const]

omit [Fintype G] in
lemma diffSmooth_nonneg (B : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ diffSmooth B f x :=
  expect_nonneg (fun _ _ ↦ expect_nonneg (fun _ _ ↦ hf _))

omit [Fintype G] in
lemma diffSmooth_le_one (B : Finset G) (hB : B.Nonempty)
    (f : G → ℝ) (hf : ∀ x, f x ≤ 1) (x : G) : diffSmooth B f x ≤ 1 := by
  letI : Nonempty B := hB.to_subtype
  exact expect_le univ_nonempty (fun b _ ↦ expect_le univ_nonempty (fun c _ ↦ hf _))

lemma diffSmooth_zero_lower (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) {δ : ℝ}
    (hbad : pairDensity B (fun x ↦ 1-f x) ≤ δ*(density B)^2) :
    1-δ ≤ diffSmooth B f 0 := by
  rw [pairDensity_eq_diffSmooth B hB, diffSmooth_sub, diffSmooth_const B hB] at hbad
  have h := (mul_le_mul_iff_right₀ (sq_pos_of_pos (density_pos B hB))).mp
    (show (density B)^2*(1-diffSmooth B f 0) ≤ (density B)^2*δ by nlinarith [hbad])
  linarith

/-- Sifting plus Croot--Sisask gives a large set of uniform almost-periods,
and the difference of any two of them preserves popular-difference concentration. -/
theorem exists_popular_almost_periods (B S : Finset G) (hB : B.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {δ : ℝ}
    (hbad : pairDensity B (fun x ↦ 1-f x) ≤ δ*(density B)^2)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hBd : Fintype.card G ≤ 2^(2*m)*B.card) :
    ∃ T : Finset G, T.Nonempty ∧ T ⊆ S ∧
      B.card^(256*m^4*r^2)*S.card ≤ 2*(B+S).card^(256*m^4*r^2)*T.card ∧
      (∀ s ∈ T, ∀ t ∈ T, ∀ x : G,
        |diffSmooth B f (x+s) - diffSmooth B f (x+t)| ≤ 2/(r : ℝ)) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        1-δ-2/(r : ℝ) ≤ diffSmooth B f (s-t) := by
  obtain ⟨T,hTS,hcard,hper⟩ := exists_uniform_almost_periods B (-B) S hB hB.neg hS f
    (fun x ↦ (abs_le.mpr ⟨by linarith [(hf x).1], (hf x).2⟩)) hm hr
    (by simpa using hBd)
  have hT : T.Nonempty := by
    by_contra h
    have hz : T = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [hz, card_empty, mul_zero] at hcard
    have : 0 < B.card^(256*m^4*r^2)*S.card := mul_pos (pow_pos hB.card_pos _) hS.card_pos
    omega
  simp only [smooth_neg_smooth] at hper
  refine ⟨T,hT,hTS,hcard,hper,?_⟩
  intro s hs t ht
  have hp := hper s hs t ht (-t)
  have h0 := diffSmooth_zero_lower B hB f hbad
  have he : -t+s = s-t := by abel
  rw [he, neg_add_cancel] at hp
  have hl := (abs_le.mp hp).1
  linarith

omit [Fintype G] in
/-- Uniform errors add when almost-periods are added. -/
lemma sum_almost_periods {I : Type*} (u : Finset I) (d : I → G) (e : I → ℝ)
    (f : G → ℝ) (h : ∀ i ∈ u, ∀ x, |f (x+d i)-f x| ≤ e i) (x : G) :
    |f (x+∑ i ∈ u, d i)-f x| ≤ ∑ i ∈ u, e i := by
  induction u using Finset.induction_on with
  | empty => simp
  | @insert i u hi ih =>
    rw [sum_insert hi, sum_insert hi]
    have hui : ∀ j ∈ u, ∀ y, |f (y+d j)-f y| ≤ e j :=
      fun j hj ↦ h j (mem_insert_of_mem hj)
    calc
      _ ≤ |f (x+(d i+∑ j ∈ u, d j))-f (x+∑ j ∈ u, d j)| +
          |f (x+∑ j ∈ u, d j)-f x| := abs_sub_le _ _ _
      _ ≤ e i + ∑ j ∈ u, e j := by
        apply add_le_add _ (ih hui)
        simpa only [add_comm, add_left_comm, add_assoc] using
          h i (mem_insert_self _ _) (x+∑ j ∈ u, d j)

#print axioms exists_popular_almost_periods
#print axioms sum_almost_periods
end Erdos3PopularAlmostPeriods
