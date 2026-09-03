import Submission.CrootSisaskLp

/-! Uniform almost-periodicity after a second smoothing. This develops an
analytic ingredient and does not assert the original conjecture. -/
namespace Erdos3CrootSisaskSup

open Finset Erdos3CrootSisaskL2 Erdos3CrootSisaskLp Erdos3FiniteSamplingMoments
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
lemma smooth_sub (B : Finset G) (f g : G → ℝ) (x : G) :
    smooth B (fun y ↦ f y - g y) x = smooth B f x - smooth B g x :=
  expect_sub_distrib _ _ _

omit [Fintype G] in
lemma smooth_translate (B : Finset G) (f : G → ℝ) (x s : G) :
    smooth B (fun y ↦ f (y+s)) x = smooth B f (x+s) := by
  apply expect_congr rfl
  intro b _
  simp only [add_right_comm]

lemma smooth_abs_le_of_evenMoment_le (B : Finset G) (hB : B.Nonempty)
    (g : G → ℝ) {m : ℕ} (hm : 0 < m) {e : ℝ} (he : 0 ≤ e)
    (hg : evenMoment g m ≤ e^(2*m)*B.card) (x : G) :
    |smooth B g x| ≤ e := by
  letI : Nonempty B := hB.to_subtype
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast card_pos.mpr hB
  have hsum : (∑ b : B, (g (x+(b : G)))^(2*m)) ≤ evenMoment g m := by
    calc
      _ = ∑ b ∈ B, (g (x+b))^(2*m) := sum_coe_sort B _
      _ = ∑ y ∈ B.image (fun b ↦ x+b), (g y)^(2*m) := by
        rw [sum_image (fun a _ b _ hab ↦ add_left_cancel hab)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun y _ _ ↦ (even_two_mul m).pow_nonneg _)
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) he (by omega : 2*m ≠ 0)).mp
  rw [(even_two_mul m).pow_abs]
  calc
    (smooth B g x)^(2*m) ≤ 𝔼 b : B, (g (x+(b : G)))^(2*m) :=
      expect_even_pow_le (even_two_mul m) _
    _ = (∑ b : B, (g (x+(b : G)))^(2*m)) / B.card := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_coe]
    _ ≤ (e^(2*m)*B.card) / B.card := div_le_div_of_nonneg_right (hsum.trans hg) hBc.le
    _ = e^(2*m) := by field_simp

omit [AddCommGroup G] in
lemma evenMoment_le_card_of_abs_le_one (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) (m : ℕ) :
    evenMoment f m ≤ Fintype.card G := by
  calc
    _ ≤ ∑ _x : G, (1 : ℝ) := by
      apply sum_le_sum
      intro x _
      rw [← (even_two_mul m).pow_abs (f x)]
      simpa using pow_le_pow_left₀ (abs_nonneg _) (hf x) (2*m)
    _ = _ := by simp

/-- Uniform almost-periodicity for a bounded function averaged over A and B.
If B has density at least 2^(-2m), the sample count 256*m⁴*r² gives error 2/r. -/
theorem exists_uniform_almost_periods (A B S : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hBd : Fintype.card G ≤ 2^(2*m)*B.card) :
    ∃ T : Finset G, T ⊆ S ∧
      A.card^(256*m^4*r^2)*S.card ≤ 2*(A+S).card^(256*m^4*r^2)*T.card ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ x : G,
        |smooth B (smooth A f) (x+s) - smooth B (smooth A f) (x+t)| ≤ 2/(r : ℝ) := by
  have hn : 0 < 256*m^4*r^2 := by positivity
  obtain ⟨T,hTS,hTc,hper⟩ := exists_many_Lp_almost_periods A S hA hS f hn hm
  refine ⟨T,hTS,hTc,?_⟩
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hcoeff : (256*(m : ℝ)^4/((256*m^4*r^2 : ℕ) : ℝ))^m =
      (1/(r : ℝ))^(2*m) := by
    push_cast
    rw [show (256*(m : ℝ)^4/(256*(m : ℝ)^4*(r : ℝ)^2)) = (1/(r : ℝ))^2 by field_simp]
    rw [← pow_mul]
  have hBdR : (Fintype.card G : ℝ) ≤ (2 : ℝ)^(2*m)*B.card := by exact_mod_cast hBd
  intro s hs t ht x
  let g : G → ℝ := fun y ↦ smooth A f (y+s) - smooth A f (y+t)
  have hg : evenMoment g m ≤ (2/(r : ℝ))^(2*m)*B.card := by
    calc
      _ ≤ (256*(m : ℝ)^4/((256*m^4*r^2 : ℕ) : ℝ))^m*evenMoment f m := hper s hs t ht
      _ = (1/(r : ℝ))^(2*m)*evenMoment f m := by rw [hcoeff]
      _ ≤ (1/(r : ℝ))^(2*m)*(Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_left (evenMoment_le_card_of_abs_le_one f hf m) (by positivity)
      _ ≤ (1/(r : ℝ))^(2*m)*((2 : ℝ)^(2*m)*B.card) :=
        mul_le_mul_of_nonneg_left hBdR (by positivity)
      _ = _ := by rw [div_pow, div_pow, one_pow]; ring
  have hh := smooth_abs_le_of_evenMoment_le B hB g hm (by positivity : (0 : ℝ) ≤ 2/r) hg x
  simpa only [g, smooth_sub, smooth_translate] using hh

#print axioms smooth_abs_le_of_evenMoment_le
#print axioms exists_uniform_almost_periods
end Erdos3CrootSisaskSup
