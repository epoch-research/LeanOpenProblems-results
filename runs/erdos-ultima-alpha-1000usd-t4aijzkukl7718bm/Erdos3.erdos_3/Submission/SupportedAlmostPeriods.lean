import Submission.AsymmetricIncrement
import Submission.CrootSisaskSup

/-! Support-sensitive Croot--Sisask. After truncation to a controlled outer enlargement,
the global sampling theorem already has the needed relative cost. Auxiliary results only. -/
namespace Erdos3SupportedAlmostPeriods
open Finset Erdos3CrootSisaskL2 Erdos3CrootSisaskLp Erdos3CrootSisaskSup
  Erdos3FiniteSamplingMoments Erdos3AsymmetricFourierSmoothing Erdos3AsymmetricSifting
  Erdos3AsymmetricIncrement Erdos3CorrelationSifting Erdos3BohrTranslation
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma evenMoment_le_card_of_support (W : Finset G) (f : G → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0)
    {m : ℕ} (hm : 0 < m) : evenMoment f m ≤ W.card := by
  calc
    _ ≤ ∑ x : G, indicator W x := by
      apply sum_le_sum
      intro x _
      by_cases hx : x ∈ W
      · simp only [indicator, if_pos hx]
        rw [← (even_two_mul m).pow_abs]
        simpa using pow_le_pow_left₀ (abs_nonneg (f x)) (hf x) (2*m)
      · simp [indicator, hx, hsupport x hx, show 2*m ≠ 0 by omega]
    _ = _ := by simp [indicator]

/-- The uniform theorem needs the size of the support of f, not the ambient group. -/
theorem exists_supported_uniform_almost_periods (A B Q W : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (hQ : Q.Nonempty)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hWB : W.card ≤ 2^(2*m)*B.card) :
    ∃ P : Finset G, P ⊆ Q ∧
      A.card^(256*m^4*r^2)*Q.card ≤ 2*(A+Q).card^(256*m^4*r^2)*P.card ∧
      ∀ s ∈ P, ∀ t ∈ P, ∀ x : G,
        |smooth B (smooth A f) (x+s)-smooth B (smooth A f) (x+t)| ≤ 2/(r : ℝ) := by
  have hn : 0 < 256*m^4*r^2 := by positivity
  obtain ⟨P,hPQ,hPc,hper⟩ := exists_many_Lp_almost_periods A Q hA hQ f hn hm
  refine ⟨P,hPQ,hPc,?_⟩
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcoeff : (256*(m : ℝ)^4/((256*m^4*r^2 : ℕ) : ℝ))^m = (1/(r : ℝ))^(2*m) := by
    push_cast
    rw [show 256*(m : ℝ)^4/(256*(m : ℝ)^4*(r : ℝ)^2) = (1/(r : ℝ))^2 by field_simp]
    rw [← pow_mul]
  have hWBR : (W.card : ℝ) ≤ (2 : ℝ)^(2*m)*B.card := by exact_mod_cast hWB
  intro s hs t ht x
  let g : G → ℝ := fun y ↦ smooth A f (y+s)-smooth A f (y+t)
  have hg : evenMoment g m ≤ (2/(r : ℝ))^(2*m)*B.card := by
    calc
      _ ≤ (256*(m : ℝ)^4/((256*m^4*r^2 : ℕ) : ℝ))^m*evenMoment f m := hper s hs t ht
      _ = (1/(r : ℝ))^(2*m)*evenMoment f m := by rw [hcoeff]
      _ ≤ (1/(r : ℝ))^(2*m)*(W.card : ℝ) := mul_le_mul_of_nonneg_left
        (evenMoment_le_card_of_support W f hf hsupport hm) (by positivity)
      _ ≤ (1/(r : ℝ))^(2*m)*((2 : ℝ)^(2*m)*B.card) :=
        mul_le_mul_of_nonneg_left hWBR (by positivity)
      _ = _ := by rw [div_pow, div_pow, one_pow]; ring
  have hh := smooth_abs_le_of_evenMoment_le B hB g hm (by positivity : (0 : ℝ) ≤ 2/r) hg x
  simpa only [g, smooth_sub, smooth_translate] using hh

/-- Sample the small inner set T, then smooth by the dense outer set S. -/
theorem exists_crossSmooth_almost_periods (S T Q W : Finset G)
    (hS : S.Nonempty) (hT : T.Nonempty) (hQ : Q.Nonempty)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) (hsupport : ∀ x, x ∉ W → f x = 0)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hWS : W.card ≤ 2^(2*m)*S.card) :
    ∃ P : Finset G, P.Nonempty ∧ P ⊆ Q ∧
      T.card^(256*m^4*r^2)*Q.card ≤ 2*(T+Q).card^(256*m^4*r^2)*P.card ∧
      ∀ s ∈ P, ∀ t ∈ P, ∀ x : G,
        |crossSmooth S T f (x+s)-crossSmooth S T f (x+t)| ≤ 2/(r : ℝ) := by
  obtain ⟨P,hPQ,hPc,hper⟩ := exists_supported_uniform_almost_periods T (-S) Q W hT hS.neg hQ
    f hf hsupport hm hr (by simpa using hWS)
  have hP : P.Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    rw [hz, card_empty, mul_zero] at hPc
    have hp : 0 < T.card^(256*m^4*r^2)*Q.card :=
      mul_pos (pow_pos hT.card_pos _) hQ.card_pos
    omega
  refine ⟨P,hP,hPQ,hPc,?_⟩
  simpa only [crossSmooth_eq] using hper

noncomputable def truncate (W : Finset G) (f : G → ℝ) (x : G) : ℝ := indicator W x*f x

lemma truncate_nonneg (W : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ truncate W f x := mul_nonneg (indicator_nonneg W x) (hf x)

lemma truncate_le (W : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    truncate W f x ≤ f x := by
  by_cases hx : x ∈ W <;> simp [truncate, indicator, hx, hf x]

lemma truncate_abs_le_one (W : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : G) : |truncate W f x| ≤ 1 := by
  rw [abs_of_nonneg (truncate_nonneg W f (fun x ↦ (hf x).1) x)]
  exact (truncate_le W f (fun x ↦ (hf x).1) x).trans (hf x).2

lemma truncate_support (W : Finset G) (f : G → ℝ) (x : G) (hx : x ∉ W) :
    truncate W f x = 0 := by simp [truncate, indicator, hx]

lemma crossAverage_one_sub (S T : Finset G) (hS : S.Nonempty) (hT : T.Nonempty) (f : G → ℝ) :
    crossAverage S T (fun x ↦ 1-f x) = 1-crossAverage S T f := by
  letI : Nonempty S := hS.to_subtype
  letI : Nonempty T := hT.to_subtype
  simp only [crossAverage, expect_sub_distrib, Fintype.expect_const]

lemma crossAverage_lower (S T : Finset G) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : G → ℝ) {δ : ℝ}
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ δ*density S*density T) :
    1-δ ≤ crossAverage S T f := by
  rw [crossPairDensity_eq_crossAverage S T hS hT, crossAverage_one_sub S T hS hT] at hbad
  have hp := mul_pos (density_pos S hS) (density_pos T hT)
  have h : 1-crossAverage S T f ≤ δ := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  linarith

lemma crossSmooth_truncate_zero (S T W : Finset G) (f : G → ℝ)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W) :
    crossSmooth S T (truncate W f) 0 = crossAverage S T f := by
  rw [crossSmooth_zero]
  unfold crossAverage
  apply expect_congr rfl
  intro s _
  apply expect_congr rfl
  intro t _
  simp [truncate, indicator, hW s s.property t t.property]

/-- A truncated popular-difference average has many global almost-periods at a cost
controlled by the outer support and the inner sumset. -/
theorem exists_supported_popular_periods (S T Q W : Finset G)
    (hS : S.Nonempty) (hT : T.Nonempty) (hQ : Q.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {δ : ℝ}
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ δ*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hWS : W.card ≤ 2^(2*m)*S.card) :
    ∃ P : Finset G, P.Nonempty ∧ P ⊆ Q ∧
      T.card^(256*m^4*r^2)*Q.card ≤ 2*(T+Q).card^(256*m^4*r^2)*P.card ∧
      (∀ s ∈ P, ∀ t ∈ P, ∀ x : G,
        |crossSmooth S T (truncate W f) (x+s)-crossSmooth S T (truncate W f) (x+t)| ≤ 2/(r : ℝ)) ∧
      (1-δ ≤ crossSmooth S T (truncate W f) 0) ∧
      ∀ s ∈ P, ∀ t ∈ P, 1-δ-2/(r : ℝ) ≤ crossSmooth S T (truncate W f) (s-t) := by
  obtain ⟨P,hP,hPQ,hPc,hper⟩ := exists_crossSmooth_almost_periods S T Q W hS hT hQ
    (truncate W f) (truncate_abs_le_one W f hf) (truncate_support W f) hm hr hWS
  have hzero : 1-δ ≤ crossSmooth S T (truncate W f) 0 := by
    rw [crossSmooth_truncate_zero S T W f hW]
    exact crossAverage_lower S T hS hT f hbad
  refine ⟨P,hP,hPQ,hPc,hper,hzero,?_⟩
  intro s hs t ht
  have hp := hper s hs t ht (-t)
  have he : -t+s = s-t := by abel
  rw [he, neg_add_cancel] at hp
  linarith [(abs_le.mp hp).1]

#print axioms exists_supported_uniform_almost_periods
#print axioms exists_crossSmooth_almost_periods
#print axioms exists_supported_popular_periods
end Erdos3SupportedAlmostPeriods
