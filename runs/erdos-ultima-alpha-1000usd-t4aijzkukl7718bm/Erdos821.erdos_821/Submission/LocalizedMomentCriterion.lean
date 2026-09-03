import Submission.CofinalMomentCriterion

/-!
# Localizing the cofinal moment criterion

An elementary geometric-growth lemma turns a frequent summatory lower
bound into a frequent lower bound in a single scale block. At cofinal
orders the constant loss can be absorbed in the permitted geometric
loss. The arithmetic lower bound remains an explicit hypothesis.
-/

open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 3000000

/-- This is a localization principle, not a source of lower bounds. -/
lemma frequently_increment_of_geometric_growth (A W : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 2*W n ≤ W (n+1))
    (ht : Tendsto W atTop atTop)
    (hA : ∃ᶠ n : ℕ in atTop, C*W n ≤ A n) :
    ∃ᶠ n : ℕ in atTop, C/4*W (n+1) ≤ A (n+1)-A n := by
  by_contra hh
  have he : ∀ᶠ n : ℕ in atTop, A (n+1)-A n < C/4*W (n+1) := by
    simpa only [not_frequently,not_le] using hh
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  have hbound : ∀ n, M ≤ n → A n ≤ C/2*W n+A M := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => nlinarith only [hW M,hC]
    | @succ n hn ih =>
      have hstep := hM n hn
      have hdouble := mul_le_mul_of_nonneg_left (hd n) (show 0 ≤ C/4 by positivity)
      linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*A M/C < W n := ht.eventually (eventually_gt_atTop _)
  obtain ⟨n,hn,hAn,hlarge⟩ := frequently_atTop.mp (hA.and_eventually hlarge) M
  have hb := hbound n hn
  have hprod := (div_lt_iff₀ hC).mp hlarge
  nlinarith

noncomputable def normalizedMomentScale (k t L : ℕ) : ℝ :=
  (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ)

lemma normalizedMomentScale_nonneg (k t L : ℕ) : 0 ≤ normalizedMomentScale k t L := by
  unfold normalizedMomentScale
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (Real.log_natCast_nonneg _) _)) (Nat.cast_nonneg _)

lemma momentScaleX_succ (t L : ℕ) :
    momentScaleX t (L+1) = momentScaleX t L*2^(128*t) := by
  unfold momentScaleX
  rw [← pow_add]
  congr 1

lemma normalizedMomentScale_double (k t L : ℕ) (ht : 1 ≤ t) :
    2*normalizedMomentScale k t L ≤ normalizedMomentScale k t (L+1) := by
  have hpow : 2 ≤ 2^(128*t) := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ 128*t by omega)
    simpa only [pow_one] using hh
  have hx : 2*momentScaleX t L ≤ momentScaleX t (L+1) := by
    rw [momentScaleX_succ]
    simpa only [mul_comm] using Nat.mul_le_mul_left (momentScaleX t L) hpow
  have hx' : momentScaleX t L ≤ momentScaleX t (L+1) := by omega
  have hlog : Real.log (momentScaleX t L) ≤ Real.log (momentScaleX t (L+1)) :=
    AnalyticSieve.log_nat_mono hx'
  have hh := mul_le_mul (show (2 : ℝ)*(momentScaleX t L : ℝ) ≤ momentScaleX t (L+1) by exact_mod_cast hx)
    (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog (k-2))
    (pow_nonneg (Real.log_natCast_nonneg _) _) (Nat.cast_nonneg _)
  have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (k.factorial))
  convert hh' using 1; unfold normalizedMomentScale; ring

lemma normalizedMomentScale_tendsto (k t : ℕ) (ht : 1 ≤ t) :
    Tendsto (normalizedMomentScale k t) atTop atTop := by
  have hp : Tendsto (fun L : ℕ => (2 : ℝ)^L/(k.factorial : ℝ)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2)).atTop_div_const
      (by positivity : (0 : ℝ)<k.factorial)
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hlog := one_le_log_momentScaleX t L ht hL
  have hx : 2^L ≤ momentScaleX t L := by
    unfold momentScaleX
    apply Nat.pow_le_pow_right (by decide)
    have hh := Nat.mul_le_mul_right L ht
    nlinarith only [hh]
  unfold normalizedMomentScale
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hxR : (2 : ℝ)^L ≤ momentScaleX t L := by exact_mod_cast hx
  exact hxR.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hlog))

noncomputable def shiftedPrimeBlockMoment (k t L : ℕ) : ℝ :=
  shiftedPrimeMoment k (momentScaleX t (L+1))-shiftedPrimeMoment k (momentScaleX t L)

lemma shiftedPrimeMoment_difference (k X Y : ℕ) (hXY : X ≤ Y) :
    shiftedPrimeMoment k Y-shiftedPrimeMoment k X =
      ∑ p ∈ (Y+1).primesBelow with X < p, (tau k (p-1) : ℝ) := by
  have hfilter : (Y+1).primesBelow.filter (fun p => ¬X < p) = (X+1).primesBelow := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpY,hp⟩,hXp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpX,hp⟩
      exact ⟨⟨by omega,hp⟩,by omega⟩
  have hh := Finset.sum_filter_add_sum_filter_not (Y+1).primesBelow
    (fun p => X < p) (fun p => (tau k (p-1) : ℝ))
  rw [hfilter] at hh
  unfold shiftedPrimeMoment
  linarith only [hh]

/-- The block is an actual nonnegative prime sum, not a cancellation weight. -/
lemma shiftedPrimeBlockMoment_eq_sum (k t L : ℕ) :
    shiftedPrimeBlockMoment k t L =
      ∑ p ∈ (momentScaleX t (L+1)+1).primesBelow with momentScaleX t L < p,
        (tau k (p-1) : ℝ) := by
  apply shiftedPrimeMoment_difference
  unfold momentScaleX
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left _ (Nat.le_succ L)

lemma shiftedPrimeBlockMoment_nonneg (k t L : ℕ) :
    0 ≤ shiftedPrimeBlockMoment k t L := by
  rw [shiftedPrimeBlockMoment_eq_sum]
  exact Finset.sum_nonneg (fun _p _ => Nat.cast_nonneg _)

/-- A summatory coefficient gives a block coefficient with only a fixed loss. -/
lemma frequently_block_moment_of_total (k t : ℕ) (ht : 1 ≤ t) (C : ℝ) (hC : 0 < C)
    (H : ∃ᶠ L : ℕ in atTop,
      C*normalizedMomentScale k t L ≤ shiftedPrimeMoment k (momentScaleX t L)) :
    ∃ᶠ L : ℕ in atTop,
      C/4*normalizedMomentScale k t (L+1) ≤ shiftedPrimeBlockMoment k t L :=
  frequently_increment_of_geometric_growth _ _ C hC
    (normalizedMomentScale_nonneg k t) (fun L => normalizedMomentScale_double k t L ht)
    (normalizedMomentScale_tendsto k t ht) H

lemma shiftedPrimeMoment_nonneg (k X : ℕ) : 0 ≤ shiftedPrimeMoment k X :=
  Finset.sum_nonneg (fun _p _ => Nat.cast_nonneg _)

lemma shiftedPrimeBlockMoment_le_total (k t L : ℕ) :
    shiftedPrimeBlockMoment k t L ≤ shiftedPrimeMoment k (momentScaleX t (L+1)) := by
  unfold shiftedPrimeBlockMoment
  linarith only [shiftedPrimeMoment_nonneg k (momentScaleX t L)]

/-- Still an unproved lower bound. Each block is between consecutive
geometric scales, not an interval of bounded additive length. -/
def CofinalLocalizedMomentLower : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ t : ℕ, 2 ≤ t → ∀ B : ℕ,
    ∃ k : ℕ, B ≤ k ∧ 2 ≤ k ∧ ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧
      θ^k*normalizedMomentScale k t (L+1) ≤ shiftedPrimeBlockMoment k t L

lemma cofinal_geometric_of_localized (H : CofinalLocalizedMomentLower) :
    CofinalGeometricMomentLower := by
  intro θ hθ0 hθ1 t ht B
  obtain ⟨k,hBk,hk,Hk⟩ := H θ hθ0 hθ1 t ht B
  refine ⟨k,hBk,hk,?_⟩
  intro M
  obtain ⟨L,hML,hL⟩ := Hk M
  refine ⟨L+1,by omega,?_⟩
  have hh := hL.trans (shiftedPrimeBlockMoment_le_total k t L)
  convert hh using 1; unfold normalizedMomentScale; ring

lemma cofinal_localized_of_geometric (H : CofinalGeometricMomentLower) :
    CofinalLocalizedMomentLower := by
  intro θ hθ0 hθ1 t ht B
  let η : ℝ := (θ+1)/2
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hθη : θ < η := by dsimp [η]; linarith
  have hratio0 : 0 ≤ θ/η := div_nonneg hθ0.le hη0.le
  have hratio1 : θ/η < 1 := (div_lt_one hη0).mpr hθη
  have hsmall : ∀ᶠ k : ℕ in atTop, (θ/η)^k < 1/4 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).eventually_lt_const (by norm_num)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hsmall
  obtain ⟨k,hBk,hk,Hk⟩ := H η hη0 hη1 t ht (max B K)
  have hcoef : θ^k ≤ η^k/4 := by
    have hh := hK k ((le_max_right _ _).trans hBk)
    rw [div_pow] at hh
    have hh' := (div_lt_iff₀ (pow_pos hη0 k)).mp hh
    linarith
  have hfreq : ∃ᶠ L : ℕ in atTop,
      η^k*normalizedMomentScale k t L ≤ shiftedPrimeMoment k (momentScaleX t L) := by
    apply frequently_atTop.mpr
    intro M
    obtain ⟨L,hML,hL⟩ := Hk M
    refine ⟨L,hML,?_⟩
    convert hL using 1; unfold normalizedMomentScale; ring
  have hblock := frequently_block_moment_of_total k t (by omega) (η^k) (pow_pos hη0 k) hfreq
  refine ⟨k,(le_max_left _ _).trans hBk,hk,?_⟩
  intro M
  obtain ⟨L,hML,hL⟩ := frequently_atTop.mp hblock M
  refine ⟨L,hML,?_⟩
  exact (mul_le_mul_of_nonneg_right hcoef (normalizedMomentScale_nonneg _ _ _)).trans hL

/-- Localization is equivalent to the previous input: it does not by
itself weaken the arithmetic needed at cofinal orders. -/
theorem cofinal_localized_iff_geometric :
    CofinalLocalizedMomentLower ↔ CofinalGeometricMomentLower :=
  ⟨cofinal_geometric_of_localized,cofinal_localized_of_geometric⟩

theorem erdos_821_of_cofinal_localized_moments (H : CofinalLocalizedMomentLower) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_cofinal_geometric_moments (cofinal_geometric_of_localized H)

end Erdos821.HigherDivisors
