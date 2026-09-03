import Submission.UncappedFamilyDensity

/-!
# A cofinal near-full-modulus criterion for Erdős 821

The lower bound in `CofinalNearFullStructuredLower` is NOT proved here.
The implication below isolates an arithmetic input sufficient for the
full conjecture, and does not use the second sieve or its endpoint cap.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

def structuredWeightLower (r t m : ℕ) : Prop :=
  (progressionScaleN (t*m) : ℝ)/
    (16*(primeProductMassConstant r : ℝ)*((m : ℝ)+1)^r) ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t*m))

lemma eventually_structuredWeightLower_below_half (r t : ℕ) (hrt : 2*r+1 ≤ t) :
    ∀ᶠ m : ℕ in atTop, structuredWeightLower r t m :=
  eventually_product_mangoldt_weight_lower r t hrt

lemma frequently_structured_count_of_weight_lower (r t : ℕ) (ht : 1 ≤ t)
    (H : ∃ᶠ m : ℕ in atTop, structuredWeightLower r t m) :
    ∃ᶠ m : ℕ in atTop,
      progressionScaleN (t*m) ≤ structuredPrimeCountConstant r t*(m+1)^(r+1)*
        (structuredWitnessPrimes r m (progressionScaleN (t*m))).card := by
  have he : ∀ᶠ m : ℕ in atTop,
      4096*(t-1).choose r*primeProductMassConstant r*t*(m+1)^(r+1) ≤ 2^(32*t*m) ∧ 1 ≤ m := by
    filter_upwards [eventually_nat_poly_le_two_pow 1
      (4096*(t-1).choose r*primeProductMassConstant r*t) (r+1),eventually_ge_atTop 1] with m hp hm
    refine ⟨?_,hm⟩
    have he : m ≤ 32*t*m := Nat.le_mul_of_pos_left m (by omega)
    simpa only [one_mul] using hp.trans (Nat.pow_le_pow_right (by decide) he)
  apply (H.and_eventually he).mono
  intro m hm
  exact structured_prime_count_of_weight r t m ht hm.2.2 hm.1 hm.2.1

lemma near_full_structured_dyadic_family (t : ℕ) (ht : 3 ≤ t)
    (H : ∃ᶠ m : ℕ in atTop, structuredWeightLower (t-2) t m) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^((64*t)*L) ∧
        p-1 ∈ Nat.smoothNumbers (2^(128*L))) ∧
      2^((64*t-1)*L) ≤ P.card := by
  have hcount := frequently_structured_count_of_weight_lower (t-2) t (by omega) H
  have he : ∀ᶠ m : ℕ in atTop,
      structuredPrimeCountConstant (t-2) t*(m+1)^((t-2)+1) ≤ 2^m ∧ 2 ≤ m := by
    filter_upwards [eventually_nat_poly_le_two_pow 1 (structuredPrimeCountConstant (t-2) t)
      ((t-2)+1),eventually_ge_atTop 2] with m hp hm
    exact ⟨by simpa only [one_mul] using hp,hm⟩
  obtain ⟨L,hML,hcount,hpoly,hL⟩ := frequently_atTop.mp (hcount.and_eventually he) M
  refine ⟨L,hML,structuredWitnessPrimes (t-2) L (progressionScaleN (t*L)),?_,?_⟩
  · intro p hp
    have h := structuredWitnessPrimes_smooth (by omega : (t-2)+2 ≤ t) hL hp
    have htr : t-(t-2)=2 := by omega
    simpa only [progressionScaleN,mul_assoc,htr,show 64*2=128 by decide] using h
  · have hpow : 2^L*2^((64*t-1)*L)=progressionScaleN (t*L) := by
      rw [← pow_add]
      unfold progressionScaleN
      congr 1
      have hh := congrArg (fun z : ℕ => z*L) (Nat.sub_add_cancel (by omega : 1 ≤ 64*t))
      nlinarith only [hh]
    apply Nat.le_of_mul_le_mul_left (c := 2^L) _ (by positivity)
    rw [hpow]
    exact hcount.trans (Nat.mul_le_mul_right _ hpoly)

/-- The order t is fixed before arbitrarily large scales m are requested.
Only cofinally many such orders are needed. This is an unproved input. -/
def CofinalNearFullStructuredLower : Prop :=
  ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧ 3 ≤ t ∧
    ∃ᶠ m : ℕ in atTop, structuredWeightLower (t-2) t m

/-- A sufficient arithmetic criterion, not an unconditional settlement. -/
theorem erdos_821_of_cofinal_near_full_structured (H : CofinalNearFullStructuredLower) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite := by
  intro ε hε
  obtain ⟨B,hB⟩ := exists_nat_gt (max 3 (3/ε))
  obtain ⟨t,hBt,ht,Ht⟩ := H B
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ)<t := by linarith
  have hlarge : 3/ε < (t : ℝ) :=
    ((le_max_right _ _).trans_lt hB).trans_le (by exact_mod_cast hBt)
  have heps : 3 < (t : ℝ)*ε := (div_lt_iff₀ hε).mp hlarge
  have hinf := infinite_g_gt_of_general_dyadic_density (64*t) (64*t-1) 128
    (by omega) (by omega) (by omega) (near_full_structured_dyadic_family t ht Ht)
  have hnum : ((64*t-1-128-2 : ℕ) : ℝ)=64*(t : ℝ)-131 := by
    rw [show 64*t-1-128-2=64*t-131 by omega,Nat.cast_sub (by omega : 131 ≤ 64*t)]
    push_cast
    rfl
  have hden : (0 : ℝ)<(64*t : ℕ) := by exact_mod_cast (show 0<64*t by omega)
  have hγ : 1-ε < ((64*t-1-128-2 : ℕ) : ℝ)/((64*t : ℕ) : ℝ) := by
    apply (lt_div_iff₀ hden).mpr
    rw [hnum]
    push_cast
    nlinarith only [heps]
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hγ.le).trans_lt hn.1

/-- A failure would force an eventual deficit at every sufficiently high
order. This is not an assertion that such a deficit occurs. -/
theorem negation_forces_near_full_structured_deficit
    (Hneg : ¬(∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ B : ℕ, ∀ t : ℕ, B ≤ t → 3 ≤ t → ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ primeProductModuli (t-2) m, residueOneMangoldt d (progressionScaleN (t*m))) <
        (progressionScaleN (t*m) : ℝ)/
          (16*(primeProductMassConstant (t-2) : ℝ)*((m : ℝ)+1)^(t-2)) := by
  have H : ¬CofinalNearFullStructuredLower := fun h =>
    Hneg (erdos_821_of_cofinal_near_full_structured h)
  unfold CofinalNearFullStructuredLower at H
  push_neg at H
  simpa only [not_frequently,structuredWeightLower,not_le] using H

end Erdos821
