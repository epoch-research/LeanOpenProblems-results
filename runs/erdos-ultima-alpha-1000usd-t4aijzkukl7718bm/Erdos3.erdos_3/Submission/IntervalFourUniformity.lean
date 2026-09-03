import Submission.CyclicIntervalMask
import Submission.Reduction

/-! Four-term-free integer intervals have large U³ for the interval-relative
balanced function, with no fixed-factor loss in the reference density. -/
namespace Erdos3IntervalFourUniformity
open Finset Erdos3CyclicIntervalMask Erdos3MaskedUniformityCounting Erdos3Reduction
  Erdos3CorrelationSifting Erdos3FiniteUniformity
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

lemma balanced_four_constant (S : Finset ℕ) (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (h₁ : a+c = b+b) (h₂ : b+d = c+c) : a = b := by
  by_contra hab
  have hno := (free_iff_not_hasNatAP (by decide : 2 ≤ 4)).mp hfree
  rcases lt_or_gt_of_ne hab with hab | hab
  · apply hno
    refine ⟨a,b-a,by omega,?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · convert hb using 1 <;> omega
    · convert hc using 1 <;> omega
    · convert hd using 1 <;> omega
  · apply hno
    refine ⟨d,c-d,by omega,?_⟩
    intro i hi
    interval_cases i
    · simpa using hd
    · convert hc using 1 <;> omega
    · convert hb using 1 <;> omega
    · convert ha using 1 <;> omega

lemma cast_four_diagonal (p N : ℕ) [NeZero p] (hp : 2*N ≤ p)
    (S : Finset ℕ) (hS : S ⊆ range N) (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    (x d : ZMod p) (hpat : ∀ i : Fin 4, x+(i.val : ZMod p)*d ∈ castSet p S) : d = 0 := by
  have hm (i : Fin 4) : ∃ a ∈ S, (a : ZMod p) = x+(i.val : ZMod p)*d := by
    exact mem_image.mp (hpat i)
  choose a ha he using hm
  have hN (i : Fin 4) : a i < N := mem_range.mp (hS (ha i))
  have h₁ : a 0+a 2 = a 1+a 1 := by
    have hc : ((a 0+a 2 : ℕ) : ZMod p) = ((a 1+a 1 : ℕ) : ZMod p) := by
      simp only [Nat.cast_add,he]
      norm_num
      ring
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast_of_lt (by have := hN 0; have := hN 2; omega),
      ZMod.val_natCast_of_lt (by have := hN 1; omega)] at hv
    exact hv
  have h₂ : a 1+a 3 = a 2+a 2 := by
    have hc : ((a 1+a 3 : ℕ) : ZMod p) = ((a 2+a 2 : ℕ) : ZMod p) := by
      simp only [Nat.cast_add,he]
      norm_num
      ring
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast_of_lt (by have := hN 1; have := hN 3; omega),
      ZMod.val_natCast_of_lt (by have := hN 2; omega)] at hv
    exact hv
  have hab := balanced_four_constant S hfree (ha 0) (ha 1) (ha 2) (ha 3) h₁ h₂
  have hc := congrArg (fun n : ℕ ↦ (n : ZMod p)) hab
  dsimp only at hc
  rw [he 0,he 1] at hc
  have hh : x+0 = x+d := by simpa using hc
  exact (add_left_cancel hh).symm

lemma four_slopes_injective (p : ℕ) [NeZero p] (hp : 4 ≤ p) :
    Function.Injective (fun i : Fin 4 ↦ (i.val : ZMod p)) := by
  intro i j hij
  have he := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt (i.isLt.trans_le hp),ZMod.val_natCast_of_lt (j.isLt.trans_le hp)] at he
  exact Fin.ext he

/-- The large uniformity parameter is a fixed power of the ORIGINAL interval
density, although the ambient modulus may be up to four times the interval. -/
theorem interval_four_uniformity_lower (p N : ℕ) [Fact p.Prime]
    (hN : 8 ≤ N) (hNp : 2*N ≤ p) (hpN : p ≤ 4*N)
    (S : Finset ℕ) (hS : S ⊆ range N) (hne : S.Nonempty)
    (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    (hsize : 4096 ≤ (intervalDensity S N)^4*(p : ℝ)) :
    ((intervalDensity S N)^4/8192)^8 <
      uniformityPower 2 (fun x ↦ ((relativeBalance p N S x : ℝ) : ℂ)) := by
  have hN0 : 0 < N := by omega
  have hNp' : N ≤ p := by omega
  have hα : 0 < intervalDensity S N := by
    apply div_pos
    · exact_mod_cast hne.card_pos
    · exact_mod_cast hN0
  have hα1 := (intervalDensity_bounds N hN0 S hS).2
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hden : density (castSet p S) ≤ 1 := by
    unfold density
    rw [ZMod.card]
    apply (div_le_one hp).mpr
    exact_mod_cast (show (castSet p S).card ≤ p by simpa only [ZMod.card] using card_le_univ (castSet p S))
  have hsmall : density (castSet p S)/(Fintype.card (ZMod p) : ℝ) ≤
      (intervalDensity S N)^4*(1/1024)/4 := by
    rw [ZMod.card]
    apply (div_le_div_of_nonneg_right hden hp.le).trans
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hsize]
  have hh := masked_pattern_uniformity_lower 2 (fun i : Fin 4 ↦ (i.val : ZMod p))
    (four_slopes_injective p (by omega)) (castSet p S) (intervalMask p N) hα hα1
    (by norm_num : (0 : ℝ) < 1/1024) (four_interval_patterns p N hN hNp' hpN) hsmall
    (cast_four_diagonal p N hNp S hS hfree)
  convert hh using 1 <;> norm_num [relativeBalance] <;> ring

#print axioms cast_four_diagonal
#print axioms interval_four_uniformity_lower
end Erdos3IntervalFourUniformity
