import Submission.HarmonicPrimeWinnerNorm
import Submission.PrimeWinnerFlux
import Submission.PrimeHarmonicBounds

/-! Each fixed-prime harmonic current is absolutely convergent. A weighted
flux identity gives positive divergence, not positivity of the currents.
There is no uniform summability claim over the prime labels. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def smoothReciprocal (B n : ℕ) : ℝ :=
  if n ∈ Nat.smoothNumbers (B+1) then 1/n else 0

lemma smoothReciprocal_nonneg (B n : ℕ) : 0≤smoothReciprocal B n := by
  unfold smoothReciprocal
  split_ifs <;> positivity

lemma smoothReciprocal_of_maxPrimeFac_le (B n : ℕ) (hn : n≠0)
    (hB : Nat.maxPrimeFac n≤B) : smoothReciprocal B n=1/n := by
  rw [smoothReciprocal,if_pos]
  apply Nat.mem_smoothNumbers'.mpr
  intro p hp hpn
  exact Nat.lt_succ_of_le ((Nat.le_maxPrimeFac hn hp hpn).trans hB)

lemma summable_smoothReciprocal (B : ℕ) : Summable (smoothReciprocal B) := by
  classical
  have hp : ∀ {p : ℕ}, p.Prime → ‖reciprocalNatHom p‖<1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖<1
    rw [norm_inv,Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have he := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (B+1)).2.summable
  have hs : Summable ((fun n : ℕ => (n : ℝ)⁻¹) ∘
      (Subtype.val : Nat.smoothNumbers (B+1) → ℕ)) := he
  have hi := summable_subtype_iff_indicator.mp hs
  convert hi using 1
  funext n
  unfold smoothReciprocal Set.indicator
  split_ifs <;> simp [one_div]

noncomputable def primeWinnerHarmonicTerm (p n : ℕ) : ℝ :=
  if primeWinner n=p then factorSign n/n else 0

noncomputable def primeLoserHarmonicTerm (p n : ℕ) : ℝ :=
  if primeLoser n=p then factorSign n/n else 0

noncomputable def rawPrimeWinnerHarmonic (p N : ℕ) : ℝ :=
  ∑ n ∈ range N, primeWinnerHarmonicTerm p n

noncomputable def rawPrimeLoserHarmonic (p N : ℕ) : ℝ :=
  ∑ n ∈ range N, primeLoserHarmonicTerm p n

lemma primeWinnerHarmonicTerm_norm_bound (p n : ℕ) :
    ‖primeWinnerHarmonicTerm p n‖≤smoothReciprocal p n := by
  by_cases hn : n=0
  · subst n
    simp only [primeWinnerHarmonicTerm,Nat.cast_zero,div_zero,ite_self,norm_zero]
    exact smoothReciprocal_nonneg p 0
  by_cases hw : primeWinner n=p
  · rw [primeWinnerHarmonicTerm,if_pos hw,norm_div,factorSign_norm,Real.norm_natCast,
      smoothReciprocal_of_maxPrimeFac_le p n hn (hw ▸ le_max_left _ _)]
  · rw [primeWinnerHarmonicTerm,if_neg hw,norm_zero]
    exact smoothReciprocal_nonneg p n

lemma primeLoserHarmonicTerm_norm_bound (p n : ℕ) :
    ‖primeLoserHarmonicTerm p n‖≤smoothReciprocal p n+2*smoothReciprocal p (n+1) := by
  by_cases hn : n=0
  · subst n
    simp only [primeLoserHarmonicTerm,Nat.cast_zero,div_zero,ite_self,norm_zero]
    have h1 := smoothReciprocal_nonneg p 0
    have h2 := smoothReciprocal_nonneg p (0+1)
    positivity
  by_cases hl : primeLoser n=p
  · rw [primeLoserHarmonicTerm,if_pos hl,norm_div,factorSign_norm,Real.norm_natCast]
    have hcase : Nat.maxPrimeFac n=p ∨ Nat.maxPrimeFac (n+1)=p := by
      unfold primeLoser at hl
      by_cases h : Nat.maxPrimeFac n≤Nat.maxPrimeFac (n+1)
      · exact Or.inl (by simpa only [min_eq_left h] using hl)
      · exact Or.inr (by simpa only [min_eq_right (not_le.mp h).le] using hl)
    rcases hcase with h|h
    · rw [smoothReciprocal_of_maxPrimeFac_le p n hn h.le]
      have hh := smoothReciprocal_nonneg p (n+1)
      linarith
    · rw [smoothReciprocal_of_maxPrimeFac_le p (n+1) (by omega) h.le]
      have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hh : (1 : ℝ)/n ≤ 2/(n+1 : ℝ) := by
        apply (div_le_div_iff₀ hn0 (by positivity)).mpr
        have hn1 : (1 : ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        linarith
      have hp0 := smoothReciprocal_nonneg p n
      push_cast
      simp only [mul_one_div]
      linarith
  · rw [primeLoserHarmonicTerm,if_neg hl,norm_zero]
    have h1 := smoothReciprocal_nonneg p n
    have h2 := smoothReciprocal_nonneg p (n+1)
    positivity

/-- Absolute summability for one fixed prime. This is not summability after
summing absolute values over all prime labels. -/
theorem summable_primeWinnerHarmonicTerm_norm (p : ℕ) :
    Summable (fun n => ‖primeWinnerHarmonicTerm p n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (primeWinnerHarmonicTerm_norm_bound p)
    (summable_smoothReciprocal p)

theorem summable_primeLoserHarmonicTerm_norm (p : ℕ) :
    Summable (fun n => ‖primeLoserHarmonicTerm p n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (primeLoserHarmonicTerm_norm_bound p)
    ((summable_smoothReciprocal p).add
      (((summable_nat_add_iff 1).mpr (summable_smoothReciprocal p)).mul_left 2))

noncomputable def primeWinnerHarmonicLimit (p : ℕ) : ℝ :=
  ∑' n, primeWinnerHarmonicTerm p n

noncomputable def primeLoserHarmonicLimit (p : ℕ) : ℝ :=
  ∑' n, primeLoserHarmonicTerm p n

theorem rawPrimeWinnerHarmonic_tendsto (p : ℕ) :
    Tendsto (rawPrimeWinnerHarmonic p) atTop (𝓝 (primeWinnerHarmonicLimit p)) :=
  (summable_primeWinnerHarmonicTerm_norm p).of_norm.hasSum.tendsto_sum_nat

theorem rawPrimeLoserHarmonic_tendsto (p : ℕ) :
    Tendsto (rawPrimeLoserHarmonic p) atTop (𝓝 (primeLoserHarmonicLimit p)) :=
  (summable_primeLoserHarmonicTerm_norm p).of_norm.hasSum.tendsto_sum_nat

#print axioms summable_primeWinnerHarmonicTerm_norm
#print axioms summable_primeLoserHarmonicTerm_norm
#print axioms rawPrimeWinnerHarmonic_tendsto
#print axioms rawPrimeLoserHarmonic_tendsto
end Erdos371
