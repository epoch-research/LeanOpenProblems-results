import Submission.SharpHarmonicDilationBudget
import Submission.PrimeWinnerHarmonicFlux

/-! Uniform per-prime absolute harmonic incidence budgets. The factor 1/p
is retained by dividing integers with largest prime factor p by p. These
bounds do not prove summability of the unweighted signed prime currents. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def primeLabelReciprocal (p n : ℕ) : ℝ :=
  if Nat.maxPrimeFac n=p then 1/n else 0

lemma primeLabelReciprocal_nonneg (p n : ℕ) : 0≤primeLabelReciprocal p n := by
  unfold primeLabelReciprocal
  split_ifs <;> positivity

lemma primeLabelReciprocal_le_smooth (p n : ℕ) :
    primeLabelReciprocal p n ≤ smoothReciprocal p n := by
  by_cases hn : n=0
  · subst n
    simp only [primeLabelReciprocal,Nat.cast_zero,div_zero,ite_self]
    exact smoothReciprocal_nonneg p 0
  by_cases hp : Nat.maxPrimeFac n=p
  · rw [primeLabelReciprocal,if_pos hp,smoothReciprocal_of_maxPrimeFac_le p n hn hp.le]
  · rw [primeLabelReciprocal,if_neg hp]
    exact smoothReciprocal_nonneg p n

lemma primeLabelReciprocal_summable (p : ℕ) : Summable (primeLabelReciprocal p) :=
  Summable.of_nonneg_of_le (primeLabelReciprocal_nonneg p)
    (primeLabelReciprocal_le_smooth p) (summable_smoothReciprocal p)

lemma primeLabelReciprocal_mul_prime (p n : ℕ) (hp : p.Prime) :
    primeLabelReciprocal p (p*n) = (1/(p : ℝ))*smoothReciprocal p n := by
  by_cases hn : n=0
  · subst n
    simp [primeLabelReciprocal,smoothReciprocal]
  have hm : n ∈ (p+1).smoothNumbers ↔ Nat.maxPrimeFac n≤p := by
    rw [mem_smoothNumbers_iff_maxPrimeFac_lt _ _ (by have := hp.pos; omega : 1<p+1)]
    simp [hn]
  simp only [primeLabelReciprocal,Nat.maxPrimeFac_mul hp.ne_zero hn,hp.maxPrimeFac_eq_self,
    max_eq_left_iff,smoothReciprocal,hm,Nat.cast_mul]
  split_ifs <;> ring

/-- Exact reciprocal mass of all positive integers with largest prime p. -/
theorem primeLabelReciprocal_tsum (p : ℕ) (hp : p.Prime) :
    (∑' n, primeLabelReciprocal p n) = (1/(p : ℝ)) *
      ∏ q ∈ (p+1).primesBelow, (1-(q : ℝ)⁻¹)⁻¹ := by
  have hinj : Function.Injective (fun n : ℕ => p*n) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hsupp : Function.support (primeLabelReciprocal p) ⊆ Set.range (fun n : ℕ => p*n) := by
    intro n hn
    have he : Nat.maxPrimeFac n=p := by
      by_contra h
      exact hn (by simp [primeLabelReciprocal,h])
    have hpn : p∣n := he ▸ Nat.maxPrimeFac_dvd
    exact ⟨n/p,Nat.mul_div_cancel' hpn⟩
  rw [← hinj.tsum_eq hsupp]
  simp_rw [primeLabelReciprocal_mul_prime p _ hp]
  rw [tsum_mul_left,(smoothReciprocal_hasSum p).tsum_eq]

lemma primeWinnerLoser_label_incidence (p n : ℕ) :
    (if primeWinner n=p then (1 : ℝ) else 0) +
      (if primeLoser n=p then 1 else 0) =
        primeLabelIndicator p n+primeLabelIndicator p (n+1) := by
  unfold primeWinner primeLoser primeLabelIndicator
  by_cases h : Nat.maxPrimeFac n≤Nat.maxPrimeFac (n+1)
  · rw [max_eq_right h,min_eq_left h,add_comm]
  · rw [max_eq_left (not_le.mp h).le,min_eq_right (not_le.mp h).le]

lemma primeWinnerHarmonicTerm_norm_eq (p n : ℕ) :
    ‖primeWinnerHarmonicTerm p n‖ = (if primeWinner n=p then (1 : ℝ) else 0)/n := by
  unfold primeWinnerHarmonicTerm
  split_ifs <;> simp only [norm_div,factorSign_norm,Real.norm_natCast,norm_zero,zero_div]

lemma primeLoserHarmonicTerm_norm_eq (p n : ℕ) :
    ‖primeLoserHarmonicTerm p n‖ = (if primeLoser n=p then (1 : ℝ) else 0)/n := by
  unfold primeLoserHarmonicTerm
  split_ifs <;> simp only [norm_div,factorSign_norm,Real.norm_natCast,norm_zero,zero_div]

/-- The two currents together charge the two edges incident to a p-labelled
integer. The successor shift costs at most a factor two. -/
lemma primeWinnerLoserHarmonicTerm_norm_bound (p n : ℕ) :
    ‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖ ≤
      primeLabelReciprocal p n+2*primeLabelReciprocal p (n+1) := by
  rw [primeWinnerHarmonicTerm_norm_eq,primeLoserHarmonicTerm_norm_eq,
    ← add_div,primeWinnerLoser_label_incidence,add_div]
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,div_zero,zero_add]
    exact add_nonneg (primeLabelReciprocal_nonneg p 0)
      (mul_nonneg (by norm_num) (primeLabelReciprocal_nonneg p 1))
  have he (m : ℕ) : primeLabelIndicator p m/(m : ℝ)=primeLabelReciprocal p m := by
    simp only [primeLabelIndicator,primeLabelReciprocal,ite_div,zero_div]
  rw [he]
  apply add_le_add_right
  by_cases hp : Nat.maxPrimeFac (n+1)=p
  · simp only [primeLabelIndicator,primeLabelReciprocal,hp,if_true]
    have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    push_cast
    rw [mul_one_div]
    apply (div_le_div_iff₀ hn0 (by positivity)).mpr
    linarith
  · simp [primeLabelIndicator,primeLabelReciprocal,hp]

/-- A uniform absolute incidence bound, retaining the 1/p gain. -/
theorem primeWinnerLoserHarmonic_abs_tsum_bound (p : ℕ) (hp : p.Prime) :
    (∑' n, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖)) ≤
      (3/(p : ℝ)) * ∏ q ∈ (p+1).primesBelow, (1-(q : ℝ)⁻¹)⁻¹ := by
  have hs := primeLabelReciprocal_summable p
  have hshift := (summable_nat_add_iff 1).mpr hs
  have he : (∑' n, primeLabelReciprocal p (n+1))=∑' n, primeLabelReciprocal p n := by
    have hh := hs.tsum_eq_zero_add
    have hz : primeLabelReciprocal p 0=0 := by simp [primeLabelReciprocal]
    rw [hz,zero_add] at hh
    exact hh.symm
  have h := Summable.tsum_le_tsum (primeWinnerLoserHarmonicTerm_norm_bound p)
    ((summable_primeWinnerHarmonicTerm_norm p).add (summable_primeLoserHarmonicTerm_norm p))
    (hs.add (hshift.mul_left 2))
  rw [hs.tsum_add (hshift.mul_left 2),hshift.tsum_mul_left,he,primeLabelReciprocal_tsum p hp] at h
  exact h.trans_eq (by ring)

theorem primeWinnerLoserHarmonic_abs_tsum_log_bound (p : ℕ) (hp : p.Prime) :
    (∑' n, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖)) ≤
      3*Real.exp 4*(1+Real.log (p+1 : ℝ)/Real.log 2)/p := by
  have he := primeEulerProduct_le_log (p+1) (by have := hp.two_le; omega)
  push_cast at he
  apply (primeWinnerLoserHarmonic_abs_tsum_bound p hp).trans
  have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ)≤3/p)
  exact h.trans_eq (by ring)

lemma primeWinnerHarmonicLimit_norm_le_incidence (p : ℕ) :
    ‖primeWinnerHarmonicLimit p‖ ≤
      ∑' n, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖) := by
  apply (norm_tsum_le_tsum_norm (summable_primeWinnerHarmonicTerm_norm p)).trans
  exact Summable.tsum_le_tsum (fun n => le_add_of_nonneg_right (norm_nonneg _))
    (summable_primeWinnerHarmonicTerm_norm p)
    ((summable_primeWinnerHarmonicTerm_norm p).add (summable_primeLoserHarmonicTerm_norm p))

lemma rawPrimeWinnerHarmonic_norm_le_incidence (p N : ℕ) :
    ‖rawPrimeWinnerHarmonic p N‖ ≤
      ∑' n, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖) := by
  calc
    _ ≤ ∑ n ∈ range N, ‖primeWinnerHarmonicTerm p n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖) :=
      sum_le_sum (fun n _ => le_add_of_nonneg_right (norm_nonneg _))
    _ ≤ _ := ((summable_primeWinnerHarmonicTerm_norm p).add
      (summable_primeLoserHarmonicTerm_norm p)).sum_le_tsum _ (fun _ _ => by positivity)

#print axioms primeLabelReciprocal_tsum
#print axioms primeWinnerLoserHarmonic_abs_tsum_log_bound
end Erdos371
