import Submission.LosingProductComparison
import Submission.PrimeCurrentL2Convergence
import Submission.RawHarmonicTauberian

/-! The entire losing-product image has summable reciprocals. Thus even
constant fibre multiplicity does not permit replacing its pushforward by
uniform sampling of integers at the squared scale. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology

noncomputable def absoluteWinnerMass (p : ℕ) : ℝ :=
  ∑' n, ‖primeWinnerHarmonicTerm p n‖

lemma absoluteWinnerMass_nonneg (p : ℕ) : 0 ≤ absoluteWinnerMass p := tsum_nonneg (fun _ => norm_nonneg _)

lemma absoluteWinnerMass_rpow_bound (p : ℕ) :
    absoluteWinnerMass p ≤ primeCurrentBudgetConstant*(p : ℝ)^(-3/4 : ℝ) := by
  by_cases hp : p.Prime
  · have hm : absoluteWinnerMass p ≤
        ∑' n, (‖primeWinnerHarmonicTerm p n‖+‖primeLoserHarmonicTerm p n‖) := by
      exact Summable.tsum_le_tsum (fun n => le_add_of_nonneg_right (norm_nonneg _))
        (summable_primeWinnerHarmonicTerm_norm p)
        ((summable_primeWinnerHarmonicTerm_norm p).add (summable_primeLoserHarmonicTerm_norm p))
    exact (hm.trans (primeWinnerLoserHarmonic_abs_tsum_log_bound p hp)).trans
      (prime_current_log_budget_le_rpow p hp.pos)
  · have hz : absoluteWinnerMass p=0 := by
      simp only [absoluteWinnerMass,primeWinnerHarmonicTerm_zero_of_not_prime p _ hp,norm_zero,tsum_zero]
    rw [hz]
    exact mul_nonneg primeCurrentBudgetConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg p) _)

lemma summable_absoluteWinnerMass_sq : Summable (fun p : ℕ => (absoluteWinnerMass p)^2) := by
  have hs := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ)< -1)).mul_left
    (primeCurrentBudgetConstant^2)
  apply hs.of_norm_bounded
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (absoluteWinnerMass_nonneg p) (absoluteWinnerMass_rpow_bound p) 2
  simpa only [mul_pow,square_neg_three_quarters] using h

noncomputable def commonWinnerPairReciprocal (nm : ℕ × ℕ) : ℝ :=
  if primeWinner nm.1 = primeWinner nm.2 then (1/(nm.1 : ℝ))*(1/(nm.2 : ℝ)) else 0

lemma commonWinnerPairReciprocal_nonneg (nm : ℕ × ℕ) :
    0 ≤ commonWinnerPairReciprocal nm := by
  unfold commonWinnerPairReciprocal
  split_ifs <;> positivity

/-- Ordered pairs with a common winner have finite total product-reciprocal
mass. No sign cancellation is used. -/
theorem summable_commonWinnerPairReciprocal : Summable commonWinnerPairReciprocal := by
  let a (p n : ℕ) := ‖primeWinnerHarmonicTerm p n‖
  have hs (p : ℕ) : Summable (fun nm : ℕ × ℕ => a p nm.1*a p nm.2) :=
    (summable_primeWinnerHarmonicTerm_norm p).mul_of_nonneg
      (summable_primeWinnerHarmonicTerm_norm p) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hts (p : ℕ) : (∑' nm : ℕ × ℕ, a p nm.1*a p nm.2)=(absoluteWinnerMass p)^2 := by
    rw [← (summable_primeWinnerHarmonicTerm_norm p).tsum_mul_tsum
      (summable_primeWinnerHarmonicTerm_norm p) (hs p),sq]
    rfl
  have htotal : Summable (fun t : ℕ × (ℕ × ℕ) => a t.1 t.2.1*a t.1 t.2.2) := by
    apply (summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    refine ⟨hs, ?_⟩
    change Summable (fun p => ∑' nm : ℕ × ℕ, a p nm.1*a p nm.2)
    simpa only [hts] using summable_absoluteWinnerMass_sq
  have hcollapsed := htotal.prod_symm.prod
  apply hcollapsed.congr
  intro nm
  change (∑' p, a p nm.1*a p nm.2)=commonWinnerPairReciprocal nm
  rw [tsum_eq_single (primeWinner nm.1)]
  · simp only [a,primeWinnerHarmonicTerm_norm_eq,if_true,commonWinnerPairReciprocal]
    by_cases he : primeWinner nm.1=primeWinner nm.2
    · simp [he]
    · simp [he,Ne.symm he]
  · intro p hp
    have he : primeWinner nm.1≠p := Ne.symm hp
    simp only [a,primeWinnerHarmonicTerm_norm_eq,if_neg he,zero_div,zero_mul]

/-- No size balance or short-cofactor restriction is imposed on this image. -/
def losingProductOutputs : Set ℕ :=
  {r | ∃ n m : ℕ, 1 < n ∧ 1 < m ∧ primeWinner n=primeWinner m ∧ losingProductIndex n m=r}

lemma losingProductIndex_reciprocal_bound (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (hp : primeWinner n=primeWinner m) :
    (1 : ℝ)/losingProductIndex n m ≤ 2*((1/(n : ℝ))*(1/(m : ℝ))) := by
  have hs := losingProductIndex_structure n m hn hm hp
  have hln : n≤losingNumber n := by unfold losingNumber; split_ifs <;> omega
  have hlm : m≤losingNumber m := by unfold losingNumber; split_ifs <;> omega
  have hb := (comparison_numbers_bounds (losingProductIndex n m) hs.1).2.2.1
  rw [hs.2.1] at hb
  have hprod : n*m ≤ 2*losingProductIndex n m := by
    have hh := Nat.mul_le_mul hln hlm
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr0 : (0 : ℝ) < losingProductIndex n m := by exact_mod_cast (by omega : 0 < losingProductIndex n m)
  rw [show 2*((1/(n : ℝ))*(1/(m : ℝ)))=2/((n : ℝ)*m) by ring]
  apply (div_le_div_iff₀ hr0 (mul_pos hn0 hm0)).mpr
  simpa only [one_mul] using (show (n : ℝ)*m ≤ 2*(losingProductIndex n m : ℝ) by exact_mod_cast hprod)

/-- The output image is not just sparse in balanced windows: its full
reciprocal series converges. -/
theorem summable_losingProductOutputs_reciprocal :
    Summable (losingProductOutputs.indicator (fun r : ℕ => (1 : ℝ)/r)) := by
  classical
  choose n m hn hm hp hr using (fun r : losingProductOutputs => r.property)
  have hinj : Function.Injective (fun r : losingProductOutputs => (n r,m r)) := by
    intro r s he
    have he₁ : n r=n s := congrArg Prod.fst he
    have he₂ : m r=m s := congrArg Prod.snd he
    apply Subtype.ext
    rw [← hr r,← hr s,he₁,he₂]
  have hs := (summable_commonWinnerPairReciprocal.mul_left 2).comp_injective hinj
  apply summable_subtype_iff_indicator.mp
  apply hs.of_norm_bounded
  intro r
  change ‖(1 : ℝ)/(r : ℕ)‖ ≤ 2*commonWinnerPairReciprocal (n r,m r)
  rw [norm_div,norm_one,Real.norm_natCast,commonWinnerPairReciprocal,if_pos (hp r)]
  rw [← hr r]
  exact losingProductIndex_reciprocal_bound (n r) (m r) (hn r) (hm r) (hp r)

/-- This density-zero theorem is about the product image, not the set of
rising comparisons in the conjecture. -/
theorem losingProductOutputs_hasDensity_zero : losingProductOutputs.HasDensity 0 := by
  classical
  let f (n : ℕ) : ℝ := if n∈losingProductOutputs then 1 else 0
  have hs : Summable (fun n => f n/(n : ℝ)) := by
    simpa only [Set.indicator_apply,f,ite_div,zero_div] using summable_losingProductOutputs_reciprocal
  have ht := prefixMean_zero_of_rawHarmonicSum_tendsto f _ hs.hasSum.tendsto_sum_nat
  change {n | n∈losingProductOutputs}.HasDensity 0
  rw [density_iff_count]
  simpa only [prefixMean,f,sum_boole] using ht

#print axioms summable_absoluteWinnerMass_sq
#print axioms summable_commonWinnerPairReciprocal
#print axioms losingProductIndex_reciprocal_bound
#print axioms summable_losingProductOutputs_reciprocal
#print axioms losingProductOutputs_hasDensity_zero
end Erdos371
