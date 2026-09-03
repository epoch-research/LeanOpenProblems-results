import Submission.PrimeBlockExponential
import Submission.CountableBandDensity

/-!
Countably many nonnegative prime-score upper bounds can be imposed with
logarithmic rather than reciprocal error-budget costs. These are fixed-block,
one-sided sources; no cubic collision separation is asserted.
-/
namespace Erdos1206.PrimeBlockExponentialSource
open Finset PrimeBlockVariance PrimeBlockExponential
open scoped Classical

noncomputable def cumulant (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, (Real.exp (t*w p)-1-t*w p)/p

/-- Any positive summable budget with total below the source prefix density
allows all of the displayed one-sided inequalities simultaneously. -/
theorem upper_source_lowerDensity_pos (S : Set ℕ)
    (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    {δ C t : ℝ} (ht : 0 < t) (hpos : ∀ n ∈ S, 0 < n)
    (hpre : ∀ N : ℕ, δ*(N:ℝ) ≤ ((S ∩ Set.Iio N).ncard:ℝ)+C)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w j p)
    (hc : ∀ j, 0 < c j) (hcs : Summable c) (hcost : ∑' j, c j < δ) :
    0 < ({n : ℕ | n ∈ S ∧ ∀ j,
      t*(primeSum (P j) (w j) n-mean (P j) (w j)) ≤
        cumulant (P j) (w j) t-Real.log (c j)} : Set ℕ).lowerDensity := by
  let f : ℕ → ℕ → ℝ := fun j n => Real.exp
    ((t*(primeSum (P j) (w j) n-mean (P j) (w j))-
      cumulant (P j) (w j) t+Real.log (c j))/2)
  have hmoment (j N : ℕ) : (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j := by
    have he (n : ℕ) : (f j n)^2 =
        Real.exp (Real.log (c j)-cumulant (P j) (w j) t)*
          Real.exp (t*(primeSum (P j) (w j) n-mean (P j) (w j))) := by
      dsimp only [f]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      norm_num
      ring
    simp_rw [he]
    rw [←mul_sum]
    have hh := mul_le_mul_of_nonneg_left
      (centered_exponential_moment_le (P j) (hP j) (w j) (hw j) ht.le N)
      (Real.exp_pos (Real.log (c j)-cumulant (P j) (w j) t)).le
    have hec : Real.exp (Real.log (c j)-cumulant (P j) (w j) t)*
        ((N:ℝ)*Real.exp (cumulant (P j) (w j) t))=(N:ℝ)*c j := by
      rw [mul_left_comm,←Real.exp_add,sub_add_cancel,Real.exp_log (hc j)]
    exact hh.trans_eq hec
  have hd := CountableBandDensity.lowerDensity_pos_of_prefix S f c hpos hpre
    (fun j => (hc j).le) hcs hmoment hcost
  have heq : {n : ℕ | n ∈ S ∧ ∀ j, |f j n| ≤ 1} =
      {n : ℕ | n ∈ S ∧ ∀ j,
        t*(primeSum (P j) (w j) n-mean (P j) (w j)) ≤
          cumulant (P j) (w j) t-Real.log (c j)} := by
    ext n
    simp only [Set.mem_setOf_eq]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro j
    rw [abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
    constructor <;> intro h <;> linarith
  rwa [heq] at hd

/-- A concrete positive-density refinement of any positive-density set of
positive integers. The parameter K absorbs the normalization of an arbitrary
positive summable error schedule. -/
theorem exists_upper_source (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n) (b : ℕ → ℝ)
    (hb : ∀ j, 0 < b j) (hbs : Summable b) :
    ∃ K : ℝ, ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (t : ℝ), 0 < t →
      (∀ j p, p ∈ P j → p.Prime) →
      (∀ j p, p ∈ P j → 0 ≤ w j p) →
      ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j,
          t*(primeSum (P j) (w j) n-mean (P j) (w j)) ≤
            cumulant (P j) (w j) t+K-Real.log (b j) := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  let B : ℝ := ∑' j, b j
  have hB : 0 < B := (hbs.tsum_pos (fun j => (hb j).le) 0 (hb 0))
  let a : ℝ := δ/(2*B)
  have ha : 0 < a := by dsimp [a]; positivity
  let c : ℕ → ℝ := fun j => a*b j
  have hc : ∀ j, 0 < c j := fun j => mul_pos ha (hb j)
  have hcs : Summable c := hbs.mul_left a
  have hct : ∑' j,c j=δ/2 := by
    rw [tsum_mul_left]
    change a*B=δ/2
    dsimp only [a]
    field_simp [hB.ne']
  refine ⟨-Real.log a,fun P w t ht hP hw => ?_⟩
  let A : Set ℕ := {n | n ∈ S ∧ ∀ j,
    t*(primeSum (P j) (w j) n-mean (P j) (w j)) ≤
      cumulant (P j) (w j) t-Real.log (c j)}
  have hden : 0 < A.lowerDensity := upper_source_lowerDensity_pos S P w c ht hpos hpre
    hP hw hc hcs (by rw [hct]; linarith)
  refine ⟨A,fun _ hn => hn.1,hden,fun n hn j => ?_⟩
  have hh := hn.2 j
  dsimp only [c] at hh
  rw [Real.log_mul ha.ne' (hb j).ne'] at hh
  linarith

/-- The inverse-square schedule makes the family-index loss only logarithmic.
The same K works for every prime-block sequence, weight sequence, and t>0. -/
theorem exists_logarithmic_upper_source (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∃ K : ℝ, ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (t : ℝ), 0 < t →
      (∀ j p, p ∈ P j → p.Prime) →
      (∀ j p, p ∈ P j → 0 ≤ w j p) →
      ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j,
          t*(primeSum (P j) (w j) n-mean (P j) (w j)) ≤
            cumulant (P j) (w j) t+K+2*Real.log ((j:ℝ)+1) := by
  let b : ℕ → ℝ := fun j => (((j:ℝ)+1)^2)⁻¹
  have hb : ∀ j, 0 < b j := fun j => by dsimp [b]; positivity
  have hbs : Summable b := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2:ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  obtain ⟨K,hK⟩ := exists_upper_source S hS hpos b hb hbs
  refine ⟨K,fun P w t ht hP hw => ?_⟩
  obtain ⟨A,hAS,hAd,hA⟩ := hK P w t ht hP hw
  refine ⟨A,hAS,hAd,fun n hn j => ?_⟩
  have hh := hA n hn j
  simpa only [b,Real.log_inv,Real.log_pow,Nat.cast_ofNat,sub_neg_eq_add] using hh


#print axioms upper_source_lowerDensity_pos
#print axioms exists_upper_source
#print axioms exists_logarithmic_upper_source
end Erdos1206.PrimeBlockExponentialSource
