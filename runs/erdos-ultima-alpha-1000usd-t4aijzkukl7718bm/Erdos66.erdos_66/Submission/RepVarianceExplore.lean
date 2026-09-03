import Submission.BernoulliVarianceExplore
import Submission.FiniteRepBernoulliExplore

/-! Natural representation counts with a variance-sensitive bound. -/
namespace Erdos66RepVariance
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66BernoulliConcentration
  Erdos66BernoulliVariance AdditiveCombinatorics
open scoped Classical

noncomputable def repVarianceProxy (L n : ℕ) (p : Fin (L+1) → ℝ) : ℝ :=
  ∑ a∈halfPairs L n, pairWeight a*(∏ i∈pairCoords a, p i)*(1-∏ i∈pairCoords a, p i)

lemma repVarianceProxy_nonneg (L n : ℕ) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : 0 ≤ repVarianceProxy L n p := by
  apply Finset.sum_nonneg
  intro a ha
  have hu := product_probability_bounds p hp (pairCoords a)
  exact mul_nonneg (mul_nonneg (pairWeight_bounds a).1 hu.1) (sub_nonneg.mpr hu.2)

lemma repVarianceProxy_le_mean (L n : ℕ) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : repVarianceProxy L n p ≤ repMean L n p := by
  apply Finset.sum_le_sum
  intro a ha
  have hu := product_probability_bounds p hp (pairCoords a)
  nlinarith [mul_nonneg (pairWeight_bounds a).1 (sq_nonneg (∏ i∈pairCoords a, p i))]

lemma rep_variance_mgf (L n : ℕ) (p : Fin (L+1) → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*((sumRep (selected L ω) n:ℝ)-repMean L n p))) ≤
      Real.exp (2*t^2*repVarianceProxy L n p) := by
  simp_rw [selected_rep]
  exact centered_mgf_variance p hp (halfPairs L n) pairCoords (pairCoords_disjoint L n)
    pairWeight (fun a _ ↦ pairWeight_bounds a) t ht

theorem exists_rep_variance_bound (L : ℕ) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ℕ) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1) (hV : ∀ n∈S, repVarianceProxy L n p ≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ ω, 0<weight p ω ∧ ∀ n∈S, |(sumRep (selected L ω) n:ℝ)-repMean L n p|<ε*V n := by
  apply exists_summed_variance_bound p hp S
    (fun n ω ↦ (sumRep (selected L ω) n:ℝ)) (fun n ↦ repMean L n p) V ε hε hε1 ?_ hsmall
  intro n hn t ht
  exact (rep_variance_mgf L n p hp t ht).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hV n hn) (by positivity)))

end Erdos66RepVariance
