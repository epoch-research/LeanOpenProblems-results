import Submission.BalancedRepVarianceExplore
import Submission.HarmonicRefreshExplore
import Submission.PrefixBalancedUpperLimitExplore

/-! Partial refresh with a retained finite prefix-discrepancy invariant.
The concentration criterion still does not yield a vanishing-error iteration. -/
namespace Erdos66BalancedHarmonicRefresh
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66RefreshAlgebra
  Erdos66RepVariance Erdos66HarmonicRefresh Erdos66Rounding Erdos66Fractional
  Erdos66Generating Erdos66BalancedRepVariance Erdos66OrderedPipagePrefix
  Erdos66PrefixBalancedUpperLimit AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000

lemma prefix_refresh_invariant (L : ℕ) (θ D : ℝ) (A : Set ℕ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hD : 0 ≤ D)
    (hprefix : ∀ k, |prefixSum (roundingError A) k| ≤ D)
    (ω : Fin (L+1) → Bool)
    (hbr : Brackets (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val))
      (fun i ↦ bit (ω i))) (k : ℕ) (hk : k ≤ L+1) :
    |(∑ i∈Finset.range k, indicator (selected L ω) i)-(∑ i∈Finset.range k, profile i)| ≤
      1+(1-θ)*D := by
  let q : ℕ → ℝ := blend θ (fun i ↦ decide (i∈A)) profile
  have hb := finite_prefix_bound L q ω hbr k hk
  have hpref : |∑ i∈Finset.range k, roundingError A i| ≤ D := by
    cases k with
    | zero => simpa using hD
    | succ k => exact hprefix k
  have he : (∑ i∈Finset.range k, q i)-(∑ i∈Finset.range k, profile i)=
      (1-θ)*(∑ i∈Finset.range k, roundingError A i) := by
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q,blend,roundingError]
    rw [bit_decide_indicator]
    ring
  have hh := abs_sub_le (∑ i∈Finset.range k, indicator (selected L ω) i)
    (∑ i∈Finset.range k, q i) (∑ i∈Finset.range k, profile i)
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ.2)] at hh
  have hm := mul_le_mul_of_nonneg_left hpref (sub_nonneg.mpr hθ.2)
  linarith

/-- The finite refresh retains prefix discrepancy at most 1+(1-theta)D.
Its representation error has only an additional additive two from dependent
rounding. This does not remove the displayed tail-budget hypothesis. -/
theorem exists_balanced_harmonic_refresh (L : ℕ) (θ D : ℝ) (A : Set ℕ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hD : 0 ≤ D)
    (hprefix : ∀ k, |prefixSum (roundingError A) k| ≤ D)
    (S : Finset ℕ) (hS : ∀ n∈S, n ≤ L) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1)
    (hV : ∀ n∈S, θ*((2-θ)*((sumRep A n:ℝ)+(harmonic (n+1):ℝ))+4*(1-θ)*D+1) ≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ B : Set ℕ, B.Finite ∧ (∀ n∈B, n ≤ L) ∧
      (∀ k ≤ L+1, |(∑ i∈Finset.range k, indicator B i)-(∑ i∈Finset.range k, profile i)| ≤
        1+(1-θ)*D) ∧
      ∀ n∈S, |(sumRep B n:ℝ)-(harmonic (n+1):ℝ)|<
        (1-θ)^2*|(sumRep A n:ℝ)-(harmonic (n+1):ℝ)|+4*θ*(1-θ)*D+θ+ε*V n+2 := by
  let p : Fin (L+1) → ℝ := blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    blend_bounds θ _ _ hθ (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)
  obtain ⟨ω,hbr,hω⟩ := exists_prefix_balanced_variance_bound L p hp S V ε hε hε1
    (fun n hn ↦ (harmonic_refresh_variance L n θ D A (hS n hn) hθ hD hprefix).trans (hV n hn)) hsmall
  refine ⟨selected L ω,selected_finite L ω,?_,
    fun k hk ↦ prefix_refresh_invariant L θ D A hθ hD hprefix ω hbr k hk,?_⟩
  · rintro n ⟨i,rfl,hi⟩
    exact Nat.le_of_lt_succ i.isLt
  · intro n hn
    have hb := refresh_mean_contraction L n θ D A (hS n hn) hθ hD hprefix
    have he : (sumRep (selected L ω) n:ℝ)-(harmonic (n+1):ℝ)=
        ((sumRep (selected L ω) n:ℝ)-repMean L n p)+
        (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ)))+
        (1-θ)^2*((sumRep A n:ℝ)-(harmonic (n+1):ℝ)) := by ring
    rw [he]
    have h₁ := abs_add_le ((sumRep (selected L ω) n:ℝ)-repMean L n p)
      (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ)))
    have h₂ := abs_add_le
      (((sumRep (selected L ω) n:ℝ)-repMean L n p)+
        (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ))))
      ((1-θ)^2*((sumRep A n:ℝ)-(harmonic (n+1):ℝ)))
    rw [abs_mul,abs_of_nonneg (sq_nonneg (1-θ))] at h₂
    change |repMean L n p-_| ≤ _ at hb
    linarith [hω n hn]

end Erdos66BalancedHarmonicRefresh
