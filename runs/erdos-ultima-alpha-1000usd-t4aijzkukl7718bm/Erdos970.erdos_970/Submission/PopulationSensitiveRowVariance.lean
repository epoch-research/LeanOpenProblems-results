import Submission.CoreFilteredSelberg

/-! Pointwise and weighted row-variance bounds that retain the actual core
population. These are not uniform small-variance estimates at critical scale,
and they do not assert a positive lower count for the initial prime core. -/
namespace Erdos970.GapAverages
open Finset Real Erdos970.Resampling

/-- A deterministic cap controls variance in terms of the actual population,
not its mean over core phases. -/
theorem rowConditionalVariance_le_cap_count (P : Finset ℕ) (m p : ℕ)
    (hp : 0 < p) (r : Phase P) (B : ℝ)
    (hcap : ∀ a : Fin p, rowCount P m p a r ≤ B) :
    rowConditionalVariance P m p r ≤
      B * (intervalCount P m r / p) - (intervalCount P m r / p)^2 := by
  have hs := residueMean_mono p (fun a : Fin p =>
    mul_le_mul_of_nonneg_right (hcap a) (rowCount_nonneg' P m p a r))
  simp only [← sq] at hs
  rw [residueMean_mul, rowCount_mean P m p hp r] at hs
  rw [rowConditionalVariance, ← rowCount_mean P m p hp r,
    residueMean_centered_square p hp, rowCount_mean P m p hp r]
  exact sub_le_sub_right hs _

/-- Nonnegative weights are arbitrary, so this remains valid after conditioning
or exponential tilting. The second weighted population moment is retained. -/
theorem weighted_rowConditionalVariance_le_cap_count (P : Finset ℕ)
    (m p : ℕ) (hp : 0 < p) (B : ℝ)
    (hcap : ∀ (r : Phase P) (a : Fin p), rowCount P m p a r ≤ B)
    (w : Phase P → ℝ) (hw : ∀ r, 0 ≤ w r) :
    phaseMean P (fun r => w r * rowConditionalVariance P m p r) ≤
      (B / p) * phaseMean P (fun r => w r * intervalCount P m r) -
        phaseMean P (fun r => w r * intervalCount P m r ^ 2) / (p : ℝ)^2 := by
  have hh := phaseMean_mono P (fun r => mul_le_mul_of_nonneg_left
    (rowConditionalVariance_le_cap_count P m p hp r B (hcap r)) (hw r))
  have he (r : Phase P) :
      w r * (B * (intervalCount P m r / p) - (intervalCount P m r / p)^2) =
      (B / p) * (w r * intervalCount P m r) -
        (w r * intervalCount P m r ^ 2) / (p : ℝ)^2 := by ring
  simp_rw [he] at hh
  rwa [phaseMean_sub, phaseMean_mul, phaseMean_div] at hh

/-- The Gibbs specialization uses the same core phase on both sides. In
particular no unweighted variance has been put inside an exponential. -/
theorem gibbs_rowConditionalVariance_le_cap_count (P : Finset ℕ)
    (m p : ℕ) (hp : 0 < p) (B t : ℝ)
    (hcap : ∀ (r : Phase P) (a : Fin p), rowCount P m p a r ≤ B) :
    phaseMean P (fun r => exp (-t * intervalCount P m r) *
      rowConditionalVariance P m p r) ≤
      (B / p) * phaseMean P (fun r => exp (-t * intervalCount P m r) *
        intervalCount P m r) -
      phaseMean P (fun r => exp (-t * intervalCount P m r) *
        intervalCount P m r ^ 2) / (p : ℝ)^2 :=
  weighted_rowConditionalVariance_le_cap_count P m p hp B hcap _
    (fun _ => (exp_pos _).le)

/-- The available upper sieve supplies an unconditional cap, including both
its rounding term and its square source cost. -/
theorem rowConditionalVariance_le_sharp_log_count (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (m p R : ℕ) (hp : 0 < p)
    (hc : ∀ q ∈ Q, p.Coprime q) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q) (r : Phase Q) :
    rowConditionalVariance Q m p r ≤
      (((m : ℝ)/p + 1)/log (R+1) + (exp 2*R/log (R+1))^2) *
        (intervalCount Q m r / p) - (intervalCount Q m r / p)^2 :=
  rowConditionalVariance_le_cap_count Q m p hp r _
    (fun a => rowCount_le_sharp_log_real Q hQ m p R hp hc hR hfull a r)

/-- The same fully charged sieve bound under arbitrary exponential tilt. -/
theorem gibbs_rowConditionalVariance_le_sharp_log_count (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (m p R : ℕ) (hp : 0 < p)
    (hc : ∀ q ∈ Q, p.Coprime q) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q) (t : ℝ) :
    phaseMean Q (fun r => exp (-t * intervalCount Q m r) *
      rowConditionalVariance Q m p r) ≤
      ((((m : ℝ)/p + 1)/log (R+1) + (exp 2*R/log (R+1))^2) / p) *
        phaseMean Q (fun r => exp (-t * intervalCount Q m r) * intervalCount Q m r) -
      phaseMean Q (fun r => exp (-t * intervalCount Q m r) *
        intervalCount Q m r ^ 2) / (p : ℝ)^2 :=
  gibbs_rowConditionalVariance_le_cap_count Q m p hp _ t
    (fun r a => rowCount_le_sharp_log_real Q hQ m p R hp hc hR hfull a r)

#print axioms rowConditionalVariance_le_cap_count
#print axioms weighted_rowConditionalVariance_le_cap_count
#print axioms gibbs_rowConditionalVariance_le_cap_count
#print axioms rowConditionalVariance_le_sharp_log_count
#print axioms gibbs_rowConditionalVariance_le_sharp_log_count
end Erdos970.GapAverages
