import Mathlib
import Submission.OccupancyBounds

/-!
# An occupancy limit criterion from fixed binomial moments

If each positive-order binomial moment, divided by an eventually positive scale,
converges to `1 / r!`, the occupied cardinality divided by that scale converges to
`1 - 1 / Real.exp 1`. The index filter is arbitrary. At each Bonferroni order we
use only finitely many moment limits; no uniformity in the order is assumed.

The factorial-residue specialization below is an implication, not an assertion
of the required moment estimates. Its first moment is exactly `p - 1`, and its
normalized first moment converges to one even along all natural numbers. The
estimates for every fixed order at least two remain hypotheses.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace OccupancyBounds

/-- The limiting Bonferroni polynomial when the normalized moments are `1 / r!`. -/
def exponentialBonferroni (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, (-1 : ℝ) ^ r * (1 / ((r + 1).factorial : ℝ))

/-- Removing the constant term from the exponential series at `-1`, and negating. -/
theorem hasSum_exponentialBonferroni :
    HasSum (fun r : ℕ => (-1 : ℝ) ^ r * (1 / ((r + 1).factorial : ℝ)))
      (1 - 1 / Real.exp 1) := by
  have hexp : HasSum (fun r : ℕ => (-1 : ℝ) ^ r / (r.factorial : ℝ))
      (Real.exp (-1)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  have htail := ((hasSum_nat_add_iff' 1).2 hexp).neg
  simpa [pow_succ, div_eq_mul_inv, Real.exp_neg] using htail

/-- All truncations of the limiting alternating series converge to the stated constant. -/
theorem tendsto_exponentialBonferroni :
    Tendsto exponentialBonferroni atTop (𝓝 (1 - 1 / Real.exp 1)) :=
  hasSum_exponentialBonferroni.tendsto_sum_nat

section General

variable {ι β : Type*} {l : Filter ι}
variable (t : ι → Finset β) (ν : ι → β → ℕ) (w : ι → ℝ)

/-- Each fixed normalized Bonferroni sum has the corresponding finite-sum limit.
No sign or nonvanishing condition on the scale is needed for this step. -/
theorem tendsto_bonferroniSum_div
    (hmoment : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun i => (binomialMoment (t i) (ν i) r : ℝ) / w i)
        l (𝓝 (1 / (r.factorial : ℝ)))) (k : ℕ) :
    Tendsto (fun i => bonferroniSum (t i) (ν i) k / w i)
      l (𝓝 (exponentialBonferroni k)) := by
  simp only [bonferroniSum, exponentialBonferroni, Finset.sum_div, mul_div_assoc]
  exact tendsto_finset_sum _ fun r _ =>
    tendsto_const_nhds.mul (hmoment (r + 1) (by omega))

/-- Fixed-order moment convergence implies convergence of the normalized support.

The filter may be arbitrary (in particular, any nontrivial filter). Eventual
positivity suffices; no growth assumption on `w`, uniformity in the moment order,
or bound on the occupancies is required. -/
theorem tendsto_occupied_div_of_binomialMoments
    (hw : ∀ᶠ i in l, 0 < w i)
    (hmoment : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun i => (binomialMoment (t i) (ν i) r : ℝ) / w i)
        l (𝓝 (1 / (r.factorial : ℝ)))) :
    Tendsto (fun i => (occupied (t i) (ν i) : ℝ) / w i)
      l (𝓝 (1 - 1 / Real.exp 1)) := by
  have heven : Tendsto (fun m : ℕ => exponentialBonferroni (2 * m))
      atTop (𝓝 (1 - 1 / Real.exp 1)) :=
    tendsto_exponentialBonferroni.comp
      (tendsto_atTop_mono (fun m : ℕ => by dsimp only [id]; omega) tendsto_id)
  have hodd : Tendsto (fun m : ℕ => exponentialBonferroni (2 * m + 1))
      atTop (𝓝 (1 - 1 / Real.exp 1)) :=
    tendsto_exponentialBonferroni.comp
      (tendsto_atTop_mono (fun m : ℕ => by dsimp only [id]; omega) tendsto_id)
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := (heven.eventually (lt_mem_nhds ha)).exists
    have hfinite := (tendsto_bonferroniSum_div t ν w hmoment (2 * m)).eventually
      (lt_mem_nhds hm)
    filter_upwards [hw, hfinite] with i hwi hi
    exact hi.trans_le (div_le_div_of_nonneg_right
      (bonferroni_even_le_occupied (t i) (ν i) m) hwi.le)
  · intro a ha
    obtain ⟨m, hm⟩ := (hodd.eventually (gt_mem_nhds ha)).exists
    have hfinite := (tendsto_bonferroniSum_div t ν w hmoment (2 * m + 1)).eventually
      (gt_mem_nhds hm)
    filter_upwards [hw, hfinite] with i hwi hi
    exact (div_le_div_of_nonneg_right
      (occupied_le_bonferroni_odd (t i) (ν i) m) hwi.le).trans_lt hi

end General

namespace FactorialResidues

/-- The source indices are exactly `1 ≤ k < p`. -/
def source (p : ℕ) : Finset ℕ := Finset.Ico 1 p

/-- The factorial residue map, with values represented by natural numbers. -/
def residue (p k : ℕ) : ℕ := k.factorial % p

/-- The canonical finite target set: the image of the factorial residue map. -/
def targets (p : ℕ) : Finset ℕ := (source p).image (residue p)

/-- Occupancy of a residue, counting only indices in the finite source. -/
def occupancy (p : ℕ) : ℕ → ℕ := fiberCard (source p) (residue p)

/-- The unnormalized factorial-residue binomial moment. -/
def moment (p r : ℕ) : ℕ := binomialMoment (targets p) (occupancy p) r

@[simp]
theorem occupied_eq_card_targets (p : ℕ) :
    occupied (targets p) (occupancy p) = (targets p).card := by
  exact occupied_fiberCard_image (source p) (residue p)

/-- The first moment is known exactly, without a primality assumption. -/
@[simp]
theorem moment_one (p : ℕ) : moment p 1 = p - 1 := by
  simp [moment, targets, occupancy, source, Nat.card_Ico]

/-- Natural numbers tending to infinity while restricted to primes. -/
def primeFilter : Filter ℕ := atTop ⊓ 𝓟 {p : ℕ | p.Prime}

/-- The prime filter is nontrivial, by the infinitude of primes. -/
instance primeFilter_neBot : NeBot primeFilter := by
  change NeBot (atTop ⊓ 𝓟 {p : ℕ | p.Prime})
  rw [← frequently_iff_neBot, frequently_atTop]
  exact Nat.exists_infinite_primes

theorem primeFilter_le_atTop : primeFilter ≤ atTop := inf_le_left

/-- The normalization by `p` is eventually positive on the prime filter. -/
theorem eventually_pos_primeFilter : ∀ᶠ (p : ℕ) in primeFilter, 0 < (p : ℝ) := by
  filter_upwards [(eventually_ge_atTop 1).filter_mono primeFilter_le_atTop] with p hp
  exact_mod_cast (show 0 < p by omega)

/-- In fact, the normalized first moment converges along all natural numbers. -/
theorem tendsto_moment_one_atTop :
    Tendsto (fun p : ℕ => (moment p 1 : ℝ) / (p : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun p : ℕ => (1 : ℝ) - 1 / (p : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  simp [moment_one, Nat.cast_sub hp, sub_div, hp0]

/-- The required first-moment asymptotic on the nontrivial prime filter. -/
theorem tendsto_moment_one :
    Tendsto (fun p : ℕ => (moment p 1 : ℝ) / (p : ℝ)) primeFilter (𝓝 1) :=
  tendsto_moment_one_atTop.mono_left primeFilter_le_atTop

/-- Conditional factorial-residue support limit: no moment estimate is asserted here. -/
theorem tendsto_card_targets_div_of_moments
    (hmoment : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun p : ℕ => (moment p r : ℝ) / (p : ℝ))
        primeFilter (𝓝 (1 / (r.factorial : ℝ)))) :
    Tendsto (fun p : ℕ => ((targets p).card : ℝ) / (p : ℝ))
      primeFilter (𝓝 (1 - 1 / Real.exp 1)) := by
  simpa only [occupied_eq_card_targets] using
    tendsto_occupied_div_of_binomialMoments targets occupancy (fun p => (p : ℝ))
      eventually_pos_primeFilter hmoment

/-- It suffices to supply the still-unproved estimates for every fixed order `r ≥ 2`.
The first-order estimate is discharged by `tendsto_moment_one`. -/
theorem tendsto_card_targets_div_of_higher_moments
    (hmoment : ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun p : ℕ => (moment p r : ℝ) / (p : ℝ))
        primeFilter (𝓝 (1 / (r.factorial : ℝ)))) :
    Tendsto (fun p : ℕ => ((targets p).card : ℝ) / (p : ℝ))
      primeFilter (𝓝 (1 - 1 / Real.exp 1)) := by
  apply tendsto_card_targets_div_of_moments
  intro r hr
  by_cases hr1 : r = 1
  · subst r
    simpa using tendsto_moment_one
  · exact hmoment r (by omega)

end FactorialResidues

end OccupancyBounds
