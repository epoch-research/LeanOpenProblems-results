import Submission.FactorialDefect

/-!
# A conditional all-prime limit criterion from dyadic squared errors

For a real-valued function `f` on the natural numbers, `dyadicSquareSum f N`
is the sum of `(f p)^2` over **all** primes in `N < p ≤ 2*N`. If this sum is
`o(N^2)` as `N → ∞` through the natural numbers, then `f p / p → 0` along
`atTop ⊓ principal {p | p.Prime}`. This is an all-prime conclusion, not a
prime-density-one conclusion. The sum is not divided by the number of primes.

We use exactly the window `Finset.Ioc N (2*N)`. For every `p ≥ 2`, the natural
number `N = (p+1)/2` is positive and satisfies `N < p ≤ 2*N`; also `N → ∞`
as `p → ∞`. In particular, the prime `2` and both parities are covered.
The proof bounds a single squared error by the nonnegative sum and then
uses the square root and the squeeze theorem.

In the factorial specialization, `D p = FactorialDefect.repetitionCount p`,
`δ = 1 / Real.exp 1`, and `d p = D p / p` (division after casting to `ℝ`).
The sole analytic premise is

`Tendsto (fun N => squaredErrorSum N / (N : ℝ)^2) atTop (𝓝 0)`,

where `squaredErrorSum N = ∑ p prime, N < p ≤ 2*N, (D p - δ*p)^2`.
This premise is **not proved or assumed globally**. Every resulting limit
is conditional on it. The exact target support limit follows using
`FactorialDefect.support_limit_iff_repetitionCount_limit.mpr`.

The finite lower bound and its frequent-bad-prime corollary are likewise
conditional; no bad-prime hypothesis or squared-error estimate is asserted.
This auxiliary file does not import the problem specification and does not
settle its proposed asymptotic. The prime filter is the existing nontrivial
one from `OccupancyBounds.FactorialResidues`.
-/

set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped BigOperators Topology

noncomputable section

namespace DefectLimitCriterion

/-- The unnormalized sum of squared values over the primes in `(N, 2*N]`.
The scaling parameter `N` ranges over all natural numbers. -/
def dyadicSquareSum (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc N (2 * N)).filter Nat.Prime, (f p) ^ 2

/-- Every summand is nonnegative. -/
theorem dyadicSquareSum_nonneg (f : ℕ → ℝ) (N : ℕ) :
    0 ≤ dyadicSquareSum f N := by
  exact Finset.sum_nonneg (fun p _ => sq_nonneg (f p))

/-- A single prime's squared value is bounded by the whole dyadic sum. -/
theorem sq_le_dyadicSquareSum {f : ℕ → ℝ} {N p : ℕ}
    (hp : p.Prime) (hNp : N < p) (hpN : p ≤ 2 * N) :
    (f p) ^ 2 ≤ dyadicSquareSum f N := by
  apply Finset.single_le_sum (fun q _ => sq_nonneg (f q))
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hNp, hpN⟩, hp⟩

/-- Normalizing by `p` only improves the bound, since `N < p`.
Positivity of `N` is explicit; there is no division by a zero scale. -/
theorem normalized_sq_le_dyadicSquareSum {f : ℕ → ℝ} {N p : ℕ}
    (hN : 0 < N) (hp : p.Prime) (hNp : N < p) (hpN : p ≤ 2 * N) :
    (f p / (p : ℝ)) ^ 2 ≤ dyadicSquareSum f N / (N : ℝ) ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNpr : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hNp.le
  rw [div_pow]
  calc
    (f p) ^ 2 / (p : ℝ) ^ 2 ≤ dyadicSquareSum f N / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (sq_le_dyadicSquareSum hp hNp hpN) (sq_nonneg _)
    _ ≤ dyadicSquareSum f N / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (dyadicSquareSum_nonneg f N) (sq_pos_of_pos hNr)
        ((sq_le_sq₀ (Nat.cast_nonneg N) (Nat.cast_nonneg p)).2 hNpr)

/-- The square-root form of the pointwise bound, suitable for squeezing. -/
theorem norm_div_le_sqrt_dyadicSquareSum {f : ℕ → ℝ} {N p : ℕ}
    (hN : 0 < N) (hp : p.Prime) (hNp : N < p) (hpN : p ≤ 2 * N) :
    ‖f p / (p : ℝ)‖ ≤ Real.sqrt (dyadicSquareSum f N) / (N : ℝ) := by
  have h := Real.sqrt_le_sqrt
    (normalized_sq_le_dyadicSquareSum (f := f) hN hp hNp hpN)
  simpa only [Real.sqrt_div (dyadicSquareSum_nonneg f N), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N),
    Real.norm_eq_abs] using h

/-- Natural-number ceiling of `p/2` gives a valid window for every `p ≥ 2`.
In particular, this lemma does not silently discard the prime `2`. -/
theorem ceilHalf_mem_dyadicWindow {p : ℕ} (hp : 2 ≤ p) :
    0 < (p + 1) / 2 ∧ (p + 1) / 2 < p ∧ p ≤ 2 * ((p + 1) / 2) := by
  omega

/-- The selected window scale tends to infinity. -/
theorem tendsto_ceilHalf_atTop :
    Tendsto (fun p : ℕ => (p + 1) / 2) atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  filter_upwards [eventually_ge_atTop (2 * N)] with p hp
  omega

/-- The squared-sum and square-root formulations of the analytic premise
are equivalent. This uses nonnegativity, not any bound on `f`. -/
theorem tendsto_dyadicSquareSum_div_sq_iff_sqrt (f : ℕ → ℝ) :
    Tendsto (fun N : ℕ => dyadicSquareSum f N / (N : ℝ) ^ 2) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => Real.sqrt (dyadicSquareSum f N) / (N : ℝ))
      atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [Real.sqrt_div (dyadicSquareSum_nonneg f _),
      Real.sqrt_sq (Nat.cast_nonneg _), Real.sqrt_zero] using h.sqrt
  · intro h
    simpa only [div_pow, Real.sq_sqrt (dyadicSquareSum_nonneg f _),
      zero_pow (by decide : 2 ≠ 0)] using h.pow 2

/-- Square-root sufficient criterion for convergence along all primes.
The conclusion uses the full prime filter, not a selected subsequence. -/
theorem tendsto_div_prime_of_sqrt_dyadicSquareSum (f : ℕ → ℝ)
    (hV : Tendsto (fun N : ℕ => Real.sqrt (dyadicSquareSum f N) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun p : ℕ => f p / (p : ℝ))
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (𝓝 0) := by
  have hscale : Tendsto (fun p : ℕ => (p + 1) / 2)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) atTop :=
    tendsto_ceilHalf_atTop.mono_left inf_le_left
  have hprime : ∀ᶠ p in atTop ⊓ Filter.principal {p : ℕ | p.Prime}, p.Prime :=
    Filter.mem_inf_of_right (by simp)
  apply squeeze_zero_norm' (a := fun p =>
    Real.sqrt (dyadicSquareSum f ((p + 1) / 2)) / (((p + 1) / 2 : ℕ) : ℝ))
    ?_ (hV.comp hscale)
  filter_upwards [hprime] with p hp
  obtain ⟨hN, hNp, hpN⟩ := ceilHalf_mem_dyadicWindow hp.two_le
  exact norm_div_le_sqrt_dyadicSquareSum hN hp hNp hpN

/-- **All-prime dyadic squared-error criterion.** If the unnormalized sum
of squares in `(N, 2*N]` is `o(N^2)`, then `f p / p → 0` along primes. -/
theorem tendsto_div_prime_of_dyadicSquareSum (f : ℕ → ℝ)
    (hV : Tendsto (fun N : ℕ => dyadicSquareSum f N / (N : ℝ) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun p : ℕ => f p / (p : ℝ))
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (𝓝 0) :=
  tendsto_div_prime_of_sqrt_dyadicSquareSum f
    ((tendsto_dyadicSquareSum_div_sq_iff_sqrt f).mp hV)

/-- One prime with relative error at least `ε` forces the normalized dyadic
sum to be at least `ε^2`. This is only a conditional finite obstruction. -/
theorem bad_prime_lower_bound {f : ℕ → ℝ} {N p : ℕ} {ε : ℝ}
    (hN : 0 < N) (hp : p.Prime) (hNp : N < p) (hpN : p ≤ 2 * N)
    (hε : 0 ≤ ε) (hbad : ε ≤ ‖f p / (p : ℝ)‖) :
    ε ^ 2 ≤ dyadicSquareSum f N / (N : ℝ) ^ 2 := by
  calc
    ε ^ 2 ≤ ‖f p / (p : ℝ)‖ ^ 2 :=
      (sq_le_sq₀ hε (norm_nonneg _)).2 hbad
    _ = (f p / (p : ℝ)) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ dyadicSquareSum f N / (N : ℝ) ^ 2 :=
      normalized_sq_le_dyadicSquareSum hN hp hNp hpN

/-- A fixed positive relative error at primes in arbitrarily large windows
rules out the squared-error premise. No existence of such primes is claimed. -/
theorem not_tendsto_dyadicSquareSum_of_frequently_bad_prime
    {f : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hbad : ∃ᶠ N : ℕ in atTop, ∃ p : ℕ,
      p.Prime ∧ N < p ∧ p ≤ 2 * N ∧ ε ≤ ‖f p / (p : ℝ)‖) :
    ¬ Tendsto (fun N : ℕ => dyadicSquareSum f N / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  intro hV
  have hsmall : ∀ᶠ N : ℕ in atTop,
      dyadicSquareSum f N / (N : ℝ) ^ 2 < ε ^ 2 :=
    hV.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨N, ⟨p, hp, hNp, hpN, hbadp⟩, hN, hsmallN⟩ :=
    (hbad.and_eventually ((eventually_gt_atTop 0).and hsmall)).exists
  exact (not_lt_of_ge (bad_prime_lower_bound hN hp hNp hpN hε.le hbadp)) hsmallN

section FactorialSpecialization

/-- The direct repetition count, without any change to its original definition. -/
abbrev D (p : ℕ) : ℕ := FactorialDefect.repetitionCount p

/-- The proposed limiting proportion of repeated factorial residues. -/
def δ : ℝ := 1 / Real.exp 1

/-- The normalized defect. The natural repetition count is cast before division. -/
def d (p : ℕ) : ℝ := (D p : ℝ) / (p : ℝ)

/-- The centered, unnormalized error. Subtraction takes place in `ℝ`, not `ℕ`. -/
def defectError (p : ℕ) : ℝ := (D p : ℝ) - δ * (p : ℝ)

/-- The precise squared-error sum required by the factorial limit criterion. -/
def squaredErrorSum (N : ℕ) : ℝ := dyadicSquareSum defectError N

/-- At a positive index the normalized centered error is exactly `d p - δ`. -/
theorem defectError_div {p : ℕ} (hp : 0 < p) :
    defectError p / (p : ℝ) = d p - δ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  simp [defectError, d, sub_div, hp0]

/-- The explicit squared-error premise implies convergence of the normalized
defect. This theorem supplies no estimate for `squaredErrorSum`. -/
theorem tendsto_normalizedDefect_of_squaredErrorSum
    (hV : Tendsto (fun N : ℕ => squaredErrorSum N / (N : ℝ) ^ 2)
      atTop (𝓝 0)) :
    Tendsto d (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (𝓝 δ) := by
  have herr := tendsto_div_prime_of_dyadicSquareSum defectError hV
  have hlim : Tendsto (fun p : ℕ => defectError p / (p : ℝ) + δ)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (𝓝 δ) := by
    simpa only [zero_add] using herr.add_const δ
  have hprime : ∀ᶠ p in atTop ⊓ Filter.principal {p : ℕ | p.Prime}, p.Prime :=
    Filter.mem_inf_of_right (by simp)
  apply hlim.congr'
  filter_upwards [hprime] with p hp
  rw [defectError_div hp.pos, sub_add_cancel]

/-- The same conditional limit with the original repetition-count notation. -/
theorem repetitionCount_limit_of_squaredErrorSum
    (hV : Tendsto (fun N : ℕ => squaredErrorSum N / (N : ℝ) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun p : ℕ => (FactorialDefect.repetitionCount p : ℝ) / p)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (𝓝 (1 / Real.exp 1)) := by
  simpa only [d, D, δ] using tendsto_normalizedDefect_of_squaredErrorSum hV

/-- **Conditional exact target limit.** The only analytic hypothesis is the
stated `o(N^2)` squared-error sum. The finite complement identity and its
limit equivalence are imported from `FactorialDefect`, not from the specification. -/
theorem support_limit_of_squaredErrorSum
    (hV : Tendsto (fun N : ℕ => squaredErrorSum N / (N : ℝ) ^ 2)
      atTop (𝓝 0)) :
    Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => k.factorial % p)).card : ℝ) / p)
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (𝓝 (1 - 1 / Real.exp 1)) :=
  FactorialDefect.support_limit_iff_repetitionCount_limit.mpr
    (repetitionCount_limit_of_squaredErrorSum hV)

end FactorialSpecialization

end DefectLimitCriterion

-- Kernel-axiom audits: no squared-error estimate is introduced as an axiom.
#print axioms DefectLimitCriterion.dyadicSquareSum_nonneg
#print axioms DefectLimitCriterion.sq_le_dyadicSquareSum
#print axioms DefectLimitCriterion.normalized_sq_le_dyadicSquareSum
#print axioms DefectLimitCriterion.norm_div_le_sqrt_dyadicSquareSum
#print axioms DefectLimitCriterion.ceilHalf_mem_dyadicWindow
#print axioms DefectLimitCriterion.tendsto_ceilHalf_atTop
#print axioms DefectLimitCriterion.tendsto_dyadicSquareSum_div_sq_iff_sqrt
#print axioms DefectLimitCriterion.tendsto_div_prime_of_sqrt_dyadicSquareSum
#print axioms DefectLimitCriterion.tendsto_div_prime_of_dyadicSquareSum
#print axioms DefectLimitCriterion.bad_prime_lower_bound
#print axioms DefectLimitCriterion.not_tendsto_dyadicSquareSum_of_frequently_bad_prime
#print axioms DefectLimitCriterion.defectError_div
#print axioms DefectLimitCriterion.tendsto_normalizedDefect_of_squaredErrorSum
#print axioms DefectLimitCriterion.repetitionCount_limit_of_squaredErrorSum
#print axioms DefectLimitCriterion.support_limit_of_squaredErrorSum
#print axioms OccupancyBounds.FactorialResidues.primeFilter_neBot
