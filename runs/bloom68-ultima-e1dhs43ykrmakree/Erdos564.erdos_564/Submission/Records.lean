import FormalConjecturesUtil

/-!
# Cofinal approximate records for real sequences

An eventually lower-bounded real sequence has arbitrarily late approximate records on
one fixed tail, for each fixed positive error. The tail cutoff may depend on the error,
but not on how late a record is requested.

For an upper-bounded sequence, the proof uses the finite real `Filter.limsup`:
eventually the sequence is below `limsup + ε / 2`, and frequently it is above
`limsup - ε / 2`. The eventual lower bound supplies the lower-coboundedness needed by
the latter assertion. For an unbounded sequence, finite prefix maxima give cofinal
exact records, without assuming that the sequence tends to infinity.

Applying this to `f n = g n - n` gives the quantitative record normalization for any
real sequence with `g n ≥ n` eventually. No Ramsey estimate is assumed or proved.
In particular, the error here is fixed; a reciprocal-sequence counterexample below
rules out replacing it by an arbitrary positive error depending on the record index.

Divergent multiplicative weights give a different, exact record principle. Polynomial
weights have vanishing slack for fixed backward drops, and logarithmic weights give
`o(1/n)` slack for those drops. These errors depend on both indices, so they do not
contradict the fixed-tail counterexample.
-/

set_option autoImplicit false

namespace RealRecords

open Filter
open scoped Topology

/-- An unbounded real sequence has cofinally many exact prefix records.
Unboundedness, rather than convergence to infinity, suffices. -/
theorem cofinal_exact_records_of_unbounded {f : ℕ → ℝ}
    (hf : ¬ BddAbove (Set.range f)) :
    ∀ N : ℕ, ∃ n ≥ N, ∀ m ≤ n, f m ≤ f n := by
  intro N
  obtain ⟨k, _, hk⟩ : ∃ k ≤ N, ∀ m ≤ N, f m ≤ f k :=
    Set.exists_max_image _ f (Set.finite_le_nat N) ⟨N, Nat.le_refl N⟩
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := not_bddAbove_iff.mp hf (f k)
  obtain ⟨n, hn, hmax⟩ : ∃ n ≤ j, ∀ m ≤ j, f m ≤ f n :=
    Set.exists_max_image _ f (Set.finite_le_nat j) ⟨j, Nat.le_refl j⟩
  refine ⟨n, ?_, fun m hm => hmax m (hm.trans hn)⟩
  by_contra! hN
  exact (not_lt_of_ge ((hmax j le_rfl).trans (hk n hN.le))) hj

/-- In the upper-bounded case, cofinally many values approximately dominate the
entire fixed tail, not merely the part of that tail preceding the chosen index. -/
theorem cofinal_near_tail_bounds_of_bounded {f : ℕ → ℝ}
    (hbelow : ∃ a : ℝ, ∀ᶠ n in atTop, a ≤ f n)
    (habove : BddAbove (Set.range f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N, ∀ m ≥ m0, f m < f n + ε := by
  obtain ⟨a, ha⟩ := hbelow
  have hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) f :=
    isCoboundedUnder_le_of_eventually_le atTop ha
  have hbd : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) f :=
    habove.isBoundedUnder_of_range
  have hupper : ∀ᶠ m in atTop, f m < limsup f atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (by linarith) hbd
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hupper
  have hlower : ∃ᶠ n in atTop, limsup f atTop - ε / 2 < f n :=
    frequently_lt_of_lt_limsup hco (by linarith)
  refine ⟨m0, ?_⟩
  intro N
  obtain ⟨n, hn, hfn⟩ := frequently_atTop.mp hlower N
  refine ⟨n, hn, ?_⟩
  intro m hm
  have hfm := hm0 m hm
  linarith

/-- Fixed-error, fixed-tail cofinal near-record lemma for an eventually
lower-bounded real sequence. The quantifier order is essential: `m0` is chosen
before `N`, while `ε > 0` is fixed before both of them. -/
theorem cofinal_near_records_of_eventually_bounded_below {f : ℕ → ℝ}
    (hf : ∃ a : ℝ, ∀ᶠ n in atTop, a ≤ f n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n → f m ≤ f n + ε := by
  classical
  by_cases hb : BddAbove (Set.range f)
  · obtain ⟨m0, hm0⟩ := cofinal_near_tail_bounds_of_bounded hf hb hε
    refine ⟨m0, ?_⟩
    intro N
    obtain ⟨n, hn, hrec⟩ := hm0 N
    exact ⟨n, hn, fun m hm _ => (hrec m hm).le⟩
  · refine ⟨0, ?_⟩
    intro N
    obtain ⟨n, hn, hrec⟩ := cofinal_exact_records_of_unbounded hb N
    exact ⟨n, hn, fun m _ hmn =>
      (hrec m hmn).trans (le_add_of_nonneg_right hε.le)⟩

/-- The near-record lemma in its eventually nonnegative form. -/
theorem cofinal_near_records {f : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n → f m ≤ f n + ε :=
  cofinal_near_records_of_eventually_bounded_below ⟨0, hf⟩ hε

/-- Quantitative record normalization, obtained by subtracting the linear term.
All subtractions in the conclusion are in `ℝ`, not in `ℕ`. -/
theorem cofinal_normalized_records {g : ℕ → ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ g n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n → g m ≤ g n - ((n : ℝ) - (m : ℝ)) + ε := by
  have hf : ∀ᶠ n in atTop, 0 ≤ g n - (n : ℝ) :=
    hg.mono fun n hn => sub_nonneg.mpr hn
  obtain ⟨m0, hm0⟩ := cofinal_near_records hf hε
  refine ⟨m0, ?_⟩
  intro N
  obtain ⟨n, hn, hrec⟩ := hm0 N
  refine ⟨n, hn, ?_⟩
  intro m hm hmn
  have h := hrec m hm hmn
  linarith

/-- A divergent positive weighting supplies cofinal exact records even if the
unweighted sequence decreases to a positive limit. Unlike the fixed-error lemma,
this gives a comparison error depending on both compared indices. -/
theorem cofinal_weighted_records {f w : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 1 ≤ f n) (hw : Tendsto w atTop atTop) :
    ∀ N : ℕ, ∃ n ≥ N, ∀ m ≤ n, w m * f m ≤ w n * f n := by
  have hle : ∀ᶠ n in atTop, w n ≤ w n * f n := by
    filter_upwards [hf, hw.eventually_ge_atTop 0] with n hfn hwn
    exact le_mul_of_one_le_right hwn hfn
  have ht : Tendsto (fun n => w n * f n) atTop atTop :=
    tendsto_atTop_mono' atTop hle hw
  exact cofinal_exact_records_of_unbounded (not_bddAbove_of_tendsto_atTop ht)

/-- Exact multiplicative form of weighted records. The cutoff in the lower
bound for `x` does not need to be imposed on the earlier comparison index. -/
theorem cofinal_weighted_ratio_records {x a w : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (hwpos : ∀ n, 0 < w n)
    (hx : ∀ᶠ n in atTop, a n ≤ x n) (hw : Tendsto w atTop atTop) :
    ∀ N : ℕ, ∃ n ≥ N, ∀ m ≤ n,
      x m ≤ (a m / a n) * (w n / w m) * x n := by
  have hf : ∀ᶠ n in atTop, 1 ≤ x n / a n := by
    filter_upwards [hx] with n hn
    exact (le_div_iff₀ (ha n)).mpr (by simpa using hn)
  intro N
  obtain ⟨n, hn, hrec⟩ := cofinal_weighted_records hf hw N
  refine ⟨n, hn, ?_⟩
  intro m hmn
  have h := mul_le_mul_of_nonneg_right (hrec m hmn)
    (div_nonneg (ha m).le (hwpos m).le)
  calc
    x m = (w m * (x m / a m)) * (a m / w m) := by
      field_simp [ne_of_gt (ha m), ne_of_gt (hwpos m)]
    _ ≤ (w n * (x n / a n)) * (a m / w m) := h
    _ = (a m / a n) * (w n / w m) * x n := by ring

/-- Polynomially weighted records for an exponential lower bound. The shift by
one keeps all weights positive. The ratio is `1 + O(1/n)` for fixed backward
drops; it is not a uniform shrinking error on one fixed entire tail. -/
theorem cofinal_polynomial_records {x : ℕ → ℝ}
    (hx : ∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) {b : ℝ} (hb : 0 < b) :
    ∀ N : ℕ, ∃ n ≥ N, ∀ m ≤ n,
      x m ≤ ((2 : ℝ) ^ m / (2 : ℝ) ^ n) *
        ((((n : ℝ) + 1) / ((m : ℝ) + 1)) ^ b) * x n := by
  have hw : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  intro N
  obtain ⟨n, hn, hrec⟩ := cofinal_weighted_ratio_records
    (a := fun n => (2 : ℝ) ^ n) (w := fun n => ((n : ℝ) + 1) ^ b)
    (fun n => by positivity) (fun n => by positivity) hx hw N
  refine ⟨n, hn, ?_⟩
  intro m hmn
  simpa only [Real.div_rpow (by positivity : 0 ≤ (n : ℝ) + 1)
    (by positivity : 0 ≤ (m : ℝ) + 1)] using hrec m hmn

/-- Logarithmically weighted records give a still smaller recent-index slack.
No new bound on a Ramsey number is asserted here. -/
theorem cofinal_logarithmic_records {x : ℕ → ℝ}
    (hx : ∀ᶠ n in atTop, (2 : ℝ) ^ n ≤ x n) :
    ∀ N : ℕ, ∃ n ≥ N, ∀ m ≤ n,
      x m ≤ ((2 : ℝ) ^ m / (2 : ℝ) ^ n) *
        (Real.log ((n : ℝ) + 2) / Real.log ((m : ℝ) + 2)) * x n := by
  apply cofinal_weighted_ratio_records
    (a := fun n => (2 : ℝ) ^ n) (w := fun n => Real.log ((n : ℝ) + 2))
  · intro n
    positivity
  · intro n
    exact Real.log_pos (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  · exact hx
  · exact Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)

/-- An explicit recent-index bound for logarithmic record weights. -/
theorem logarithmic_recent_slack_bound (n j : ℕ) :
    0 ≤ (n : ℝ) * (Real.log ((n : ℝ) + j + 2) /
      Real.log ((n : ℝ) + 2) - 1) ∧
    (n : ℝ) * (Real.log ((n : ℝ) + j + 2) /
      Real.log ((n : ℝ) + 2) - 1) ≤
      (j : ℝ) / Real.log ((n : ℝ) + 2) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hp : 0 < (n : ℝ) + 2 := by linarith
  have hq : 0 < (n : ℝ) + j + 2 := by linarith
  have hl : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hlog : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + j + 2) :=
    (Real.log_le_log_iff hp hq).mpr (by linarith)
  have hdelta : Real.log ((n : ℝ) + j + 2) - Real.log ((n : ℝ) + 2) ≤
      (j : ℝ) / ((n : ℝ) + 2) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at h
    convert h using 1
    field_simp
    ring
  constructor
  · exact mul_nonneg hn (sub_nonneg.mpr
      ((le_div_iff₀ hl).mpr (by simpa using hlog)))
  · have heq : (n : ℝ) * (Real.log ((n : ℝ) + j + 2) /
        Real.log ((n : ℝ) + 2) - 1) =
        (n : ℝ) * (Real.log ((n : ℝ) + j + 2) - Real.log ((n : ℝ) + 2)) /
          Real.log ((n : ℝ) + 2) := by
      field_simp
    rw [heq]
    apply (div_le_div_iff_of_pos_right hl).mpr
    calc
      (n : ℝ) * (Real.log ((n : ℝ) + j + 2) - Real.log ((n : ℝ) + 2)) ≤
          (n : ℝ) * ((j : ℝ) / ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hdelta hn
      _ ≤ (j : ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hp).mpr
        nlinarith

/-- For each fixed backward drop, the error in logarithmically weighted
records is `o(1/n)`, not merely `O(1/n)`. This does not assert a uniform
shrinking error over all earlier indices. -/
theorem tendsto_logarithmic_recent_slack (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (Real.log ((n : ℝ) + j + 2) / Real.log ((n : ℝ) + 2) - 1))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun n : ℕ => (j : ℝ) / Real.log ((n : ℝ) + 2))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => (logarithmic_recent_slack_bound n j).1)
    (fun n => (logarithmic_recent_slack_bound n j).2)

/- Sanity checks. -/

/-- Constant sequences may have an arbitrary, possibly negative, lower bound. -/
example (c ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n → c ≤ c + ε := by
  exact cofinal_near_records_of_eventually_bounded_below
    (f := fun _ => c) ⟨c, Eventually.of_forall fun _ => le_rfl⟩ hε

/-- A decreasing positive sequence still has the fixed-error near-record property. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n →
        1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) + ε := by
  apply cofinal_near_records (f := fun n => 1 / ((n : ℝ) + 1)) _ hε
  exact Eventually.of_forall fun n => by positivity

/-- The normalized estimate applies even when `g n - n` is decreasing. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n →
        (m : ℝ) + 1 / ((m : ℝ) + 1) ≤
          (n : ℝ) + 1 / ((n : ℝ) + 1) - ((n : ℝ) - (m : ℝ)) + ε := by
  apply cofinal_normalized_records (g := fun n => (n : ℝ) + 1 / ((n : ℝ) + 1)) _ hε
  exact Eventually.of_forall fun n => le_add_of_nonneg_right (by positivity)

/-- The error cannot in general shrink with the record index: both
`f n = 1 / (n + 1)` and `ε n = 1 / (n + 1)` are positive, but no fixed tail
has cofinal near-records with this error. -/
theorem reciprocal_shrinking_error_fails :
    ¬ ∃ m0 : ℕ, ∀ N : ℕ, ∃ n ≥ N,
      ∀ m ≥ m0, m ≤ n →
        (1 : ℝ) / ((m : ℝ) + 1) ≤
          1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
  rintro ⟨m0, hm0⟩
  obtain ⟨n, hn, hrec⟩ := hm0 (2 * m0 + 2)
  have hmn : m0 ≤ n := by omega
  have h := hrec m0 le_rfl hmn
  rw [← add_div] at h
  have hmpos : 0 < (m0 : ℝ) + 1 := by positivity
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hprod := (div_le_div_iff₀ hmpos hnpos).mp h
  have hnr : 2 * (m0 : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

end RealRecords

#print axioms RealRecords.cofinal_exact_records_of_unbounded
#print axioms RealRecords.cofinal_near_tail_bounds_of_bounded
#print axioms RealRecords.cofinal_near_records_of_eventually_bounded_below
#print axioms RealRecords.cofinal_near_records
#print axioms RealRecords.cofinal_normalized_records
#print axioms RealRecords.reciprocal_shrinking_error_fails

#print axioms RealRecords.cofinal_weighted_records
#print axioms RealRecords.cofinal_weighted_ratio_records
#print axioms RealRecords.cofinal_polynomial_records
#print axioms RealRecords.cofinal_logarithmic_records

#print axioms RealRecords.logarithmic_recent_slack_bound
#print axioms RealRecords.tendsto_logarithmic_recent_slack
