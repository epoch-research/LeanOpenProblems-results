import FormalConjecturesUtil

/-!
An elementary all-scale criterion for sequences with vanishing dyadic
increments. This file does not assert that either hypothesis holds for the
prime-factor ordering statistic.
-/

namespace Erdos371Scale

open Filter

/-- Every sufficiently large starting point reaches a small value after a
uniformly bounded number of dyadic dilations. The bound can depend on the
requested error, but not on the starting point. -/
def BoundedDyadicAccess (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
    ∃ j : ℕ, j < K ∧ |a (2 ^ j * N)| < ε

/-- Flatness under doubling propagates to every fixed dyadic dilation. -/
theorem flatness_pow {a : ℕ → ℝ}
    (h : Tendsto (fun N => a (2 * N) - a N) atTop (nhds 0)) (j : ℕ) :
    Tendsto (fun N => a (2 ^ j * N) - a N) atTop (nhds 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp : Tendsto (fun N : ℕ => 2 ^ j * N) atTop atTop := by
      apply tendsto_atTop_mono _ tendsto_id
      intro N
      dsimp only
      exact Nat.le_mul_of_pos_left N (by positivity)
    have hs := (h.comp hp).add ih
    simpa only [Function.comp_def, pow_succ', mul_assoc, sub_add_sub_cancel, zero_add]
      using hs

/-- A bounded wait for good scales upgrades dyadic flatness to convergence
at every scale. No logarithmic-to-ordinary limit passage is assumed. -/
theorem tendsto_zero_of_flatness_of_access {a : ℕ → ℝ}
    (hflat : Tendsto (fun N => a (2 * N) - a N) atTop (nhds 0))
    (haccess : BoundedDyadicAccess a) :
    Tendsto a atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 2 := half_pos hε
  obtain ⟨K, hK⟩ := haccess (ε / 2) he
  have hj (j : Fin K) : ∀ᶠ N : ℕ in atTop, |a (2 ^ (j : ℕ) * N) - a N| < ε / 2 := by
    have ht := (Metric.tendsto_nhds.mp (flatness_pow hflat j)) (ε / 2) he
    simpa only [Real.dist_eq, sub_zero] using ht
  have hjs : ∀ᶠ N : ℕ in atTop, ∀ j : Fin K,
      |a (2 ^ (j : ℕ) * N) - a N| < ε / 2 :=
    Filter.eventually_all.mpr hj
  filter_upwards [hK, hjs] with N hn hs
  obtain ⟨j, hjK, hjval⟩ := hn
  have hdiff := hs ⟨j, hjK⟩
  change |a N - 0| < ε
  rw [sub_zero]
  calc
    |a N| = |(a N - a (2 ^ j * N)) + a (2 ^ j * N)| := by congr 1; ring
    _ ≤ |a N - a (2 ^ j * N)| + |a (2 ^ j * N)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [abs_sub_comm] using hdiff) hjval
    _ = ε := add_halves ε

/-- Convergence trivially supplies bounded access, so under flatness this
access condition is equivalent to convergence. -/
theorem access_iff_tendsto_zero {a : ℕ → ℝ}
    (hflat : Tendsto (fun N => a (2 * N) - a N) atTop (nhds 0)) :
    BoundedDyadicAccess a ↔ Tendsto a atTop (nhds 0) := by
  constructor
  · exact tendsto_zero_of_flatness_of_access hflat
  · intro h ε hε
    refine ⟨1, ?_⟩
    have he := (Metric.tendsto_nhds.mp h) ε hε
    filter_upwards [he] with N hN
    refine ⟨0, by omega, ?_⟩
    simpa only [pow_zero, one_mul, Real.dist_eq, sub_zero] using hN

#print axioms flatness_pow
#print axioms tendsto_zero_of_flatness_of_access
#print axioms access_iff_tendsto_zero

end Erdos371Scale
