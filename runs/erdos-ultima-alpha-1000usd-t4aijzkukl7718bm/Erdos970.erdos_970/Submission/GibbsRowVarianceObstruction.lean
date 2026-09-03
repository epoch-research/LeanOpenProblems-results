import Submission.PopulationSensitiveRowVariance

/-! An exact obstruction to moving an unweighted row-variance estimate inside
an arbitrary Gibbs expectation. This is an auxiliary counterexample, not a
negation of the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.GibbsRowExample
open Finset Real Erdos970.Resampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def primes : Finset ℕ := {2, 3}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]

def phase (a : Fin 6) : Phase primes := fun p =>
  ⟨a.val % p.val, Nat.mod_lt _ (primes_prime p.val p.property).pos⟩

lemma phase_injective : Function.Injective phase := by
  intro a b he
  have h2 := congrArg (fun r : Phase primes => (r ⟨2, by decide⟩).val) he
  have h3 := congrArg (fun r : Phase primes => (r ⟨3, by decide⟩).val) he
  change a.val ≡ b.val [MOD 2] at h2
  change a.val ≡ b.val [MOD 3] at h3
  have h6 := (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 2 3)).mp ⟨h2,h3⟩
  exact Fin.ext (h6.eq_of_lt_of_lt a.isLt b.isLt)

lemma phase_card : Fintype.card (Phase primes) = 6 := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [prod_coe_sort primes (fun p : ℕ => p)]
  norm_num [primes]

noncomputable def phaseEquiv : Fin 6 ≃ Phase primes :=
  Equiv.ofBijective phase ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨phase_injective, by rw [Fintype.card_fin, phase_card]⟩)

def rawCount (a : ℕ) : ℕ :=
  ((range 35).filter (fun x => x % 2 ≠ a % 2 ∧ x % 3 ≠ a % 3)).card

def rawRow (a b : ℕ) : ℕ :=
  ((range 35).filter (fun x => x % 2 ≠ a % 2 ∧ x % 3 ≠ a % 3 ∧ x % 7 = b)).card

def low (a : Fin 6) : Prop := a.val = 0 ∨ a.val = 4
instance (a : Fin 6) : Decidable (low a) := inferInstanceAs (Decidable (_ ∨ _))

lemma raw_data : ∀ a : Fin 6,
    rawCount a.val = (if low a then 11 else 12) ∧
      (∑ b : Fin 7, rawRow a.val b.val ^ 2) = (if low a then 19 else 22) := by
  decide +kernel

lemma count_raw (a : Fin 6) :
    intervalCount primes 35 (phase a) = (rawCount a.val : ℝ) := by
  simp [intervalCount, CoverFibers.point_eq_avoidance_indicator, phase, primes,
    Subtype.forall, rawCount]

lemma row_raw (a : Fin 6) (b : Fin 7) :
    rowCount primes 35 7 b (phase a) = (rawRow a.val b.val : ℝ) := by
  simp [rowCount, CoverFibers.point_eq_avoidance_indicator, phase, primes,
    Subtype.forall, rawRow, filter_filter, and_comm, and_assoc]

lemma count_table (a : Fin 6) :
    intervalCount primes 35 (phase a) = if low a then 11 else 12 := by
  rw [count_raw, (raw_data a).1]
  split_ifs <;> norm_num

lemma variance_table (a : Fin 6) :
    rowConditionalVariance primes 35 7 (phase a) =
      if low a then 12 / 49 else 10 / 49 := by
  rw [rowConditionalVariance, ← rowCount_mean primes 35 7 (by norm_num) (phase a),
    residueMean_centered_square 7 (by norm_num),
    rowCount_mean primes 35 7 (by norm_num), count_table]
  have he : residueMean 7 (fun b => rowCount primes 35 7 b (phase a) ^ 2) =
      (if low a then (19 : ℝ) else 22) / 7 := by
    simp only [residueMean, row_raw]
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (raw_data a).2
    push_cast at hh
    rw [hh]
    split_ifs <;> rfl
  rw [he]
  split_ifs <;> norm_num

/-- The complete joint distribution, over actual independent core phases. -/
lemma joint_mean (f : ℝ → ℝ → ℝ) :
    phaseMean primes (fun r => f (intervalCount primes 35 r)
      (rowConditionalVariance primes 35 7 r)) =
      (f 11 (12/49) + 2 * f 12 (10/49)) / 3 := by
  unfold phaseMean
  rw [← phaseEquiv.sum_comp (fun r => f (intervalCount primes 35 r)
    (rowConditionalVariance primes 35 7 r))]
  change (∑ a : Fin 6, f (intervalCount primes 35 (phase a))
    (rowConditionalVariance primes 35 7 (phase a))) / _ = _
  simp_rw [count_table, variance_table]
  rw [prod_coe_sort primes (fun p : ℕ => (p : ℝ))]
  norm_num [primes, Fin.sum_univ_succ, low]
  ring

/-- Weighting toward low counts increases, rather than decreases, the average
row variance. This holds for every positive parameter, however small. -/
theorem gibbs_row_variance_strictly_increases (t : ℝ) (ht : 0 < t) :
    phaseMean primes (rowConditionalVariance primes 35 7) *
      phaseMean primes (fun r => exp (-t * intervalCount primes 35 r)) <
    phaseMean primes (fun r => exp (-t * intervalCount primes 35 r) *
      rowConditionalVariance primes 35 7 r) := by
  have hv := joint_mean (fun _ v => v)
  have hw := joint_mean (fun n _ => exp (-t*n))
  have hwv := joint_mean (fun n v => exp (-t*n)*v)
  rw [hv, hw, hwv]
  have he : exp (-t*12) < exp (-t*11) := exp_lt_exp.mpr (by linarith)
  nlinarith

/-- In particular, a uniform nonpositive Gibbs covariance claim is false,
even for a complete initial prime core and a larger new prime. -/
theorem not_uniform_gibbs_row_variance_suppression :
    ¬∀ P : Finset ℕ, (∀ q ∈ P, q.Prime) → ∀ m p : ℕ,
      p.Prime → (∀ q ∈ P, q < p) → ∀ t : ℝ, 0 < t →
      phaseMean P (fun r => exp (-t * intervalCount P m r) *
        rowConditionalVariance P m p r) ≤
      phaseMean P (rowConditionalVariance P m p) *
        phaseMean P (fun r => exp (-t * intervalCount P m r)) := by
  intro h
  exact (gibbs_row_variance_strictly_increases 1 (by norm_num)).not_ge
    (h primes primes_prime 35 7 (by norm_num) (by norm_num [primes]) 1 (by norm_num))

#print axioms gibbs_row_variance_strictly_increases
#print axioms not_uniform_gibbs_row_variance_suppression
end Erdos970.GapAverages.GibbsRowExample
