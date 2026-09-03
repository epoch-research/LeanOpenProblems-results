import Submission.BooleanCoupledDuality

/-! A certified gap between global coverage polynomials and ALL normalized
prior-supported first-hit kernels, at six equal marginals1/3 and m100.
These are not distinct-prime marginals and this is not a Jacobsthal disproof. -/
namespace Erdos970.FiniteSelberg.CoupledExample
open Finset

def qRat (_ : Fin 6) : ℚ := 1 / 3
def hitCount (ω : Fin 6 → Bool) : ℕ := (univ.filter (fun i => ω i = true)).card
def prefixTable : ℕ → ℕ → ℚ
  | 0, 0 => 103 / 3
  | 1, 0 => 218 / 9
  | 1, 1 => 91 / 9
  | 2, 0 => 508 / 27
  | 2, 1 => 146 / 27
  | 2, 2 => 127 / 27
  | 3, 0 => 1448 / 81
  | 3, 1 => 76 / 81
  | 3, 2 => 362 / 81
  | 3, 3 => 19 / 81
  | 4, 0 => 151 / 9
  | 4, 2 => 55 / 27
  | 4, 3 => 4 / 3
  | 5, 0 => 1321 / 81
  | 5, 2 => 19 / 54
  | 5, 3 => 235 / 162
  | _, _ => 0

def globalTable : ℕ → ℚ
  | 1 => 1321 / 81
  | 3 => 19 / 54
  | 4 => 235 / 162
  | _ => 0

def prefixWeight (i : Fin 6) (ω : Fin 6 → Bool) : ℚ :=
  if ∀ j : Fin 6, i ≤ j → ω j = false then prefixTable i.val (hitCount ω) else 0

def globalWeight (ω : Fin 6 → Bool) : ℚ := globalTable (hitCount ω)

def coefficient (T : Finset (Fin 6)) : ℚ :=
  match T.card with
  | 1 => 1
  | 2 => -5 / 6
  | 3 => 1 / 2
  | _ => 0

def hitRat (T : Finset (Fin 6)) (ω : Fin 6 → Bool) : ℚ :=
  if ∀ i ∈ T, ω i = true then 1 else 0

def valueRat (ω : Fin 6 → Bool) : ℚ :=
  ∑ T : Finset (Fin 6), coefficient T * hitRat T ω

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact dual certificates for every prior-coordinate upper-weight problem. -/
theorem prefix_certificate :
    (∀ i ω, 0 ≤ prefixWeight i ω) ∧
    (∀ i T, (∀ j ∈ T, j < i) →
      |(∑ ω, prefixWeight i ω * hitRat T ω) - (100 * qRat i) * ∏ j ∈ T, qRat j| ≤ 1) ∧
    (∑ i, prefixWeight i (fun _ => false)) = 385 / 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The global dual has no empty atom and satisfies all nonempty moment bounds. -/
theorem global_certificate :
    (∀ ω, 0 ≤ globalWeight ω) ∧ globalWeight (fun _ => false) = 0 ∧
    (∀ T : Finset (Fin 6), T.Nonempty →
      |(∑ ω, globalWeight ω * hitRat T ω) - 100 * ∏ i ∈ T, qRat i| ≤ 1) ∧
    (∑ ω, globalWeight ω) = 6839 / 54 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The symmetric cubic coverage polynomial attains the global dual value. -/
theorem primal_certificate :
    coefficient ∅ = 0 ∧
    (∀ ω : Fin 6 → Bool, ω ≠ (fun _ => false) → 1 ≤ valueRat ω) ∧
    (100 * (∑ T : Finset (Fin 6), coefficient T * ∏ i ∈ T, qRat i) +
      ∑ T : Finset (Fin 6), |coefficient T|) = 6839 / 54 := by
  decide +kernel

noncomputable def q (i : Fin 6) : ℝ := qRat i
noncomputable def a (T : Finset (Fin 6)) : ℝ := coefficient T
noncomputable def w (ω : Fin 6 → Bool) : ℝ := globalWeight ω
noncomputable def u (i : Fin 6) (ω : Fin 6 → Bool) : ℝ := prefixWeight i ω

lemma cast_hitRat (T : Finset (Fin 6)) (ω : Fin 6 → Bool) :
    (hitRat T ω : ℝ) = hitMonomial T ω := by
  rw [hitMonomial_eq]
  simp only [hitRat]
  split_ifs <;> norm_num

lemma cast_valueRat (ω : Fin 6 → Bool) : (valueRat ω : ℝ) = booleanValue a ω := by
  simp only [valueRat, Rat.cast_sum, Rat.cast_mul, cast_hitRat, booleanValue, a]

lemma prefix_dual_feasible : FirstHitDualFeasible q 100 u := by
  constructor
  · intro i ω
    change (0 : ℝ) ≤ (prefixWeight i ω : ℝ)
    exact_mod_cast prefix_certificate.1 i ω
  · intro i T hT
    have hh : |(∑ ω, (prefixWeight i ω : ℝ) * (hitRat T ω : ℝ)) -
        (100 * (qRat i : ℝ)) * ∏ j ∈ T, (qRat j : ℝ)| ≤ 1 := by
      exact_mod_cast prefix_certificate.2.1 i T hT
    simpa only [cast_hitRat, u, q] using hh

lemma prefix_dual_value : (∑ i, u i (fun _ => false)) = 385 / 3 := by
  unfold u
  have h := congrArg (fun x : ℚ => (x : ℝ)) prefix_certificate.2.2
  push_cast at h
  exact h

lemma coverage_majorant : IsCoverageMajorant a := by
  constructor
  · unfold a
    exact_mod_cast primal_certificate.1
  · intro ω hω
    rw [← cast_valueRat]
    exact_mod_cast primal_certificate.2.1 ω hω

lemma primal_objective : booleanObjective q 100 a = 6839 / 54 := by
  unfold booleanObjective q a
  have h := congrArg (fun x : ℚ => (x : ℝ)) primal_certificate.2.2
  push_cast at h
  exact h

lemma global_nonnegative (ω : Fin 6 → Bool) : 0 ≤ w ω := by
  unfold w
  exact_mod_cast global_certificate.1 ω

lemma global_empty : w (fun _ => false) = 0 := by
  unfold w
  exact_mod_cast global_certificate.2.1

lemma global_moments (T : Finset (Fin 6)) (hT : T.Nonempty) :
    |(∑ ω, w ω * hitMonomial T ω) - 100 * ∏ i ∈ T, q i| ≤ 1 := by
  have hh : |(∑ ω, (globalWeight ω : ℝ) * (hitRat T ω : ℝ)) -
      100 * ∏ i ∈ T, (qRat i : ℝ)| ≤ 1 := by
    exact_mod_cast global_certificate.2.2.1 T hT
  simpa only [cast_hitRat, w, q] using hh

lemma global_dual_value : (∑ ω, w ω) = 6839 / 54 := by
  unfold w
  have h := congrArg (fun x : ℚ => (x : ℝ)) global_certificate.2.2.2
  push_cast at h
  exact h

/-- Exact global optimality among ALL real coverage-majorant polynomials. -/
theorem global_optimal (b : Finset (Fin 6) → ℝ) (hb : IsCoverageMajorant b) :
    booleanObjective q 100 a ≤ booleanObjective q 100 b := by
  rw [primal_objective, ← global_dual_value]
  exact coverageObjective_dual_bound q 100 w global_nonnegative global_empty global_moments b hb

/-- An objective lower bound for EVERY normalized signed first-hit family. -/
theorem all_firstHit_lower_bound (c : Fin 6 → Finset (Fin 6) → ℝ)
    (hc : ∀ i, (∑ Q : Finset (Fin 6), c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    (385 / 3 : ℝ) ≤ ∑ i, booleanKernelObjective q (100 * q i) (c i) := by
  rw [← prefix_dual_value]
  exact firstHit_objective_dual_bound q 100 u prefix_dual_feasible c hc hprior

/-- The global method beats every first-hit family by at least91/54 in this
finite equal-marginal example. No distinct-prime or asymptotic claim is made. -/
theorem strict_method_gap (c : Fin 6 → Finset (Fin 6) → ℝ)
    (hc : ∀ i, (∑ Q : Finset (Fin 6), c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    booleanObjective q 100 a + 91 / 54 ≤
      ∑ i, booleanKernelObjective q (100 * q i) (c i) := by
  have hh := all_firstHit_lower_bound c hc hprior
  rw [primal_objective]
  linarith

#print axioms prefix_certificate
#print axioms global_certificate
#print axioms primal_certificate
#print axioms global_optimal
#print axioms strict_method_gap
end Erdos970.FiniteSelberg.CoupledExample
