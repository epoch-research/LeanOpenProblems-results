import Submission.BooleanKernelDuality
import Submission.BooleanKernelUpperWeights

/-! An exact global optimum for the Boolean upper-weight problem at the first
six primes and X=1000. The LP solver output is independently checked in Lean.
This is a finite result, not a uniform Jacobsthal bound. -/
namespace Erdos970.FiniteSelberg.BooleanOptimum
open Finset

def prime : Fin 6 → ℕ := ![2, 3, 5, 7, 11, 13]
def qRat (i : Fin 6) : ℚ := 1 / prime i

def subsetCode (T : Finset (Fin 6)) : ℕ := ∑ i ∈ T, 2 ^ i.val
def patternCode (ω : Fin 6 → Bool) : ℕ := ∑ i, if ω i then 2 ^ i.val else 0

def aCode : ℕ → ℚ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => 1
  | 4 => -1
  | 5 => 1
  | 6 => 1
  | 7 => -1
  | 8 => -1
  | 9 => 1
  | 10 => 1
  | 11 => -1
  | 12 => 1
  | 13 => -1
  | 14 => -1
  | 15 => 1
  | 16 => -1
  | 17 => 1
  | 18 => 1
  | 19 => -1
  | 20 => 1
  | 21 => -1
  | 22 => -1
  | 23 => 1
  | 24 => 1
  | 25 => -1
  | 26 => -1
  | 27 => 1
  | _ => 0

def wCode : ℕ → ℚ
  | 0 => 54668 / 231
  | 1 => 508558 / 3003
  | 2 => 75984 / 1001
  | 3 => 105401 / 1001
  | 4 => 29984 / 1001
  | 5 => 169406 / 3003
  | 6 => 94954 / 3003
  | 7 => 62812 / 3003
  | 8 => 44294 / 3003
  | 9 => 124109 / 3003
  | 10 => 484 / 21
  | 11 => 13004 / 1001
  | 12 => 284 / 21
  | 13 => 16409 / 3003
  | 14 => 6364 / 3003
  | 15 => 883 / 231
  | 16 => 7258 / 3003
  | 17 => 3929 / 143
  | 18 => 532 / 33
  | 19 => 19106 / 3003
  | 20 => 332 / 33
  | 21 => 2501 / 1001
  | 22 => 200 / 231
  | 23 => 471 / 143
  | 24 => 1924 / 231
  | 27 => 7291 / 3003
  | 29 => 3494 / 3003
  | 30 => 38 / 231
  | 31 => 316 / 429
  | 33 => 10187 / 429
  | 34 => 556 / 39
  | 35 => 482 / 91
  | 36 => 356 / 39
  | 37 => 6703 / 3003
  | 38 => 86 / 1001
  | 39 => 1013 / 429
  | 40 => 3010 / 429
  | 43 => 4891 / 3003
  | 45 => 498 / 1001
  | 46 => 1436 / 3003
  | 47 => 172 / 143
  | 48 => 786 / 143
  | 51 => 571 / 429
  | 57 => 329 / 429
  | 61 => 57 / 143
  | _ => 0

def aRat (T : Finset (Fin 6)) : ℚ := aCode (subsetCode T)
def wRat (ω : Fin 6 → Bool) : ℚ := wCode (patternCode ω)
def hitRat (T : Finset (Fin 6)) (ω : Fin 6 → Bool) : ℚ :=
  if ∀ i ∈ T, ω i = true then 1 else 0
def valueRat (ω : Fin 6 → Bool) : ℚ := ∑ T : Finset (Fin 6), aRat T * hitRat T ω

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All feasibility conditions and the matching objective are kernel checked. -/
theorem rational_certificate :
    (∀ ω : Fin 6 → Bool, 0 ≤ wRat ω) ∧
    (∀ T : Finset (Fin 6),
      |(∑ ω, wRat ω * hitRat T ω) - 1000 * ∏ i ∈ T, qRat i| ≤ 1) ∧
    (∀ ω : Fin 6 → Bool, 0 ≤ valueRat ω) ∧
    valueRat (fun _ => false) = 1 ∧
    (1000 * (∑ T : Finset (Fin 6), aRat T * ∏ i ∈ T, qRat i) +
      ∑ T : Finset (Fin 6), |aRat T|) = 54668 / 231 ∧
    wRat (fun _ => false) = 54668 / 231 := by
  decide +kernel

noncomputable def q (i : Fin 6) : ℝ := qRat i
noncomputable def a (T : Finset (Fin 6)) : ℝ := aRat T
noncomputable def w (ω : Fin 6 → Bool) : ℝ := wRat ω

lemma cast_hitRat (T : Finset (Fin 6)) (ω : Fin 6 → Bool) :
    (hitRat T ω : ℝ) = hitMonomial T ω := by
  rw [hitMonomial_eq]
  simp only [hitRat]
  split_ifs <;> norm_num

lemma cast_valueRat (ω : Fin 6 → Bool) :
    (valueRat ω : ℝ) = booleanValue a ω := by
  simp only [valueRat, Rat.cast_sum, Rat.cast_mul, cast_hitRat, booleanValue, a]

lemma dual_feasible : BooleanDualFeasible q 1000 w := by
  constructor
  · intro ω
    change (0 : ℝ) ≤ (wRat ω : ℝ)
    exact_mod_cast rational_certificate.1 ω
  · intro T
    have hr : |(∑ ω, (wRat ω : ℝ) * (hitRat T ω : ℝ)) -
        1000 * ∏ i ∈ T, (qRat i : ℝ)| ≤ 1 := by
      exact_mod_cast rational_certificate.2.1 T
    simpa only [cast_hitRat, q, w] using hr

lemma weight_nonnegative (ω : Fin 6 → Bool) : 0 ≤ booleanValue a ω := by
  rw [← cast_valueRat]
  exact_mod_cast rational_certificate.2.2.1 ω

lemma weight_normalized : booleanValue a (fun _ => false) = 1 := by
  rw [← cast_valueRat]
  exact_mod_cast rational_certificate.2.2.2.1

lemma exact_objective : booleanObjective q 1000 a = 54668 / 231 := by
  unfold booleanObjective q a
  have h := congrArg (fun x : ℚ => (x : ℝ)) rational_certificate.2.2.2.2.1
  push_cast at h
  exact h

lemma dual_value : w (fun _ => false) = 54668 / 231 := by
  unfold w
  have h := congrArg (fun x : ℚ => (x : ℝ)) rational_certificate.2.2.2.2.2
  push_cast at h
  exact h

/-- The exact global optimum over ALL normalized nonnegative Boolean upper weights. -/
theorem global_upper_weight_optimum (b : Finset (Fin 6) → ℝ)
    (hb : ∀ ω, 0 ≤ booleanValue b ω) (h0 : booleanValue b (fun _ => false) = 1) :
    (54668 / 231 : ℝ) ≤ booleanObjective q 1000 b := by
  rw [← dual_value]
  exact booleanObjective_dual_bound q 1000 w dual_feasible b hb h0

lemma marginal_bounds (i : Fin 6) : 0 < q i ∧ q i < 1 := by
  fin_cases i <;> norm_num [q, qRat, prime]

/-- The same optimum is attained by a signed orthogonal kernel, and no normalized
kernel on the complete six-coordinate cube can do better. -/
theorem global_kernel_optimum :
    (∃ c : Finset (Fin 6) → ℝ, (∑ Q : Finset (Fin 6), c Q) = 1 ∧
      booleanKernelObjective q 1000 c = 54668 / 231) ∧
    ∀ c : Finset (Fin 6) → ℝ, (∑ Q : Finset (Fin 6), c Q) = 1 →
      (54668 / 231 : ℝ) ≤ booleanKernelObjective q 1000 c := by
  constructor
  · obtain ⟨c, hc, he⟩ := upperWeight_objective_attained q marginal_bounds 1000 a
      weight_nonnegative weight_normalized
    exact ⟨c, hc, he.trans exact_objective⟩
  · intro c hc
    rw [← dual_value]
    exact booleanKernelObjective_dual_bound q 1000 w dual_feasible c hc

#print axioms rational_certificate
#print axioms global_upper_weight_optimum
#print axioms global_kernel_optimum
end Erdos970.FiniteSelberg.BooleanOptimum
