import Submission.OrderMixtureCriterion

/-! A three-coordinate exact example. Different orders can cancel coefficient
costs, and their average need not admit any one-order representation.
The displayed sieve comparison is only with the three chosen components, not
with the optimum single-order sieve or the simple union bound. -/
namespace Erdos970.FiniteSelberg.OrderMixtureExample
open Finset
abbrev Pattern := Finset (Fin 3)

def component (j : Fin 3) (T : Pattern) : ℚ :=
  if T.card = 1 then 1 else if T.card = 2 then (if j ∈ T then 1 else -1)
    else if T.card = 3 then -3 else 0

def mixed (T : Pattern) : ℚ :=
  if T.card = 1 then 1 else if T.card = 2 then 1/3
    else if T.card = 3 then -3 else 0

def bit (b : Bool) : ℚ := if b then 1 else 0

def value (a : Pattern → ℚ) (v : Fin 3 → Bool) : ℚ :=
  ∑ T : Pattern, a T * ∏ i ∈ T, bit (v i)

def cost (a : Pattern → ℚ) : ℚ := ∑ T : Pattern, |a T|

def q : Fin 3 → ℚ := ![1/5, 1/7, 1/11]

def mean (a : Pattern → ℚ) : ℚ := ∑ T : Pattern, a T * ∏ i ∈ T, q i

def objective (a : Pattern → ℚ) : ℚ := 15 * mean a + cost a

def order (j : Fin 3) : Equiv.Perm (Fin 3) := Equiv.swap 2 j

def stageWeight (j i : Fin 3) (v : Fin 3 → Bool) : ℚ :=
  if i = 0 then 1 else if i = 1 then 1 - bit (v (order j 0))
    else 1 + bit (v (order j 0)) + bit (v (order j 1)) -
      3 * bit (v (order j 0)) * bit (v (order j 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_tables :
    (∀ T, mixed T = ∑ j : Fin 3, (1/3 : ℚ) * component j T) ∧
    (∀ j, cost (component j) = 9) ∧ cost mixed = 7 ∧
    (∀ j v, v ≠ (fun _ => false) → 1 ≤ value (component j) v) ∧
    (∀ v, v ≠ (fun _ => false) → 1 ≤ value mixed v) ∧
    value mixed (fun _ => true) = 1 ∧
    (∀ j, value mixed (fun l => decide (l ≠ j)) = 7/3) ∧
    mean mixed = 103/231 ∧ objective mixed = 1054/77 ∧
    objective mixed < 15 ∧
    (∀ j, 15 < objective (component j)) ∧
    (∀ j, order j 2 = j) ∧
    (∀ j i v, 0 ≤ stageWeight j i v) ∧
    (∀ j i, stageWeight j i (fun _ => false) = 1) ∧
    (∀ j i v u, (∀ l, l < i → v (order j l) = u (order j l)) →
      stageWeight j i v = stageWeight j i u) ∧
    (∀ j v, value (component j) v =
      ∑ i : Fin 3, bit (v (order j i)) * stageWeight j i v) := by
  decide +kernel

lemma cast_value (a : Pattern → ℚ) (v : Fin 3 → Bool) :
    booleanValue (fun T => (a T : ℝ)) v = (value a v : ℝ) := by
  simp only [booleanValue, value, hitMonomial, bit, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_prod, apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_one, Rat.cast_zero]

lemma cast_objective (a : Pattern → ℚ) :
    booleanObjective (fun i => (q i : ℝ)) 15 (fun T => (a T : ℝ)) =
      (objective a : ℝ) := by
  simp only [booleanObjective, objective, mean, cost, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_sum, Rat.cast_prod, Rat.cast_abs]

/-- The component polynomials are actual normalized nonnegative first-hit
majorants in their respective orders. -/
theorem components_first_hit (j : Fin 3) :
    (∀ i v, 0 ≤ (stageWeight j i v : ℝ)) ∧
    (∀ i, (stageWeight j i (fun _ => false) : ℝ) = 1) ∧
    PrefixDependent (order j) (fun i v => (stageWeight j i v : ℝ)) ∧
    (∀ v, booleanValue (fun T => (component j T : ℝ)) v =
      orderedHitValue (order j) (fun i v => (stageWeight j i v : ℝ)) v) := by
  rcases exact_tables with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnonneg, hnorm, hprior, heq⟩
  refine ⟨fun i v => by exact_mod_cast hnonneg j i v,
    fun i => by exact_mod_cast hnorm j i, ?_, ?_⟩
  · intro i v u h
    exact congrArg (fun x : ℚ => (x : ℝ)) (hprior j i v u h)
  · intro v
    rw [cast_value, heq j v]
    simp only [orderedHitValue, Rat.cast_sum, Rat.cast_mul, bit,
      apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_one, Rat.cast_zero]

theorem mixed_coefficients :
    coefficientMixture (fun _ : Fin 3 => (1/3 : ℝ))
      (fun j T => (component j T : ℝ)) = fun T => (mixed T : ℝ) := by
  funext T
  have h := congrArg (fun x : ℚ => (x : ℝ)) (exact_tables.1 T)
  simpa only [coefficientMixture, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using h.symm

/-- Cancellation is strict: the merged cost is seven, not nine. -/
theorem strict_cost_cancellation :
    (∑ T : Pattern, |(mixed T : ℝ)|) = 7 ∧
    (∀ j, (∑ T : Pattern, |(component j T : ℝ)|) = 9) := by
  constructor
  · have h := congrArg (fun x : ℚ => (x : ℝ)) exact_tables.2.2.1
    simpa only [cost, Rat.cast_sum, Rat.cast_abs, Rat.cast_ofNat] using h
  · intro j
    have h := congrArg (fun x : ℚ => (x : ℝ)) (exact_tables.2.1 j)
    simpa only [cost, Rat.cast_sum, Rat.cast_abs, Rat.cast_ofNat] using h

/-- The average is not a first-hit sum in any one order, even with arbitrary
nonnegative prefix-dependent weights and without a normalization requirement. -/
theorem mixed_not_single_order :
    ¬ ∃ (e : Equiv.Perm (Fin 3)) (W : Fin 3 → (Fin 3 → Bool) → ℝ),
      (∀ i v, 0 ≤ W i v) ∧ PrefixDependent e W ∧
      ∀ v, booleanValue (fun T => (mixed T : ℝ)) v = orderedHitValue e W v := by
  rintro ⟨e, W, hW, hprior, hval⟩
  have h := orderedHitValue_last_le (n := 2) e W hW hprior
  rw [← hval, ← hval, cast_value, cast_value] at h
  rcases exact_tables with ⟨_, _, _, _, _, htop, hminus, _⟩
  rw [htop, hminus] at h
  norm_num at h

/-- The mixed criterion succeeds where each of these three chosen components
fails. This does not compare with the best single-order construction. -/
theorem mixed_criterion_succeeds :
    booleanObjective (fun i => (q i : ℝ)) 15 (fun T => (mixed T : ℝ)) < 15 ∧
    ∀ j, 15 < booleanObjective (fun i => (q i : ℝ)) 15
      (fun T => (component j T : ℝ)) := by
  rcases exact_tables with ⟨_, _, _, _, _, _, _, _, _, hm, hc, _⟩
  constructor
  · rw [cast_objective]
    exact_mod_cast hm
  · intro j
    rw [cast_objective]
    exact_mod_cast hc j

theorem mixed_survivor (ω : ℕ → Fin 3 → Bool)
    (herr : ∀ T : Pattern,
      |(∑ j ∈ range 15, hitMonomial T (ω j)) - (15 : ℝ) *
        ∏ i ∈ T, (q i : ℝ)| ≤ 1) :
    ∃ j < 15, ∀ i, ω j i = false := by
  apply survivor_of_boolean_cover (fun i => (q i : ℝ))
    (fun T => (mixed T : ℝ)) _ 15 ω herr mixed_criterion_succeeds.1
  intro v hv
  rw [cast_value]
  exact_mod_cast exact_tables.2.2.2.2.1 v hv

#print axioms exact_tables
#print axioms components_first_hit
#print axioms mixed_not_single_order
#print axioms mixed_survivor
end Erdos970.FiniteSelberg.OrderMixtureExample
