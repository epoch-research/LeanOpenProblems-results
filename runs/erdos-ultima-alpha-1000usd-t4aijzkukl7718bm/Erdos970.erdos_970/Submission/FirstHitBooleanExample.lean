import Submission.FirstHitDisjointCost

/-! A small exact separation between the Boolean-reduced and old square-cost
first-hit criteria. This is not an asymptotic or optimality result. -/
namespace Erdos970.FiniteSelberg.BooleanExample
open Finset

noncomputable def q (i : Fin 2) : ℝ := if i = 0 then 1 / 2 else 1 / 3
noncomputable def c (i : Fin 2) (Q : Finset (Fin 2)) : ℝ :=
  if i = 0 then (if Q = ∅ then 1 else 0)
  else if Q ⊆ {0} then 1 / 2 else 0

lemma patterns : (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by
  decide

lemma sum_patterns (f : Finset (Fin 2) → ℝ) :
    (∑ Q : Finset (Fin 2), f Q) = f ∅ + (f {0} + (f {1} + f {0, 1})) := by
  rw [patterns, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]

lemma normalized : ∀ i, (∑ Q : Finset (Fin 2), c i Q) = 1 := by
  intro i
  rw [sum_patterns]
  fin_cases i <;> norm_num [c, Finset.ext_iff, Fin.forall_fin_succ]

lemma prior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i := by
  intro i Q hQ j hj
  fin_cases i
  · have hzero : Q = ∅ := by
      by_contra hn
      simp [c, hn] at hQ
    simp [hzero] at hj
  · have hsub : Q ⊆ {0} := by
      by_contra hn
      simp [c, hn] at hQ
    have hj0 : j = 0 := mem_singleton.mp (hsub hj)
    subst j
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- At m=12 the new left side is 11, but the old left side is 13. -/
theorem exact_objectives :
    (∑ i : Fin 2, ((12 : ℝ) * q i *
      (∑ Q : Finset (Fin 2), c i Q ^ 2 * variance q Q) +
        booleanSquareCost (ordinaryCoefficient q (c i)))) = 11 ∧
    (∑ i : Fin 2, ((12 : ℝ) * q i *
      (∑ Q : Finset (Fin 2), c i Q ^ 2 * variance q Q) + kernelCost q (c i) ^ 2)) = 13 := by
  norm_num [booleanSquareCost, booleanSquareCoefficient, kernelCost,
    ordinaryCoefficient, sum_patterns, Fin.sum_univ_succ, c, q, variance, Finset.ext_iff, Fin.forall_fin_succ]

/-- This exact example satisfies the new criterion, even though it fails the old one. -/
theorem strict_improvement :
    (∑ i : Fin 2, ((12 : ℝ) * q i *
      (∑ Q : Finset (Fin 2), c i Q ^ 2 * variance q Q) +
        booleanSquareCost (ordinaryCoefficient q (c i)))) < 12 ∧
    ¬(∑ i : Fin 2, ((12 : ℝ) * q i *
      (∑ Q : Finset (Fin 2), c i Q ^ 2 * variance q Q) + kernelCost q (c i) ^ 2)) < 12 := by
  rw [exact_objectives.1, exact_objectives.2]
  norm_num

/-- The certified improvement applies to every population with these moment bounds. -/
theorem survivor (ω : ℕ → Fin 2 → Bool)
    (herr : ∀ T : Finset (Fin 2),
      |(∑ j ∈ range 12, hitMonomial T (ω j)) - (12 : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    ∃ j < 12, ∀ i, ω j i = false := by
  apply survivor_of_first_hit_boolean_cost q _ c normalized prior 12 ω herr
  · exact strict_improvement.1
  · intro i
    fin_cases i <;> norm_num [q]

#print axioms exact_objectives
#print axioms survivor
end Erdos970.FiniteSelberg.BooleanExample
