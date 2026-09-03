import Submission.RecursiveSieveRational

/-! An exact finite improvement on the unstructured first-hit envelope at
specified rational marginals. These are NOT the first-prime marginals, and
this example is not a proof or disproof of the Jacobsthal conjecture. -/
namespace Erdos970.FirstHitOptimalityExample
open FiniteSelberg RecursiveSieve

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Reciprocal denominators 3,16/5,37/10,9/2,9,23/2,14,20. -/
def qNat : ℕ → ℚ
  | 0 => 1 / 3
  | 1 => 5 / 16
  | 2 => 10 / 37
  | 3 => 2 / 9
  | 4 => 1 / 9
  | 5 => 2 / 23
  | 6 => 1 / 14
  | 7 => 1 / 20
  | _ => 0

/-- The polynomial is
`prod_{i<4}(1-Xi) - X4*(H-2)*(H-3)/6
 - sum_{5<=i<8} Xi*(1-X0)*(1-X1)`, where `H=sum_{i<4} Xi`.
The middle upper weight is nonnegative at every integer hit count. -/
def data : Fin 39 → Finset (Fin 8) × ℚ :=
  ![(∅, 1),
    ({0}, -1),
    ({1}, -1),
    ({0, 1}, 1),
    ({2}, -1),
    ({0, 2}, 1),
    ({1, 2}, 1),
    ({0, 1, 2}, -1),
    ({3}, -1),
    ({0, 3}, 1),
    ({1, 3}, 1),
    ({0, 1, 3}, -1),
    ({2, 3}, 1),
    ({0, 2, 3}, -1),
    ({1, 2, 3}, -1),
    ({0, 1, 2, 3}, 1),
    ({4}, -1),
    ({0, 4}, 2 / 3),
    ({1, 4}, 2 / 3),
    ({0, 1, 4}, -1 / 3),
    ({2, 4}, 2 / 3),
    ({0, 2, 4}, -1 / 3),
    ({1, 2, 4}, -1 / 3),
    ({3, 4}, 2 / 3),
    ({0, 3, 4}, -1 / 3),
    ({1, 3, 4}, -1 / 3),
    ({2, 3, 4}, -1 / 3),
    ({5}, -1),
    ({0, 5}, 1),
    ({1, 5}, 1),
    ({0, 1, 5}, -1),
    ({6}, -1),
    ({0, 6}, 1),
    ({1, 6}, 1),
    ({0, 1, 6}, -1),
    ({7}, -1),
    ({0, 7}, 1),
    ({1, 7}, 1),
    ({0, 1, 7}, -1)]

def coefficient (a : Fin 39) : ℚ := (data a).2

def support (a : Fin 39) : Finset (Fin 8) := (data a).1

def rationalValue (ω : Fin 8 → Bool) : ℚ :=
  ∑ a : Fin 39, coefficient a * if ∀ i ∈ support a, ω i = true then 1 else 0

/-- Kernel-checked pointwise lower-sieve condition on all 256 hit patterns. -/
theorem pointwise : ∀ ω : Fin 8 → Bool, ω ≠ (fun _ => false) → rationalValue ω ≤ 0 := by
  decide +kernel

/-- The full coefficient error is charged, including the constant coefficient. -/
theorem mean_cost :
    (∑ a : Fin 39, coefficient a * ∏ i ∈ support a, qNat i.val) =
      (83359379 / 694824480 : ℚ) ∧
    (∑ a : Fin 39, |coefficient a|) = (101 / 3 : ℚ) := by
  decide +kernel

theorem positive_margin :
    (∑ a : Fin 39, |coefficient a|) < (281 : ℚ) *
      ∑ a : Fin 39, coefficient a * ∏ i ∈ support a, qNat i.val := by
  rw [mean_cost.1, mean_cost.2]
  norm_num

/-- At exactly the same mass and marginals the old first-hit lower envelope
returns zero. The new certificate is therefore a strict method improvement. -/
theorem rational_recurrence_zero : (linearEnvelope qNat 8 (281 : ℚ)).1 = 0 := by
  decide +kernel

lemma cast_value (ω : Fin 8 → Bool) :
    (rationalValue ω : ℝ) =
      ∑ a : Fin 39, (coefficient a : ℝ) * hitMonomial (support a) ω := by
  simp only [rationalValue, Rat.cast_sum, Rat.cast_mul, hitMonomial_eq,
    apply_ite (fun x : ℚ => (x : ℝ)), Rat.cast_one, Rat.cast_zero]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> norm_num

theorem pointwise_real (ω : Fin 8 → Bool) (hω : ω ≠ (fun _ => false)) :
    (∑ a : Fin 39, (coefficient a : ℝ) * hitMonomial (support a) ω) ≤ 0 := by
  rw [← cast_value]
  exact_mod_cast pointwise ω hω

theorem positive_margin_real :
    (∑ a : Fin 39, |(coefficient a : ℝ)|) < (281 : ℝ) *
      ∑ a : Fin 39, (coefficient a : ℝ) * ∏ i ∈ support a, (qNat i.val : ℝ) := by
  exact_mod_cast positive_margin

theorem real_recurrence_zero :
    (linearEnvelope (fun i => (qNat i : ℝ)) 8 (281 : ℝ)).1 = 0 := by
  have hh := congrArg Prod.fst (cast_linearEnvelope qNat 8 (281 : ℚ))
  simp only [Prod.map_fst, rational_recurrence_zero, Rat.cast_zero] at hh
  simpa using hh.symm

/-- Unlike the old recursive lower value, the displayed polynomial really
forces a survivor from the same uniform unit-error moment assumptions. -/
theorem survivor_by_polynomial (ω : ℕ → Fin 8 → Bool)
    (herr : ∀ T : Finset (Fin 8),
      |(∑ j ∈ Finset.range 281, hitMonomial T (ω j)) -
        (281 : ℝ) * ∏ i ∈ T, (qNat i.val : ℝ)| ≤ 1) :
    ∃ j < 281, ∀ i, ω j i = false := by
  have hq : ∀ i : Fin 8, (qNat i.val : ℝ) < 1 ∧
      (qNat i.val : ℝ) ≤ (qNat i.val : ℝ) ∧ (qNat i.val : ℝ) ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [qNat]
  exact survivor_from_dominating_moments (Finset.univ : Finset (Fin 39))
    (fun a => (coefficient a : ℝ)) support
    (fun i : Fin 8 => (qNat i.val : ℝ)) (fun i : Fin 8 => (qNat i.val : ℝ))
    hq 281 ω herr pointwise_real positive_margin_real

#print axioms pointwise
#print axioms mean_cost
#print axioms rational_recurrence_zero
#print axioms real_recurrence_zero
#print axioms survivor_by_polynomial
end Erdos970.FirstHitOptimalityExample
