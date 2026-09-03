import Submission.BooleanKernelDuality

/-! A cover-majorant criterion with merged coefficients, convexity of its exact
objective, and a necessary endpoint inequality for any single-order first-hit sum.
No uniform asymptotic estimate is asserted. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An arbitrary majorant of the nonempty hit patterns yields a survivor whenever
its mean plus its merged coefficient cost is smaller than the population. -/
theorem survivor_of_boolean_cover (q : ι → ℝ) (a : Finset ι → ℝ)
    (ha : ∀ v, v ≠ (fun _ => false) → 1 ≤ booleanValue a v)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : booleanObjective q m a < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ range m, booleanValue a (ω j) := by
    calc
      _ = ∑ j ∈ range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply ha
        intro heq
        obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
        exact hi (congrFun heq i)
  have he := finite_polynomial_interval_error univ a id q m ω herr
  have havg : average q (fun v => ∑ T : Finset ι, a T * hitMonomial T v) =
      ∑ T : Finset ι, a T * ∏ i ∈ T, q i := by
    rw [average_sum]
    simp only [average_mul_const, average_hitMonomial]
  dsimp only [id_eq] at he
  rw [havg] at he
  change |(∑ j ∈ range m, booleanValue a (ω j)) -
      (m : ℝ) * (∑ T : Finset ι, a T * ∏ i ∈ T, q i)| ≤ ∑ T : Finset ι, |a T| at he
  unfold booleanObjective at hmain
  linarith [(abs_le.mp he).2]

noncomputable def coefficientMixture (w : κ → ℝ) (a : κ → Finset ι → ℝ)
    (T : Finset ι) : ℝ := ∑ j, w j * a j T

lemma booleanValue_mixture (w : κ → ℝ) (a : κ → Finset ι → ℝ) (v : ι → Bool) :
    booleanValue (coefficientMixture w a) v = ∑ j, w j * booleanValue (a j) v := by
  classical
  simp only [booleanValue, coefficientMixture, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro T hT
  ring

lemma coefficientMixture_cover (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : (∑ j, w j) = 1) (a : κ → Finset ι → ℝ)
    (ha : ∀ j v, v ≠ (fun _ => false) → 1 ≤ booleanValue (a j) v)
    (v : ι → Bool) (hv : v ≠ (fun _ => false)) :
    1 ≤ booleanValue (coefficientMixture w a) v := by
  classical
  rw [booleanValue_mixture, ← hs]
  apply sum_le_sum
  intro j hj
  simpa using mul_le_mul_of_nonneg_left (ha j v hv) (hw j)

lemma coefficientMixture_cost_le (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (a : κ → Finset ι → ℝ) :
    (∑ T : Finset ι, |coefficientMixture w a T|) ≤
      ∑ j, w j * ∑ T : Finset ι, |a j T| := by
  classical
  simp only [coefficientMixture, mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro T hT
  calc
    _ ≤ ∑ j, |w j * a j T| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (hw _)]

lemma booleanObjective_mixture_le (q : ι → ℝ) (X : ℝ)
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (a : κ → Finset ι → ℝ) :
    booleanObjective q X (coefficientMixture w a) ≤
      ∑ j, w j * booleanObjective q X (a j) := by
  classical
  have hmean : (∑ T : Finset ι, coefficientMixture w a T * ∏ i ∈ T, q i) =
      ∑ j, w j * ∑ T : Finset ι, a j T * ∏ i ∈ T, q i := by
    simp only [coefficientMixture, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro T hT
    ring
  have he : X * (∑ T : Finset ι, coefficientMixture w a T * ∏ i ∈ T, q i) =
      ∑ j, w j * (X * ∑ T : Finset ι, a j T * ∏ i ∈ T, q i) := by
    rw [hmean, mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  simp only [booleanObjective, mul_add, sum_add_distrib]
  rw [he]
  exact add_le_add (le_refl _) (coefficientMixture_cost_le w hw a)

/-- A fixed-order first-hit sum. Its stage weight depends only on earlier bits.
Weights need not be squares, nor have any normalization, for the endpoint lemma. -/
noncomputable def orderedHitValue {n : ℕ} (e : Fin n ≃ ι)
    (W : Fin n → (ι → Bool) → ℝ) (v : ι → Bool) : ℝ :=
  ∑ i, (if v (e i) then (1 : ℝ) else 0) * W i v

def PrefixDependent {n : ℕ} (e : Fin n ≃ ι)
    (W : Fin n → (ι → Bool) → ℝ) : Prop :=
  ∀ i v u, (∀ l, l < i → v (e l) = u (e l)) → W i v = W i u

/-- Switching on the last coordinate cannot decrease a nonnegative first-hit sum. -/
theorem orderedHitValue_last_le {n : ℕ} (e : Fin (n+1) ≃ ι)
    (W : Fin (n+1) → (ι → Bool) → ℝ) (hW : ∀ i v, 0 ≤ W i v)
    (hprior : PrefixDependent e W) :
    orderedHitValue e W (fun j => decide (j ≠ e (Fin.last n))) ≤
      orderedHitValue e W (fun _ => true) := by
  classical
  apply sum_le_sum
  intro i hi
  by_cases he : i = Fin.last n
  · subst i
    simpa using hW (Fin.last n) (fun _ => true)
  · have hi' : e i ≠ e (Fin.last n) := fun h => he (e.injective h)
    have hp : W i (fun j => decide (j ≠ e (Fin.last n))) = W i (fun _ => true) := by
      apply hprior
      intro l hl
      have hl' : e l ≠ e (Fin.last n) := by
        intro h
        have hh := e.injective h
        have hle : i ≤ Fin.last n := Fin.le_last i
        exact (not_lt_of_ge hle) (hh ▸ hl)
      simp [hl']
    rw [hp]
    simp [hi']

#print axioms survivor_of_boolean_cover
#print axioms booleanObjective_mixture_le
#print axioms orderedHitValue_last_le
end Erdos970.FiniteSelberg
