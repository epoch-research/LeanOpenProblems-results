import Submission.ConditionalExitMeasure
import Submission.TernaryCurrentRealization

/-! An actual probability measure avoiding the specified ternary/five-adic
stem construction. No assertion is made for other current residue families. -/
namespace Erdos7CombCurrentMeasure
open scoped BigOperators
open Erdos7ConditionalExitMeasure Erdos7TernaryCurrentRealization
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The three conditioned exit digits are1,2,3. -/
def exitDigit (c : Fin 3) : Fin 5 := ⟨c.val+1, by omega⟩
def rowDigit (u : Fin 4) : Fin 5 := ⟨(label u).val, by have := (label u).isLt; omega⟩

lemma exit_ne_stem (c : Fin 3) : exitDigit c ≠ (4 : Fin 5) := by
  intro h
  have hh := congrArg Fin.val h
  have := c.isLt
  simp only [exitDigit, Fin.val_mk] at hh
  omega

lemma row_ne_stem (u : Fin 4) : rowDigit u ≠ (4 : Fin 5) := by
  intro h
  have hh := congrArg Fin.val h
  have := (label u).isLt
  simp only [rowDigit, Fin.val_mk] at hh
  omega

lemma code_firstExit {E : ℕ} (u : Fin 4) (b : Fin E) (y : Fin E → Fin 5)
    (hcode : codeEvent (label u) b y) : firstExit (4 : Fin 5) E y = some (rowDigit u) := by
  apply firstExit_of_stop (4 : Fin 5) (rowDigit u) (row_ne_stem u) b y
  · intro j hj
    have he : j ≠ b := by intro h; subst j; omega
    have hh := hcode j (by omega)
    rw [if_neg he] at hh
    exact Fin.ext hh
  · have hh := hcode b le_rfl
    simp only [ite_true] at hh
    exact Fin.ext hh

lemma conditioned_zero_of_code {E : ℕ} (u : Fin 4) (c : Fin 3) (b : Fin E)
    (y : Fin E → Fin 5) (hcode : codeEvent (label u) b y)
    (hne : (label u).val ≠ c.val+1) : density (4 : Fin 5) (exitDigit c) y = 0 := by
  have hd : rowDigit u ≠ exitDigit c := by
    intro h
    exact hne (congrArg Fin.val h)
  simp only [density, raw_classified, code_firstExit u b y hcode, if_neg hd,
    Nat.cast_zero, zero_div]

/-- Mix the conditioned measures with arbitrary nonnegative coarse weights. -/
def mixed {E : ℕ} (μ : Fin 27 → Fin 3 → ℚ)
    (z : Fin 27 × (Fin E → Fin 5)) : ℚ :=
  ∑ c : Fin 3, μ z.1 c * density (4 : Fin 5) (exitDigit c) z.2

lemma mixed_nonneg {E : ℕ} (μ : Fin 27 → Fin 3 → ℚ) (hμ : ∀ x c, 0 ≤ μ x c)
    (z : Fin 27 × (Fin E → Fin 5)) : 0 ≤ mixed μ z := by
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ z.1 c) (density_nonneg _ _ _))

lemma mixed_mass (E : ℕ) (μ : Fin 27 → Fin 3 → ℚ) :
    (∑ z : Fin 27 × (Fin E → Fin 5), mixed μ z) = ∑ x, ∑ c, μ x c := by
  simp only [mixed, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum, density_mass (by omega) _ _ (exit_ne_stem c), mul_one]

/-- Coarse support is sufficient for avoidance of all current five-adic
classes, including every deeper level, without discarding the stem. -/
theorem mixed_avoids_current {E : ℕ} (μ : Fin 27 → Fin 3 → ℚ)
    (hsupp : ∀ x c, μ x c ≠ 0 → coarseAllowed x c)
    (x : Fin 27) (y : Fin E → Fin 5) (hbad : y ∈ badFiber x) : mixed μ (x,y) = 0 := by
  classical
  obtain ⟨⟨u,b⟩, _, h⟩ := Finset.mem_biUnion.mp hbad
  obtain ⟨_, ho, hc⟩ := Finset.mem_filter.mp h
  apply Finset.sum_eq_zero
  intro c _
  by_cases hμ : μ x c = 0
  · simp only [hμ, zero_mul]
  · have hd := coarse_disjoint_row x c u (hsupp x c hμ) ho
    rw [conditioned_zero_of_code u c b y hc hd, mul_zero]

theorem mixed_avoids_pure {E : ℕ} (μ : Fin 27 → Fin 3 → ℚ)
    (hsupp : ∀ x c, μ x c ≠ 0 → coarseAllowed x c)
    (x : Fin 27) (y : Fin E → Fin 5) (hx : ¬ survivor x) : mixed μ (x,y) = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  have hμ : μ x c = 0 := by
    by_contra h
    exact hx (hsupp x c h).1
  simp only [hμ, zero_mul]

/-- The normalized coarse weights give a genuine finite avoiding probability
measure. This concerns only the stated partial family; it is not a full
covering-system obstruction or a conjecture settlement. -/
theorem admissible_probability (E : ℕ) (μ : Fin 27 → Fin 3 → ℚ)
    (hμ : ∀ x c, 0 ≤ μ x c) (hmass : (∑ x, ∑ c, μ x c) = 1)
    (hsupp : ∀ x c, μ x c ≠ 0 → coarseAllowed x c) :
    ∃ ν : Fin 27 × (Fin E → Fin 5) → ℚ,
      (∀ z, 0 ≤ ν z) ∧ (∑ z, ν z) = 1 ∧
      (∀ x y, y ∈ badFiber x → ν (x,y) = 0) ∧
      (∀ x y, ¬ survivor x → ν (x,y) = 0) := by
  refine ⟨mixed μ, mixed_nonneg μ hμ, ?_, mixed_avoids_current μ hsupp, mixed_avoids_pure μ hsupp⟩
  rw [mixed_mass, hmass]

#print axioms admissible_probability
end Erdos7CombCurrentMeasure
