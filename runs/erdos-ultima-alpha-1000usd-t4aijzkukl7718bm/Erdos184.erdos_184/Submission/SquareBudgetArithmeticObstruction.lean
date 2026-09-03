import Mathlib.Tactic

/-! The numerical square-extraction estimates alone allow superlinear initial
counts. These are arithmetic data, not graphs or a disproof of Erdős 184. -/
namespace Erdos184Work.SquareBudgetArithmeticObstruction

private lemma lt_five_pow (t : ℕ) : t < 5 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [pow_succ]
    nlinarith [(show 0 < (5 : ℕ) ^ t by positivity)]

/-- Abstract count sequences satisfy all the displayed descent inequalities
and the simple-graph edge cap, but have arbitrarily large initial count/order
ratio. Their realization as graph decomposition numbers is NOT asserted. -/
theorem no_linear_bound_from_accounting (C : ℕ) :
    ∃ (n t : ℕ) (k m : ℕ → ℕ),
      0 < n ∧ C * n < k 0 ∧ k t = n ∧
      (∀ i, 0 < k i ∧ m i ≤ n * (n - 1) / 2) ∧
      (∀ i < t, k (i + 1) < k i ∧
        k i ≤ 15 * n + 5 * k (i + 1) ∧
        m (i + 1) + 4 * k i ≤ m i + 24 * n) := by
  let t := C
  let n := 10 * 5 ^ t + 1
  let k : ℕ → ℕ := fun i => n * 5 ^ (t - i)
  let m : ℕ → ℕ := fun i => 5 * k i
  have hn : 0 < n := by dsimp [n]; omega
  have hk (i : ℕ) : 0 < k i :=
    by dsimp [k]; positivity
  have hcap : 2 * m 0 = n * (n - 1) := by
    dsimp [m, k]
    have hsub : n - 1 = 10 * 5 ^ t := by omega
    rw [hsub]
    ring
  have hbound (i : ℕ) : m i ≤ n * (n - 1) / 2 := by
    have hp : 5 ^ (t - i) ≤ 5 ^ t :=
      Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have hm : m i ≤ m 0 := by
      dsimp [m, k]
      exact Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left n hp)
    omega
  refine ⟨n, t, k, m, hn, ?_, ?_, fun i => ⟨hk i, hbound i⟩, ?_⟩
  · dsimp [k]
    have hp : C < 5 ^ t := lt_five_pow C
    nlinarith
  · simp [k]
  · intro i hi
    have he : t - i = (t - (i + 1)) + 1 := by omega
    have hstep : k i = 5 * k (i + 1) := by
      dsimp [k]
      rw [he, pow_succ]
      ring
    have hmstep : m (i + 1) + 4 * k i = m i := by
      dsimp only [m]
      rw [hstep]
      ring
    exact ⟨by have := hk (i + 1); omega, by omega, by omega⟩

end Erdos184Work.SquareBudgetArithmeticObstruction
#print axioms Erdos184Work.SquareBudgetArithmeticObstruction.no_linear_bound_from_accounting
