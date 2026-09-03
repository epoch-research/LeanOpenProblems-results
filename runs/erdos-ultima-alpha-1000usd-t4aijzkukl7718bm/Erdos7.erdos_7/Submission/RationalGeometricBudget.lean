import Submission.ArithmeticReduction

/-!
# Rational, integer-state geometric tail budgets

A finite sum bounds all prime-exponent caps for a monotone test with an
affine tail. This module supplies scalar comparisons only.
-/
namespace Erdos7RationalGeometricBudget
open scoped BigOperators
open Erdos7CompressionSieve
set_option maxHeartbeats 4000000

def tail (p c : ℚ) (j : ℕ) : ℚ := c/(p^j*(p-1))
def op (p c : ℚ) (f : ℕ → ℚ) (E x : ℕ) : ℚ :=
  f x + ∑ j ∈ Finset.range E, c/p^(j+1)*(f ((j+2)*x)-f ((j+1)*x))
def budget (p c : ℚ) (f : ℕ → ℚ) (S : ℚ) (R x : ℕ) : ℚ :=
  op p c f R x + tail p c R*S*x

lemma tail_nonneg (p c : ℚ) (hp : 1 < p) (hc : 0 ≤ c) (j : ℕ) :
    0 ≤ tail p c j := by
  unfold tail
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p-1 := by linarith
  positivity

lemma tail_step (p c : ℚ) (hp : 1 < p) (j : ℕ) :
    c/p^(j+1)+tail p c (j+1)=tail p c j := by
  have hp0 : p≠0 := by linarith
  have hp1 : p-1≠0 := by linarith
  dsimp [tail]
  rw [pow_succ]
  field_simp
  <;> ring

lemma finite_tail_bound (u T : ℕ → ℚ) (N : ℕ)
    (hu : ∀ j, 0 ≤ u j) (hT : ∀ j, 0 ≤ T j)
    (hstep : ∀ j, N ≤ j → u j+T (j+1) ≤ T j) (E : ℕ) :
    (∑ j ∈ Finset.range E, u j) ≤ (∑ j ∈ Finset.range N, u j)+T N := by
  by_cases he : E ≤ N
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono he)
      (fun j _ _ => hu j)).trans (le_add_of_nonneg_right (hT N))
  · have hNE : N ≤ E := by omega
    have hb : ∀ k, N ≤ k → (∑ j ∈ Finset.range k, u j)+T k ≤
        (∑ j ∈ Finset.range N, u j)+T N := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        linarith [hstep k hk]
    exact (le_add_of_nonneg_right (hT E)).trans (hb E hNE)

lemma affine_increment (f : ℕ → ℚ) (T : ℕ) (S b : ℚ)
    (hf : ∀ x, T ≤ x → f x=S*x+b) (x j : ℕ) (hj : T ≤ (j+1)*x) :
    f ((j+2)*x)-f ((j+1)*x)=S*x := by
  rw [hf _ (hj.trans (Nat.mul_le_mul_right x (by omega))),hf _ hj]
  push_cast
  ring

/-- A monotone affine-tail test has a finite geometric upper budget. -/
theorem op_le_budget (p c : ℚ) (hp : 1 < p) (hc : 0 ≤ c)
    (f : ℕ → ℚ) (hmf : Monotone f) (T : ℕ) (S b : ℚ) (hS : 0 ≤ S)
    (hf : ∀ x, T ≤ x → f x=S*x+b)
    (R E x : ℕ) (hT : T ≤ (R+1)*x) :
    op p c f E x ≤ budget p c f S R x := by
  have hinc0 (j : ℕ) : 0 ≤ f ((j+2)*x)-f ((j+1)*x) := by
    apply sub_nonneg.mpr
    apply hmf
    exact Nat.mul_le_mul_right x (by omega)
  have hjT (j : ℕ) (hj : R ≤ j) : T ≤ (j+1)*x := by
    exact hT.trans (Nat.mul_le_mul_right x (by omega))
  have hb := finite_tail_bound
    (fun j => c/p^(j+1)*(f ((j+2)*x)-f ((j+1)*x)))
    (fun j => tail p c j*S*x) R
    (fun j => mul_nonneg (by positivity) (hinc0 j))
    (fun j => mul_nonneg (mul_nonneg (tail_nonneg p c hp hc j) hS) (Nat.cast_nonneg x))
    (fun j hj => by
      dsimp only
      rw [affine_increment f T S b hf x j (hjT j hj)]
      have hh := congrArg (fun z : ℚ => z*S*x) (tail_step p c hp j)
      nlinarith) E
  dsimp only [op,budget]
  linarith

lemma op_zero (p c : ℚ) (f : ℕ → ℚ) (E : ℕ) : op p c f E 0=f 0 := by
  simp [op]

lemma budget_zero (p c : ℚ) (f : ℕ → ℚ) (S : ℚ) (R : ℕ) :
    budget p c f S R 0=f 0 := by simp [budget,op_zero]

/-- The usual positive exponent mixture equals this finite increment sum. -/
lemma op_eq_mixture (p : ℕ) (c : ℚ) (E : ℕ) (f : ℕ → ℚ) (x : ℕ) :
    op p c f E x = (1-powerTail p c E 0)*f x +
      ∑ g ∈ Finset.range E, (powerTail p c E g-powerTail p c E (g+1))*f ((g+2)*x) := by
  have hh := chain_summation_by_parts (fun g => f ((g+1)*x)) (powerTail p c E) E
  rw [powerTail_terminal,zero_mul,add_zero] at hh
  have hsum : op p c f E x = f x + ∑ g ∈ Finset.range E,
      powerTail p c E g * (f ((g+2)*x)-f ((g+1)*x)) := by
    unfold op
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [powerTail,if_pos (Finset.mem_range.mp hg)]
    simp only [div_eq_mul_inv,inv_pow]
  rw [hsum]
  simpa only [Nat.zero_add,Nat.one_mul,Nat.add_assoc,show 1+1=2 from rfl] using hh

/-- Positive-mixture monotonicity does not require monotonicity in the state. -/
lemma op_mono (p : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) (hcp : c ≤ p)
    (E : ℕ) (f g : ℕ → ℚ) (hfg : ∀ x, f x ≤ g x) (x : ℕ) :
    op p c f E x ≤ op p c g E x := by
  rw [op_eq_mixture,op_eq_mixture]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hfg x)
      (sub_nonneg.mpr (powerTail_zero_le_one p hp c hcp E))
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hfg _) (sub_nonneg.mpr
      (powerTail_decreasing p hp c hc E j))

lemma sum_tail (p c : ℚ) (hp : 1 < p) (R : ℕ) :
    (∑ j ∈ Finset.range R, c/p^(j+1))+tail p c R=c/(p-1) := by
  induction R with
  | zero => simp [tail]
  | succ R ih =>
    rw [Finset.sum_range_succ]
    have hh := tail_step p c hp R
    linarith

lemma budget_affine (p c : ℚ) (hp : 1 < p) (f : ℕ → ℚ)
    (T : ℕ) (S b : ℚ) (hf : ∀ x, T ≤ x → f x=S*x+b)
    (R x : ℕ) (hx : T ≤ x) :
    budget p c f S R x = (1+c/(p-1))*S*x+b := by
  have hinc (j : ℕ) : f ((j+2)*x)-f ((j+1)*x)=S*x :=
    affine_increment f T S b hf x j (hx.trans (by nlinarith))
  dsimp only [budget,op]
  simp_rw [hinc]
  rw [hf x hx,← Finset.sum_mul]
  have hh := congrArg (fun z : ℚ => z*S*x) (sum_tail p c hp R)
  nlinarith

lemma expect_op (p : ℕ) (c : ℚ) (E : ℕ) (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    Erdos7BinarySieve.expect μ (fun x => op p c f E x) =
      Erdos7BinarySieve.expect (Erdos7ExponentLaw.step E (powerTail p c E) μ) f := by
  rw [Erdos7ExponentLaw.expect_step]
  simp_rw [op_eq_mixture]
  rw [Erdos7BinarySieve.expect_add,Erdos7BinarySieve.expect_mul]
  congr 1
  unfold Erdos7BinarySieve.expect
  simp only [Finsupp.sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro x hx
  ring

#print axioms op_le_budget
#print axioms op_eq_mixture
#print axioms op_mono
#print axioms budget_affine
#print axioms expect_op
end Erdos7RationalGeometricBudget
