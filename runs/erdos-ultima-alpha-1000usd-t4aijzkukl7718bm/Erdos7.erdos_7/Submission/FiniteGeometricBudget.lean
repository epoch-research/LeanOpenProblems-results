import Submission.FiniteHingeFunctions
import Submission.FiniteRetainedMixture

/-! Finite geometric tail budgets for affine-tail convex tests. No infinite
series or truncation limit is used in these comparisons. -/
namespace Erdos7FiniteGeometricBudget
open scoped BigOperators
open Erdos7FiniteHingeFunctions
set_option maxHeartbeats 2000000

noncomputable def tail (p c : ℝ) (j : ℕ) : ℝ := c/(p^j*(p-1))
noncomputable def q (p c h : ℝ) (j : ℕ) : ℝ := min h (c/p^(j+1))
noncomputable def op (p c h : ℝ) (f : ℝ → ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  h*f x+∑ j ∈ Finset.range R, q p c h j*(f ((j+2)*x)-f ((j+1)*x))
noncomputable def budget (p c h : ℝ) (f : ℝ → ℝ) (S : ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  op p c h f R x+tail p c R*S*x
noncomputable def moment (p c h : ℝ) (R : ℕ) : ℝ :=
  h+∑ j ∈ Finset.range R, q p c h j+tail p c R

lemma tail_nonneg (p c : ℝ) (hp : 1<p) (hc : 0 ≤ c) (j : ℕ) : 0 ≤ tail p c j := by
  unfold tail
  apply div_nonneg hc
  exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)

lemma tail_step (p c : ℝ) (hp : 1<p) (j : ℕ) :
    c/p^(j+1)+tail p c (j+1)=tail p c j := by
  have hp0 : p≠0 := by linarith
  have hp1 : p-1≠0 := by linarith
  dsimp [tail]
  rw [pow_succ]
  field_simp
  <;> ring

lemma q_nonneg (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) (hh : 0 ≤ h) (j : ℕ) :
    0 ≤ q p c h j := by
  exact le_min hh (div_nonneg hc (pow_nonneg (by linarith) _))

lemma q_antitone (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) : Antitone (q p c h) := by
  intro j k hjk
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_left hc (pow_pos (by linarith) _)
  exact pow_le_pow_right₀ hp.le (by omega)

/-- A nonnegative telescoping potential bounds every finite sum. -/
lemma finite_tail_bound (u T : ℕ → ℝ) (N : ℕ)
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

/-- A finite partial first moment plus a geometric tail decreases when its
explicit prefix is enlarged. This is valid for every h, not just live h. -/
lemma moment_antitone (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) :
    Antitone (moment p c h) := by
  apply antitone_nat_of_succ_le
  intro j
  dsimp [moment]
  rw [Finset.sum_range_succ]
  have hh := min_le_right h (c/p^(j+1))
  have he := tail_step p c hp j
  dsimp [q]
  linarith

lemma op_nondec_cap (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hf : Monotone f) (x : ℝ) (hx : 0 ≤ x) :
    Monotone (fun E => op p c h f E x) := by
  intro E R hER
  dsimp [op]
  apply add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hER)
  intro j _ _
  apply mul_nonneg (q_nonneg p c h hp hc hh j)
  apply sub_nonneg.mpr
  apply hf
  nlinarith

lemma affine_increment (f : ℝ → ℝ) (T S : ℝ)
    (hf : ∀ x, T ≤ x → f x=f T+S*(x-T))
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : T ≤ (j+1)*x) :
    f ((j+2)*x)-f ((j+1)*x)=S*x := by
  rw [hf _ (by nlinarith), hf _ hj]
  ring

/-- The finite row formula dominates every finite geometric exponent cap.
The scalar function may have a signed constant term. -/
theorem op_le_budget (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hmf : Monotone f) (T S : ℝ) (hS : 0 ≤ S)
    (hf : ∀ x, T ≤ x → f x=f T+S*(x-T))
    (N E : ℕ) (x : ℝ) (hx : 0 ≤ x) (hT : T ≤ (N+1)*x) :
    op p c h f E x ≤ budget p c h f S N x := by
  have hjT (j : ℕ) (hj : N ≤ j) : T ≤ (j+1)*x := by
    have hcast : (N:ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hinc0 (j : ℕ) : 0 ≤ f ((j+2)*x)-f ((j+1)*x) := by
    exact sub_nonneg.mpr (hmf (by nlinarith))
  have hbound := finite_tail_bound
    (fun j => q p c h j*(f ((j+2)*x)-f ((j+1)*x)))
    (fun j => tail p c j*S*x) N
    (fun j => mul_nonneg (q_nonneg p c h hp hc hh j) (hinc0 j))
    (fun j => mul_nonneg (mul_nonneg (tail_nonneg p c hp hc j) hS) hx)
    (fun j hj => by
      dsimp only
      rw [affine_increment f T S hf x hx j (hjT j hj)]
      have hq := mul_le_mul_of_nonneg_right (min_le_right h (c/p^(j+1))) (mul_nonneg hS hx)
      have ht := congrArg (fun z : ℝ => z*S*x) (tail_step p c hp j)
      dsimp only [q]
      nlinarith) E
  dsimp only [op, budget]
  linarith

lemma op_positive (p c h : ℝ) (f : ℝ → ℝ) (R : ℕ) (x : ℝ) :
    op p c h f R x = (h-q p c h 0)*f x +
      (∑ j ∈ Finset.range R, (q p c h j-q p c h (j+1))*f ((j+2)*x))+
        q p c h R*f ((R+1)*x) := by
  have hh := Erdos7FiniteRetainedMixture.mixture_positive_form h (q p c h)
    (fun j => f ((j+1)*x)) R
  simpa only [op, Erdos7FiniteRetainedMixture.mixture, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, zero_add, one_mul, add_assoc, one_add_one_eq_two] using hh

lemma convex_scale (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (d : ℝ) :
    ConvexOn ℝ Set.univ (fun x => f (d*x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hf.2 (Set.mem_univ (d*x)) (Set.mem_univ (d*y)) ha hb hab
  simpa only [smul_eq_mul, mul_add, mul_left_comm d a, mul_left_comm d b] using hh

lemma budget_convex (p c h : ℝ) (hp : 1<p) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (S : ℝ) (R : ℕ) :
    ConvexOn ℝ Set.univ (budget p c h f S R) := by
  have hb : 0 ≤ h-q p c h 0 := sub_nonneg.mpr (min_le_left _ _)
  have h₀ : ConvexOn ℝ Set.univ (fun x => (h-q p c h 0)*f x) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hb hf
  have h₁ : ConvexOn ℝ Set.univ (fun x => ∑ j ∈ Finset.range R,
      (q p c h j-q p c h (j+1))*f ((j+2)*x)) := by
    apply Erdos7FiniteHingeFunctions.convex_sum
    intro j _
    have hq : 0 ≤ q p c h j-q p c h (j+1) :=
      sub_nonneg.mpr (q_antitone p c h hp hc (Nat.le_succ j))
    simpa only [smul_eq_mul] using ConvexOn.smul hq (convex_scale f hf (j+2))
  have h₂ : ConvexOn ℝ Set.univ (fun x => q p c h R*f ((R+1)*x)) := by
    simpa only [smul_eq_mul] using ConvexOn.smul (q_nonneg p c h hp hc hh R)
      (convex_scale f hf (R+1))
  have h₃ : ConvexOn ℝ Set.univ (fun x => tail p c R*S*x) := by
    simpa only [add_zero] using convex_affine (tail p c R*S) 0
  convert ((h₀.add h₁).add h₂).add h₃ using 1
  funext x
  exact congrArg (fun z : ℝ => z+tail p c R*S*x) (op_positive p c h f R x)

lemma budget_affine_tail (p c h : ℝ) (f : ℝ → ℝ) (T S : ℝ)
    (hT : 0 ≤ T) (hf : ∀ x, T ≤ x → f x=f T+S*(x-T))
    (R : ℕ) (x : ℝ) (hx : T ≤ x) :
    budget p c h f S R x = budget p c h f S R T+S*moment p c h R*(x-T) := by
  have hx0 : 0 ≤ x := hT.trans hx
  have hinc (j : ℕ) : f ((j+2)*x)-f ((j+1)*x)=S*x :=
    affine_increment f T S hf x hx0 j (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; nlinarith)
  have hincT (j : ℕ) : f ((j+2)*T)-f ((j+1)*T)=S*T :=
    affine_increment f T S hf T hT j (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; nlinarith)
  dsimp only [budget, op, moment]
  simp_rw [hinc, hincT]
  rw [hf x hx, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

#print axioms op_le_budget
#print axioms budget_convex
#print axioms budget_affine_tail
end Erdos7FiniteGeometricBudget
