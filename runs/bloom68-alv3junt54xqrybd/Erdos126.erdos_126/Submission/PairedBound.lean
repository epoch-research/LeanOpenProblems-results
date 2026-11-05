import Submission.PairedMatrixBlocks

/-!
# Abstract finite paired-matrix polynomial bound

The hypotheses here are entirely finite-dimensional. No arithmetic,
laminarity, or Hall theorem is assumed or proved in this file: the coherent
orientations and the capacity-five mates are supplied explicitly.

`polynomial_bound` proves the strict constant-12 bound. Its `indegree`
hypothesis is exactly the cardinality of `univ.filter (fun i => mate p i = j)`;
the definition internalizes classical decidability. Empty block and owner
types are allowed: the negative offdiagonal hypothesis and `2 ≤ card ι`
automatically force positive total trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.Paired

variable {ι τ P : Type*} [Fintype ι] [Fintype τ] [Fintype P]

/-- The total trace mass of the ratio-five balanced blocks. -/
noncomputable def goodTrace (b : τ → Block ι) : ℝ := by
  classical
  exact ∑ t, if (b t).Balanced 5 then (b t).traceMass else 0

/-- Cross mass assigned to a single owner, without a balance restriction. -/
noncomputable def ownedCrossMass (b : τ → Block ι) (owner : τ → P) (p : P) : ℝ := by
  classical
  exact ∑ t, if owner t = p then (b t).crossMass else 0

/-- The root orientations bound the full cross mass by the number of
owners times the full trace, including arbitrarily unbalanced blocks. -/
theorem orientation_total_cross_bound
    (b : τ → Block ι) (owner : τ → P) (hb : ∀ t, (b t).Valid)
    (hoff : ∀ i j, i ≠ j → gramSum b i j < 0)
    (sigma : P → ι → ℝ) (hsigma : ∀ p i, |sigma p i| ≤ 1)
    (hleft : ∀ t i, i ∈ (b t).left → sigma (owner t) i = 1)
    (hright : ∀ t i, i ∈ (b t).right → sigma (owner t) i = -1) :
    totalSum (crossSum b) ≤ (Fintype.card P : ℝ) * traceSum (gramSum b) := by
  classical
  have hcharge (p : P) : 2 * ownedCrossMass b owner p ≤ qform (gramSum b) (sigma p) := by
    unfold ownedCrossMass
    rw [Finset.mul_sum, qform_gramSum]
    apply Finset.sum_le_sum
    intro t ht
    by_cases ho : owner t = p
    · simp only [ho, if_true]
      apply (b t).oriented_crossMass (hb t).2.2.2
      · intro i hi
        simpa [ho] using hleft t i hi
      · intro i hi
        simpa [ho] using hright t i hi
    · simp only [ho, if_false, mul_zero]
      exact (b t).psd_gram (hb t).2.2.2 (sigma p)
  have howner (p : P) : ownedCrossMass b owner p ≤ traceSum (gramSum b) := by
    have hu := qform_le_twice_trace (gramSum b) (gramSum_psd b hb)
      (gramSum_diag_nonneg b hb) (fun i j hij => (hoff i j hij).le)
      (sigma p) (hsigma p)
    linarith [hcharge p]
  calc
    totalSum (crossSum b) = ∑ p, ownedCrossMass b owner p := by
      rw [total_crossSum]
      unfold ownedCrossMass
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ _p : P, traceSum (gramSum b) := Finset.sum_le_sum fun p _ => howner p
    _ = (Fintype.card P : ℝ) * traceSum (gramSum b) := by simp

/-- More than half of the full trace belongs to balanced blocks. The
negative offdiagonal assumption is used only for the full Gram matrix,
never for the Gram matrix after deleting bad blocks. -/
theorem trace_lt_twice_goodTrace
    (b : τ → Block ι) (hb : ∀ t, (b t).Valid)
    (hn : 2 ≤ Fintype.card ι)
    (hoff : ∀ i j, i ≠ j → gramSum b i j < 0) :
    traceSum (gramSum b) < 2 * goodTrace b := by
  classical
  have hbad : 2 * (traceSum (gramSum b) - goodTrace b) ≤
      qform (gramSum b) (fun _ => 1) := by
    rw [trace_gramSum b hb, qform_one_gramSum]
    unfold goodTrace
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hg : (b t).Balanced 5
    · simp only [hg, if_true, sub_self, mul_zero]
      exact mul_nonneg (hb t).2.2.2 (sq_nonneg _)
    · simp only [hg, if_false, sub_zero]
      exact (b t).bad_mass (hb t) hg
  have hu := qform_one_lt_trace (gramSum b) hn hoff
  linarith

/-- Balanced-block coverage charges all good trace to the selected entries
of the full cross matrix. Mates may differ from owner to owner. -/
theorem goodTrace_le_mate_sum
    (b : τ → Block ι) (owner : τ → P) (hb : ∀ t, (b t).Valid)
    (mate : P → ι → ι)
    (hcover : ∀ p t, owner t = p → (b t).Balanced 5 →
      (∀ i, i ∈ (b t).left → mate p i ∈ (b t).right) ∧
      (∀ i, i ∈ (b t).right → mate p i ∈ (b t).left)) :
    goodTrace b ≤ ∑ p, ∑ i, crossSum b i (mate p i) := by
  classical
  have hblock (t : τ) :
      (if (b t).Balanced 5 then (b t).traceMass else 0) ≤
        ∑ p, ∑ i, (b t).cross i (mate p i) := by
    have hnonneg (p : P) : 0 ≤ ∑ i, (b t).cross i (mate p i) :=
      Finset.sum_nonneg fun i _ => (b t).cross_nonneg (hb t).2.2.2 i (mate p i)
    by_cases hg : (b t).Balanced 5
    · simp only [hg, if_true]
      have hc := hcover (owner t) t rfl hg
      rw [(b t).covered_trace (hb t) (mate (owner t)) hc.1 hc.2]
      exact Finset.single_le_sum (fun p _ => hnonneg p) (Finset.mem_univ (owner t))
    · simp only [hg, if_false]
      exact Finset.sum_nonneg fun p _ => hnonneg p
  unfold goodTrace
  calc
    (∑ t, if (b t).Balanced 5 then (b t).traceMass else 0) ≤
        ∑ t, ∑ p, ∑ i, (b t).cross i (mate p i) :=
      Finset.sum_le_sum fun t _ => hblock t
    _ = ∑ p, ∑ i, crossSum b i (mate p i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      rfl

/-- The capacity-five CND estimate, summed independently over owners. -/
theorem goodTrace_cnd_bound
    (b : τ → Block ι) (owner : τ → P) (hb : ∀ t, (b t).Valid)
    (hn : 0 < Fintype.card ι) (hcnd : CND (crossSum b))
    (mate : P → ι → ι) (hdegree : ∀ p j, indegree (mate p) j ≤ 5)
    (hcover : ∀ p t, owner t = p → (b t).Balanced 5 →
      (∀ i, i ∈ (b t).left → mate p i ∈ (b t).right) ∧
      (∀ i, i ∈ (b t).right → mate p i ∈ (b t).left)) :
    (Fintype.card ι : ℝ) * goodTrace b ≤
      6 * (Fintype.card P : ℝ) * totalSum (crossSum b) := by
  classical
  have hm (p : P) : (Fintype.card ι : ℝ) * (∑ i, crossSum b i (mate p i)) ≤
      6 * totalSum (crossSum b) := by
    have h := cnd_mate_bound (crossSum b) (crossSum_symm b) (crossSum_self b hb)
      hcnd hn (mate p) 5 (hdegree p)
    norm_num at h
    exact h
  calc
    (Fintype.card ι : ℝ) * goodTrace b ≤
        (Fintype.card ι : ℝ) * (∑ p, ∑ i, crossSum b i (mate p i)) :=
      mul_le_mul_of_nonneg_left (goodTrace_le_mate_sum b owner hb mate hcover)
        (Nat.cast_nonneg _)
    _ = ∑ p, (Fintype.card ι : ℝ) * (∑ i, crossSum b i (mate p i)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _p : P, 6 * totalSum (crossSum b) := Finset.sum_le_sum fun p _ => hm p
    _ = 6 * (Fintype.card P : ℝ) * totalSum (crossSum b) := by simp; ring

/-- The scalar final step, with `H` the good trace and `B` the total cross
mass. This criterion is also usable independently of the block interface. -/
theorem scalar_polynomial_bound (n s T B H : ℝ)
    (hn : 0 < n) (hs : 0 ≤ s) (hT : 0 < T)
    (hgood : T < 2 * H) (hcross : B ≤ s * T) (hmate : n * H ≤ 6 * s * B) :
    n < 12 * s ^ 2 := by
  have h1 := mul_lt_mul_of_pos_left hgood hn
  have h2 := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 6 * s by positivity)
  have h3 : n * T < (12 * s ^ 2) * T := by nlinarith
  exact (mul_lt_mul_iff_of_pos_right hT).mp h3

/-- **Abstract paired-block polynomial bound (constant 12).**

Every block has two nonempty disjoint sides and nonnegative weight.
The full cross matrix is CND and the full Gram matrix has strictly
negative offdiagonals. Each owner admits a unit-cube orientation agreeing
with all its blocks, and a mate of indegree at most five covering every
ratio-five balanced block of that owner. Then the number of vertices is
strictly less than twelve times the square of the number of owners.
-/
theorem polynomial_bound
    (b : τ → Block ι) (owner : τ → P)
    (hn : 2 ≤ Fintype.card ι) (hb : ∀ t, (b t).Valid)
    (hcnd : CND (crossSum b))
    (hoff : ∀ i j, i ≠ j → gramSum b i j < 0)
    (sigma : P → ι → ℝ) (hsigma : ∀ p i, |sigma p i| ≤ 1)
    (hleft : ∀ t i, i ∈ (b t).left → sigma (owner t) i = 1)
    (hright : ∀ t i, i ∈ (b t).right → sigma (owner t) i = -1)
    (mate : P → ι → ι) (hdegree : ∀ p j, indegree (mate p) j ≤ 5)
    (hcover : ∀ p t, owner t = p → (b t).Balanced 5 →
      (∀ i, i ∈ (b t).left → mate p i ∈ (b t).right) ∧
      (∀ i, i ∈ (b t).right → mate p i ∈ (b t).left)) :
    (Fintype.card ι : ℝ) < 12 * (Fintype.card P : ℝ) ^ 2 := by
  have hn0 : 0 < Fintype.card ι := by omega
  have hu := qform_one_lt_trace (gramSum b) hn hoff
  have hpsd := gramSum_psd b hb (fun _ => 1)
  have hT : 0 < traceSum (gramSum b) := lt_of_le_of_lt hpsd hu
  exact scalar_polynomial_bound (Fintype.card ι : ℝ) (Fintype.card P : ℝ)
    (traceSum (gramSum b)) (totalSum (crossSum b)) (goodTrace b)
    (by exact_mod_cast hn0) (Nat.cast_nonneg _) hT
    (trace_lt_twice_goodTrace b hb hn hoff)
    (orientation_total_cross_bound b owner hb hoff sigma hsigma hleft hright)
    (goodTrace_cnd_bound b owner hb hn0 hcnd mate hdegree hcover)

/-- A version of `polynomial_bound` using the literal filtered-fiber
cardinality. The extra decidable equality instance is only for this syntax. -/
theorem polynomial_bound_of_filter_card [DecidableEq ι]
    (b : τ → Block ι) (owner : τ → P)
    (hn : 2 ≤ Fintype.card ι) (hb : ∀ t, (b t).Valid)
    (hcnd : CND (crossSum b))
    (hoff : ∀ i j, i ≠ j → gramSum b i j < 0)
    (sigma : P → ι → ℝ) (hsigma : ∀ p i, |sigma p i| ≤ 1)
    (hleft : ∀ t i, i ∈ (b t).left → sigma (owner t) i = 1)
    (hright : ∀ t i, i ∈ (b t).right → sigma (owner t) i = -1)
    (mate : P → ι → ι)
    (hdegree : ∀ p j, (Finset.univ.filter (fun i => mate p i = j)).card ≤ 5)
    (hcover : ∀ p t, owner t = p → (b t).Balanced 5 →
      (∀ i, i ∈ (b t).left → mate p i ∈ (b t).right) ∧
      (∀ i, i ∈ (b t).right → mate p i ∈ (b t).left)) :
    (Fintype.card ι : ℝ) < 12 * (Fintype.card P : ℝ) ^ 2 := by
  apply polynomial_bound b owner hn hb hcnd hoff sigma hsigma hleft hright mate _ hcover
  intro p j
  rw [indegree_eq_filter_card]
  exact hdegree p j

end Erdos126Aux.Paired
