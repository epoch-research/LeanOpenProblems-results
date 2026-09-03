import Submission.CappedFiberMixture

/-! Weighted root-cylinder bounds and a common comparison for separately
indexed real-count families. These are auxiliary lemmas, not a settlement
of the odd covering-system conjecture. -/
namespace Erdos7WeightedRootComparison
open scoped BigOperators
open Erdos7RealChain Erdos7RetainedRealCompression
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def branchMass {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (q : Ω → Bool) (b : Bool) : ℝ :=
  ∑ x, if q x = b then μ x*v x else 0

lemma branchMass_nonneg {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hv : ∀ x, 0 ≤ v x)
    (q : Ω → Bool) (b : Bool) : 0 ≤ branchMass μ v q b := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact mul_nonneg (hμ x) (hv x)
  · exact le_rfl

lemma branchMass_add {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (q : Ω → Bool) :
    branchMass μ v q false+branchMass μ v q true = ∑ x, μ x*v x := by
  rw [branchMass, branchMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases q x <;> simp

lemma branchMass_max_le_mass {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hv : ∀ x, 0 ≤ v x)
    (q : Ω → Bool) :
    max (branchMass μ v q false) (branchMass μ v q true) ≤ ∑ x, μ x*v x := by
  have h₀ := branchMass_nonneg μ v hμ hv q false
  have h₁ := branchMass_nonneg μ v hμ hv q true
  have hh := branchMass_add μ v q
  exact max_le (by linarith) (by linarith)

/-- A cylinder of small original mass can carry at most the upper-weight
mass given by any hinge dual parameter. No independence is assumed. -/
theorem weighted_event_hinge_bound {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (E : Ω → Prop) [DecidablePred E] (τ ell : ℝ) (hell : 0 ≤ ell)
    (hE : (∑ x, if E x then μ x else 0) ≤ τ) :
    (∑ x, if E x then μ x*v x else 0) ≤
      ell*τ+∑ x, μ x*max 0 (v x-ell) := by
  have hp (x : Ω) : (if E x then μ x*v x else 0) ≤
      ell*(if E x then μ x else 0)+μ x*max 0 (v x-ell) := by
    by_cases hx : E x
    · simp only [hx, if_true]
      have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (v x-ell)) (hμ x)
      nlinarith
    · simp only [hx, if_false, mul_zero, zero_add]
      exact mul_nonneg (hμ x) (le_max_left _ _)
  calc
    _ ≤ ∑ x, (ell*(if E x then μ x else 0)+μ x*max 0 (v x-ell)) :=
      Finset.sum_le_sum (fun x _ => hp x)
    _ = ell*(∑ x, if E x then μ x else 0)+∑ x, μ x*max 0 (v x-ell) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hE hell]

lemma weighted_event_branch_bound {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hv : ∀ x, 0 ≤ v x)
    (q : Ω → Bool) (E : Ω → Prop) [DecidablePred E]
    (b : Bool) (hb : ∀ x, E x → q x = b) :
    (∑ x, if E x then μ x*v x else 0) ≤ branchMass μ v q b := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp [hx, hb x hx]
  · simp only [hx, if_false]
    split_ifs
    · exact mul_nonneg (hμ x) (hv x)
    · exact le_rfl

/-- A deeper cylinder is contained in one coarse branch. Its weighted mass
is bounded by BOTH the common branch cap and the small-original-mass cap. -/
theorem weighted_cylinder_bound {Ω : Type*} [Fintype Ω]
    (μ v : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hv : ∀ x, 0 ≤ v x)
    (q : Ω → Bool) (E : Ω → Prop) [DecidablePred E]
    (hb : ∃ b, ∀ x, E x → q x = b)
    (τ ell : ℝ) (hell : 0 ≤ ell) (hE : (∑ x, if E x then μ x else 0) ≤ τ) :
    (∑ x, if E x then μ x*v x else 0) ≤
      min (max (branchMass μ v q false) (branchMass μ v q true))
        (ell*τ+∑ x, μ x*max 0 (v x-ell)) := by
  apply le_min
  · obtain ⟨b,hb⟩ := hb
    apply (weighted_event_branch_bound μ v hμ hv q E b hb).trans
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact weighted_event_hinge_bound μ v hμ E τ ell hell hE

noncomputable def chainValue (m : ℝ) (β : ℕ → ℝ) (R : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (m-β 0)*φ 1+∑ j ∈ Finset.range R, (β j-β (j+1))*φ ((j:ℝ)+2)

/-- Each positive-exponent group is a real average in[0,1]. Marginal bounds
under the SAME weighted measure give a common convex comparison law. -/
theorem real_group_comparison {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (s : ℕ → Ω → ℝ) (β : ℕ → ℝ) (R : ℕ)
    (hs : ∀ j<R, ∀ x, s j x ∈ Set.Icc (0:ℝ) 1)
    (hmarg : ∀ j<R, (∑ x, ν x*s j x) ≤ β j) (hβR : β R=0)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, ν x*φ (1+∑ j ∈ Finset.range R, s j x)) ≤
      chainValue (∑ x, ν x) β R φ := by
  have hb := retained_group_mixture ν hν 1 (∑ x, ν x) (by ring)
    φ hφ hmφ 1 (fun _ => 1) s β R (fun _ _ => by norm_num)
    (fun j hj x => (hs j hj x).1) (fun j hj x => (hs j hj x).2)
    (fun j hj => by simpa using hmarg j hj) hβR
  simpa only [chainValue, prefixWeight, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, one_mul,
    show ∀ j : ℕ, (1:ℝ)+((j:ℝ)+1) = (j:ℝ)+2 by intro j; ring] using hb

lemma chainValue_mono (m : ℝ) (β : ℕ → ℝ) (R : ℕ)
    (hm : β 0 ≤ m) (hβ : ∀ j<R, β (j+1) ≤ β j)
    (φ ψ : ℝ → ℝ) (h : ∀ x, φ x ≤ ψ x) :
    chainValue m β R φ ≤ chainValue m β R ψ := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h 1) (sub_nonneg.mpr hm)
  · exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (h _)
      (sub_nonneg.mpr (hβ j (Finset.mem_range.mp hj))))

lemma chainValue_sum {I : Type*} [Fintype I]
    (m : ℝ) (β : ℕ → ℝ) (R : ℕ) (φ : I → ℝ → ℝ) :
    (∑ i, chainValue m β R (φ i)) = chainValue m β R (fun x => ∑ i, φ i x) := by
  simp only [chainValue, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- Different tests may use different actual count families. A common
positive comparison law still permits summing their budget bounds. -/
theorem separate_families {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (s : I → ℕ → Ω → ℝ) (β : ℕ → ℝ) (R : ℕ)
    (hs : ∀ i j, j<R → ∀ x, s i j x ∈ Set.Icc (0:ℝ) 1)
    (hmarg : ∀ i j, j<R → (∑ x, ν x*s i j x) ≤ β j)
    (hβR : β R=0) (hm : β 0 ≤ ∑ x, ν x) (hβ : ∀ j<R, β (j+1) ≤ β j)
    (φ : I → ℝ → ℝ) (hφ : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i, Monotone (φ i)) (F : ℝ → ℝ) (hF : ∀ t, (∑ i, φ i t) ≤ F t) :
    (∑ i, ∑ x, ν x*φ i (1+∑ j ∈ Finset.range R, s i j x)) ≤
      chainValue (∑ x, ν x) β R F := by
  calc
    _ ≤ ∑ i, chainValue (∑ x, ν x) β R (φ i) :=
      Finset.sum_le_sum (fun i _ => real_group_comparison ν hν (s i) β R
        (hs i) (hmarg i) hβR (φ i) (hφ i) (hmφ i))
    _ = chainValue (∑ x, ν x) β R (fun t => ∑ i, φ i t) := chainValue_sum _ _ _ _
    _ ≤ _ := chainValue_mono _ β R hm hβ _ F hF

#print axioms weighted_cylinder_bound
#print axioms real_group_comparison
#print axioms separate_families
end Erdos7WeightedRootComparison
