import Submission.EvenReduction

/-!
# Logical equivalences for the Erdős 184 target

The exact asymptotic proposition is equivalent to the existence of a nonnegative
uniform linear bound, both for all finite simple graphs and for finite even
simple graphs (with the same cycle-or-edge pieces).

For the converse, a Big-O witness gives a constant `C` and a threshold `N`.
Above the threshold we use the hypothesized decomposition and the real norm
bound. Below it we use the canonical singleton-edge decomposition and
`n.choose 2 ≤ n * n ≤ N * n`. Thus `K = max |C| N` works, including at `n = 0`.

These are equivalences only: none of the three propositions is proved here.
Neither admitted proof in `Submission.Spec` is used. The audit checks the copied
target proposition against the original statement using only `type_of%`.
-/

open Filter SimpleGraph

namespace Erdos184.UniformEquivalence

open Infrastructure

universe u

open scoped Classical in
/-- An explicit copy of the exact asymptotic target, not its admitted proof. -/
def ExactTarget : Prop :=
  ∃ f : ℕ → ℝ,
    (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧
      (D.card : ℝ) ≤ f (Fintype.card V)

open scoped Classical in
/-- A uniform linear bound for exact cycle-or-edge decompositions of all finite graphs. -/
def UniformLinearBound (K : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
    IsDecomposition G D ∧
    (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)

open scoped Classical in
/-- The same uniform bound restricted to even graphs; singleton-edge pieces remain allowed. -/
def UniformEvenLinearBound (K : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  (∀ v, Even (G.degree v)) →
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
    IsDecomposition G D ∧
    (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)

/--
The converse to `Infrastructure.asymptotic_of_uniform_linear_bound`.
The target is a hypothesis, and the constant is independent of the vertex type
and graph. No positivity of the number of vertices is assumed.
-/
theorem uniform_linear_bound_of_asymptotic (h : ExactTarget.{u}) :
    ∃ K : ℝ, 0 ≤ K ∧ UniformLinearBound.{u} K := by
  classical
  obtain ⟨f, hf, hgraphs⟩ := h
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC
  refine ⟨max |C| (N : ℝ), (abs_nonneg C).trans (le_max_left _ _), ?_⟩
  intro V _ _ G
  by_cases hn : N ≤ Fintype.card V
  · obtain ⟨D, hpieces, hD, hcount⟩ := hgraphs G
    refine ⟨D, hpieces, hD, hcount.trans ?_⟩
    calc
      f (Fintype.card V) ≤ ‖f (Fintype.card V)‖ := Real.le_norm_self _
      _ ≤ C * ‖(Fintype.card V : ℝ)‖ := hN _ hn
      _ = C * (Fintype.card V : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ |C| * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg _)
      _ ≤ max |C| (N : ℝ) * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  · refine ⟨singletonEdgeDecomposition G, singletonEdgeDecomposition_isCycleOrEdge,
      singletonEdgeDecomposition_isDecomposition, ?_⟩
    have hsmall : Fintype.card V ≤ N := (Nat.lt_of_not_ge hn).le
    have hquad : (Fintype.card V).choose 2 ≤ Fintype.card V * Fintype.card V := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans
        (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    calc
      ((singletonEdgeDecomposition G).card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by
        exact_mod_cast (singletonEdgeDecomposition_card_le (G := G))
      _ ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
        exact_mod_cast hquad
      _ ≤ (N : ℝ) * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) (Nat.cast_nonneg _)
      _ ≤ max |C| (N : ℝ) * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)

/-- The exact asymptotic target is equivalent to a nonnegative uniform linear bound. -/
theorem asymptotic_iff_uniform_linear_bound :
    ExactTarget.{u} ↔ ∃ K : ℝ, 0 ≤ K ∧ UniformLinearBound.{u} K := by
  constructor
  · exact uniform_linear_bound_of_asymptotic
  · rintro ⟨K, _, hK⟩
    exact Infrastructure.asymptotic_of_uniform_linear_bound K hK

/-- Restrict the bound extracted from the target to graphs whose degrees are all even. -/
theorem uniform_even_linear_bound_of_asymptotic (h : ExactTarget.{u}) :
    ∃ K : ℝ, 0 ≤ K ∧ UniformEvenLinearBound.{u} K := by
  obtain ⟨K, hK, hbound⟩ := uniform_linear_bound_of_asymptotic h
  refine ⟨K, hK, ?_⟩
  intro V _ _ G _
  exact hbound G

/--
The exact target is also equivalent to a nonnegative uniform cycle-or-edge bound
for finite even graphs. The reverse implication is the existing parity-forest
reduction, not an unconditional even-graph bound.
-/
theorem asymptotic_iff_uniform_even_linear_bound :
    ExactTarget.{u} ↔ ∃ K : ℝ, 0 ≤ K ∧ UniformEvenLinearBound.{u} K := by
  constructor
  · exact uniform_even_linear_bound_of_asymptotic
  · rintro ⟨K, _, hK⟩
    exact EvenReduction.asymptotic_of_even_linear_bound K hK

/-- Existence of a uniform bound for all graphs is equivalent to existence of one for even graphs. -/
theorem uniform_linear_bound_iff_uniform_even_linear_bound :
    (∃ K : ℝ, 0 ≤ K ∧ UniformLinearBound.{u} K) ↔
      ∃ K : ℝ, 0 ≤ K ∧ UniformEvenLinearBound.{u} K :=
  asymptotic_iff_uniform_linear_bound.symm.trans asymptotic_iff_uniform_even_linear_bound

end Erdos184.UniformEquivalence
