import FormalConjecturesUtil

/-!
# Weighted proper-induced goodness and critical link pressure

Stable-set and clique budgets are stated directly for finite vertex subsets of
an actual `SimpleGraph`. Proper-induced goodness is a hypothesis, not a claim
about all graphs. The main bound is the audited link inequality from §5 of
`eh_global_perturbation_bridge/lemma_notes.md`.

These auxiliary results are independent of the unresolved Erdős–Hajnal theorem.
In particular, this file does not import `Submission.Spec` or use its statements.
-/

namespace Erdos61Research

open SimpleGraph

variable {V : Type*}

/-- Every independent finite subset of `A` has `x`-weight at most `a`. -/
def WeightStableBound (G : SimpleGraph V) (A : Finset V) (x : V → ℝ) (a : ℝ) : Prop :=
  ∀ I : Finset V, I ⊆ A → G.IsIndepSet (I : Set V) → ∑ v ∈ I, x v ≤ a

/-- Every clique finite subset of `A` has `y`-weight at most `b`. -/
def WeightCliqueBound (G : SimpleGraph V) (A : Finset V) (y : V → ℝ) (b : ℝ) : Prop :=
  ∀ C : Finset V, C ⊆ A → G.IsClique (C : Set V) → ∑ v ∈ C, y v ≤ b

/-- The weighted power inequality on `A`, for all nonnegative normalized pairs. -/
def WpOn (G : SimpleGraph V) (A : Finset V) (p : ℝ) : Prop :=
  ∀ x y : V → ℝ, (∀ v, 0 ≤ x v) → (∀ v, 0 ≤ y v) →
    WeightStableBound G A x 1 → WeightCliqueBound G A y 1 →
    ∑ v ∈ A, (x v * y v) ^ p ≤ 1

/-- Every proper induced vertex subset, including the empty one, satisfies `WpOn`. -/
def AllProperWp [Fintype V] (G : SimpleGraph V) (p : ℝ) : Prop :=
  ∀ A : Finset V, A ≠ Finset.univ → WpOn G A p

/-- Restricting the vertex set preserves a stable-set budget. -/
theorem WeightStableBound.mono {G : SimpleGraph V} {A B : Finset V} {x : V → ℝ} {a : ℝ}
    (h : WeightStableBound G A x a) (hBA : B ⊆ A) : WeightStableBound G B x a := by
  intro I hI hstable
  exact h I (hI.trans hBA) hstable

/-- Restricting the vertex set preserves a clique budget. -/
theorem WeightCliqueBound.mono {G : SimpleGraph V} {A B : Finset V} {y : V → ℝ} {b : ℝ}
    (h : WeightCliqueBound G A y b) (hBA : B ⊆ A) : WeightCliqueBound G B y b := by
  intro C hC hclique
  exact h C (hC.trans hBA) hclique

/-- Singleton independent sets bound each individual weight on `A`. -/
theorem WeightStableBound.le_of_mem [DecidableEq V] {G : SimpleGraph V} {A : Finset V}
    {x : V → ℝ} {a : ℝ} (h : WeightStableBound G A x a) {v : V} (hv : v ∈ A) :
    x v ≤ a := by
  have hsingle : G.IsIndepSet (({v} : Finset V) : Set V) := by
    simp [SimpleGraph.IsIndepSet]
  simpa using h {v} (Finset.singleton_subset_iff.mpr hv) hsingle

/-- Singleton cliques bound each individual weight on `A`. -/
theorem WeightCliqueBound.le_of_mem [DecidableEq V] {G : SimpleGraph V} {A : Finset V}
    {y : V → ℝ} {b : ℝ} (h : WeightCliqueBound G A y b) {v : V} (hv : v ∈ A) :
    y v ≤ b := by
  have hsingle : G.IsClique (({v} : Finset V) : Set V) := by
    simp
  simpa using h {v} (Finset.singleton_subset_iff.mpr hv) hsingle

/-- Division by a positive stable-set budget gives budget one. -/
theorem WeightStableBound.div {G : SimpleGraph V} {A : Finset V} {x : V → ℝ} {a : ℝ}
    (h : WeightStableBound G A x a) (ha : 0 < a) :
    WeightStableBound G A (fun v => x v / a) 1 := by
  intro I hI hstable
  rw [← Finset.sum_div]
  exact (div_le_one ha).mpr (h I hI hstable)

/-- Division by a positive clique budget gives budget one. -/
theorem WeightCliqueBound.div {G : SimpleGraph V} {A : Finset V} {y : V → ℝ} {b : ℝ}
    (h : WeightCliqueBound G A y b) (hb : 0 < b) :
    WeightCliqueBound G A (fun v => y v / b) 1 := by
  intro C hC hclique
  rw [← Finset.sum_div]
  exact (div_le_one hb).mpr (h C hC hclique)

/-- Positive-budget normalization. This is valid for every real exponent, hence
in particular for positive exponents. No positivity of individual weights is needed. -/
theorem WpOn.scale {G : SimpleGraph V} {A : Finset V} {p : ℝ} (hgood : WpOn G A p)
    {x y : V → ℝ} {a b : ℝ} (hx : ∀ v, 0 ≤ x v) (hy : ∀ v, 0 ≤ y v)
    (hstable : WeightStableBound G A x a) (hclique : WeightCliqueBound G A y b)
    (ha : 0 < a) (hb : 0 < b) : ∑ v ∈ A, (x v * y v) ^ p ≤ (a * b) ^ p := by
  have hnormalized := hgood (fun v => x v / a) (fun v => y v / b)
    (fun v => div_nonneg (hx v) ha.le) (fun v => div_nonneg (hy v) hb.le)
    (hstable.div ha) (hclique.div hb)
  have hsum : (∑ v ∈ A, (x v / a * (y v / b)) ^ p) =
      (∑ v ∈ A, (x v * y v) ^ p) / (a * b) ^ p := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    rw [div_mul_div_comm, Real.div_rpow (mul_nonneg (hx v) (hy v)) (mul_pos ha hb).le p]
  rw [hsum] at hnormalized
  exact (div_le_one (Real.rpow_pos_of_pos (mul_pos ha hb) p)).mp hnormalized

/-- Positive exponents also permit zero budgets: singleton bounds force the
corresponding weights to vanish throughout `A`. -/
theorem WpOn.scale_nonneg [DecidableEq V] {G : SimpleGraph V} {A : Finset V} {p : ℝ}
    (hgood : WpOn G A p) (hp : 0 < p) {x y : V → ℝ} {a b : ℝ}
    (hx : ∀ v, 0 ≤ x v) (hy : ∀ v, 0 ≤ y v)
    (hstable : WeightStableBound G A x a) (hclique : WeightCliqueBound G A y b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : ∑ v ∈ A, (x v * y v) ^ p ≤ (a * b) ^ p := by
  by_cases ha0 : a = 0
  · subst a
    have hxzero : ∀ v ∈ A, x v = 0 := fun v hv =>
      le_antisymm (hstable.le_of_mem hv) (hx v)
    simp only [zero_mul, Real.zero_rpow (ne_of_gt hp)]
    apply le_of_eq
    exact Finset.sum_eq_zero (fun v hv => by
      rw [hxzero v hv, zero_mul, Real.zero_rpow (ne_of_gt hp)])
  by_cases hb0 : b = 0
  · subst b
    have hyzero : ∀ v ∈ A, y v = 0 := fun v hv =>
      le_antisymm (hclique.le_of_mem hv) (hy v)
    simp only [mul_zero, Real.zero_rpow (ne_of_gt hp)]
    apply le_of_eq
    exact Finset.sum_eq_zero (fun v hv => by
      rw [hyzero v hv, mul_zero, Real.zero_rpow (ne_of_gt hp)])
  exact hgood.scale hx hy hstable hclique
    (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0))

section FiniteLinks

variable [Fintype V]

/-- The finite neighbor set of the actual graph. Decidability is chosen locally. -/
noncomputable def neighborVertices (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (G.neighborSet v).toFinset

/-- Nonneighbors other than `v`, equivalently the complement of the closed neighborhood. -/
noncomputable def nonneighborVertices (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact ((G.neighborSet v)ᶜ \ {v}).toFinset

@[simp] theorem mem_neighborVertices (G : SimpleGraph V) (v w : V) :
    w ∈ neighborVertices G v ↔ G.Adj v w := by
  classical
  simp [neighborVertices, SimpleGraph.mem_neighborSet]

@[simp] theorem mem_nonneighborVertices (G : SimpleGraph V) (v w : V) :
    w ∈ nonneighborVertices G v ↔ w ≠ v ∧ ¬G.Adj v w := by
  classical
  simp [nonneighborVertices, SimpleGraph.mem_neighborSet, and_comm]

@[simp] theorem coe_neighborVertices (G : SimpleGraph V) (v : V) :
    (neighborVertices G v : Set V) = G.neighborSet v := by
  classical
  simp [neighborVertices]

@[simp] theorem coe_nonneighborVertices (G : SimpleGraph V) (v : V) :
    (nonneighborVertices G v : Set V) = (G.neighborSet v)ᶜ \ {v} := by
  classical
  simp [nonneighborVertices]

@[simp] theorem notMem_neighborVertices_self (G : SimpleGraph V) (v : V) :
    v ∉ neighborVertices G v := by
  simp

@[simp] theorem notMem_nonneighborVertices_self (G : SimpleGraph V) (v : V) :
    v ∉ nonneighborVertices G v := by
  simp

/-- Looplessness makes the neighbor set proper. -/
theorem neighborVertices_ne_univ (G : SimpleGraph V) (v : V) :
    neighborVertices G v ≠ Finset.univ := by
  intro h
  exact notMem_neighborVertices_self G v (by rw [h]; exact Finset.mem_univ v)

/-- Excluding the distinguished vertex makes the nonneighbor set proper. -/
theorem nonneighborVertices_ne_univ (G : SimpleGraph V) (v : V) :
    nonneighborVertices G v ≠ Finset.univ := by
  intro h
  exact notMem_nonneighborVertices_self G v (by rw [h]; exact Finset.mem_univ v)

/-- The two links are disjoint. -/
theorem disjoint_link_vertices (G : SimpleGraph V) (v : V) :
    Disjoint (neighborVertices G v) (nonneighborVertices G v) := by
  refine Finset.disjoint_left.mpr ?_
  intro w hw hn
  exact ((mem_nonneighborVertices G v w).mp hn).2 ((mem_neighborVertices G v w).mp hw)

variable [DecidableEq V]

/-- Together with `v`, the two links partition the entire vertex set. -/
theorem insert_union_link_vertices (G : SimpleGraph V) (v : V) :
    insert v (neighborVertices G v ∪ nonneighborVertices G v) = Finset.univ := by
  classical
  ext w
  simp only [Finset.mem_insert, Finset.mem_union, mem_neighborVertices,
    mem_nonneighborVertices, Finset.mem_univ, iff_true]
  tauto

/-- Exact finite-sum decomposition into the neighbor link, the nonneighbor link, and `v`. -/
theorem sum_univ_link_partition (G : SimpleGraph V) (v : V) (f : V → ℝ) :
    ∑ w : V, f w = (∑ w ∈ neighborVertices G v, f w) +
      (∑ w ∈ nonneighborVertices G v, f w) + f v := by
  have hnot : v ∉ neighborVertices G v ∪ nonneighborVertices G v := by simp
  rw [← insert_union_link_vertices G v, Finset.sum_insert hnot,
    Finset.sum_union (disjoint_link_vertices G v)]
  ring

/-- Cliques in the neighbor link extend to cliques by adding `v`. -/
theorem isClique_insert_of_subset_neighborVertices {G : SimpleGraph V} {v : V}
    {C : Finset V} (hC : C ⊆ neighborVertices G v) (hclique : G.IsClique (C : Set V)) :
    G.IsClique ((insert v C : Finset V) : Set V) := by
  rw [Finset.coe_insert]
  exact hclique.insert (fun w hw _ => (mem_neighborVertices G v w).mp (hC hw))

/-- Stable sets in the nonneighbor link extend to stable sets by adding `v`. -/
theorem isIndepSet_insert_of_subset_nonneighborVertices {G : SimpleGraph V} {v : V}
    {I : Finset V} (hI : I ⊆ nonneighborVertices G v) (hstable : G.IsIndepSet (I : Set V)) :
    G.IsIndepSet ((insert v I : Finset V) : Set V) := by
  rw [Finset.coe_insert, SimpleGraph.isIndepSet_iff]
  exact hstable.insert_of_symmetric (fun _ _ hn ha => hn ha.symm)
    (fun w hw _ => ((mem_nonneighborVertices G v w).mp (hI hw)).2)

/-- In the neighbor link the clique budget improves by the weight of `v`. -/
theorem WeightCliqueBound.on_neighbors {G : SimpleGraph V} {y : V → ℝ} {b : ℝ}
    (h : WeightCliqueBound G Finset.univ y b) (v : V) :
    WeightCliqueBound G (neighborVertices G v) y (b - y v) := by
  intro C hC hclique
  have hv : v ∉ C := fun hv => notMem_neighborVertices_self G v (hC hv)
  have hsum := h (insert v C) (Finset.subset_univ _)
    (isClique_insert_of_subset_neighborVertices hC hclique)
  rw [Finset.sum_insert hv] at hsum
  linarith

/-- In the nonneighbor link the stable-set budget improves by the weight of `v`. -/
theorem WeightStableBound.on_nonneighbors {G : SimpleGraph V} {x : V → ℝ} {a : ℝ}
    (h : WeightStableBound G Finset.univ x a) (v : V) :
    WeightStableBound G (nonneighborVertices G v) x (a - x v) := by
  intro I hI hstable
  have hv : v ∉ I := fun hv => notMem_nonneighborVertices_self G v (hI hv)
  have hsum := h (insert v I) (Finset.subset_univ _)
    (isIndepSet_insert_of_subset_nonneighborVertices hI hstable)
  rw [Finset.sum_insert hv] at hsum
  linarith

/-- Audited link pressure. Only the weights at the chosen vertex need be below one. -/
theorem AllProperWp.link_pressure {G : SimpleGraph V} {p : ℝ}
    (hproper : AllProperWp G p) (hp : 0 < p) {x y : V → ℝ}
    (hx : ∀ w, 0 ≤ x w) (hy : ∀ w, 0 ≤ y w)
    (hstable : WeightStableBound G Finset.univ x 1)
    (hclique : WeightCliqueBound G Finset.univ y 1)
    (v : V) (hxv : x v < 1) (hyv : y v < 1) :
    ∑ w : V, (x w * y w) ^ p ≤
      (1 - x v) ^ p + (1 - y v) ^ p + (x v * y v) ^ p := by
  have hN : (∑ w ∈ neighborVertices G v, (x w * y w) ^ p) ≤ (1 - y v) ^ p := by
    simpa only [one_mul] using
      (hproper (neighborVertices G v) (neighborVertices_ne_univ G v)).scale_nonneg hp hx hy
        (hstable.mono (Finset.subset_univ _)) (hclique.on_neighbors v)
        (by norm_num : (0 : ℝ) ≤ 1) (sub_pos.mpr hyv).le
  have hM : (∑ w ∈ nonneighborVertices G v, (x w * y w) ^ p) ≤ (1 - x v) ^ p := by
    simpa only [mul_one] using
      (hproper (nonneighborVertices G v) (nonneighborVertices_ne_univ G v)).scale_nonneg hp hx hy
        (hstable.on_nonneighbors v) (hclique.mono (Finset.subset_univ _))
        (sub_pos.mpr hxv).le (by norm_num : (0 : ℝ) ≤ 1)
  rw [sum_univ_link_partition G v (fun w => (x w * y w) ^ p)]
  linarith

/-- The globally subunit version of the link-pressure inequality. -/
theorem weighted_link_pressure {G : SimpleGraph V} {p : ℝ}
    (hproper : AllProperWp G p) (hp : 0 < p) {x y : V → ℝ}
    (hx : ∀ w, 0 ≤ x w) (hy : ∀ w, 0 ≤ y w)
    (hstable : WeightStableBound G Finset.univ x 1)
    (hclique : WeightCliqueBound G Finset.univ y 1)
    (hxlt : ∀ w, x w < 1) (hylt : ∀ w, y w < 1) (v : V) :
    ∑ w : V, (x w * y w) ^ p ≤
      (1 - x v) ^ p + (1 - y v) ^ p + (x v * y v) ^ p :=
  hproper.link_pressure hp hx hy hstable hclique v (hxlt v) (hylt v)

/-- If the normalized pair violates `WpOn` globally, the audited upper bound
is strictly greater than one. This is conditional pressure, not an EH conclusion. -/
theorem AllProperWp.critical_link_pressure {G : SimpleGraph V} {p : ℝ}
    (hproper : AllProperWp G p) (hp : 0 < p) {x y : V → ℝ}
    (hx : ∀ w, 0 ≤ x w) (hy : ∀ w, 0 ≤ y w)
    (hstable : WeightStableBound G Finset.univ x 1)
    (hclique : WeightCliqueBound G Finset.univ y 1)
    (hZ : 1 < ∑ w : V, (x w * y w) ^ p) (v : V)
    (hxv : x v < 1) (hyv : y v < 1) :
    1 < (1 - x v) ^ p + (1 - y v) ^ p + (x v * y v) ^ p :=
  hZ.trans_le (hproper.link_pressure hp hx hy hstable hclique v hxv hyv)

end FiniteLinks

end Erdos61Research
