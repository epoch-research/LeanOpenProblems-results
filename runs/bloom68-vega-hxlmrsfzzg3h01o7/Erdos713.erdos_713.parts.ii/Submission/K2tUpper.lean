import FormalConjecturesUtil

/-!
# A non-sharp Kővári–Sós–Turán upper bound for K₂,t

For `t ≥ 1`, every finite graph avoiding `completeBipartiteGraph (Fin 2) (Fin t)`
has at most `t * n^(3/2)` edges. The proof bounds the common neighbors of distinct
vertices, double-counts ordered walks of length two, and applies Cauchy–Schwarz.

These results concern only K₂,t and graphs contained in K₂,t. They do not resolve
the universal rational-exponent question of Erdős Problem 713.
-/

open Filter Asymptotics SimpleGraph
open scoped BigOperators

namespace Erdos713K2tUpper

universe u v

/-- The forbidden complete bipartite graph, with left part of size two. -/
abbrev K2t (t : ℕ) : SimpleGraph (Fin 2 ⊕ Fin t) :=
  completeBipartiteGraph (Fin 2) (Fin t)

section Finite

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two distinct vertices with at least `t` common neighbors give a copy of K₂,t. -/
lemma k2t_isContained_of_le_card_commonNeighbors {t : ℕ} {x y : V}
    (hxy : x ≠ y) (ht : t ≤ Fintype.card (G.commonNeighbors x y)) :
    K2t t ⊑ G := by
  classical
  have ht' : t ≤ (G.commonNeighbors x y).toFinset.card := by simpa using ht
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq ht'
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{x, y}, s, by simp [hxy], by simpa using hcard, ?_⟩
  intro a ha b hb
  have hab : G.Adj x b ∧ G.Adj y b := by
    simpa only [Set.mem_toFinset, mem_commonNeighbors] using hs hb
  have ha' : a = x ∨ a = y := by simpa using ha
  rcases ha' with rfl | rfl
  · exact hab.1
  · exact hab.2

/-- In a K₂,t-free graph, distinct vertices have fewer than `t` common neighbors. -/
lemma card_commonNeighbors_lt_of_free {t : ℕ} (hfree : (K2t t).Free G)
    {x y : V} (hxy : x ≠ y) : Fintype.card (G.commonNeighbors x y) < t := by
  by_contra! h
  exact hfree (k2t_isContained_of_le_card_commonNeighbors hxy h)

/-- The usual common-neighbor bound, in natural-number form. -/
lemma card_commonNeighbors_le_of_free {t : ℕ} (hfree : (K2t t).Free G)
    {x y : V} (hxy : x ≠ y) : Fintype.card (G.commonNeighbors x y) ≤ t - 1 := by
  have := card_commonNeighbors_lt_of_free hfree hxy
  omega

/-- Double-count ordered walks of length two, allowing their endpoints to coincide. -/
lemma sum_degree_sq_eq_sum_commonNeighbors :
    (∑ z : V, G.degree z ^ 2) =
      ∑ x : V, ∑ y : V, Fintype.card (G.commonNeighbors x y) := by
  classical
  have hdeg (z : V) : G.degree z = ∑ x : V, if G.Adj z x then 1 else 0 := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]
  have hcommon (x y : V) : Fintype.card (G.commonNeighbors x y) =
      ∑ z : V, (if G.Adj z x then 1 else 0) * (if G.Adj z y then 1 else 0) := by
    rw [← Set.toFinset_card]
    have hset : (G.commonNeighbors x y).toFinset =
        Finset.univ.filter (fun z => G.Adj z x ∧ G.Adj z y) := by
      ext z
      simp [mem_commonNeighbors, adj_comm]
    rw [hset, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hx : G.Adj z x <;> by_cases hy : G.Adj z y <;> simp [hx, hy]
  simp_rw [hcommon]
  calc
    (∑ z : V, G.degree z ^ 2) =
        ∑ z : V, ∑ x : V, ∑ y : V,
          (if G.Adj z x then 1 else 0) * (if G.Adj z y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hdeg, pow_two, Finset.sum_mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]

/-- A crude second-moment degree bound. Off the diagonal there are at most
`t - 1` common neighbors, while each diagonal contribution is at most `|V|`. -/
lemma sum_degree_sq_le {t : ℕ} (ht : 1 ≤ t) (hfree : (K2t t).Free G) :
    (∑ z : V, G.degree z ^ 2) ≤ t * Fintype.card V ^ 2 := by
  classical
  rw [sum_degree_sq_eq_sum_commonNeighbors]
  calc
    (∑ x : V, ∑ y : V, Fintype.card (G.commonNeighbors x y)) ≤
        ∑ x : V, ∑ y : V, ((t - 1) + if y = x then Fintype.card V else 0) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      by_cases hxy : y = x
      · subst y
        simp only [ite_true]
        exact (G.card_commonNeighbors_lt_card_verts x x).le.trans (Nat.le_add_left _ _)
      · simpa only [if_neg hxy, Nat.add_zero] using
          card_commonNeighbors_le_of_free hfree (Ne.symm hxy)
    _ = (t - 1 + 1) * Fintype.card V ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    _ = t * Fintype.card V ^ 2 := by rw [Nat.sub_add_cancel ht]

/-- A finite algebraic Kővári–Sós–Turán bound, valid even when the host has no vertices. -/
theorem four_mul_card_edges_sq_le {t : ℕ} (ht : 1 ≤ t) (hfree : (K2t t).Free G) :
    4 * G.edgeFinset.card ^ 2 ≤ t * Fintype.card V ^ 3 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
    (fun z => G.degree z) (fun _ => (1 : ℕ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    G.sum_degrees_eq_twice_card_edges] at hCS
  have hsum := Nat.mul_le_mul_right (Fintype.card V) (sum_degree_sq_le ht hfree)
  nlinarith

/-- A simpler, deliberately non-sharp algebraic form: `m² ≤ t n³`. -/
theorem card_edges_sq_le {t : ℕ} (ht : 1 ≤ t) (hfree : (K2t t).Free G) :
    G.edgeFinset.card ^ 2 ≤ t * Fintype.card V ^ 3 := by
  have := four_mul_card_edges_sq_le ht hfree
  omega

/-- The real-valued edge bound with the convenient non-sharp constant `C(t) = t`. -/
theorem card_edges_le_rpow {t : ℕ} (ht : 1 ≤ t) (hfree : (K2t t).Free G) :
    (G.edgeFinset.card : ℝ) ≤ (t : ℝ) * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) := by
  have hsq : (G.edgeFinset.card : ℝ) ^ 2 ≤
      (t : ℝ) * (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast card_edges_sq_le ht hfree
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht2 : (t : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
  have hpow : ((Fintype.card V : ℝ) ^ (3 / 2 : ℝ)) ^ 2 =
      (Fintype.card V : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  apply (sq_le_sq₀ (by positivity)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))).mp
  rw [mul_pow, hpow]
  exact hsq.trans (mul_le_mul_of_nonneg_right ht2 (by positivity))

/-- Avoiding any graph contained in K₂,t implies the same algebraic edge bound. -/
theorem card_edges_sq_le_of_isContained {W : Type v} {H : SimpleGraph W}
    {t : ℕ} (ht : 1 ≤ t) (hH : H ⊑ K2t t) (hfree : H.Free G) :
    G.edgeFinset.card ^ 2 ≤ t * Fintype.card V ^ 3 :=
  card_edges_sq_le ht (fun h => hfree (hH.trans h))

end Finite

/-- A pointwise non-sharp Kővári–Sós–Turán bound on the extremal number. -/
theorem extremalNumber_le_rpow {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    (extremalNumber n (K2t t) : ℝ) ≤ (t : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  rw [← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg (K2t t) (by positivity)).mpr
  intro G _ hfree
  exact card_edges_le_rpow ht hfree

/-- For every fixed `t ≥ 1`, the K₂,t extremal number is `O(n^(3/2))`. -/
theorem extremalNumber_isBigO_rpow {t : ℕ} (ht : 1 ≤ t) :
    (fun n : ℕ => (extremalNumber n (K2t t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  refine IsBigO.of_bound (t : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  simpa only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using
      extremalNumber_le_rpow ht n

/-- The pointwise bound is inherited by every forbidden graph contained in K₂,t. -/
theorem extremalNumber_le_rpow_of_isContained {W : Type v} {H : SimpleGraph W}
    {t : ℕ} (ht : 1 ≤ t) (hH : H ⊑ K2t t) (n : ℕ) :
    (extremalNumber n H : ℝ) ≤ (t : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hle : (extremalNumber n H : ℝ) ≤ (extremalNumber n (K2t t) : ℝ) := by
    exact_mod_cast hH.extremalNumber_le (n := n)
  exact hle.trans (extremalNumber_le_rpow ht n)

/-- In particular, every fixed forbidden graph contained in some K₂,t has extremal
number `O(n^(3/2))`. No hypotheses on bipartitions or vertex labels are needed. -/
theorem extremalNumber_isBigO_rpow_of_isContained {W : Type v} {H : SimpleGraph W}
    {t : ℕ} (ht : 1 ≤ t) (hH : H ⊑ K2t t) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  refine IsBigO.of_bound (t : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  simpa only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using
      extremalNumber_le_rpow_of_isContained ht hH n

end Erdos713K2tUpper

#print axioms Erdos713K2tUpper.k2t_isContained_of_le_card_commonNeighbors
#print axioms Erdos713K2tUpper.card_commonNeighbors_lt_of_free
#print axioms Erdos713K2tUpper.card_commonNeighbors_le_of_free
#print axioms Erdos713K2tUpper.sum_degree_sq_eq_sum_commonNeighbors
#print axioms Erdos713K2tUpper.sum_degree_sq_le
#print axioms Erdos713K2tUpper.four_mul_card_edges_sq_le
#print axioms Erdos713K2tUpper.card_edges_sq_le
#print axioms Erdos713K2tUpper.card_edges_le_rpow
#print axioms Erdos713K2tUpper.card_edges_sq_le_of_isContained
#print axioms Erdos713K2tUpper.extremalNumber_le_rpow
#print axioms Erdos713K2tUpper.extremalNumber_isBigO_rpow
#print axioms Erdos713K2tUpper.extremalNumber_le_rpow_of_isContained
#print axioms Erdos713K2tUpper.extremalNumber_isBigO_rpow_of_isContained
