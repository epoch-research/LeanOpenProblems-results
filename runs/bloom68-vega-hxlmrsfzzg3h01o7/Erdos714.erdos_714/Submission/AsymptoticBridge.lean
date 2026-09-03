import FormalConjecturesUtil
import Submission.IncidenceBridge

/-!
# Conditional construction-to-asymptotic bridges

Isolated-vertex padding preserves freeness when every vertex of the forbidden
graph has a neighbor. Consequently its extremal number is monotone in the
number of vertices. We use this to interpolate lower bounds supplied by
constructions on a geometric sequence of sizes.

The results in this file are conditional infrastructure: existence of the
input graphs or function families is always a hypothesis. This file does not
import `Submission.Spec` or assert the full Erdős 714 conjecture.
-/

namespace AsymptoticBridge

open Filter SimpleGraph

section Padding

variable {U V W : Type*} {H : SimpleGraph W} {G : SimpleGraph V}

/-- A copy of a graph with no isolated vertices in a padded graph factors
through the original graph: every vertex of the copy lies on an edge, hence
belongs to the range of the padding embedding. -/
theorem isContained_map_iff_of_noIsolated
    (hH : ∀ w, ∃ w', H.Adj w w') (e : V ↪ U) :
    H.IsContained (G.map e) ↔ H.IsContained G := by
  classical
  constructor
  · rintro ⟨φ⟩
    have hrange : ∀ w, ∃ v, e v = φ w := by
      intro w
      obtain ⟨w', hw⟩ := hH w
      obtain ⟨v, v', _, hv, _⟩ := (map_adj e G _ _).mp (φ.toHom.map_adj hw)
      exact ⟨v, hv⟩
    choose g hg using hrange
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro w w' hw
      have hadj : (G.map e).Adj (φ w) (φ w') := φ.toHom.map_adj hw
      rw [← hg w, ← hg w'] at hadj
      exact map_adj_apply.mp hadj
    · intro w w' heq
      change g w = g w' at heq
      apply φ.injective
      change φ w = φ w'
      rw [← hg w, ← hg w', heq]
  · rintro ⟨φ⟩
    exact ⟨(SimpleGraph.Embedding.map e G).toCopy.comp φ⟩

/-- Adding isolated vertices preserves freeness for a forbidden graph with
no isolated vertices. -/
theorem free_map_iff_of_noIsolated
    (hH : ∀ w, ∃ w', H.Adj w w') (e : V ↪ U) :
    H.Free (G.map e) ↔ H.Free G :=
  not_congr (isContained_map_iff_of_noIsolated hH e)

/-- For a forbidden graph with no isolated vertices, extremal numbers are
monotone in the number of vertices. -/
theorem extremalNumber_monotone_of_noIsolated
    (hH : ∀ w, ∃ w', H.Adj w w') : Monotone (fun n => extremalNumber n H) := by
  classical
  intro m n hmn
  rw [← Fintype.card_fin m, extremalNumber_le_iff]
  intro G _ hfree
  have hpad := card_edgeFinset_le_extremalNumber
    ((free_map_iff_of_noIsolated hH (Fin.castLEEmb hmn)).2 hfree)
  calc
    G.edgeFinset.card = (G.map (Fin.castLEEmb hmn)).edgeFinset.card := by
      simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using
        (card_edgeFinset_map (Fin.castLEEmb hmn) G).symm
    _ ≤ extremalNumber n H := by simpa only [Fintype.card_fin] using hpad

/-- A finite free construction on at most `n` vertices gives a lower bound
at `n`, not just at its exact vertex count. -/
theorem card_edgeFinset_le_extremalNumber_of_card_le
    [Fintype V] [DecidableRel G.Adj]
    (hH : ∀ w, ∃ w', H.Adj w w') (hfree : H.Free G)
    {n : ℕ} (hcard : Fintype.card V ≤ n) :
    G.edgeFinset.card ≤ extremalNumber n H :=
  (card_edgeFinset_le_extremalNumber hfree).trans
    (extremalNumber_monotone_of_noIsolated hH hcard)

/-- A concrete padded graph with exactly the same number of edges. -/
theorem exists_padding_of_noIsolated [Fintype V] [DecidableRel G.Adj]
    (hH : ∀ w, ∃ w', H.Adj w w') (hfree : H.Free G)
    {n : ℕ} (hcard : Fintype.card V ≤ n) :
    ∃ G' : SimpleGraph (Fin n), ∃ _ : DecidableRel G'.Adj,
      H.Free G' ∧ G'.edgeFinset.card = G.edgeFinset.card := by
  classical
  let e : V ↪ Fin n := (Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb hcard)
  exact ⟨G.map e, inferInstance,
    (free_map_iff_of_noIsolated hH e).2 hfree, card_edgeFinset_map e G⟩

/-- Every vertex of `K_{r,r}` has a neighbor when `r > 0`. -/
theorem completeBipartiteGraph_noIsolated {r : ℕ} (hr : 0 < r) :
    ∀ w : Fin r ⊕ Fin r, ∃ w', (completeBipartiteGraph (Fin r) (Fin r)).Adj w w' := by
  intro w
  cases w with
  | inl i => exact ⟨Sum.inr ⟨0, hr⟩, by simp⟩
  | inr i => exact ⟨Sum.inl ⟨0, hr⟩, by simp⟩

/-- In particular, `ex(n, K_{r,r})` is monotone for every `r > 0`. -/
theorem extremalNumber_completeBipartiteGraph_monotone {r : ℕ} (hr : 0 < r) :
    Monotone (fun n => extremalNumber n (completeBipartiteGraph (Fin r) (Fin r))) :=
  extremalNumber_monotone_of_noIsolated (completeBipartiteGraph_noIsolated hr)

end Padding

section Interpolation

/-- Interpolate a power lower bound along any unbounded sequence whose
successive sizes have a bounded ratio. The sizes themselves need not be
monotone; only `f` must be monotone. The proof uses the last size before the
first crossing of `n`. In particular, a positive constant is not lost when
passing from the sequence to all sufficiently large natural numbers. -/
theorem eventually_rpow_lower_bound_of_sequence
    {f : ℕ → ℝ} (hf : Monotone f) {s : ℕ → ℕ}
    (hunbounded : ∀ n, ∃ k, n < s k)
    {a B Q : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (hQ : 0 < Q)
    (hstep : ∀ k, 1 ≤ k → (s (k + 1) : ℝ) ≤ Q * (s k : ℝ))
    (hbound : ∀ k, 1 ≤ k → B * (s k : ℝ) ^ a ≤ f (s k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ f n := by
  classical
  have hQa : 0 < Q ^ a := Real.rpow_pos_of_pos hQ a
  refine ⟨B / Q ^ a, div_pos hB hQa, eventually_atTop.2 ⟨max (s 0) (s 1), ?_⟩⟩
  intro n hn
  let j := Nat.find (hunbounded n)
  have hj : n < s j := Nat.find_spec (hunbounded n)
  have hj1 : 1 < j := by
    by_contra h
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with h | h <;> rw [h] at hj <;> omega
  let k := j - 1
  have hk : 1 ≤ k := by omega
  have hkj : k + 1 = j := by omega
  have hkn : s k ≤ n := by
    exact Nat.le_of_not_gt (Nat.find_min (hunbounded n) (show k < j by omega))
  have hnstep : (n : ℝ) ≤ Q * (s k : ℝ) := by
    have hnj : (n : ℝ) ≤ (s (k + 1) : ℝ) := by exact_mod_cast (hkj ▸ hj.le)
    exact hnj.trans (hstep k hk)
  calc
    B / Q ^ a * (n : ℝ) ^ a ≤ B / Q ^ a * (Q * (s k : ℝ)) ^ a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n) hnstep ha)
        (div_pos hB hQa).le
    _ = B * (s k : ℝ) ^ a := by
      rw [Real.mul_rpow hQ.le (Nat.cast_nonneg _)]
      field_simp
    _ ≤ f (s k) := hbound k hk
    _ ≤ f n := hf hkn

/-- Convenient geometric specialization: a bound of order `(q^k)^a` at
sizes `A*q^k`, for fixed positive `A` and `q > 1`, suffices for an eventual
power lower bound for an arbitrary monotone real-valued function. -/
theorem eventually_rpow_lower_bound_of_geometric
    {f : ℕ → ℝ} (hf : Monotone f) {A q : ℕ} (hA : 0 < A) (hq : 1 < q)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hbound : ∀ k, 1 ≤ k → B * ((q ^ k : ℕ) : ℝ) ^ a ≤ f (A * q ^ k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ f n := by
  have hAr : 0 < (A : ℝ) := Nat.cast_pos.mpr hA
  have hAa : 0 < (A : ℝ) ^ a := Real.rpow_pos_of_pos hAr a
  refine eventually_rpow_lower_bound_of_sequence hf
    (s := fun k => A * q ^ k) (B := B / (A : ℝ) ^ a) (Q := (q : ℝ))
    ?_ ha (div_pos hB hAa) (by exact_mod_cast (show 0 < q by omega)) ?_ ?_
  · intro n
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt n hq
    exact ⟨k, hk.trans_le (Nat.le_mul_of_pos_left _ hA)⟩
  · intro k _
    exact le_of_eq (by push_cast; rw [pow_succ]; ring)
  · intro k hk
    calc
      B / (A : ℝ) ^ a * ((A * q ^ k : ℕ) : ℝ) ^ a =
          B * ((q ^ k : ℕ) : ℝ) ^ a := by
        rw [Nat.cast_mul, Real.mul_rpow hAr.le (Nat.cast_nonneg _)]
        field_simp
      _ ≤ f (A * q ^ k) := hbound k hk

/-- The real-power identity matching the vertex and edge exponents in the
balanced complete-bipartite problem. It includes `k = 0` and needs no
positivity assumption on the natural base. -/
theorem criticalExponent_pow {b r k : ℕ} (hr : 0 < r) :
    ((b ^ (r * k) : ℕ) : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) =
      ((b ^ ((2 * r - 1) * k) : ℕ) : ℝ) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hexp : ((r * k : ℕ) : ℝ) * ((2 : ℝ) - 1 / (r : ℝ)) =
      (((2 * r - 1) * k : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    field_simp
  rw [Nat.cast_pow, ← Real.rpow_natCast (b : ℝ) (r * k),
    ← Real.rpow_mul (Nat.cast_nonneg b), hexp, Real.rpow_natCast, Nat.cast_pow]

/-- The critical exponent is positive already for `r ≥ 1`. -/
theorem criticalExponent_pos {r : ℕ} (hr : 0 < r) :
    0 < (2 : ℝ) - 1 / (r : ℝ) := by
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hdiv : 1 / (r : ℝ) ≤ 1 := (div_le_one hrR).2 hr1
  linarith

end Interpolation

section Constructions

/-- Sparse-sequence criterion for the desired complete-bipartite exponent.
The hypotheses are finite lower bounds, not the eventual conclusion. -/
theorem eventually_extremalNumber_lower_bound_of_geometric_bounds
    {r A B b : ℕ} (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B) (hb : 2 ≤ b)
    (hbound : ∀ k, 1 ≤ k → B * b ^ ((2 * r - 1) * k) ≤
      extremalNumber (A * b ^ (r * k)) (completeBipartiteGraph (Fin r) (Fin r))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  have hr0 : 0 < r := by omega
  refine eventually_rpow_lower_bound_of_geometric
    (Nat.mono_cast.comp (extremalNumber_completeBipartiteGraph_monotone hr0))
    (A := A) (q := b ^ r) hA (Nat.one_lt_pow hr0.ne' (by omega))
    (criticalExponent_pos hr0).le (B := (B : ℝ)) (Nat.cast_pos.mpr hB) ?_
  intro k hk
  simpa only [← pow_mul, criticalExponent_pow hr0, Nat.cast_mul] using
    (Nat.cast_le.mpr (hbound k hk) :
      ((B * b ^ ((2 * r - 1) * k) : ℕ) : ℝ) ≤
        (extremalNumber (A * b ^ (r * k))
          (completeBipartiteGraph (Fin r) (Fin r)) : ℝ))

/-- A supplied family of finite constructions. For each `k ≥ 1`, the graph
has at most `A*b^(r*k)` vertices and at least `B*b^((2*r-1)*k)` edges.
`Fin m` represents an arbitrary finite vertex set, and `Nat.card` avoids any
decidability choices in this hypothesis. -/
def HasGeometricKrrConstructions (r A B b : ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∃ m : ℕ, m ≤ A * b ^ (r * k) ∧
    ∃ G : SimpleGraph (Fin m),
      (completeBipartiteGraph (Fin r) (Fin r)).Free G ∧
        B * b ^ ((2 * r - 1) * k) ≤ Nat.card G.edgeSet

/-- Main conditional graph-construction criterion. Isolated-vertex padding
allows the input graphs to have *at most* the prescribed sizes. -/
theorem eventually_extremalNumber_lower_bound_of_constructions
    {r A B b : ℕ} (hr : 2 ≤ r) (hA : 0 < A) (hB : 0 < B) (hb : 2 ≤ b)
    (hconstruction : HasGeometricKrrConstructions r A B b) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  classical
  apply eventually_extremalNumber_lower_bound_of_geometric_bounds hr hA hB hb
  intro k hk
  obtain ⟨m, hm, G, hfree, hedges⟩ := hconstruction k hk
  apply hedges.trans
  have h := card_edgeFinset_le_extremalNumber_of_card_le
    (completeBipartiteGraph_noIsolated (by omega : 0 < r)) hfree
    (by simpa only [Fintype.card_fin] using hm)
  simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using h

/-- The all-`r` quantifier adapter. Constants and construction bases may
depend on `r`, but must be fixed as `k` varies. This is an implication from
supplied constructions, not an assertion that they exist. -/
theorem all_r_eventual_lower_bound_of_constructions
    (h : ∀ r : ℕ, 2 ≤ r → ∃ A B b : ℕ,
      0 < A ∧ 0 < B ∧ 2 ≤ b ∧ HasGeometricKrrConstructions r A B b) :
    ∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  intro r hr
  obtain ⟨A, B, b, hA, hB, hb, hconstruction⟩ := h r hr
  exact eventually_extremalNumber_lower_bound_of_constructions hr hA hB hb hconstruction

end Constructions

section FunctionFamilies

/-- Function families of the critical sizes, supplied separately for every
`k ≥ 1`. No existence claim is made by this definition. -/
def HasCriticalFunctionFamilies (r b : ℕ) : Prop :=
  ∀ k, 1 ≤ k →
    ∃ f : Fin (b ^ (r * k)) → Fin (b ^ ((r - 1) * k)) → Fin (b ^ k),
      ¬ IncidenceBridge.HasAgreementRectangle f r

/-- The exact counts for a function family with the critical sizes. The
incidence graph has `2*b^(r*k)` vertices and `b^((2*r-1)*k)` edges. These
identities are independent of the no-agreement-rectangle condition. -/
theorem criticalFunctionFamily_counts {r b k : ℕ} (hr : 0 < r)
    (f : Fin (b ^ (r * k)) → Fin (b ^ ((r - 1) * k)) → Fin (b ^ k)) :
    Fintype.card (Fin (b ^ (r * k)) ⊕
      (Fin (b ^ ((r - 1) * k)) × Fin (b ^ k))) = 2 * b ^ (r * k) ∧
      Nat.card (IncidenceBridge.incidenceGraph f).edgeSet = b ^ ((2 * r - 1) * k) := by
  classical
  have hcoord : (r - 1) * k + k = r * k := by
    calc
      (r - 1) * k + k = (r - 1 + 1) * k := by ring
      _ = r * k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
  constructor
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_add, hcoord]
    omega
  · rw [Nat.card_eq_fintype_card, IncidenceBridge.incidenceGraph_card_edgeSet]
    simp only [Fintype.card_fin]
    rw [← pow_add, ← Nat.add_mul, show r + (r - 1) = 2 * r - 1 by omega]

/-- Supplied critical function families give actual finite free graph
constructions with `A = 2` and `B = 1`. The finite vertex set is relabelled
as `Fin (2*b^(r*k))` by the generic padding theorem. -/
theorem constructions_of_criticalFunctionFamilies {r b : ℕ} (hr : 0 < r)
    (hfamily : HasCriticalFunctionFamilies r b) :
    HasGeometricKrrConstructions r 2 1 b := by
  classical
  intro k hk
  obtain ⟨f, hf⟩ := hfamily k hk
  obtain ⟨hvertices, hedges⟩ := criticalFunctionFamily_counts hr f
  have hfree := (IncidenceBridge.free_iff_noAgreementRectangle f hr).2 hf
  obtain ⟨G, _, hG, hcount⟩ := exists_padding_of_noIsolated
    (completeBipartiteGraph_noIsolated hr) hfree hvertices.le
  refine ⟨2 * b ^ (r * k), le_rfl, G, hG, ?_⟩
  rw [one_mul]
  apply le_of_eq
  apply hedges.symm.trans
  simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using hcount.symm

/-- Main conditional function-family criterion, with exactly the spaces
`Fin (b^(r*k))`, `Fin (b^((r-1)*k))`, and `Fin (b^k)`.
The only combinatorial hypothesis is absence of an agreement rectangle. -/
theorem eventually_extremalNumber_lower_bound_of_functionFamilies
    {r b : ℕ} (hr : 2 ≤ r) (hb : 2 ≤ b)
    (hfamily : HasCriticalFunctionFamilies r b) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) :=
  eventually_extremalNumber_lower_bound_of_constructions hr (by norm_num) (by norm_num) hb
    (constructions_of_criticalFunctionFamilies (by omega) hfamily)

/-- All-`r` adapter for supplied no-agreement-rectangle families. The base
may depend on `r` but is uniform in `k`. The conclusion matches the
quantifier and real-power form of Erdős 714, conditionally on these families. -/
theorem all_r_eventual_lower_bound_of_functionFamilies
    (h : ∀ r : ℕ, 2 ≤ r → ∃ b : ℕ, 2 ≤ b ∧ HasCriticalFunctionFamilies r b) :
    ∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  intro r hr
  obtain ⟨b, hb, hfamily⟩ := h r hr
  exact eventually_extremalNumber_lower_bound_of_functionFamilies hr hb hfamily

end FunctionFamilies

end AsymptoticBridge
