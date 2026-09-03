import FormalConjecturesUtil

/-!
# Finite degree-tail bounds from hereditary power bounds

This file is independent of `Submission.Spec`. All induced-subgraph hypotheses
are quantified over every vertex subset of the finite host. The averaging
argument is deterministic: deleting a minimum-weight element does not decrease
an average. No extremality or forbidden-subgraph hypothesis is used.
-/

open Finset SimpleGraph

namespace Erdos713DegreeTail

universe u

/-- Among the `k`-element subsets of a finite weighted set, one has at least
its proportional share of the total weight. The weights may be arbitrary reals. -/
theorem exists_subset_card_mul_sum_ge {V : Type u} (U : Finset V) (w : V → ℝ)
    (k : ℕ) (hk : k ≤ U.card) :
    ∃ T ⊆ U, T.card = k ∧
      (k : ℝ) * (∑ v ∈ U, w v) ≤ (U.card : ℝ) * (∑ v ∈ T, w v) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    exact ⟨∅, empty_subset _, by simp, by simp⟩
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases heq : k = U.card
    · exact ⟨U, Subset.refl _, heq.symm, by rw [heq]⟩
    have hlt : k < U.card := lt_of_le_of_ne hk heq
    obtain ⟨x, hx, hmin⟩ := U.exists_min_image w (card_pos.mp (by omega))
    have hk' : k ≤ (U.erase x).card := by rw [card_erase_of_mem hx]; omega
    obtain ⟨T, hTU, hT, hsum⟩ := ih (U.erase x) (erase_ssubset hx) hk'
    refine ⟨T, hTU.trans (erase_subset _ _), hT, ?_⟩
    have hminsum : (U.card : ℝ) * w x ≤ ∑ v ∈ U, w v := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hmin
    have hc : (U.card : ℝ) = ((U.erase x).card : ℝ) + 1 := by
      exact_mod_cast (card_erase_add_one hx).symm
    have hpos : 0 < ((U.erase x).card : ℝ) := by exact_mod_cast (show 0 < (U.erase x).card by omega)
    rw [← sum_erase_add U w hx, hc] at hminsum ⊢
    have hp := mul_le_mul_of_nonneg_left hsum (show 0 ≤ ((U.erase x).card : ℝ) + 1 by positivity)
    have hq := mul_le_mul_of_nonneg_left hminsum (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    apply (mul_le_mul_iff_of_pos_left hpos).mp
    nlinarith

section Graph

variable {V : Type u}

open scoped Classical

/-- The directed cut count is the sum of the neighbor counts in its right part. -/
lemma card_interedges_eq_sum (G : SimpleGraph V) (S T : Finset V) :
    (G.interedges S T).card = ∑ v ∈ S, (T.filter (G.Adj v)).card := by
  simp only [SimpleGraph.interedges_def, card_filter, sum_product]

/-- Interchanging the two parts does not change the cut count. -/
lemma card_interedges_comm (G : SimpleGraph V) (S T : Finset V) :
    (G.interedges S T).card = (G.interedges T S).card :=
  Rel.card_interedges_comm G.symm S T

variable [Fintype V]

omit [Fintype V] in
/-- Counting both orientations of the edges of an induced subgraph. -/
lemma card_interedges_self (G : SimpleGraph V) (S : Finset V) :
    (G.interedges S S).card = 2 * (G.induce (S : Set V)).edgeFinset.card := by
  rw [card_interedges_eq_sum, ← (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges,
    ← sum_coe_sort S]
  apply sum_congr rfl
  intro v _
  rw [card_filter]
  exact (sum_coe_sort S (fun w => if G.Adj v.val w then 1 else 0)).symm.trans
    ((G.induce (S : Set V)).degree_eq_sum_if_adj (R := ℕ) v).symm

variable [DecidableEq V]

/-- The degree sum on `S` counts internal edges twice and cut edges once. -/
lemma sum_degrees_eq_internal_add_cut (G : SimpleGraph V) (S : Finset V) :
    (∑ v ∈ S, G.degree v) =
      2 * (G.induce (S : Set V)).edgeFinset.card + (G.interedges S Sᶜ).card := by
  rw [← card_interedges_self, card_interedges_eq_sum, card_interedges_eq_sum,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  simp only [card_filter, sum_add_sum_compl]
  exact G.degree_eq_sum_if_adj v

omit [Fintype V] in
/-- For disjoint parts, the cut is a subset of the edges induced by their union. -/
lemma card_interedges_le_induce_union (G : SimpleGraph V) {S T : Finset V}
    (hST : Disjoint S T) :
    (G.interedges S T).card ≤ (G.induce ((S ∪ T : Finset V) : Set V)).edgeFinset.card := by
  have hdis : Disjoint (G.interedges S T) (G.interedges T S) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hST (G.mem_interedges_iff.mp he).1 (G.mem_interedges_iff.mp hf).1
  have hsub : G.interedges S T ∪ G.interedges T S ⊆ G.interedges (S ∪ T) (S ∪ T) := by
    exact union_subset (G.interedges_mono subset_union_left subset_union_right)
      (G.interedges_mono subset_union_right subset_union_left)
  have h := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_interedges_comm G T S, card_interedges_self] at h
  omega

omit [Fintype V] [DecidableEq V] in
/-- Finite cut averaging, with no probability space and no graph-density
hypothesis: a `k`-subset of the right part captures at least a `k / |U|` share. -/
theorem exists_cut_subset (G : SimpleGraph V) (S U : Finset V)
    (k : ℕ) (hk : k ≤ U.card) :
    ∃ T ⊆ U, T.card = k ∧
      k * (G.interedges S U).card ≤ U.card * (G.interedges S T).card := by
  obtain ⟨T, hTU, hT, havg⟩ := exists_subset_card_mul_sum_ge U
    (fun v => ((S.filter (G.Adj v)).card : ℝ)) k hk
  refine ⟨T, hTU, hT, ?_⟩
  rw [card_interedges_comm G S U, card_interedges_comm G S T,
    card_interedges_eq_sum, card_interedges_eq_sum]
  exact_mod_cast havg

/-- The requested equal-size cut averaging bound, including the empty case. -/
theorem exists_equal_size_cut (G : SimpleGraph V) (S : Finset V)
    (hS : S.card ≤ Fintype.card V - S.card) :
    ∃ T ⊆ Sᶜ, T.card = S.card ∧
      S.card * (G.interedges S Sᶜ).card ≤
        (Fintype.card V - S.card) * (G.interedges S T).card := by
  simpa only [card_compl] using exists_cut_subset G S Sᶜ S.card (by simpa only [Finset.card_compl] using hS)

/-- A hereditary power bound means an edge upper bound for **every** induced
vertex subset, measured using the cardinality of that subset. -/
def HereditaryPowerBound (G : SimpleGraph V) (C a : ℝ) : Prop :=
  ∀ U : Finset V, ((G.induce (U : Set V)).edgeFinset.card : ℝ) ≤ C * (U.card : ℝ) ^ a

/-- The sharp cut estimate obtained by sampling an equally sized set in the
complement. This finite assertion does not require restrictions on `a`. -/
theorem cut_le_of_hereditary_power_bound (G : SimpleGraph V) {C a : ℝ}
    (hG : HereditaryPowerBound G C a) {S : Finset V} (hs : 0 < S.card)
    (hS : S.card ≤ Fintype.card V - S.card) :
    ((G.interedges S Sᶜ).card : ℝ) ≤
      C * (2 : ℝ) ^ a * ((Fintype.card V - S.card : ℕ) : ℝ) * (S.card : ℝ) ^ (a - 1) := by
  obtain ⟨T, hTsub, hTcard, havg⟩ := exists_equal_size_cut G S hS
  have hST : Disjoint S T := disjoint_of_subset_right hTsub disjoint_compl_right
  have hcard : ((S ∪ T).card : ℝ) = 2 * (S.card : ℝ) := by
    rw [card_union_of_disjoint hST, hTcard, Nat.cast_add]
    ring
  have he : ((G.interedges S T).card : ℝ) ≤ C * (2 * (S.card : ℝ)) ^ a := by
    calc
      _ ≤ ((G.induce ((S ∪ T : Finset V) : Set V)).edgeFinset.card : ℝ) := by
        exact_mod_cast card_interedges_le_induce_union G hST
      _ ≤ C * ((S ∪ T).card : ℝ) ^ a := hG (S ∪ T)
      _ = _ := by rw [hcard]
  have hs' : 0 < (S.card : ℝ) := by exact_mod_cast hs
  have hscale : C * (2 * (S.card : ℝ)) ^ a =
      (S.card : ℝ) * (C * (2 : ℝ) ^ a * (S.card : ℝ) ^ (a - 1)) := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _), Real.rpow_sub_one hs'.ne']
    field_simp
  have havg' : (S.card : ℝ) * ((G.interedges S Sᶜ).card : ℝ) ≤
      ((Fintype.card V - S.card : ℕ) : ℝ) * ((G.interedges S T).card : ℝ) := by
    exact_mod_cast havg
  apply (mul_le_mul_iff_of_pos_left hs').mp
  calc
    _ ≤ ((Fintype.card V - S.card : ℕ) : ℝ) * ((G.interedges S T).card : ℝ) := havg'
    _ ≤ ((Fintype.card V - S.card : ℕ) : ℝ) *
        ((S.card : ℝ) * (C * (2 : ℝ) ^ a * (S.card : ℝ) ^ (a - 1))) := by
      rw [← hscale]
      exact mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The degree sum on at most half the vertices is bounded by
`C * (2 + 2^a) * n * s^(a-1)`. There is no lower bound on `s`, and no
regularity, extremality, or forbidden-subgraph assumption. -/
theorem sum_degrees_le_of_hereditary_power_bound (G : SimpleGraph V) {C a : ℝ}
    (hC : 0 ≤ C) (hG : HereditaryPowerBound G C a) (S : Finset V)
    (hS : S.card ≤ Fintype.card V - S.card) :
    (∑ v ∈ S, (G.degree v : ℝ)) ≤
      (C * (2 + (2 : ℝ) ^ a)) * (Fintype.card V : ℝ) * (S.card : ℝ) ^ (a - 1) := by
  obtain rfl | hs := S.eq_empty_or_nonempty
  · simp only [sum_empty, card_empty, Nat.cast_zero]
    positivity
  have hsplit : (∑ v ∈ S, (G.degree v : ℝ)) =
      2 * ((G.induce (S : Set V)).edgeFinset.card : ℝ) + ((G.interedges S Sᶜ).card : ℝ) := by
    exact_mod_cast sum_degrees_eq_internal_add_cut G S
  have hs' : 0 < (S.card : ℝ) := by exact_mod_cast hs.card_pos
  have hpow : (S.card : ℝ) ^ a = (S.card : ℝ) * (S.card : ℝ) ^ (a - 1) := by
    rw [Real.rpow_sub_one hs'.ne']
    field_simp
  have hsn : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast S.card_le_univ
  have hcn : ((Fintype.card V - S.card : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.sub_le (Fintype.card V) S.card
  calc
    _ = 2 * ((G.induce (S : Set V)).edgeFinset.card : ℝ) +
        ((G.interedges S Sᶜ).card : ℝ) := hsplit
    _ ≤ 2 * (C * (S.card : ℝ) ^ a) +
        C * (2 : ℝ) ^ a * ((Fintype.card V - S.card : ℕ) : ℝ) * (S.card : ℝ) ^ (a - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left (hG S) (by norm_num))
        (cut_le_of_hereditary_power_bound G hG hs.card_pos hS)
    _ = 2 * (C * ((S.card : ℝ) * (S.card : ℝ) ^ (a - 1))) +
        C * (2 : ℝ) ^ a * ((Fintype.card V - S.card : ℕ) : ℝ) * (S.card : ℝ) ^ (a - 1) := by
      rw [hpow]
    _ ≤ 2 * (C * ((Fintype.card V : ℝ) * (S.card : ℝ) ^ (a - 1))) +
        C * (2 : ℝ) ^ a * (Fintype.card V : ℝ) * (S.card : ℝ) ^ (a - 1) := by
      gcongr
    _ = _ := by ring

/-- A convenient uniform constant for all exponents `a ≤ 2`. In particular
this applies in the desired range `1 < a < 2`. -/
theorem sum_degrees_le_eight_mul (G : SimpleGraph V) {C a : ℝ}
    (hC : 0 ≤ C) (ha : a ≤ 2) (hG : HereditaryPowerBound G C a) (S : Finset V)
    (hS : S.card ≤ Fintype.card V - S.card) :
    (∑ v ∈ S, (G.degree v : ℝ)) ≤
      (8 * C) * (Fintype.card V : ℝ) * (S.card : ℝ) ^ (a - 1) := by
  refine (sum_degrees_le_of_hereditary_power_bound G hC hG S hS).trans ?_
  have htwo : (2 : ℝ) ^ a ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h ⊢
    exact h
  have hcoeff : C * (2 + (2 : ℝ) ^ a) ≤ 8 * C := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The hereditary hypothesis includes the whole host. -/
lemma card_edges_le_of_hereditary_power_bound (G : SimpleGraph V) {C a : ℝ}
    (hG : HereditaryPowerBound G C a) :
    (G.edgeFinset.card : ℝ) ≤ C * (Fintype.card V : ℝ) ^ a := by
  have h := hG univ
  have he : (G.induce ((univ : Finset V) : Set V)).edgeFinset.card = G.edgeFinset.card := by
    have heq := sum_degrees_eq_internal_add_cut G (univ : Finset V)
    simp only [compl_univ, SimpleGraph.interedges_def, product_empty, filter_empty,
      card_empty, add_zero, G.sum_degrees_eq_twice_card_edges] at heq
    omega
  simpa only [he, card_univ] using h

/-- The vertices whose host degree exceeds `L * n^(a-1)`. -/
noncomputable def highDegreeSet (G : SimpleGraph V) (a L : ℝ) : Finset V :=
  univ.filter fun v => L * (Fintype.card V : ℝ) ^ (a - 1) < (G.degree v : ℝ)

omit [DecidableEq V] in
@[simp]
lemma mem_highDegreeSet (G : SimpleGraph V) (a L : ℝ) (v : V) :
    v ∈ highDegreeSet G a L ↔ L * (Fintype.card V : ℝ) ^ (a - 1) < (G.degree v : ℝ) := by
  simp only [highDegreeSet, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
/-- The threshold times the tail size is bounded by the degrees in the tail. -/
lemma highDegree_card_mul_threshold_le (G : SimpleGraph V) (a L : ℝ) :
    ((highDegreeSet G a L).card : ℝ) * (L * (Fintype.card V : ℝ) ^ (a - 1)) ≤
      ∑ v ∈ highDegreeSet G a L, (G.degree v : ℝ) := by
  simpa only [sum_const, nsmul_eq_mul] using
    (sum_le_sum fun v hv => ((mem_highDegreeSet G a L v).mp hv).le)

/-- The preliminary Markov bound, with the denominator cleared. -/
theorem highDegree_card_mul_le (G : SimpleGraph V) {C a : ℝ}
    (hG : HereditaryPowerBound G C a) (L : ℝ) :
    ((highDegreeSet G a L).card : ℝ) * L ≤ 2 * C * (Fintype.card V : ℝ) := by
  by_cases hn : Fintype.card V = 0
  · have hs : (highDegreeSet G a L).card = 0 := by
      have h := (highDegreeSet G a L).card_le_univ
      omega
    simp only [hs, hn, Nat.cast_zero, zero_mul, mul_zero, le_refl]
  have hn' : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : 0 < (Fintype.card V : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hn' _
  have htotal : (∑ v : V, (G.degree v : ℝ)) ≤ 2 * C * (Fintype.card V : ℝ) ^ a := by
    calc
      _ = 2 * (G.edgeFinset.card : ℝ) := by exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * (C * (Fintype.card V : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left (card_edges_le_of_hereditary_power_bound G hG) (by norm_num)
      _ = _ := by ring
  have hsum : (∑ v ∈ highDegreeSet G a L, (G.degree v : ℝ)) ≤ ∑ v : V, (G.degree v : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => Nat.cast_nonneg _)
  have hpow : (Fintype.card V : ℝ) ^ a =
      (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (a - 1) := by
    rw [Real.rpow_sub_one hn'.ne']
    field_simp
  apply (mul_le_mul_iff_of_pos_right hp).mp
  calc
    _ = ((highDegreeSet G a L).card : ℝ) * (L * (Fintype.card V : ℝ) ^ (a - 1)) := by ring
    _ ≤ 2 * C * (Fintype.card V : ℝ) ^ a :=
      (highDegree_card_mul_threshold_le G a L).trans (hsum.trans htotal)
    _ = _ := by rw [hpow]; ring

/-- The usual Markov form of the preliminary tail estimate. -/
theorem highDegree_card_le_markov (G : SimpleGraph V) {C a L : ℝ}
    (hG : HereditaryPowerBound G C a) (hL : 0 < L) :
    ((highDegreeSet G a L).card : ℝ) ≤ 2 * C * (Fintype.card V : ℝ) / L :=
  (le_div_iff₀ hL).mpr (highDegree_card_mul_le G hG L)

/-- For `L ≥ 4C`, the high-degree vertices occupy at most half the host. -/
theorem highDegree_card_le_half (G : SimpleGraph V) {C a L : ℝ}
    (hC : 0 < C) (hG : HereditaryPowerBound G C a) (hL : 4 * C ≤ L) :
    (highDegreeSet G a L).card ≤ Fintype.card V - (highDegreeSet G a L).card := by
  have hmarkov := highDegree_card_mul_le G hG L
  have hmul := mul_le_mul_of_nonneg_left hL
    (Nat.cast_nonneg (highDegreeSet G a L).card : (0 : ℝ) ≤ _)
  have hhalf : (2 : ℝ) * ((highDegreeSet G a L).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * C by positivity)).mp
    nlinarith
  have hhalf' : 2 * (highDegreeSet G a L).card ≤ Fintype.card V := by exact_mod_cast hhalf
  omega

/-- Inverting the degree-sum inequality gives the characteristic exponent
`1 / (2-a)`. This analytic lemma also allows `s = 0`. -/
lemma cardinal_tail_of_power_inequality {s n K L a : ℝ}
    (hs : 0 ≤ s) (hn : 0 < n) (hK : 0 ≤ K) (hL : 0 < L) (ha : a < 2)
    (h : s * (L * n ^ (a - 1)) ≤ K * n * s ^ (a - 1)) :
    s ≤ n * (K / L) ^ (1 / (2 - a)) := by
  obtain rfl | hs' := hs.eq_or_lt
  · positivity
  have hb : 0 < 2 - a := sub_pos.mpr ha
  have hsp : 0 < s ^ (a - 1) := Real.rpow_pos_of_pos hs' _
  have hnp : 0 < n ^ (a - 1) := Real.rpow_pos_of_pos hn _
  have hid : (s / n) ^ (2 - a) = (s * n ^ (a - 1)) / (n * s ^ (a - 1)) := by
    rw [show 2 - a = 1 - (a - 1) by ring, Real.rpow_sub (div_pos hs' hn),
      Real.rpow_one, Real.div_rpow hs'.le hn.le]
    field_simp
  have hratio : (s / n) ^ (2 - a) ≤ K / L := by
    rw [hid, div_le_div_iff₀ (mul_pos hn hsp) hL]
    nlinarith [h]
  have hroot : s / n ≤ (K / L) ^ (1 / (2 - a)) := by
    rw [one_div]
    exact (Real.le_rpow_inv_iff_of_pos (div_nonneg hs'.le hn.le) (div_nonneg hK hL.le) hb).mpr hratio
  simpa only [mul_comm] using (div_le_iff₀ hn).mp hroot

/-- The finite cardinality tail bound. This already improves the Markov
exponent; the strict lower bound `1 < a` is only needed for the edge tail below. -/
theorem highDegree_card_le (G : SimpleGraph V) {C a L : ℝ}
    (hC : 0 < C) (ha : a < 2) (hG : HereditaryPowerBound G C a) (hL : 4 * C ≤ L) :
    ((highDegreeSet G a L).card : ℝ) ≤
      (Fintype.card V : ℝ) * (8 * C / L) ^ (1 / (2 - a)) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * C) hL
  by_cases hn : Fintype.card V = 0
  · have hs : (highDegreeSet G a L).card = 0 := by
      have h := (highDegreeSet G a L).card_le_univ
      omega
    simp only [hs, hn, Nat.cast_zero, zero_mul, le_refl]
  have hn' : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply cardinal_tail_of_power_inequality (Nat.cast_nonneg _) hn' (by positivity) hLpos ha
  exact (highDegree_card_mul_threshold_le G a L).trans
    (sum_degrees_le_eight_mul G hC.le ha.le hG _ (highDegree_card_le_half G hC hG hL))

/-- The high-degree vertices carry at most the indicated vanishing fraction
of the natural edge scale `n^a`. This is a degree-sum bound, so it also bounds
every edge incident with the high-degree set, counted only once. -/
theorem highDegree_sum_degrees_le (G : SimpleGraph V) {C a L : ℝ}
    (hC : 0 < C) (ha1 : 1 < a) (ha2 : a < 2)
    (hG : HereditaryPowerBound G C a) (hL : 4 * C ≤ L) :
    (∑ v ∈ highDegreeSet G a L, (G.degree v : ℝ)) ≤
      (8 * C) * (Fintype.card V : ℝ) ^ a * (8 * C / L) ^ ((a - 1) / (2 - a)) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * C) hL
  have hbase : 0 ≤ 8 * C / L := by positivity
  have hcard := highDegree_card_le G hC ha2 hG hL
  have hscale : (Fintype.card V : ℝ) ^ a =
      (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (a - 1) := by
    have h := Real.rpow_one_add' (Nat.cast_nonneg (Fintype.card V))
      (show 1 + (a - 1) ≠ 0 by linarith)
    rwa [show 1 + (a - 1) = a by ring] at h
  calc
    _ ≤ (8 * C) * (Fintype.card V : ℝ) * ((highDegreeSet G a L).card : ℝ) ^ (a - 1) :=
      sum_degrees_le_eight_mul G hC.le ha2.le hG _ (highDegree_card_le_half G hC hG hL)
    _ ≤ (8 * C) * (Fintype.card V : ℝ) *
        ((Fintype.card V : ℝ) * (8 * C / L) ^ (1 / (2 - a))) ^ (a - 1) := by
      gcongr
      linarith
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hbase _),
        ← Real.rpow_mul hbase, show 1 / (2 - a) * (a - 1) = (a - 1) / (2 - a) by ring, hscale]
      ring

/-- The edges incident with a vertex set, counted once even when both
endpoints belong to the set. -/
noncomputable def incidentEdges (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion (fun v => G.incidenceFinset v)

@[simp]
lemma mem_incidentEdges (G : SimpleGraph V) (S : Finset V) (e : Sym2 V) :
    e ∈ incidentEdges G S ↔ e ∈ G.edgeFinset ∧ ∃ v ∈ S, v ∈ e := by
  simp only [incidentEdges, mem_biUnion, G.incidenceFinset_eq_filter, mem_filter]
  aesop

lemma incidentEdges_subset (G : SimpleGraph V) (S : Finset V) :
    incidentEdges G S ⊆ G.edgeFinset := by
  intro e he
  exact ((mem_incidentEdges G S e).mp he).1

/-- Counting an edge once is bounded by counting its incidences with `S`. -/
lemma card_incidentEdges_le_sum_degrees (G : SimpleGraph V) (S : Finset V) :
    (incidentEdges G S).card ≤ ∑ v ∈ S, G.degree v := by
  simpa only [incidentEdges, card_incidenceFinset_eq_degree] using
    (card_biUnion_le (s := S) (t := fun v => G.incidenceFinset v))

/-- Edges not incident with `S` are exactly the edges induced on its complement. -/
lemma card_edges_induce_compl_add_incident (G : SimpleGraph V) (S : Finset V) :
    (G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset.card + (incidentEdges G S).card =
      G.edgeFinset.card := by
  have heq : G.edgeFinset \ incidentEdges G S = G.edgeFinset ∩ Sᶜ.sym2 := by
    ext e
    simp only [mem_sdiff, mem_incidentEdges, mem_inter, mem_sym2_iff, mem_compl]
    aesop
  have hcard : (G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset.card =
      (G.edgeFinset \ incidentEdges G S).card := by
    have hmap := congrArg Finset.card
      (G.map_edgeFinset_induce (s := ((Sᶜ : Finset V) : Set V)))
    simp only [card_map, toFinset_coe, ← heq] at hmap
    convert hmap using 2
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  rw [hcard]
  exact card_sdiff_add_card_eq_card (incidentEdges_subset G S)

/-- The number of edges removed by deleting all high-degree vertices. -/
theorem highDegree_incident_edges_le (G : SimpleGraph V) {C a L : ℝ}
    (hC : 0 < C) (ha1 : 1 < a) (ha2 : a < 2)
    (hG : HereditaryPowerBound G C a) (hL : 4 * C ≤ L) :
    ((incidentEdges G (highDegreeSet G a L)).card : ℝ) ≤
      (8 * C) * (Fintype.card V : ℝ) ^ a * (8 * C / L) ^ ((a - 1) / (2 - a)) := by
  have h : ((incidentEdges G (highDegreeSet G a L)).card : ℝ) ≤
      ∑ v ∈ highDegreeSet G a L, (G.degree v : ℝ) := by
    exact_mod_cast card_incidentEdges_le_sum_degrees G (highDegreeSet G a L)
  exact h.trans (highDegree_sum_degrees_le G hC ha1 ha2 hG hL)

/-- Explicit induced-subgraph edge-loss bound. No fixed max/min-degree ratio
or exact leading-constant regularity is asserted. -/
theorem highDegree_edge_loss_le (G : SimpleGraph V) {C a L : ℝ}
    (hC : 0 < C) (ha1 : 1 < a) (ha2 : a < 2)
    (hG : HereditaryPowerBound G C a) (hL : 4 * C ≤ L) :
    (G.edgeFinset.card : ℝ) -
        ((G.induce (((highDegreeSet G a L)ᶜ : Finset V) : Set V)).edgeFinset.card : ℝ) ≤
      (8 * C) * (Fintype.card V : ℝ) ^ a * (8 * C / L) ^ ((a - 1) / (2 - a)) := by
  have heq : ((G.induce (((highDegreeSet G a L)ᶜ : Finset V) : Set V)).edgeFinset.card : ℝ) +
      ((incidentEdges G (highDegreeSet G a L)).card : ℝ) = (G.edgeFinset.card : ℝ) := by
    exact_mod_cast card_edges_induce_compl_add_incident G (highDegreeSet G a L)
  have h := highDegree_incident_edges_le G hC ha1 ha2 hG hL
  linarith

/-- After removing the high-degree vertices, every remaining degree is at
most the chosen host-scale cutoff. -/
theorem degree_induce_compl_highDegree_le (G : SimpleGraph V) (a L : ℝ)
    (v : (((highDegreeSet G a L)ᶜ : Finset V) : Set V)) :
    ((G.induce (((highDegreeSet G a L)ᶜ : Finset V) : Set V)).degree v : ℝ) ≤
      L * (Fintype.card V : ℝ) ^ (a - 1) := by
  have hv : v.val ∉ highDegreeSet G a L := mem_compl.mp v.property
  have hcut : (G.degree v.val : ℝ) ≤ L * (Fintype.card V : ℝ) ^ (a - 1) := by
    exact le_of_not_gt (fun h => hv ((mem_highDegreeSet G a L v.val).mpr h))
  have hdeg : (G.induce (((highDegreeSet G a L)ᶜ : Finset V) : Set V)).degree v ≤ G.degree v.val := by
    calc
      _ = ∑ w : (((highDegreeSet G a L)ᶜ : Finset V) : Set V),
          if G.Adj v.val w.val then 1 else 0 :=
        (G.induce (((highDegreeSet G a L)ᶜ : Finset V) : Set V)).degree_eq_sum_if_adj (R := ℕ) v
      _ = ∑ w ∈ (highDegreeSet G a L)ᶜ, if G.Adj v.val w then 1 else 0 :=
        (sum_subtype _ (fun _ => Iff.rfl) (fun w => if G.Adj v.val w then 1 else 0)).symm
      _ ≤ ∑ w : V, if G.Adj v.val w then 1 else 0 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
      _ = _ := (G.degree_eq_sum_if_adj (R := ℕ) v.val).symm
  exact (Nat.cast_le.mpr hdeg).trans hcut

end Graph

open Filter
open scoped Topology Classical

/-- A single degree cutoff makes the incident-edge loss arbitrarily small
relative to `n^a`, uniformly over all finite hosts satisfying the hereditary
bound. To obtain a small fraction of the actual edges, one additionally needs
a positive lower bound of order `n^a` for the host edge count. -/
theorem exists_uniform_degree_cutoff {C a ε : ℝ}
    (hC : 0 < C) (ha1 : 1 < a) (ha2 : a < 2) (hε : 0 < ε) :
    ∃ L : ℝ, 4 * C ≤ L ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), HereditaryPowerBound G C a →
        ((incidentEdges G (highDegreeSet G a L)).card : ℝ) ≤ ε * (n : ℝ) ^ a := by
  have hp : 0 < (a - 1) / (2 - a) := div_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2)
  have hdiv : Tendsto (fun L : ℝ => 8 * C / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (8 * C)
  have hlim : Tendsto (fun L : ℝ => (8 * C) * (8 * C / L) ^ ((a - 1) / (2 - a)))
      atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne', mul_zero] using
      (hdiv.rpow_const (Or.inr hp.le)).const_mul (8 * C)
  obtain ⟨L, hL, hsmall⟩ := ((eventually_ge_atTop (4 * C)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨L, hL, ?_⟩
  intro n G hG
  calc
    _ ≤ (8 * C) * (n : ℝ) ^ a * (8 * C / L) ^ ((a - 1) / (2 - a)) := by
      simpa only [Fintype.card_fin] using highDegree_incident_edges_le G hC ha1 ha2 hG hL
    _ = ((8 * C) * (8 * C / L) ^ ((a - 1) / (2 - a))) * (n : ℝ) ^ a := by ring
    _ ≤ ε * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg (Nat.cast_nonneg n) a)

end Erdos713DegreeTail

#print axioms Erdos713DegreeTail.exists_subset_card_mul_sum_ge
#print axioms Erdos713DegreeTail.card_interedges_eq_sum
#print axioms Erdos713DegreeTail.card_interedges_comm
#print axioms Erdos713DegreeTail.card_interedges_self
#print axioms Erdos713DegreeTail.sum_degrees_eq_internal_add_cut
#print axioms Erdos713DegreeTail.card_interedges_le_induce_union
#print axioms Erdos713DegreeTail.exists_cut_subset
#print axioms Erdos713DegreeTail.exists_equal_size_cut
#print axioms Erdos713DegreeTail.HereditaryPowerBound
#print axioms Erdos713DegreeTail.cut_le_of_hereditary_power_bound
#print axioms Erdos713DegreeTail.sum_degrees_le_of_hereditary_power_bound
#print axioms Erdos713DegreeTail.sum_degrees_le_eight_mul
#print axioms Erdos713DegreeTail.card_edges_le_of_hereditary_power_bound
#print axioms Erdos713DegreeTail.highDegreeSet
#print axioms Erdos713DegreeTail.mem_highDegreeSet
#print axioms Erdos713DegreeTail.highDegree_card_mul_threshold_le
#print axioms Erdos713DegreeTail.highDegree_card_mul_le
#print axioms Erdos713DegreeTail.highDegree_card_le_markov
#print axioms Erdos713DegreeTail.highDegree_card_le_half
#print axioms Erdos713DegreeTail.cardinal_tail_of_power_inequality
#print axioms Erdos713DegreeTail.highDegree_card_le
#print axioms Erdos713DegreeTail.highDegree_sum_degrees_le
#print axioms Erdos713DegreeTail.incidentEdges
#print axioms Erdos713DegreeTail.mem_incidentEdges
#print axioms Erdos713DegreeTail.incidentEdges_subset
#print axioms Erdos713DegreeTail.card_incidentEdges_le_sum_degrees
#print axioms Erdos713DegreeTail.card_edges_induce_compl_add_incident
#print axioms Erdos713DegreeTail.highDegree_incident_edges_le
#print axioms Erdos713DegreeTail.highDegree_edge_loss_le
#print axioms Erdos713DegreeTail.degree_induce_compl_highDegree_le
#print axioms Erdos713DegreeTail.exists_uniform_degree_cutoff
