import Mathlib

/-!
# Finite minimum-degree and rooted reductions

This file proves finite, conditional reductions, not an extremal construction
or an asymptotic lower bound. Graph freeness uses injective, not necessarily
induced, copies. The rooted relation has *labelled* left and right sides;
these may overlap as subsets of the original vertex set.
-/

namespace CriticalRooting

open SimpleGraph Finset

variable {V X Y : Type*}

/-- Oriented `K_{r,s}`-freeness: the `r` vertices must be on the left. -/
def OrientedFree (r s : ℕ) (R : X → Y → Prop) : Prop :=
  ∀ (a : Fin r → X) (b : Fin s → Y),
    Function.Injective a → Function.Injective b → ¬ ∀ i j, R (a i) (b j)

/-- Number of edges of a finite relation, counted once per ordered left/right pair. -/
def edgeCount [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R] : ℕ :=
  ∑ y : Y, (Finset.univ.filter fun x : X => R x y).card

/-- Looplessness makes the two images of any complete adjacency rectangle
 disjoint. No bipartiteness assumption on the ambient graph is needed. -/
theorem rectangle_disjoint (G : SimpleGraph V) {r s : ℕ}
    (a : Fin r → V) (b : Fin s → V) (hab : ∀ i j, G.Adj (a i) (b j)) :
    ∀ i j, a i ≠ b j := fun i j => (hab i j).ne

/-- A complete rectangle with injections on each side is a genuine injective
 copy, even when the ambient graph is not bipartite. -/
theorem contains_of_rectangle (G : SimpleGraph V) {r s : ℕ}
    (a : Fin r → V) (b : Fin s → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, G.Adj (a i) (b j)) :
    (completeBipartiteGraph (Fin r) (Fin s)).IsContained G := by
  refine ⟨⟨⟨Sum.elim a b, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl i' => simp at huv
      | inr j => exact hab i j
    | inr j =>
      cases v with
      | inl i => exact (hab i j).symm
      | inr j' => simp at huv
  · exact Sum.elim_injective.mpr ⟨ha, hb, rectangle_disjoint G a b hab⟩

/-- The root is removed only from the left side. The right side is a chosen
 set of its neighbors, not a disjointness restriction on the original graph. -/
def rootedRelation (G : SimpleGraph V) (x : V) (U : Finset V) :
    {v : V // v ≠ x} → U → Prop := fun v u => G.Adj v.1 u.1

instance (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (U : Finset V) :
    DecidableRel (rootedRelation G x U) := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

/-- Adjoining the root to the left of an oriented `K_{r,s}` gives `K_{r+1,s}`.
 All possible cross-side collisions are ruled out by graph looplessness. -/
theorem rooted_free (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {r s : ℕ} (hG : (completeBipartiteGraph (Fin (r + 1)) (Fin s)).Free G)
    (x : V) (U : Finset V) (hU : U ⊆ G.neighborFinset x) :
    OrientedFree r s (rootedRelation G x U) := by
  intro a b ha hb hab
  let a' : Fin (r + 1) → V := Fin.cons x (fun i => (a i).1)
  have ha' : Function.Injective a' := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      exact (a i).2 hi
    · exact Subtype.val_injective.comp ha
  have hb' : Function.Injective (fun j => (b j).1) := Subtype.val_injective.comp hb
  apply hG
  apply contains_of_rectangle G a' (fun j => (b j).1) ha' hb'
  intro i j
  cases i using Fin.cases with
  | zero => exact (G.mem_neighborFinset x _).mp (hU (b j).2)
  | succ i => exact hab i j

section RootedCount

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The right degree of a chosen neighbor is exactly its old degree minus one. -/
theorem rooted_column_card (x : V) (U : Finset V) (hU : U ⊆ G.neighborFinset x)
    (u : U) :
    (Finset.univ.filter fun v : {v : V // v ≠ x} => rootedRelation G x U v u).card =
      G.degree u.1 - 1 := by
  have hx : x ∈ G.neighborFinset u.1 :=
    (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp (hU u.2)).symm
  calc
    _ = ((G.neighborFinset u.1).erase x).card := by
      apply Finset.card_bij (fun v _ => v.1)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, rootedRelation] at hv
        exact Finset.mem_erase.mpr ⟨v.2, (G.mem_neighborFinset _ _).mpr hv.symm⟩
      · intro v hv w hw h
        exact Subtype.ext h
      · intro v hv
        obtain ⟨hvx, hv⟩ := Finset.mem_erase.mp hv
        exact ⟨⟨v, hvx⟩, by simpa [rootedRelation] using
          ((G.mem_neighborFinset _ _).mp hv).symm, rfl⟩
    _ = G.degree u.1 - 1 := by
      rw [Finset.card_erase_of_mem hx, G.card_neighborFinset_eq_degree]

/-- Exact count, including edges whose two underlying vertices both lie in `U`:
 their two orientations are different relation edges. -/
theorem rooted_edgeCount (x : V) (U : Finset V) (hU : U ⊆ G.neighborFinset x) :
    edgeCount (rootedRelation G x U) = ∑ u : U, (G.degree u.1 - 1) := by
  unfold edgeCount
  exact Finset.sum_congr rfl (fun u _ => rooted_column_card G x U hU u)

/-- The finite rooted edge lower bound. Subtraction is natural subtraction,
 so the statement also includes `d = 0`. -/
theorem rooted_edgeCount_lower (x : V) (U : Finset V)
    (hU : U ⊆ G.neighborFinset x) (d : ℕ) (hd : ∀ u ∈ U, d ≤ G.degree u) :
    U.card * (d - 1) ≤ edgeCount (rootedRelation G x U) := by
  rw [rooted_edgeCount G x U hU]
  calc
    _ = ∑ _u : U, (d - 1) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun u _ => Nat.sub_le_sub_right (hd u.1 u.2) 1)

/-- The freeness and edge conclusions packaged together. -/
theorem rooted_reduction {r s d : ℕ}
    (hG : (completeBipartiteGraph (Fin (r + 1)) (Fin s)).Free G)
    (x : V) (U : Finset V) (hU : U ⊆ G.neighborFinset x)
    (hd : ∀ u ∈ U, d ≤ G.degree u) :
    OrientedFree r s (rootedRelation G x U) ∧
      U.card * (d - 1) ≤ edgeCount (rootedRelation G x U) :=
  ⟨rooted_free G hG x U hU, rooted_edgeCount_lower G x U hU d hd⟩

end RootedCount

section Core

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Undirected edges with both endpoints in a given finite vertex set. -/
def internalEdges (S : Finset V) : Finset (Sym2 V) := G.edgeFinset ∩ S.sym2

/-- The internal-edge count is the usual induced-graph edge count. -/
theorem internalEdges_card (S : Finset V) :
    (internalEdges G S).card = (G.induce (S : Set V)).edgeFinset.card := by
  have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := G) (s := (S : Set V)))
  convert h.symm using 1 <;> simp [internalEdges]
  congr
  apply Subsingleton.elim

/-- Degrees in an induced graph are numbers of neighbors retained in the set. -/
theorem degree_induce_eq (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v.1 ∩ S).card := by
  have h := congrArg Finset.card (SimpleGraph.map_neighborFinset_induce (G := G) v)
  convert h using 1 <;> simp
  congr
  apply Subsingleton.elim

/-- Deleting a vertex removes exactly its internal degree, not twice that degree. -/
theorem internalEdges_erase_add (S : Finset V) {v : V} (hv : v ∈ S) :
    (internalEdges G (S.erase v)).card + (G.neighborFinset v ∩ S).card =
      (internalEdges G S).card := by
  have hinc : ((internalEdges G S).filter fun e => v ∈ e).card =
      (G.neighborFinset v ∩ S).card := by
    symm
    apply Finset.card_bij (fun w _ => s(v, w))
    · intro w hw
      simpa [internalEdges, hv] using hw
    · intro a ha b hb h
      rcases Sym2.eq_iff.mp h with h | h
      · exact h.2
      · exact h.2.trans h.1
    · intro e he
      obtain ⟨he, hve⟩ := Finset.mem_filter.mp he
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
      exact ⟨w, by simpa [internalEdges, hv] using he, rfl⟩
  have herase : internalEdges G (S.erase v) =
      (internalEdges G S).filter (fun e => v ∉ e) := by
    ext ⟨a, b⟩
    simp [internalEdges, Sym2.mem_iff, ne_comm, and_assoc, and_left_comm, and_comm]
  rw [herase, ← hinc]
  simpa [add_comm] using
    (Finset.card_filter_add_card_filter_not (s := internalEdges G S) (fun e => v ∈ e))

/-- If `E ≥ |V| * d`, some nonempty induced graph has every degree at least
 the real number `d`. The nonempty ambient-vertex hypothesis is necessary.
 The proof chooses a smallest nonempty set meeting the density threshold. -/
theorem exists_induced_core_real [Nonempty V] (d : ℝ)
    (hE : (Fintype.card V : ℝ) * d ≤ (G.edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v : S, d ≤ ((G.induce (S : Set V)).degree v : ℝ) := by
  let T : Finset (Finset V) := Finset.univ.filter fun S =>
    S.Nonempty ∧ (S.card : ℝ) * d ≤ ((internalEdges G S).card : ℝ)
  have hT : T.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simpa [T, internalEdges] using hE
  obtain ⟨S, hS, hmin⟩ := T.exists_min_image Finset.card hT
  have hS' : S.Nonempty ∧ (S.card : ℝ) * d ≤ ((internalEdges G S).card : ℝ) :=
    (Finset.mem_filter.mp hS).2
  refine ⟨S, hS'.1, ?_⟩
  intro v
  by_contra h
  have hdeg : ((G.neighborFinset v.1 ∩ S).card : ℝ) < d := by
    have ht := lt_of_not_ge h
    rw [degree_induce_eq G S v] at ht
    exact ht
  have he : ((internalEdges G (S.erase v.1)).card : ℝ) +
      ((G.neighborFinset v.1 ∩ S).card : ℝ) = ((internalEdges G S).card : ℝ) := by
    exact_mod_cast internalEdges_erase_add G S v.2
  have hc : ((S.erase v.1).card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one v.2
  have hstrict : ((S.erase v.1).card : ℝ) * d <
      ((internalEdges G (S.erase v.1)).card : ℝ) := by
    nlinarith [hS'.2]
  have hn : (S.erase v.1).Nonempty := by
    by_contra hn
    have hem := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hem, internalEdges] at hstrict
  have hmem : S.erase v.1 ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, hstrict.le⟩
  exact (not_le_of_gt (Finset.card_erase_lt_of_mem v.2)) (hmin _ hmem)

/-- Natural-number version, stated using Mathlib's actual minimum degree. -/
theorem exists_induced_core [Nonempty V] (d : ℕ)
    (hE : Fintype.card V * d ≤ G.edgeFinset.card) :
    ∃ S : Finset V, S.Nonempty ∧ d ≤ (G.induce (S : Set V)).minDegree := by
  obtain ⟨S, hS, hd⟩ := exists_induced_core_real G (d : ℝ) (by exact_mod_cast hE)
  letI : Nonempty S := hS.to_subtype
  refine ⟨S, hS, SimpleGraph.le_minDegree_of_forall_le_degree _ d ?_⟩
  intro v
  exact_mod_cast hd v

/-- The guaranteed real degree is `E / |V|`, half the average degree. -/
theorem exists_induced_core_ratio [Nonempty V] :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v : S,
      (G.edgeFinset.card : ℝ) / Fintype.card V ≤ ((G.induce (S : Set V)).degree v : ℝ) := by
  apply exists_induced_core_real
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos.ne')
  rw [mul_div_cancel₀ _ hn]

/-- In particular, with total vertex count `2*n` the threshold is `E/(2*n)`.
 This applies to bipartite graphs with `n` vertices on each side, and in fact
 does not require bipartiteness. -/
theorem exists_induced_core_two_n {n : ℕ} (hn : 0 < n) (hV : Fintype.card V = 2 * n) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v : S,
      (G.edgeFinset.card : ℝ) / (2 * n) ≤ ((G.induce (S : Set V)).degree v : ℝ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  simpa [hV] using exists_induced_core_ratio G

end Core

section Padding

variable {X' Y' : Type*}

/-- The column sum is also the cardinality of the set of relation pairs. -/
theorem edgeCount_eq_card [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R] :
    edgeCount R = (Finset.univ.filter fun p : X × Y => R p.1 p.2).card := by
  simp only [edgeCount, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Transport along injections and pad the unused vertices with isolated vertices. -/
def padRelation (R : X → Y → Prop) (e : X ↪ X') (f : Y ↪ Y') : X' → Y' → Prop :=
  fun x' y' => ∃ x y, R x y ∧ e x = x' ∧ f y = y'

instance [Fintype X] [Fintype Y] [DecidableEq X'] [DecidableEq Y']
    (R : X → Y → Prop) [DecidableRel R] (e : X ↪ X') (f : Y ↪ Y') :
    DecidableRel (padRelation R e f) := fun _ _ => inferInstanceAs (Decidable (∃ _ _, _))

/-- Positive forbidden side sizes ensure that isolated padding creates no copies. -/
theorem padRelation_free {R : X → Y → Prop} {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hR : OrientedFree r s R) (e : X ↪ X') (f : Y ↪ Y') :
    OrientedFree r s (padRelation R e f) := by
  intro a b ha hb hab
  have hleft : ∀ i, ∃ x, e x = a i := by
    intro i
    obtain ⟨x, y, _, hx, _⟩ := hab i ⟨0, hs⟩
    exact ⟨x, hx⟩
  have hright : ∀ j, ∃ y, f y = b j := by
    intro j
    obtain ⟨x, y, _, _, hy⟩ := hab ⟨0, hr⟩ j
    exact ⟨y, hy⟩
  choose a' ha' using hleft
  choose b' hb' using hright
  apply hR a' b'
  · intro i j h
    apply ha
    rw [← ha' i, ← ha' j, h]
  · intro i j h
    apply hb
    rw [← hb' i, ← hb' j, h]
  · intro i j
    obtain ⟨x, y, hxy, hx, hy⟩ := hab i j
    have hx' : x = a' i := e.injective (hx.trans (ha' i).symm)
    have hy' : y = b' j := f.injective (hy.trans (hb' j).symm)
    simpa [hx', hy'] using hxy

/-- Padding and relabelling preserve the exact relation edge count. -/
theorem padRelation_edgeCount [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    [DecidableEq X'] [DecidableEq Y'] (R : X → Y → Prop) [DecidableRel R]
    (e : X ↪ X') (f : Y ↪ Y') : edgeCount (padRelation R e f) = edgeCount R := by
  rw [edgeCount_eq_card, edgeCount_eq_card]
  symm
  apply Finset.card_bij (fun p _ => (e p.1, f p.2))
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1, p.2,
      (Finset.mem_filter.mp hp).2, rfl, rfl⟩
  · intro p hp q hq h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))
  · intro p hp
    obtain ⟨x, y, hxy, hx, hy⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, Prod.ext hx hy⟩

end Padding

/-- Combined finite reduction: take a minimum-degree core, root it, select `k`
 neighbors, and pad to exactly `N` left and `M` right vertices. -/
theorem exists_oriented_reduction (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableEq V] [DecidableRel G.Adj]
    {r s N M k d : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hG : (completeBipartiteGraph (Fin (r + 1)) (Fin s)).Free G)
    (hE : Fintype.card V * d ≤ G.edgeFinset.card)
    (hN : Fintype.card V ≤ N) (hkM : k ≤ M) (hkd : k ≤ d) :
    ∃ R : Fin N → Fin M → Prop, ∃ _ : DecidableRel R,
      OrientedFree r s R ∧ k * (d - 1) ≤ edgeCount R := by
  classical
  obtain ⟨S, hS, hδ⟩ := exists_induced_core G d hE
  let H := G.induce (S : Set V)
  let x : S := ⟨hS.choose, hS.choose_spec⟩
  have hx : k ≤ (H.neighborFinset x).card := by
    rw [H.card_neighborFinset_eq_degree]
    exact hkd.trans (hδ.trans (H.minDegree_le_degree x))
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hx
  have hH : (completeBipartiteGraph (Fin (r + 1)) (Fin s)).Free H := by
    intro ⟨φ⟩
    exact hG ⟨(SimpleGraph.Copy.induce G (S : Set V)).comp φ⟩
  have hf := rooted_free H hH x U hU
  have he := rooted_edgeCount_lower H x U hU d
    (fun u _ => hδ.trans (H.minDegree_le_degree u))
  let e₀ : {v : S // v ≠ x} ↪ V :=
    ⟨fun v => v.1.1, Subtype.val_injective.comp Subtype.val_injective⟩
  let e := e₀.trans ((Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb hN))
  let f : U ↪ Fin M := (Fintype.equivFin U).toEmbedding.trans
    (Fin.castLEEmb (by simpa only [Fintype.card_coe, hcard] using hkM))
  refine ⟨padRelation (rootedRelation H x U) e f, inferInstance,
    padRelation_free hr hs hf e f, ?_⟩
  rw [padRelation_edgeCount, ← hcard]
  exact he

/-- An unconditional finite `ex(q^4,K44)` to oriented `q^4`-by-`q^3` reduction.
 With `d = floor(ex(q^4,K44)/q^4)`, it supplies at least
 `min(q^3,d)*(d-1)` edges. If `q^3 ≤ d`, the minimum is just `q^3`.
 This does not assert a lower bound on `ex`, or any asymptotic conclusion. -/
theorem critical_finite_reduction {q : ℕ} (hq : 0 < q) :
    let d := extremalNumber (q ^ 4) (completeBipartiteGraph (Fin 4) (Fin 4)) / q ^ 4
    ∃ R : Fin (q ^ 4) → Fin (q ^ 3) → Prop, ∃ _ : DecidableRel R,
      OrientedFree 3 4 R ∧ min (q ^ 3) d * (d - 1) ≤ edgeCount R := by
  classical
  haveI : Nonempty (Fin (q ^ 4)) := ⟨⟨0, pow_pos hq _⟩⟩
  have hK : completeBipartiteGraph (Fin 4) (Fin 4) ≠ ⊥ := by
    intro h
    have h' := congrArg (fun H : SimpleGraph (Fin 4 ⊕ Fin 4) =>
      H.Adj (Sum.inl 0) (Sum.inr 0)) h
    simp at h'
  obtain ⟨G, hDec, hG⟩ := SimpleGraph.exists_isExtremal_free (V := Fin (q ^ 4)) hK
  letI := hDec
  apply exists_oriented_reduction G (by norm_num) (by norm_num) hG.prop
    (N := q ^ 4) (M := q ^ 3)
  · rw [SimpleGraph.card_edgeFinset_of_isExtremal_free hG, Fintype.card_fin]
    exact Nat.mul_div_le _ _
  · simp
  · exact Nat.min_le_left _ _
  · exact Nat.min_le_right _ _

end CriticalRooting
