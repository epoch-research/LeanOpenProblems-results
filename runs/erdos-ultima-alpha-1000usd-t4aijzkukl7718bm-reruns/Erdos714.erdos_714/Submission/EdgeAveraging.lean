import FormalConjecturesUtil

/-!
Uniform-cover averaging for finite group actions. This provides obstructions to
retaining a positive fraction of the edges in certain proposed extremal hosts;
it is not a proof or disproof of Erdős Problem 714.
-/

set_option maxHeartbeats 2000000

open Finset Classical

namespace Erdos714Averaging

variable {E I : Type*} [Fintype E] [Fintype I] [DecidableEq E]

/-- Counting incidences between a selected set and a finite family of blocks. -/
lemma count_selected (B : I → Finset E) (S : Finset E) :
    (∑ i, (S.filter (fun e => e ∈ B i)).card) =
      ∑ e ∈ S, (univ.filter (fun i => e ∈ B i)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Uniform covers transfer a bound on each block to a density bound in the universe. -/
theorem uniform_cover_bound [Nonempty I] (B : I → Finset E) (S : Finset E)
    (t m b : ℕ) (hsize : ∀ i, (B i).card = t)
    (hcover : ∀ e, (univ.filter (fun i => e ∈ B i)).card = m)
    (hbound : ∀ i, (S.filter (fun e => e ∈ B i)).card ≤ b) :
    t * S.card ≤ b * Fintype.card E := by
  have htotal : Fintype.card I * t = Fintype.card E * m := by
    have h := count_selected B (univ : Finset E)
    simpa [hsize, hcover] using h
  have hselected : S.card * m ≤ Fintype.card I * b := by
    have h := Finset.sum_le_sum (s := univ) (fun i _ => hbound i)
    rw [count_selected B S] at h
    simpa [hcover] using h
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card I) _ Fintype.card_pos
  calc
    Fintype.card I * (t * S.card) = Fintype.card E * (S.card * m) := by
      rw [← mul_assoc, htotal]
      ring
    _ ≤ Fintype.card E * (Fintype.card I * b) := Nat.mul_le_mul_left _ hselected
    _ = Fintype.card I * (b * Fintype.card E) := by ring

variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable (ρ : Γ →* Equiv.Perm E)

/-- A finite-set translate, for a permutation representation of the group. -/
noncomputable def translate (g : Γ) (T : Finset E) : Finset E :=
  T.map (ρ g).toEmbedding

@[simp] lemma mem_translate (g : Γ) (T : Finset E) (e : E) :
    e ∈ translate ρ g T ↔ (ρ g).symm e ∈ T := by
  simp [translate]

@[simp] lemma card_translate (g : Γ) (T : Finset E) :
    (translate ρ g T).card = T.card := by simp [translate]

/-- Two points related by the group action have equal coverage multiplicity. -/
lemma coverage_eq (T : Finset E) (x y : E) (h : ∃ g, ρ g x = y) :
    (univ.filter (fun g => x ∈ translate ρ g T)).card =
      (univ.filter (fun g => y ∈ translate ρ g T)).card := by
  obtain ⟨a, rfl⟩ := h
  apply Finset.card_equiv (Equiv.mulLeft a)
  intro g
  simp only [mem_filter, mem_univ, true_and, mem_translate,
    Equiv.mulLeft]
  change ((ρ g).symm x ∈ T) ↔ ((ρ (a * g)).symm (ρ a x) ∈ T)
  rw [map_mul]
  change ((ρ g).symm x ∈ T) ↔ ((ρ g).symm ((ρ a).symm (ρ a x)) ∈ T)
  rw [Equiv.symm_apply_apply]

/-- No transitive group orbit of blocks can all have small intersection with a
selected set unless that selected set has correspondingly small density. -/
theorem transitive_bound (htrans : ∀ x y : E, ∃ g, ρ g x = y)
    (T S : Finset E) (b : ℕ)
    (hb : ∀ g, (S.filter (fun e => e ∈ translate ρ g T)).card ≤ b) :
    T.card * S.card ≤ b * Fintype.card E := by
  cases isEmpty_or_nonempty E with
  | inl h => simp [Finset.eq_empty_of_isEmpty T]
  | inr h =>
    let x : E := Classical.choice h
    apply uniform_cover_bound (translate ρ · T) S T.card
      ((univ.filter (fun g => x ∈ translate ρ g T)).card) b
    · intro g; exact card_translate ρ g T
    · intro y; exact coverage_eq ρ T y x (htrans y x)
    · exact hb

end Erdos714Averaging

#print axioms Erdos714Averaging.uniform_cover_bound
#print axioms Erdos714Averaging.transitive_bound

namespace Erdos714GraphAveraging

open SimpleGraph

variable {V W Z : Type*} [Fintype V] [Fintype W]

/-- Automorphisms act by permutations on the edge set. -/
def edgeAction (G : SimpleGraph V) : (G ≃g G) →* Equiv.Perm G.edgeSet where
  toFun := SimpleGraph.Iso.mapEdgeSet
  map_one' := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change Sym2.map (1 : G ≃g G) e.val = e.val
    simp [RelIso.coe_one, Sym2.map_id]
  map_mul' g h := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change Sym2.map (g * h) e.val = Sym2.map g (Sym2.map h e.val)
    rw [Sym2.map_map]
    rfl

/-- We use edge transitivity in its direct, unbundled form. -/
def EdgeTransitive (G : SimpleGraph V) : Prop :=
  ∀ x y : G.edgeSet, ∃ g : G ≃g G, g.mapEdgeSet x = y

/-- Count the edges of a spanning subgraph as a subset of host edges. -/
lemma selected_edge_card (H G : SimpleGraph V) (hHG : H ≤ G) :
    (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)).card =
      H.edgeFinset.card := by
  rw [edgeFinset_card, Fintype.card_subtype]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    refine ⟨⟨e, edgeSet_mono hHG (mem_filter.mp he).2⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩

/-- Switching which set is filtered makes image cardinalities easy to compute. -/
lemma filter_image_card {A B : Type*} [DecidableEq B] (S : Finset B) (T : Finset A) (f : A ↪ B) :
    (S.filter (fun b => b ∈ T.map f)).card =
      (T.filter (fun a => f a ∈ S)).card := by
  have h : S.filter (fun b => b ∈ T.map f) = (T.map f).filter (fun b => b ∈ S) := by
    ext b
    simp [and_comm]
  rw [h, Finset.filter_map, Finset.card_map]
  rfl

/-- Pulling back along an injection preserves forbidden-copy freeness. -/
lemma free_comap (F : SimpleGraph Z) (H : SimpleGraph V) (f : W ↪ V)
    (hH : F.Free H) : F.Free (H.comap f) := by
  rintro ⟨c⟩
  exact hH ⟨(SimpleGraph.Embedding.comap f H).toCopy.comp c⟩

/-- A translated block inside a free subgraph has at most the corresponding
extremal number of edges. The block need not be induced. -/
lemma block_bound (F : SimpleGraph Z) (H G : SimpleGraph V) (A : SimpleGraph W)
    (c : A.Copy G) (hH : F.Free H) (g : G ≃g G) :
    ((univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (edgeAction G) g
        (univ.map c.mapEdgeSet))).card ≤ extremalNumber (Fintype.card W) F := by
  let f : W ↪ V := c.toEmbedding.trans g.toEquiv.toEmbedding
  let B : SimpleGraph W := H.comap f
  have hB : F.Free B := free_comap F H f hH
  apply (show _ ≤ B.edgeFinset.card from ?_).trans (card_edgeFinset_le_extremalNumber hB)
  rw [Erdos714Averaging.translate, Finset.map_map]
  rw [filter_image_card (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet))
    univ (c.mapEdgeSet.trans ((edgeAction G) g).toEmbedding)]
  apply Finset.card_le_card_of_injOn (fun e : A.edgeSet => e.val)
  · intro e he
    change e.val ∈ B.edgeFinset
    rw [mem_edgeFinset]
    have hm := (mem_filter.mp he).2
    change (edgeAction G g) (c.mapEdgeSet e) ∈
      univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet) at hm
    have hm' := (mem_filter.mp hm).2
    change Sym2.map g (Sym2.map c e.val) ∈ H.edgeSet at hm'
    rw [Sym2.map_map] at hm'
    change e.val ∈ (H.comap f).edgeSet
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y => exact hm'
  · intro e he e' he' hh
    exact Subtype.ext hh

/-- An exact edge-density bound for every free spanning subgraph of an
edge-transitive host containing a prescribed finite block. -/
theorem edge_transitive_bound (F : SimpleGraph Z) (H G : SimpleGraph V)
    (A : SimpleGraph W) (c : A.Copy G) (hHG : H ≤ G)
    (hH : F.Free H) (htrans : EdgeTransitive G) :
    A.edgeFinset.card * H.edgeFinset.card ≤
      extremalNumber (Fintype.card W) F * G.edgeFinset.card := by
  letI : Fintype (G ≃g G) := Fintype.ofInjective RelIso.toEquiv RelIso.toEquiv_injective
  have h := Erdos714Averaging.transitive_bound (edgeAction G) htrans
    (univ.map c.mapEdgeSet) (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet))
    (extremalNumber (Fintype.card W) F) (block_bound F H G A c hH)
  simpa only [Finset.card_map, Finset.card_univ, selected_edge_card H G hHG,
    SimpleGraph.card_edgeSet] using h

end Erdos714GraphAveraging

#print axioms Erdos714GraphAveraging.edge_transitive_bound

namespace Erdos714GraphAveraging

open SimpleGraph

lemma complete_bipartite_edges (X Y : Type*) [Fintype X] [Fintype Y] :
    (completeBipartiteGraph X Y).edgeFinset.card = Fintype.card X * Fintype.card Y := by
  let e : X × Y ↪ Sym2 (X ⊕ Y) :=
    ⟨fun p => s(Sum.inl p.1, Sum.inr p.2), by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, or_false] at h
      exact Prod.ext h.1 h.2⟩
  have he : (completeBipartiteGraph X Y).edgeFinset = univ.map e := by
    ext z
    induction z using Sym2.inductionOn with
    | hf x y =>
      cases x <;> cases y <;>
        simp [mem_edgeFinset, mem_edgeSet, Finset.mem_map, e, eq_comm]
  rw [he, card_map, card_univ, Fintype.card_prod]

/-- The specialization relevant to forbidding balanced complete bipartite graphs. -/
theorem biclique_bound {V : Type*} [Fintype V] (H G : SimpleGraph V) (r t : ℕ)
    (c : (completeBipartiteGraph (Fin t) (Fin t)).Copy G) (hHG : H ≤ G)
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) (htrans : EdgeTransitive G) :
    t ^ 2 * H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) * G.edgeFinset.card := by
  have h := edge_transitive_bound (completeBipartiteGraph (Fin r) (Fin r)) H G
    (completeBipartiteGraph (Fin t) (Fin t)) c hHG hH htrans
  simpa [complete_bipartite_edges, Fintype.card_sum, Fintype.card_fin, pow_two, two_mul] using h

end Erdos714GraphAveraging

#print axioms Erdos714GraphAveraging.biclique_bound
