import Submission.ArcAdjoint

/-!
An auxiliary ultrafilter obstruction for Erdős 595. This file does not settle
that problem. An ultrafilter avoiding every triangle-free edge set has equal
endpoint marginals; in a K4-free graph that marginal has empty neighborhood
trace and is isolated in the mutual ultrafilter extension.
-/

open SimpleGraph Set
namespace Erdos595BadEdge
open Erdos595Work Erdos595ArcAdjoint

variable {V : Type*}

/-- A finite palette of triangle-free graphs covers all original edges. -/
def FiniteCover (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (H : Fin n → SimpleGraph V), (∀ i, (H i).CliqueFree 3) ∧
    ∀ a b, G.Adj a b → ∃ i, (H i).Adj a b

/-- The edge ultrafilter avoids every triangle-free subgraph, including cuts. -/
def Avoids (G : SimpleGraph V) (D : Ultrafilter (Arc G)) : Prop :=
  ∀ H : SimpleGraph V, H.CliqueFree 3 → {e | H.Adj e.val.1 e.val.2} ∉ D

/-- Failure of finite covering has a compactness witness on directed edges. -/
theorem exists_avoiding (G : SimpleGraph V) (hG : ¬FiniteCover G) :
    ∃ D : Ultrafilter (Arc G), Avoids G D := by
  classical
  let S : Set (Set (Arc G)) :=
    {s | ∃ H : SimpleGraph V, H.CliqueFree 3 ∧ s = {e | ¬H.Adj e.val.1 e.val.2}}
  have hfip : ∀ T : Finset (Set (Arc G)), (↑T : Set (Set (Arc G))) ⊆ S →
      (⋂₀ (↑T : Set (Set (Arc G)))).Nonempty := by
    intro T hT
    choose H hH he using fun s : T => hT s.property
    let equiv := T.equivFin
    by_contra hempty
    apply hG
    refine ⟨T.card, fun i => H (equiv.symm i), fun i => hH _, ?_⟩
    intro a b hab
    by_contra hn
    push_neg at hn
    apply hempty
    refine ⟨⟨(a,b), hab⟩, ?_⟩
    intro s hs
    let t : T := ⟨s,hs⟩
    have hnt := hn (equiv t)
    simp only [Equiv.symm_apply_apply] at hnt
    change (⟨(a,b),hab⟩ : Arc G) ∈ t.val
    rw [he t]
    exact hnt
  obtain ⟨D, hD⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty S hfip
  refine ⟨D, ?_⟩
  intro H hH hm
  have hc : {e : Arc G | ¬H.Adj e.val.1 e.val.2} ∈ D :=
    hD ⟨H,hH,rfl⟩
  obtain ⟨e,he,hn⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hm hc)
  exact hn he

/-- The two endpoint maps agree on membership in every vertex subset, almost
surely for the avoiding ultrafilter. -/
theorem endpoint_agreement (G : SimpleGraph V) (D : Ultrafilter (Arc G))
    (hD : Avoids G D) (S : Set V) :
    {e : Arc G | (e.val.1 ∈ S ↔ e.val.2 ∈ S)} ∈ D := by
  classical
  let cut : SimpleGraph V := (⊤ : SimpleGraph Bool).comap (fun v => decide (v ∈ S))
  have hcut : cut.CliqueFree 3 :=
    (SimpleGraph.Coloring.mk (G := cut) (fun v => decide (v ∈ S))
      (fun h => h)).colorable.cliqueFree (by decide)
  have hn := hD cut hcut
  have hc := Ultrafilter.compl_mem_iff_notMem.mpr hn
  simpa only [Set.compl_setOf, cut, SimpleGraph.comap_adj, SimpleGraph.top_adj,
    not_not, decide_eq_decide] using hc

/-- A cut-avoiding edge ultrafilter has equal endpoint marginals. -/
theorem marginals_equal (G : SimpleGraph V) (D : Ultrafilter (Arc G))
    (hD : Avoids G D) :
    D.map (fun e => e.val.1) = D.map (fun e => e.val.2) := by
  apply Ultrafilter.ext
  intro S
  simp only [Ultrafilter.mem_map]
  have he := endpoint_agreement G D hD S
  constructor
  · intro h
    exact Filter.mem_of_superset (Filter.inter_mem h he) (fun e he => he.2.mp he.1)
  · intro h
    exact Filter.mem_of_superset (Filter.inter_mem h he) (fun e he => he.2.mpr he.1)

/-- Edges internal to a fixed neighborhood form a triangle-free graph. -/
def neighborhoodPiece (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj v a ∧ G.Adj v b
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1.ne rfl

lemma neighborhoodPiece_cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) (v : V) :
    (neighborhoodPiece G v).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact no_adj_common_neighbors hG hab.2.1 hab.2.2 hab.1 hac.2.2 hac.1 hbc.1

/-- The common endpoint marginal contains no original neighborhood. -/
theorem neighborhood_not_mem (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (v : V) :
    G.neighborSet v ∉ D.map (fun e => e.val.1) := by
  intro hv
  have hw : G.neighborSet v ∈ D.map (fun e => e.val.2) :=
    marginals_equal G D hD ▸ hv
  have he : {e : Arc G | (neighborhoodPiece G v).Adj e.val.1 e.val.2} ∈ D :=
    Filter.mem_of_superset (Filter.inter_mem hv hw) (fun e he => ⟨e.property,he⟩)
  exact hD _ (neighborhoodPiece_cliqueFree G hG v) he

/-- Consequently this marginal is an isolated vertex in the mutual extension. -/
theorem marginal_isolated (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (q : Ultrafilter V) :
    ¬(ultrafilterGraph G hG).Adj (D.map (fun e => e.val.1)) q := by
  intro h
  obtain ⟨v,hv⟩ := Ultrafilter.nonempty_of_mem h.2
  exact neighborhood_not_mem G hG D hD v hv


/-- The compactness witness characterizes failure of finite, not countable,
covering. The distinction is essential. -/
theorem no_finite_cover_iff (G : SimpleGraph V) :
    ¬FiniteCover G ↔ ∃ D : Ultrafilter (Arc G), Avoids G D := by
  refine ⟨exists_avoiding G, ?_⟩
  rintro ⟨D,hD⟩ ⟨n,H,hH,hcov⟩
  have he : ∀ᶠ e : Arc G in D, ∃ i, (H i).Adj e.val.1 e.val.2 :=
    Filter.Eventually.of_forall (fun e => hcov _ _ e.property)
  obtain ⟨i,hi⟩ := Ultrafilter.eventually_exists_iff.mp he
  exact hD _ (hH i) hi

/-- The common endpoint marginal is nonprincipal, even without a clique bound. -/
theorem marginal_ne_pure (G : SimpleGraph V) (D : Ultrafilter (Arc G))
    (hD : Avoids G D) (v : V) :
    D.map (fun e => e.val.1) ≠ pure v := by
  intro heq
  have ha : {v} ∈ D.map (fun e => e.val.1) := by simp [heq]
  have hb : {v} ∈ D.map (fun e => e.val.2) := marginals_equal G D hD ▸ ha
  change {e : Arc G | e.val.1 = v} ∈ D at ha
  change {e : Arc G | e.val.2 = v} ∈ D at hb
  obtain ⟨e,he₁,he₂⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem ha hb)
  exact e.property.ne (he₁.trans he₂.symm)

/-- In particular, this marginal contains the cofinite filter. -/
theorem marginal_le_cofinite (G : SimpleGraph V) (D : Ultrafilter (Arc G))
    (hD : Avoids G D) :
    ((D.map (fun e => e.val.1) : Ultrafilter V) : Filter V) ≤ Filter.cofinite := by
  rcases (D.map (fun e => e.val.1)).le_cofinite_or_eq_pure with h | ⟨v,h⟩
  · exact h
  · exact (marginal_ne_pure G D hD v h).elim

/-- Finite covers give covers in the original sense, after intersecting
all pieces with G and padding the palette with empty graphs. -/
theorem FiniteCover.countable {G : SimpleGraph V} (hG : FiniteCover G) :
    IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨n,H,hH,hcov⟩ := hG
  let F : ℕ → SimpleGraph V := fun i => if hi : i < n then G ⊓ H ⟨i,hi⟩ else ⊥
  refine ⟨F,?_,?_⟩
  · intro i s hs
    by_cases hi : i < n
    · have ht := hs
      rw [show F i = G ⊓ H ⟨i,hi⟩ by simp [F,hi]] at ht
      obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hH ⟨i,hi⟩ _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.2,hac.2,hbc.2⟩)
    · have hb : (F i).CliqueFree 3 := by
        simpa only [F,dif_neg hi] using (SimpleGraph.cliqueFree_bot (α := V) (n := 3)
          (by omega))
      exact hb s hs
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      obtain ⟨i,hi⟩ := hcov a b hab
      exact ⟨i.val,by simpa only [F,dif_pos i.isLt,SimpleGraph.inf_adj] using
        (show G.Adj a b ∧ (H i).Adj a b from ⟨hab,hi⟩)⟩
    · rintro ⟨i,hi⟩
      by_cases h : i < n
      · have he : (F i).Adj a b ↔ G.Adj a b ∧ (H ⟨i,h⟩).Adj a b := by simp [F,h]
        exact (he.mp hi).1
      · simp [F,h] at hi

/-- This necessary condition for the original conjecture has now been checked;
it is not a sufficient condition for a counterexample. -/
theorem isolated_marginal_of_no_countable_cover (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (hn : ¬IsCountableUnionOfTriangleFree G) :
    ∃ D : Ultrafilter (Arc G), Avoids G D ∧
      D.map (fun e => e.val.1) = D.map (fun e => e.val.2) ∧
      (∀ v, G.neighborSet v ∉ D.map (fun e => e.val.1)) ∧
      (∀ q, ¬(ultrafilterGraph G hG).Adj (D.map (fun e => e.val.1)) q) := by
  obtain ⟨D,hD⟩ := exists_avoiding G (fun h => hn h.countable)
  exact ⟨D,hD,marginals_equal G D hD,neighborhood_not_mem G hG D hD,
    marginal_isolated G hG D hD⟩

#print axioms no_finite_cover_iff
#print axioms marginal_le_cofinite
#print axioms FiniteCover.countable
#print axioms isolated_marginal_of_no_countable_cover

#print axioms exists_avoiding
#print axioms marginals_equal
#print axioms marginal_isolated
end Erdos595BadEdge
