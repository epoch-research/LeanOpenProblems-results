import Submission.WeakProjection
import Submission.MinimalCounterexample

/-!
Degree-dominating representatives turn loop-erasing projection into a
nonincreasing cycle-count operation. Missing a representative gives an
additional strict saving. No universally available contraction is asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.DominantFiberProjection
open WeakProjection
variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {K : SimpleGraph W}

noncomputable def fiberPieces (f : V → W) (D : Finset G.Subgraph) (w : W) :
    Finset G.Subgraph := D.filter (fun H => w ∈ f '' H.verts)

noncomputable def missedPieces (f : V → W) (r : W → V)
    (D : Finset G.Subgraph) (w : W) : Finset G.Subgraph :=
  (fiberPieces f D w).filter (fun H => r w ∉ H.verts)

lemma image_incidence_sum (f : V → W) (D : Finset G.Subgraph) :
    (∑ H ∈ D, (f '' H.verts).ncard) = ∑ w, (fiberPieces f D w).card := by
  have hcard (H : G.Subgraph) : (f '' H.verts).ncard =
      (Finset.univ.filter (fun w => w ∈ f '' H.verts)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp
  simp only [hcard, fiberPieces, Finset.card_filter]
  rw [Finset.sum_comm]

omit [Fintype W] in
lemma fiber_degree_identity (f : V → W) (r : W → V)
    (hr : Function.RightInverse r f) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (w : W) :
    G.degree (r w) + 2 * (missedPieces f r D w).card =
      2 * (fiberPieces f D w).card := by
  have hfilter : (fiberPieces f D w).filter (fun H => r w ∈ H.verts) =
      D.filter (fun H => r w ∈ H.verts) := by
    ext H
    simp only [fiberPieces, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      exact ⟨⟨h.1,⟨r w,h.2,hr w⟩⟩,h.2⟩
  have hcount := Finset.card_filter_add_card_filter_not
    (s := fiberPieces f D w) (fun H : G.Subgraph => r w ∈ H.verts)
  rw [hfilter] at hcount
  have hdeg := cycle_decomposition_vertex_count G D hc hd (r w)
  change _ + (missedPieces f r D w).card = _ at hcount
  omega

/-- The exact incidence balance before imposing degree domination. -/
lemma incidence_degree_identity (f : V → W) (r : W → V)
    (hr : Function.RightInverse r f) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    (∑ w, G.degree (r w)) + 2 * (∑ w, (missedPieces f r D w).card) =
      2 * (∑ H ∈ D, (f '' H.verts).ncard) := by
  rw [image_incidence_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => fiber_degree_identity f r hr D hc hd w)

/-- Degree-dominating representatives pay for all projection splitting.
Each fibre-piece incidence missing its representative saves another piece. -/
lemma project_with_savings
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (r : W → V) (hr : Function.RightInverse r f)
    (hdeg : ∀ w, K.degree w ≤ G.degree (r w))
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧
      E.card + (∑ w, (missedPieces f r D w).card) ≤ D.card := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition f hf hi hs D hc hd
  have hb := incidence_degree_identity f r hr D hc hd
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hdeg w)
  have hh := K.sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hh
  rw [Nat.card_coe_set_eq] at hh
  refine ⟨E,?_,hdE,by omega⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 v

/-- The general degree budget, including any strict degree excess. -/
lemma project_degree_budget
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (r : W → V) (hr : Function.RightInverse r f)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧
      2 * E.card + (∑ w, G.degree (r w)) +
        2 * (∑ w, (missedPieces f r D w).card) ≤
      2 * D.card + (∑ w, K.degree w) := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition f hf hi hs D hc hd
  have hb := incidence_degree_identity f r hr D hc hd
  have hh := K.sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  refine ⟨E,?_,hdE,by omega⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 v

/-- A cardinality-nonincreasing lift is an explicit extra hypothesis, not a
consequence of having a weak quotient map. -/
def HasNonincreasingLift (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∀ E : Finset K.Subgraph,
    (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    IsDecomposition K E →
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ E.card

lemma project_nonincreasing
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card ≤ D.card := by
  choose r hr hdeg using hdom
  obtain ⟨E,hcE,hdE,hbE⟩ := project_with_savings f hf hi hs r hr hdeg D hc hd
  refine ⟨E,?_,hdE,by omega⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 v

/-- Any minimum partition saturates every chosen degree-dominating
representative: a piece visiting its fibre must contain it. -/
lemma minimum_contains_representatives
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (r : W → V) (hr : Function.RightInverse r f)
    (hdeg : ∀ w, K.degree w ≤ G.degree (r w))
    (hlift : HasNonincreasingLift G K)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ F : Finset G.Subgraph,
      (∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G F → D.card ≤ F.card) :
    ∀ H ∈ D, ∀ w ∈ f '' H.verts, r w ∈ H.verts := by
  obtain ⟨E,hcE,hdE,hbE⟩ := project_with_savings f hf hi hs r hr hdeg D hc hd
  obtain ⟨F,hcF,hdF,hbF⟩ := hlift E hcE hdE
  have hmin := hm F hcF hdF
  intro H hH w hw
  by_contra hn
  have hmem : H ∈ missedPieces f r D w :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hH,hw⟩,hn⟩
  have hpos := Finset.card_pos.mpr ⟨H,hmem⟩
  have hle : (missedPieces f r D w).card ≤
      ∑ z, (missedPieces f r D z).card :=
    Finset.single_le_sum (f := fun z : W => (missedPieces f r D z).card)
      (fun z _ => Nat.zero_le _) (Finset.mem_univ w)
  omega

/-- The representative can be chosen independently in each fibre. -/
lemma minimum_contains_any_dominating_vertex
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (hlift : HasNonincreasingLift G K)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ F : Finset G.Subgraph,
      (∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G F → D.card ≤ F.card)
    (H : G.Subgraph) (hH : H ∈ D) (v : V)
    (hv : K.degree (f v) ≤ G.degree v) (hhit : f v ∈ f '' H.verts) :
    v ∈ H.verts := by
  choose r hr hdeg using hdom
  let r' : W → V := fun w => if w = f v then v else r w
  have hr' : Function.RightInverse r' f := by
    intro w
    dsimp only [r']
    split_ifs with hw
    · exact hw.symm
    · exact hr w
  have hd' : ∀ w, K.degree w ≤ G.degree (r' w) := by
    intro w
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hv ⊢
    dsimp only [r']
    split_ifs with hw
    · simpa only [hw] using hv
    · exact hdeg w
  have hh := minimum_contains_representatives f hf hi hs r' hr' hd' hlift D hc hd hm H hH (f v) hhit
  simpa only [r',if_pos rfl] using hh

/-- In an all-optimal source, saturation holds for every cycle, not merely
for the pieces of one chosen optimum. -/
lemma all_optimal_cycle_saturation
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (hlift : HasNonincreasingLift G K)
    (hopt : MinimalCounterexample.AllCyclesOptimal G)
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (v : V) (hv : K.degree (f v) ≤ G.degree v)
    (hhit : f v ∈ f '' H.verts) : v ∈ H.verts := by
  obtain ⟨D,hc,hd,hHD,hm⟩ := hopt H hcH
  exact minimum_contains_any_dominating_vertex f hf hi hs hdom hlift D hc hd hm H hHD v hv hhit

/-- A cycle missing one dominating vertex of a visited fibre rules out
all-optimality, provided the reverse nonincreasing lift is established. -/
lemma not_all_optimal_of_missed_vertex
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (hlift : HasNonincreasingLift G K)
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (v : V) (hv : K.degree (f v) ≤ G.degree v)
    (hhit : f v ∈ f '' H.verts) (hmiss : v ∉ H.verts) :
    ¬MinimalCounterexample.AllCyclesOptimal G := by
  intro hopt
  exact hmiss (all_optimal_cycle_saturation f hf hi hs hdom hlift hopt H hcH v hv hhit)

/-- Under a nonincreasing reverse lift, degree domination is necessarily
an equality at every representative. No optimality of the source is needed. -/
lemma dominating_degrees_equal
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (r : W → V) (hr : Function.RightInverse r f)
    (hdeg : ∀ w, K.degree w ≤ G.degree (r w))
    (hlift : HasNonincreasingLift G K) (he : ∀ v, Even (G.degree v)) :
    ∀ w, K.degree w = G.degree (r w) := by
  obtain ⟨D,hc,hd,hm⟩ := minimum_cycle_decomposition G he
  obtain ⟨E,hcE,hdE,hbE⟩ := project_degree_budget f hf hi hs r hr D hc hd
  obtain ⟨F,hcF,hdF,hbF⟩ := hlift E hcE hdE
  have hmin := hm F hcF hdF
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hdeg w)
  have heq : (∑ w, K.degree w) = ∑ w, G.degree (r w) := by omega
  exact fun w => (Finset.sum_eq_sum_iff_of_le (fun z _ => hdeg z)).mp heq w (Finset.mem_univ w)

/-- Count one saving for every fibre in a specified finite set that has
a piece missing some degree-dominating representative. The representatives
may depend on the fibre and on the decomposition. -/
lemma project_penalty_per_fiber
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (B : Finset W)
    (hB : ∀ w ∈ B, ∃ v, f v = w ∧ K.degree w ≤ G.degree v ∧
      ∃ H ∈ D, w ∈ f '' H.verts ∧ v ∉ H.verts) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card + B.card ≤ D.card := by
  have hex : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v ∧
      (w ∈ B → ∃ H ∈ D, w ∈ f '' H.verts ∧ v ∉ H.verts) := by
    intro w
    by_cases hw : w ∈ B
    · obtain ⟨v,hv,hdeg,H,hH,hhit,hmiss⟩ := hB w hw
      exact ⟨v,hv,hdeg,fun _ => ⟨H,hH,hhit,hmiss⟩⟩
    · obtain ⟨v,hv,hdeg⟩ := hdom w
      exact ⟨v,hv,hdeg,fun h => (hw h).elim⟩
  choose r hr hdeg hmiss using hex
  obtain ⟨E,hcE,hdE,hbE⟩ := project_with_savings f hf hi hs r hr hdeg D hc hd
  have hsum : B.card ≤ ∑ w, (missedPieces f r D w).card := by
    calc
      B.card = ∑ w ∈ B, 1 := by simp
      _ ≤ ∑ w ∈ B, (missedPieces f r D w).card := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨H,hH,hhit,hn⟩ := hmiss w hw
        exact Finset.card_pos.mpr ⟨H,
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hH,hhit⟩,hn⟩⟩
      _ ≤ ∑ w, (missedPieces f r D w).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ B)
  refine ⟨E,?_,hdE,by omega⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 v

end Erdos184.DominantFiberProjection
