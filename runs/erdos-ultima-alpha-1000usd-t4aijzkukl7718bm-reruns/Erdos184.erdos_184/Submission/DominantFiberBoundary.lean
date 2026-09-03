import Submission.DominantFiberProjection

/-!
A nontrivial degree-dominating fibre in a simple graph of minimum degree
at least four has an internal cycle avoiding a dominating representative.
Together with nonincreasing lifting, this rules out all-optimality.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.DominantFiberBoundary
open WeakProjection DominantFiberProjection
variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {K : SimpleGraph W}

noncomputable def innerCount (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  (G.neighborFinset x ∩ S).card
noncomputable def outerCount (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  (G.neighborFinset x \ S).card

lemma degree_split (G : SimpleGraph V) (S : Finset V) (x : V) :
    innerCount G S x + outerCount G S x = G.degree x := by
  exact Finset.card_inter_add_card_sdiff _ _

lemma innerCount_induce (G : SimpleGraph V) (S : Finset V) (x : S) :
    innerCount G S x.val = (G.induce (S : Set V)).degree x := by
  have hh := congrArg Finset.card (G.map_neighborFinset_induce (s := (S : Set V)) x)
  simpa only [Finset.card_map,Finset.toFinset_coe,card_neighborFinset_eq_degree,innerCount,← card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hh.symm

lemma innerCount_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ x ∈ S, innerCount G S x) = 2 * (G.induce (S : Set V)).edgeFinset.card := by
  rw [← Finset.sum_coe_sort S]
  simp_rw [innerCount_induce]
  exact (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges

lemma innerCount_insert (G : SimpleGraph V) (U : Finset V) {v : V} (hv : v ∉ U) (x : V) :
    innerCount G (insert v U) x = innerCount G U x + if G.Adj x v then 1 else 0 := by
  unfold innerCount
  rw [Finset.inter_comm (G.neighborFinset x),Finset.inter_insert]
  by_cases hx : G.Adj x v
  · have hn : v ∉ U ∩ G.neighborFinset x := fun h => hv (Finset.mem_inter.mp h).1
    simp only [mem_neighborFinset,hx,if_pos]
    rw [Finset.card_insert_of_notMem hn,Finset.inter_comm U]
  · simp only [mem_neighborFinset,hx,if_false,add_zero,Finset.inter_comm U]

lemma adjacency_sum (G : SimpleGraph V) (U : Finset V) (v : V) :
    (∑ x ∈ U, if G.Adj x v then 1 else 0) = innerCount G U v := by
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  unfold innerCount
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_inter,mem_neighborFinset]
  exact ⟨fun h => ⟨h.2.symm,h.1⟩,fun h => ⟨h.2,h.1.symm⟩⟩

/-- A cut no larger than the degree of one vertex cannot enclose a nonempty
forest after that vertex is removed, if all the other enclosed vertices
have degree at least four. -/
lemma not_acyclic_of_cut_le_degree (G : SimpleGraph V) (U : Finset V)
    (hne : U.Nonempty) (v : V) (hv : v ∉ U)
    (hdeg : ∀ x ∈ U, 4 ≤ G.degree x)
    (hcut : (∑ x ∈ insert v U, outerCount G (insert v U) x) ≤ G.degree v) :
    ¬(G.induce (U : Set V)).IsAcyclic := by
  intro ha
  haveI : Nonempty (U : Set V) := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨⟨x,hx⟩⟩
  have hforest := forest_edge_card_lt_vertex_card (G.induce (U : Set V)) ha
  simp only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_coe_finset] at hforest
  have hin_v : innerCount G (insert v U) v = innerCount G U v := by
    rw [innerCount_insert G U hv]
    simp
  have hsplit_v := degree_split G (insert v U) v
  rw [hin_v] at hsplit_v
  rw [Finset.sum_insert hv] at hcut
  have hsum := Finset.sum_congr rfl (fun x (_ : x ∈ U) => degree_split G (insert v U) x)
  simp_rw [innerCount_insert G U hv] at hsum
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,innerCount_sum,adjacency_sum] at hsum
  have hsmall : innerCount G U v ≤ U.card := Finset.card_le_card Finset.inter_subset_right
  have hlarge : 4 * U.card ≤ ∑ x ∈ U, G.degree x := by
    have hh := Finset.sum_le_sum hdeg
    simpa only [Finset.sum_const,smul_eq_mul,Nat.mul_comm] using hh
  omega

noncomputable def boundaryPairs (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S.product Finset.univ).filter (fun p => G.Adj p.1 p.2 ∧ p.2 ∉ S)

lemma boundaryPairs_card (G : SimpleGraph V) (S : Finset V) :
    (boundaryPairs G S).card = ∑ x ∈ S, outerCount G S x := by
  unfold boundaryPairs
  rw [Finset.card_filter]
  calc
    _ = ∑ x ∈ S, ∑ y : V, if G.Adj x y ∧ y ∉ S then (1 : ℕ) else 0 := by
      exact Finset.sum_product S Finset.univ (fun p : V × V => if G.Adj p.1 p.2 ∧ p.2 ∉ S then (1 : ℕ) else 0)
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  unfold outerCount
  congr 1
  ext y
  simp

/-- Surviving-edge injectivity bounds a fibre's boundary by the degree of
its image vertex. Surjectivity on target edges is not needed for this bound. -/
lemma fiber_boundary_le_degree (f : V → W)
    (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f)) (w : W) :
    (∑ x ∈ Finset.univ.filter (fun x => f x = w),
      outerCount G (Finset.univ.filter (fun x => f x = w)) x) ≤ K.degree w := by
  let S := Finset.univ.filter (fun x => f x = w)
  change (∑ x ∈ S, outerCount G S x) ≤ K.degree w
  rw [← boundaryPairs_card]
  have hmem (p : V × V) : p ∈ boundaryPairs G S ↔
      f p.1 = w ∧ G.Adj p.1 p.2 ∧ f p.2 ≠ w := by
    simp [boundaryPairs,S]
  apply Finset.card_le_card_of_injOn (fun p : V × V => f p.2)
  · intro p hp
    obtain ⟨hx,ha,hy⟩ := (hmem p).mp hp
    have hne : f p.1 ≠ f p.2 := fun h => hy (h.symm.trans hx)
    have hk : K.Adj w (f p.2) := hx ▸ (hf ha).resolve_left hne
    exact (K.mem_neighborFinset _ _).mpr hk
  · intro p hp q hq heq
    obtain ⟨hx,ha,hy⟩ := (hmem p).mp hp
    obtain ⟨hu,hb,hz⟩ := (hmem q).mp hq
    have hp' : s(p.1,p.2) ∈ survivingEdges G f := by
      refine ⟨ha,?_⟩
      simpa only [Sym2.map_pair_eq,Sym2.mk_isDiag_iff,hx] using Ne.symm hy
    have hq' : s(q.1,q.2) ∈ survivingEdges G f := by
      refine ⟨hb,?_⟩
      simpa only [Sym2.map_pair_eq,Sym2.mk_isDiag_iff,hu] using Ne.symm hz
    have hh := hi hp' hq' (by simp only [Sym2.map_pair_eq,hx,hu,heq])
    rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext h1 h2
    · exact (hz ((congrArg f h1).symm.trans hx)).elim

/-- A nontrivial fibre whose boundary is dominated by one vertex contains
a cycle avoiding that vertex, provided the other fibre vertices have
degree at least four. This uses simplicity in the forest count. -/
lemma fiber_cycle_avoiding_representative (f : V → W)
    (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (v : V) (hdom : K.degree (f v) ≤ G.degree v)
    (hmin : ∀ x, f x = f v → x ≠ v → 4 ≤ G.degree x)
    (hne : ∃ x, f x = f v ∧ x ≠ v) :
    ∃ H : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      f v ∈ f '' H.verts ∧ v ∉ H.verts ∧ ∀ x ∈ H.verts, f x = f v := by
  let S := Finset.univ.filter (fun x => f x = f v)
  let U := S.erase v
  have hvS : v ∈ S := by simp [S]
  have huS : insert v U = S := Finset.insert_erase hvS
  have hvU : v ∉ U := by simp [U]
  have hU : U.Nonempty := by
    obtain ⟨x,hx,hn⟩ := hne
    exact ⟨x,Finset.mem_erase.mpr ⟨hn,by simp [S,hx]⟩⟩
  have hdeg : ∀ x ∈ U, 4 ≤ G.degree x := by
    intro x hx
    have hh := Finset.mem_erase.mp hx
    exact hmin x (Finset.mem_filter.mp hh.2).2 hh.1
  have hcut : (∑ x ∈ insert v U, outerCount G (insert v U) x) ≤ G.degree v := by
    rw [huS]
    exact (fiber_boundary_le_degree f hf hi (f v)).trans hdom
  have hna := not_acyclic_of_cut_le_degree G U hU v hvU hdeg hcut
  obtain ⟨u,p,hp⟩ : ∃ u, ∃ p : (G.induce (U : Set V)).Walk u u, p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hna
  let φ := (SimpleGraph.Embedding.induce (G := G) (U : Set V)).toHom
  let q := p.map φ
  have hq : q.IsCycle := hp.map Subtype.val_injective
  let H := q.toSubgraph
  have hverts : ∀ x ∈ H.verts, x ∈ U := by
    intro x hx
    have hh : x ∈ (p.map φ).support := (q.mem_verts_toSubgraph).mp hx
    rw [Walk.support_map] at hh
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hh
    exact y.property
  have hc := cycle_subgraph_regular G hq
  refine ⟨H,?_,?_,?_,?_⟩
  · refine ⟨hc.1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 x
  · refine ⟨u.val,(q.mem_verts_toSubgraph).mpr q.start_mem_support,?_⟩
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp u.property).2).2
  · exact fun h => hvU (hverts v h)
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hverts x hx)).2).2

lemma not_all_optimal_of_nontrivial_dominating_fiber
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (hlift : HasNonincreasingLift G K)
    (v : V) (hv : K.degree (f v) ≤ G.degree v)
    (hmin : ∀ x, f x = f v → x ≠ v → 4 ≤ G.degree x)
    (hne : ∃ x, f x = f v ∧ x ≠ v) :
    ¬MinimalCounterexample.AllCyclesOptimal G := by
  obtain ⟨H,hcH,hhit,hmiss,_⟩ := fiber_cycle_avoiding_representative f hf hi v hv hmin hne
  exact not_all_optimal_of_missed_vertex f hf hi hs hdom hlift H hcH v hv hhit hmiss

/-- In an all-optimal simple graph of minimum degree at least four, any
weak quotient with degree-dominating fibres and a nonincreasing reverse
lift must be injective. The existence of such a nontrivial quotient in
arbitrary critical graphs is not asserted. -/
lemma all_optimal_quotient_injective
    (f : V → W) (hf : IsWeakMap (G := G) (K := K) f)
    (hi : Set.InjOn (Sym2.map f) (survivingEdges G f))
    (hs : Set.SurjOn (Sym2.map f) (survivingEdges G f) K.edgeSet)
    (hdom : ∀ w, ∃ v, f v = w ∧ K.degree w ≤ G.degree v)
    (hlift : HasNonincreasingLift G K)
    (hmin : ∀ v, 4 ≤ G.degree v)
    (hopt : MinimalCounterexample.AllCyclesOptimal G) : Function.Injective f := by
  intro a b hab
  obtain ⟨v,hv,hdeg⟩ := hdom (f a)
  have hdv : K.degree (f v) ≤ G.degree v := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hv] using hdeg
  have hall : ∀ x, f x = f v → x = v := by
    intro x hx
    by_contra hn
    exact not_all_optimal_of_nontrivial_dominating_fiber f hf hi hs hdom hlift v hdv
      (fun y _ _ => hmin y) ⟨x,hx,hn⟩ hopt
  exact (hall a hv.symm).trans (hall b (hab.symm.trans hv.symm)).symm

end Erdos184.DominantFiberBoundary
