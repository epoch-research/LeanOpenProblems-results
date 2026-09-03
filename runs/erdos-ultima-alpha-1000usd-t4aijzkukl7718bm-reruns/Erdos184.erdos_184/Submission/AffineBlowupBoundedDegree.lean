import Submission.AffineBlowup

/-!
Every connected even graph of maximum degree less than `q` has a partition
of its independent finite-field `q`-blowup into at most `q²` simple cycles.
This result concerns blowups, not a bound for the original graph.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.AffineBlowup

variable {V W F : Type*}

/-- The elementary greedy bound for a finite colour set. -/
lemma exists_colour_of_degree_lt [Fintype V] [Fintype F] [Nonempty F]
    (G : SimpleGraph V) (hd : ∀ v, G.degree v < Fintype.card F) :
    ∃ c : V → F, ∀ {u v}, G.Adj u v → c u ≠ c v := by
  have hpartial : ∀ S : Finset V, ∃ c : V → F,
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.arbitrary F, by simp⟩
    | @insert w S hw ih =>
      obtain ⟨c,hc⟩ := ih
      have hlt : ((G.neighborFinset w).image c).card < (Finset.univ : Finset F).card := by
        calc
          _ ≤ (G.neighborFinset w).card := Finset.card_image_le
          _ = G.degree w := G.card_neighborFinset_eq_degree w
          _ < Fintype.card F := hd w
          _ = _ := (Finset.card_univ).symm
      obtain ⟨d,_,hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      let c' : V → F := fun x => if x = w then d else c x
      refine ⟨c', ?_⟩
      intro u hu v hv huv
      by_cases huw : u = w
      · subst u
        have hvw : v ≠ w := huv.ne.symm
        simp only [c',if_pos rfl,if_neg hvw]
        intro heq
        exact hd (Finset.mem_image.mpr ⟨v, (G.mem_neighborFinset w v).mpr huv, heq.symm⟩)
      · by_cases hvw : v = w
        · subst v
          simp only [c',if_pos rfl,if_neg huw]
          intro heq
          exact hd (Finset.mem_image.mpr ⟨u, (G.mem_neighborFinset w u).mpr huv.symm, heq⟩)
        · have huS : u ∈ S := (Finset.mem_insert.mp hu).resolve_left huw
          have hvS : v ∈ S := (Finset.mem_insert.mp hv).resolve_left hvw
          simpa only [c',if_neg huw,if_neg hvw] using hc u huS v hvS huv
  obtain ⟨c,hc⟩ := hpartial Finset.univ
  exact ⟨c,fun {u v} huv => hc u (Finset.mem_univ _) v (Finset.mem_univ _) huv⟩

/-- Edge-injectivity lets each fibre use distinct labels from the target
neighbour set. No injectivity of the vertex projection is assumed. -/
lemma exists_offsets_of_degree_le [Fintype V] [Fintype W] [Fintype F] [Field F]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : K →g G)
    (hi : Set.InjOn (Sym2.map f) K.edgeSet)
    (hn : ∀ i, ∃ j, K.Adj i j)
    (hd : ∀ v, G.degree v ≤ Fintype.card F) :
    ∃ offset : W → F, SeparatesFibres f offset := by
  choose next hnext using hn
  have hemb : ∀ v, Nonempty (G.neighborSet v ↪ F) := by
    intro v
    apply Function.Embedding.nonempty_of_card_le
    simpa only [card_neighborSet_eq_degree] using hd v
  let emb : ∀ v, G.neighborSet v ↪ F := fun v => Classical.choice (hemb v)
  let offset : W → F := fun i => emb (f i) ⟨f (next i), f.map_rel (hnext i)⟩
  refine ⟨offset, ?_⟩
  intro i j hij ho
  change f i = f j at hij
  have hcompare : ∀ (v v' : V) (x : G.neighborSet v) (y : G.neighborSet v'),
      v = v' → emb v x = emb v' y → x.val = y.val := by
    intro v v' x y hv
    subst v'
    intro hh
    exact congrArg Subtype.val ((emb v).injective hh)
  have hnij : f (next i) = f (next j) :=
    hcompare (f i) (f j) ⟨f (next i), f.map_rel (hnext i)⟩
      ⟨f (next j), f.map_rel (hnext j)⟩ hij ho
  have he : s(i,next i) = s(j,next j) :=
    hi (hnext i) (hnext j) (by simp only [Sym2.map_pair_eq,hij,hnij])
  rcases Sym2.eq_iff.mp he with he | he
  · exact he.1
  · exact ((f.map_rel (hnext i)).ne (hij.trans (congrArg f he.2).symm)).elim

set_option maxHeartbeats 1000000 in
/-- The cycle count of an independent blowup need not retain the complexity
of the original bounded-degree graph. The bound is independent of its order. -/
theorem bounded_degree_blowup [Fintype V] [Fintype F] [Field F]
    (G : SimpleGraph V) (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v))
    (hdegree : ∀ v, G.degree v < Fintype.card F) :
    ∃ D : Finset (graph G F).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (graph G F) D ∧ D.card ≤ Fintype.card F ^ 2 := by
  by_cases hbot : G = ⊥
  · subst G
    refine ⟨∅, by simp, ⟨by simp, ?_⟩, by simp⟩
    simp [graph]
  obtain ⟨u,p,hp⟩ := exists_eulerian_closed_walk G hconn heven
  obtain ⟨v,c,hc⟩ := exists_cycle_of_even_nonempty G heven hbot
  have hlen : p.length = G.edgeFinset.card := by
    have hh := congrArg Finset.card hp.edgesFinset_eq
    simpa only [Walk.IsTrail.edgesFinset, Finset.card_mk, Multiset.coe_card,
      Walk.length_edges] using hh
  have hthree : 3 ≤ p.length := by
    rw [hlen]
    exact hc.three_le_length.trans hc.isTrail.length_le_card_edgeFinset
  obtain ⟨n,hn⟩ : ∃ n, p.length = n+3 := ⟨p.length-3, by omega⟩
  let f := tourCycleHom p hn
  have hb := tourCycleHom_edge_bijective p hn hp
  have hr : (cycleGraph (n+3)).IsRegularOfDegree 2 := by
    intro i
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (cycleGraph_degree_three_le (v := i))
  obtain ⟨colour,hcolour⟩ := exists_colour_of_degree_lt G hdegree
  obtain ⟨offset,hoffset⟩ := exists_offsets_of_degree_le (F := F) f hb.1 (by
    intro i
    apply (cycleGraph (n+3)).degree_pos_iff_exists_adj i |>.mp
    have hri := hr i
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hri ⊢
    omega) (fun v => (hdegree v).le)
  exact affine_decomposition f colour offset hoffset cycleGraph_connected (by
    intro i
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr i)
    hb.1 hb.2 hcolour

end Erdos184.AffineBlowup
