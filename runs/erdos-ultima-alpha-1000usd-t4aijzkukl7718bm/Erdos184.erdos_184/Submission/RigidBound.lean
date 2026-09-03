import Submission.CleanRings

/-! A linear bound for even cycle-rigid graphs. Minimal-core rigidity is not assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open ChordalIncidence
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma ring_of_incidence_walk (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    {a : V} (p : (primal (pieceVertices D)).Walk a a) (hp : p.IsCycle)
    (label : {e : Sym2 V // e ∈ p.edges} → D)
    (hl : ∀ e x, x ∈ p.support → (x ∈ pieceVertices D (label e) ↔ x ∈ e.val))
    {n : ℕ} (hlen : p.length = n+3) : Nonempty (Ring G n) := by
  let vertex : Fin (n+3) → V := fun i => p.getVert i.val
  have hinj : Function.Injective vertex := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
      (by change j.val ≤ p.length-1; omega) he
  have hnext (i : Fin (n+3)) : vertex (i+1) = p.getVert (i.val+1) := by
    dsimp only [vertex]
    rw [Fin.val_add_eq_ite,Fin.val_one]
    split_ifs with hi
    · have he : i.val+1 = p.length := by omega
      have he0 : i.val+1-(n+3) = 0 := by omega
      rw [he0,he,Walk.getVert_zero,Walk.getVert_length]
    · rfl
  have hedge (i : Fin (n+3)) : s(vertex i,vertex (i+1)) ∈ p.edges := by
    rw [hnext]
    exact consecutive_mem_edges p i.val (by omega)
  let edge (i : Fin (n+3)) : {e : Sym2 V // e ∈ p.edges} := ⟨s(vertex i,vertex (i+1)),hedge i⟩
  have einj : Function.Injective edge := by
    intro i j he
    have he' : s(vertex i,vertex (i+1)) = s(vertex j,vertex (j+1)) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp he' with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact hinj hi
    · have hi' := hinj hi
      have hj' := hinj hj
      exact (two_next_ne n i (by rw [hj',← hi'])).elim
  have linj := incidence_label_injective p label hl
  refine ⟨{
    vertex := vertex
    injective := hinj
    piece := fun i => (label (edge i)).val
    cycle := fun i => hD _ (label (edge i)).property
    disjoint := ?_
    incidence := ?_
  }⟩
  · intro i j hij
    exact hd (label (edge i)).property (label (edge j)).property
      (fun he => hij (einj (linj (Subtype.ext he))))
  · intro i j
    have hmem : vertex i ∈ p.support := p.getVert_mem_support i.val
    have he := hl (edge j) (vertex i) hmem
    simpa only [pieceVertices,Set.mem_toFinset,edge,Sym2.mem_iff,hinj.eq_iff] using he

lemma no_incidenceCycle (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ¬ IncidenceCycle (pieceVertices D) := by
  rintro ⟨a,p,hp,label,hl⟩
  have hlen : p.length = (p.length-3)+3 := by have := hp.three_le_length; omega
  exact no_ring hrig heven _ (ring_of_incidence_walk D hD hd p hp label hl hlen)

lemma rigid_number_le_support (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v)) :
    Critical.number G ≤ G.support.ncard := by
  obtain ⟨D,hD,hdec,_⟩ := Rigidity.minimum_cycles heven
  exact rigid_number_bound_of_no_incidenceCycle hrig D hD hdec (no_incidenceCycle hrig heven D hD hdec.1)

#print axioms ring_of_incidence_walk
#print axioms no_incidenceCycle
#print axioms rigid_number_le_support
end Erdos184Work.CycleRings
