import Submission.OddForestReduction

/-! Extracting simple paths with distinct endpoints, leaving an even graph.
The residual cycles have not been absorbed; this is not the all-odd simple-path
decomposition theorem and does not settle Erdős184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def oddVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => Odd (Nat.card (G.neighborSet v)))

@[simp] lemma mem_oddVertices {v : V} :
    v ∈ oddVertices G ↔ Odd (Nat.card (G.neighborSet v)) := by simp [oddVertices]

lemma even_card_oddVertices (G : SimpleGraph V) : Even (oddVertices G).card := by
  simpa only [oddVertices, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using G.even_card_odd_degree_vertices

lemma exists_other_odd_reachable {u : V} (hu : u ∈ oddVertices G) :
    ∃ v : V, v ≠ u ∧ G.Reachable u v ∧ v ∈ oddVertices G := by
  by_contra! hn
  let S : Set V := {v | G.Reachable u v}
  let H := G.induce S
  let a : S := ⟨u,.rfl⟩
  have hd : ∀ v : S, Nat.card (H.neighborSet v) = Nat.card (G.neighborSet v.val) := by
    intro v
    have h := SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := S) (v := v)
      (by intro w hvw; exact v.property.trans hvw.reachable)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h
  have hs : oddVertices H = {a} := by
    ext v
    simp only [mem_oddVertices, Finset.mem_singleton, hd]
    constructor
    · intro hv
      apply Subtype.ext
      by_contra hne
      exact hn v.val hne v.property (mem_oddVertices.mpr hv)
    · rintro rfl
      exact mem_oddVertices.mp hu
  have he := even_card_oddVertices H
  rw [hs] at he
  norm_num at he

/-- Degree parity of the graph of a nonclosed simple path. -/
lemma path_odd_iff {u v : V} (p : G.Walk u v) (hp : p.IsPath) (huv : u ≠ v) (w : V) :
    Odd (Nat.card (p.toSubgraph.spanningCoe.neighborSet w)) ↔ w = u ∨ w = v := by
  let H := p.toSubgraph.spanningCoe
  have hmem : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    exact p.mem_edges_toSubgraph.mpr he
  let q := p.transfer H hmem
  have hq : q.IsEulerian := by
    apply (hp.transfer hmem).isTrail.isEulerian_of_forall_mem
    intro e he
    simpa only [q,Walk.edges_transfer] using p.mem_edges_toSubgraph.mp he
  have he := hq.even_degree_iff (x := w)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he
  rw [← Nat.not_even_iff_odd, he]
  tauto

lemma oddVertices_delete_path {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (huv : u ≠ v) (hu : u ∈ oddVertices G) (hv : v ∈ oddVertices G) :
    oddVertices (G \ p.toSubgraph.spanningCoe) = ((oddVertices G).erase u).erase v := by
  ext w
  have hd := degree_sdiff_add G p.toSubgraph.spanningCoe p.toSubgraph.spanningCoe_le w
  have hb := path_odd_iff p hp huv w
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
  simp only [Finset.mem_erase,mem_oddVertices]
  by_cases hwu : w = u
  · subst w
    have ho := Nat.odd_iff.mp (mem_oddVertices.mp hu)
    have hp' := Nat.odd_iff.mp (hb.mpr (Or.inl rfl))
    simp only [ne_eq,not_true_eq_false,and_false,false_and,iff_false,Nat.odd_iff]
    omega
  · by_cases hwv : w = v
    · subst w
      have ho := Nat.odd_iff.mp (mem_oddVertices.mp hv)
      have hp' := Nat.odd_iff.mp (hb.mpr (Or.inr rfl))
      simp only [ne_eq,not_true_eq_false,and_false,false_and,iff_false,Nat.odd_iff]
      omega
    · have hn : ¬ Odd (Nat.card (p.toSubgraph.spanningCoe.neighborSet w)) := by
        rw [hb]
        exact fun h => h.elim hwu hwv
      rw [Nat.odd_iff] at hn
      simp only [ne_eq,hwu,hwv,not_false_eq_true,true_and,Nat.odd_iff]
      omega

/-- A nonempty simple path with its endpoints retained as data. -/
structure Piece (G : SimpleGraph V) where
  src : V
  dst : V
  walk : G.Walk src dst
  isPath : walk.IsPath
  ne : src ≠ dst

namespace Piece
variable {H : SimpleGraph V}

def mapLe (h : G ≤ H) (p : Piece G) : Piece H where
  src := p.src
  dst := p.dst
  walk := p.walk.mapLe h
  isPath := p.isPath.mapLe h
  ne := p.ne

@[simp] lemma mapLe_src (h : G ≤ H) (p : Piece G) : (p.mapLe h).src = p.src := rfl
@[simp] lemma mapLe_dst (h : G ≤ H) (p : Piece G) : (p.mapLe h).dst = p.dst := rfl
@[simp] lemma mapLe_edges (h : G ≤ H) (p : Piece G) : (p.mapLe h).walk.edges = p.walk.edges :=
  Walk.edges_mapLe_eq_edges h p.walk
end Piece

def edgeList (L : List (Piece G)) : List (Sym2 V) := L.flatMap (fun p => p.walk.edges)
def endpoints (L : List (Piece G)) : List V := L.flatMap (fun p => [p.src,p.dst])

@[simp] lemma edgeList_nil : edgeList ([] : List (Piece G)) = [] := rfl
@[simp] lemma endpoints_nil : endpoints ([] : List (Piece G)) = [] := rfl
@[simp] lemma edgeList_cons (p : Piece G) (L : List (Piece G)) :
    edgeList (p::L) = p.walk.edges ++ edgeList L := rfl
@[simp] lemma endpoints_cons (p : Piece G) (L : List (Piece G)) :
    endpoints (p::L) = p.src :: p.dst :: endpoints L := rfl

@[simp] lemma edgeList_mapLe {H : SimpleGraph V} (h : G ≤ H) (L : List (Piece G)) :
    edgeList (L.map (Piece.mapLe h)) = edgeList L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [ih]

@[simp] lemma endpoints_mapLe {H : SimpleGraph V} (h : G ≤ H) (L : List (Piece G)) :
    endpoints (L.map (Piece.mapLe h)) = endpoints L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [ih]

lemma endpoints_length (L : List (Piece G)) : (endpoints L).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]; omega

/-- Every odd vertex is used exactly once as a path endpoint. No residual cycle
bound, and no absorption of the residual even graph, is asserted. -/
lemma exists_extraction (G : SimpleGraph V) :
    ∃ (L : List (Piece G)) (R : SimpleGraph V),
      R ≤ G ∧ (∀ v, Even (Nat.card (R.neighborSet v))) ∧
      (edgeList L).Nodup ∧ (endpoints L).Nodup ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L ∨ e ∈ R.edgeSet) ∧
      (∀ e, e ∈ edgeList L → e ∉ R.edgeSet) ∧
      (∀ v, v ∈ endpoints L ↔ v ∈ oddVertices G) := by
  have main : ∀ n : ℕ, ∀ H : SimpleGraph V, (oddVertices H).card = n →
      ∃ (L : List (Piece H)) (R : SimpleGraph V),
        R ≤ H ∧ (∀ v, Even (Nat.card (R.neighborSet v))) ∧
        (edgeList L).Nodup ∧ (endpoints L).Nodup ∧
        (∀ e, e ∈ H.edgeSet ↔ e ∈ edgeList L ∨ e ∈ R.edgeSet) ∧
        (∀ e, e ∈ edgeList L → e ∉ R.edgeSet) ∧
        (∀ v, v ∈ endpoints L ↔ v ∈ oddVertices H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hn
      by_cases hz : (oddVertices H) = ∅
      · refine ⟨[],H,le_rfl,?_,by simp,by simp,by simp,by simp,by simp [hz]⟩
        intro v
        have hv : v ∉ oddVertices H := by rw [hz]; simp
        rw [mem_oddVertices, ← Nat.not_even_iff_odd, not_not] at hv
        exact hv
      obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      obtain ⟨v,hvu,huv,hv⟩ := exists_other_odd_reachable hu
      obtain ⟨p,hp⟩ := huv.exists_isPath
      let P : Piece H := ⟨u,v,p,hp,Ne.symm hvu⟩
      let K := H \ p.toSubgraph.spanningCoe
      have hKG : K ≤ H := sdiff_le
      have ho : oddVertices K = ((oddVertices H).erase u).erase v :=
        oddVertices_delete_path p hp (Ne.symm hvu) hu hv
      have hvc : v ∈ (oddVertices H).erase u := Finset.mem_erase.mpr ⟨hvu,hv⟩
      have hcard : (oddVertices K).card + 2 = n := by
        rw [ho,Finset.card_erase_of_mem hvc,Finset.card_erase_of_mem hu]
        have hu0 : 0 < (oddVertices H).card := Finset.card_pos.mpr ⟨u,hu⟩
        have hv0 : 0 < ((oddVertices H).erase u).card := Finset.card_pos.mpr ⟨v,hvc⟩
        rw [Finset.card_erase_of_mem hu] at hv0
        omega
      obtain ⟨L,R,hRK,he,hEdges,hEnds,hCover,hDis,hTerm⟩ :=
        ih (oddVertices K).card (by omega) K rfl
      let L' := L.map (Piece.mapLe hKG)
      have hmem : ∀ e, e ∈ edgeList L → e ∈ K.edgeSet :=
        fun e he => (hCover e).mpr (Or.inl he)
      have hdis : p.edges.Disjoint (edgeList L) := by
        intro e hep heL
        have hh := hmem e heL
        rw [SimpleGraph.edgeSet_sdiff] at hh
        exact hh.2 (p.mem_edges_toSubgraph.mpr hep)
      have hne_u : u ∉ endpoints L := by
        rw [hTerm,ho]
        simp
      have hne_v : v ∉ endpoints L := by
        rw [hTerm,ho]
        simp
      refine ⟨P::L',R,hRK.trans hKG,he,?_,?_,?_,?_,?_⟩
      · simp only [edgeList_cons,P,L',edgeList_mapLe,List.nodup_append]
        exact ⟨hp.isTrail.edges_nodup,hEdges,List.disjoint_iff_ne.mp hdis⟩
      · simp only [endpoints_cons,P,L',endpoints_mapLe,List.nodup_cons,List.mem_cons]
        exact ⟨not_or.mpr ⟨Ne.symm hvu,hne_u⟩,hne_v,hEnds⟩
      · intro e
        simp only [edgeList_cons,P,L',edgeList_mapLe,List.mem_append]
        constructor
        · intro heH
          by_cases hep : e ∈ p.edges
          · exact Or.inl (Or.inl hep)
          · have heK : e ∈ K.edgeSet := by
              rw [SimpleGraph.edgeSet_sdiff]
              exact ⟨heH,fun hh => hep (p.mem_edges_toSubgraph.mp hh)⟩
            exact (hCover e).mp heK |>.imp Or.inr id
        · rintro ((hep | heL) | heR)
          · exact p.edges_subset_edgeSet hep
          · exact SimpleGraph.edgeSet_mono hKG (hmem e heL)
          · exact SimpleGraph.edgeSet_mono (hRK.trans hKG) heR
      · intro e heL heR
        simp only [edgeList_cons,P,L',edgeList_mapLe,List.mem_append] at heL
        rcases heL with hep | heL
        · have hh := SimpleGraph.edgeSet_mono hRK heR
          rw [SimpleGraph.edgeSet_sdiff] at hh
          exact hh.2 (p.mem_edges_toSubgraph.mpr hep)
        · exact hDis e heL heR
      · intro w
        simp only [endpoints_cons,P,L',endpoints_mapLe,List.mem_cons,hTerm,ho,Finset.mem_erase]
        by_cases hwu : w = u
        · subst w
          simp [hu]
        · by_cases hwv : w = v
          · subst w
            simp [hv]
          · simp [hwu,hwv]
  exact main (oddVertices G).card G rfl

lemma path_count (L : List (Piece G)) (hn : (endpoints L).Nodup)
    (ht : ∀ v, v ∈ endpoints L ↔ v ∈ oddVertices G) :
    2 * L.length = (oddVertices G).card := by
  have he : (endpoints L).toFinset = oddVertices G := by
    ext v
    simpa only [List.mem_toFinset] using ht v
  calc
    2 * L.length = (endpoints L).length := (endpoints_length L).symm
    _ = (endpoints L).toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ = (oddVertices G).card := congrArg Finset.card he

/-- On an all-odd graph, extraction gives exactly n/2 simple paths with unique
endpoints, but can still leave a nonempty even residual. -/
lemma all_odd_extraction (G : SimpleGraph V)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∃ (L : List (Piece G)) (R : SimpleGraph V),
      R ≤ G ∧ (∀ v, Even (Nat.card (R.neighborSet v))) ∧
      (edgeList L).Nodup ∧ (endpoints L).Nodup ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L ∨ e ∈ R.edgeSet) ∧
      (∀ e, e ∈ edgeList L → e ∉ R.edgeSet) ∧
      (∀ v, v ∈ endpoints L) ∧ 2 * L.length = Fintype.card V := by
  obtain ⟨L,R,hRG,he,hed,hen,hcover,hdis,hterm⟩ := exists_extraction G
  have ht : oddVertices G = Finset.univ := by
    ext v
    simp only [mem_oddVertices,Finset.mem_univ,iff_true]
    exact hodd v
  have hc := path_count L hen hterm
  rw [ht,Finset.card_univ] at hc
  exact ⟨L,R,hRG,he,hed,hen,hcover,hdis,
    fun v => (hterm v).mpr (mem_oddVertices.mpr (hodd v)),hc⟩

/-- In a forest the even residual is empty, so extraction is a genuine simple-
path partition with exactly half as many paths as odd vertices. -/
lemma forest_path_partition (G : SimpleGraph V) (hacyc : G.IsAcyclic) :
    ∃ L : List (Piece G),
      (edgeList L).Nodup ∧ (endpoints L).Nodup ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      (∀ v, v ∈ endpoints L ↔ v ∈ oddVertices G) ∧
      2 * L.length = (oddVertices G).card := by
  obtain ⟨L,R,hRG,he,hed,hen,hcover,hdis,hterm⟩ := exists_extraction G
  have hR : R = ⊥ := acyclic_even_eq_bot R (hacyc.anti hRG) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
  refine ⟨L,hed,hen,?_,hterm,path_count L hen hterm⟩
  simpa only [hR,SimpleGraph.edgeSet_bot,Set.mem_empty_iff_false,or_false] using hcover

#print axioms all_odd_extraction
#print axioms forest_path_partition

#print axioms exists_other_odd_reachable
#print axioms path_odd_iff
#print axioms exists_extraction
end Erdos184Work.OddPaths
