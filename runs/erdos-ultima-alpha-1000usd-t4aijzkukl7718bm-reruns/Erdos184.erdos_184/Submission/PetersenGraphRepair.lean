import Submission.PetersenFloorRemainder
import Submission.Cycles

/-! Graph-level noncompletion of the fixed floor family. Not a disproof of
Erdős 184: the uniform multicover may instead be rerounded globally. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.PetersenGraphRepair
open PetersenFloorRemainder
open DoubledPetersenCertificate (incident EvenVector NonzeroVector)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

abbrev Core := Fin 10
abbrev BaseEdge := Fin 15

def liftV (v : Core) : V := ⟨v.val,by omega⟩
def liftE (e : BaseEdge) : E := ⟨e.val,by omega⟩
def baseEdge (e : BaseEdge) : Sym2 V := s((ends (liftE e)).1,(ends (liftE e)).2)
def neigh : Core → Fin 3 → V := ![![1,4,5],![0,2,6],![1,3,7],![2,4,8],![0,3,9],![0,7,8],![1,8,9],![2,5,9],![3,5,6],![4,6,7]]

lemma neigh_injective (v : Core) : Function.Injective (neigh v) := by revert v; decide
lemma neigh_edge (v : Core) (i : Fin 3) : s(liftV v,neigh v i) = baseEdge (incident v i) := by
  revert v i; decide
lemma neigh_complete (v : Core) (w : V) :
    G.Adj (liftV v) w ↔ w = 10 ∨ ∃ i, neigh v i = w := by revert v w; decide
lemma edge_cases (u v : V) (h : G.Adj u v) :
    u = 10 ∨ v = 10 ∨ ∃ e : BaseEdge, s(u,v) = baseEdge e := by revert u v; decide
lemma apex_edge (v : Core) :
    s(liftV v,(10 : V)) = s((ends ⟨15+v.val,by omega⟩).1,(ends ⟨15+v.val,by omega⟩).2) := by
  revert v; decide
lemma remainder_base (e : BaseEdge) : remainder (liftE e) = PetersenDemandHole.demand e := by
  revert e; decide
lemma remainder_apex (v : Core) : remainder ⟨15+v.val,by omega⟩ = 0 := by revert v; decide

noncomputable def vec (A : SimpleGraph V) (e : BaseEdge) : ℕ :=
  if baseEdge e ∈ A.edgeSet then 1 else 0
lemma vec_binary (A : SimpleGraph V) (e : BaseEdge) : vec A e < 2 := by
  unfold vec; split_ifs <;> omega

lemma degree_core (A : SimpleGraph V) (hAG : A ≤ G)
    (hz : ∀ v, ¬ A.Adj v 10) (v : Core) :
    A.degree (liftV v) = vec A (incident v 0) + vec A (incident v 1) + vec A (incident v 2) := by
  let S : Finset (Fin 3) := Finset.univ.filter (fun i => A.Adj (liftV v) (neigh v i))
  have hN : A.neighborFinset (liftV v) = S.image (neigh v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image]
    constructor
    · intro hw
      rcases (neigh_complete v w).mp (hAG hw) with rfl | ⟨i,rfl⟩
      · exact (hz _ hw).elim
      · exact ⟨i,by simp [S,hw],rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact (Finset.mem_filter.mp hi).2
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hN,
    Finset.card_image_of_injective S (neigh_injective v)]
  have hs : S.card = ∑ i : Fin 3, vec A (incident v i) := by
    have hb : (∑ i : Fin 3, if A.Adj (liftV v) (neigh v i) then 1 else 0) = S.card := by
      simp [S]
    rw [← hb]
    apply Finset.sum_congr rfl
    intro i _
    unfold vec
    rw [← neigh_edge v i]
    rfl
  rw [hs,Fin.sum_univ_three]

lemma vec_even (A : SimpleGraph V) (hAG : A ≤ G)
    (hz : ∀ v, ¬ A.Adj v 10) (he : ∀ v, Even (A.degree v)) : EvenVector (vec A) := by
  intro v
  have hh := he (liftV v)
  rw [degree_core A hAG hz v] at hh
  exact Nat.even_iff.mp hh

lemma vec_nonzero (A : SimpleGraph V) (hAG : A ≤ G)
    (hz : ∀ v, ¬ A.Adj v 10) (hn : A ≠ ⊥) : NonzeroVector (vec A) := by
  obtain ⟨u,v,h⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hn
  rcases edge_cases u v (hAG h) with rfl | rfl | ⟨e,he⟩
  · exact (hz _ h.symm).elim
  · exact (hz _ h).elim
  · refine ⟨e,?_⟩
    have hm : baseEdge e ∈ A.edgeSet := he ▸ h
    simp [vec,hm]

/-- No finite family of nonempty even binary subgraphs can realize the
remainder. This is stronger than excluding a family of simple cycles. -/
lemma no_even_graph_repair {J : Type*} [Fintype J]
    (A : J → SimpleGraph V) (hAG : ∀ j, A j ≤ G)
    (he : ∀ j v, Even ((A j).degree v)) (hn : ∀ j, A j ≠ ⊥) :
    ¬ (∀ e : E, (∑ j, if s((ends e).1,(ends e).2) ∈ (A j).edgeSet then 1 else 0) = remainder e) := by
  intro hc
  have hz (j : J) (v : V) : ¬ (A j).Adj v 10 := by
    intro hv
    by_cases hv10 : v = 10
    · subst v; exact (A j).loopless _ hv
    · have hvlt : v.val < 10 := by
        have hvn : v.val ≠ 10 := fun h => hv10 (Fin.ext h)
        omega
      let w : Core := ⟨v.val,hvlt⟩
      have hw : liftV w = v := rfl
      have hh := hc ⟨15+w.val,by omega⟩
      rw [remainder_apex] at hh
      have hzero := (Finset.sum_eq_zero_iff.mp hh) j (Finset.mem_univ _)
      rw [← apex_edge w,hw] at hzero
      simp only [SimpleGraph.mem_edgeSet,if_pos hv] at hzero
      omega
  apply PetersenDemandHole.no_binary_even_cover (fun j => vec (A j))
    (fun j => vec_even _ (hAG j) (hz j) (he j))
    (fun j => vec_binary _) (fun j => vec_nonzero _ (hAG j) (hz j) (hn j))
  intro e
  have hh := hc (liftE e)
  rw [remainder_base] at hh
  exact hh

/-- Arbitrary ordinary cycle pieces, with repetitions allowed by the indexing
function, cannot cover the prescribed remainder. -/
lemma no_cycle_repair {J : Type*} [Fintype J] (H : J → G.Subgraph)
    (hcy : ∀ j, (H j).coe.Connected ∧ (H j).coe.IsRegularOfDegree 2) :
    ¬ (∀ e : E, (∑ j, if s((ends e).1,(ends e).2) ∈ (H j).edgeSet then 1 else 0) = remainder e) := by
  apply no_even_graph_repair (fun j => (H j).spanningCoe) (fun j => (H j).spanningCoe_le)
  · intro j v
    rw [Subgraph.degree_spanningCoe]
    by_cases hv : v ∈ (H j).verts
    · have hh := (hcy j).2 ⟨v,hv⟩
      rw [Subgraph.coe_degree] at hh
      simp only [Subgraph.degree,← Nat.card_eq_fintype_card] at hh ⊢
      rw [hh]
      decide
    · rw [Subgraph.degree_of_notMem_verts hv]
      decide
  · intro j hbot
    obtain ⟨e,he⟩ := cycle_edgeSet_nonempty (H j) (hcy j).1 (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hcy j).2 v)
    have hm : e ∈ (H j).spanningCoe.edgeSet := he
    simp [hbot] at hm

/-- A genuine graph-level obstruction to fixing all independently rounded
cycles and then completing the half-cover. The input is the uniform four-cover
proved in PetersenFloorRemainder.four_cover; its fifteen distinct cycle types
and multiplicities are fixed there. No number of further ordinary cycles can
complete the fixed floor family to uniform coverage two. -/
lemma no_floor_completion {J : Type*} [Fintype J] (H : J → G.Subgraph)
    (hcy : ∀ j, (H j).coe.Connected ∧ (H j).coe.IsRegularOfDegree 2) :
    ¬ (∀ e : E,
      (∑ i : I, PetersenFloorRemainder.multiplicity i / 2 * col i e) +
      (∑ j, if s((ends e).1,(ends e).2) ∈ (H j).edgeSet then 1 else 0) = 2) := by
  intro hc
  apply no_cycle_repair H hcy
  intro e
  have h₁ := hc e
  have h₂ := floor_remainder e
  omega

end Erdos184.PetersenGraphRepair
