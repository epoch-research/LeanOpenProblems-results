import Submission.SubdivisionCollapse
import Submission.CountCritical

/-! Genuine edge subdivision preserves minimum cycle count and fixed-count
criticality. The result does not suppress a vertex onto an existing edge. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.EdgeSubdivision
open CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma number_graph (G : SimpleGraph V) (R : Set (Sym2 V))
    (he : ∀ v, Even (G.degree v)) : cycleNumber (graph G R) = cycleNumber G := by
  obtain ⟨D,hc,hd,hsize⟩ := minimum_exists G he
  obtain ⟨E,hcE,hdE,hsizeE,_⟩ := transport_decomposition R D hc hd
  have hle := number_le (graph G R) E hcE hdE
  rw [hsizeE,hsize] at hle
  obtain ⟨F,hcF,hdF,hsizeF⟩ := minimum_exists (graph G R) (graph_even G R he)
  obtain ⟨K,hcK,hdK,hsizeK⟩ := collapse_decomposition F hcF hdF
  have hge := number_le G K hcK hdK
  rw [hsizeK,hsizeF] at hge
  exact Nat.le_antisymm hle hge

omit [Fintype V] in
/-- An edge restriction with its isolated vertices omitted from the subgraph
vertex set. This allows the new-vertex degree test to be used exactly. -/
def supportSubgraph {W : Type*} {G A : SimpleGraph W} (h : A ≤ G) : G.Subgraph where
  verts := A.support
  Adj := A.Adj
  symm := A.symm
  adj_sub := fun {_ _} huv => h huv
  edge_vert := fun {_ v} huv => ⟨v,huv⟩

lemma exists_even_base (G : SimpleGraph V) (R : Set (Sym2 V))
    (A : SimpleGraph (V ⊕ R)) (hAG : A ≤ graph G R)
    (heA : ∀ x, Even (A.degree x)) :
    ∃ B : SimpleGraph V, B ≤ G ∧ (∀ v, Even (B.degree v)) ∧ graph B R = A := by
  let H := supportSubgraph hAG
  have hn (e : R) (he : Sum.inr e ∈ H.verts) : H.degree (.inr e) = 2 := by
    have hs : Sum.inr e ∈ A.support := he
    have hp := (A.degree_pos_iff_mem_support (.inr e)).mpr hs
    obtain ⟨x,hx⟩ := hs
    have hge : e.val ∈ G.edgeSet := by
      cases x with
      | inl x => exact (hAG hx).1
      | inr d => exact (hAG hx).elim
    have hb := SimpleGraph.degree_le_of_le (v := Sum.inr e) hAG
    have hg := degree_new G R e hge
    have ha := heA (.inr e)
    have hH : H.spanningCoe = A := rfl
    rw [← Subgraph.degree_spanningCoe]
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp hb hg ha ⊢
    rw [hH]
    obtain ⟨k,hk⟩ := ha
    omega
  have hl := lift_collapse H hn
  have hspan : graph (collapse H).spanningCoe R = A := congrArg Subgraph.spanningCoe hl
  refine ⟨(collapse H).spanningCoe,(collapse H).spanningCoe_le,?_,hspan⟩
  apply even_of_graph_even
  intro x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  rw [hspan]
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heA x

lemma critical_graph_iff (G : SimpleGraph V) (R : Set (Sym2 V)) (k : ℕ) :
    IsCountCritical k (graph G R) ↔ IsCountCritical k G := by
  constructor
  · intro h
    have heG := even_of_graph_even G R h.1
    refine ⟨heG,?_,?_⟩
    · rw [← number_graph G R heG]
      exact h.2.1
    · intro A hAG hne heA
      have hne' : graph A R ≠ graph G R := fun hh => hne (graph_injective R hh)
      have he' : ∀ x, Even ((graph A R).degree x) := graph_even A R heA
      have hh := h.2.2 (graph A R) (graph_mono R hAG) hne' (by
        intro x
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he' x)
      rwa [number_graph A R heA] at hh
  · intro h
    refine ⟨graph_even G R h.1,?_,?_⟩
    · rw [number_graph G R h.1]
      exact h.2.1
    · intro A hAG hne heA
      obtain ⟨B,hBG,heB,hBA⟩ := exists_even_base G R A hAG heA
      have hneB : B ≠ G := by
        intro hh
        exact hne (hBA.symm.trans (congrArg (fun X => graph X R) hh))
      have hb := h.2.2 B hBG hneB heB
      rw [← hBA,number_graph B R heB]
      exact hb

lemma invariant_graph_iff (G : SimpleGraph V) (R : Set (Sym2 V)) :
    InvariantPartitions.HasInvariantCount (graph G R) ↔
      InvariantPartitions.HasInvariantCount G := by
  constructor
  · intro h D E hcD hdD hcE hdE
    obtain ⟨D',hcD',hdD',hsD,_⟩ := transport_decomposition R D hcD hdD
    obtain ⟨E',hcE',hdE',hsE,_⟩ := transport_decomposition R E hcE hdE
    have hh := h D' E' hcD' hdD' hcE' hdE'
    simpa only [hsD,hsE] using hh
  · intro h D E hcD hdD hcE hdE
    obtain ⟨D',hcD',hdD',hsD⟩ := collapse_decomposition D hcD hdD
    obtain ⟨E',hcE',hdE',hsE⟩ := collapse_decomposition E hcE hdE
    have hh := h D' E' hcD' hdD' hcE' hdE'
    simpa only [hsD,hsE] using hh

end Erdos184.EdgeSubdivision
