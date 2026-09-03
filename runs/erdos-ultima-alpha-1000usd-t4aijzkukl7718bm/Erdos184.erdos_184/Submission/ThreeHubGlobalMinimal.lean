import Submission.ThreeHubCompleteNumber

/-! A structural proof that K_(3,3q+1) is globally minimal for q >= 2.
This concerns an auxiliary linear-size family, not a disproof of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeHubGlobalMinimal
open Critical EdgeHull ThreeHubFullStructure ThreeHubCompleteNumber
set_option maxHeartbeats 1600000
variable {B : Type*} [Fintype B] {G : SimpleGraph (Fin 3 ⊕ B)}

def fullGraph (G : SimpleGraph (Fin 3 ⊕ B)) : SimpleGraph (Fin 3 ⊕ B) where
  Adj
    | .inl _, .inr b => Full G b
    | .inr b, .inl _ => Full G b
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp

lemma fullGraph_le : fullGraph G ≤ G := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl c => exact h.elim
    | inr b => exact (h a).symm
  | inr b =>
    cases y with
    | inl a => exact h a
    | inr c => exact h.elim

noncomputable def fullEmbedding (G : SimpleGraph (Fin 3 ⊕ B)) :
    Fin 3 ⊕ {b : B // Full G b} ↪ Fin 3 ⊕ B :=
  ⟨Sum.map id Subtype.val, by
    intro x y h
    cases x <;> cases y <;> simp_all
    exact Subtype.ext h⟩

lemma fullGraph_eq_map : fullGraph G =
    (completeBipartiteGraph (Fin 3) {b : B // Full G b}).map (fullEmbedding G) := by
  ext x y
  cases x <;> cases y <;>
    simp [fullGraph, fullEmbedding, SimpleGraph.map_adj, completeBipartiteGraph, Sum.exists]

lemma fullGraph_number_le : number (fullGraph G) ≤
    number (completeBipartiteGraph (Fin 3) {b : B // Full G b}) := by
  rw [fullGraph_eq_map]
  exact number_map_le _ _

lemma fullGraph_card : Nat.card (fullGraph G).edgeSet =
    3 * Fintype.card {b : B // Full G b} := by
  have h := SimpleGraph.card_edgeFinset_map (fullEmbedding G)
    (completeBipartiteGraph (Fin 3) {b : B // Full G b})
  have hc := BipartiteLower.complete_edge_card (A := Fin 3) (B := {b : B // Full G b})
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h hc
  rw [← fullGraph_eq_map, hc] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

lemma remainder_card_le (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) {b₀ : B} (hfull : Full G b₀) :
    Nat.card (G \ fullGraph G).edgeSet ≤ Fintype.card {b : B // ¬ Full G b} := by
  let R := G \ fullGraph G
  have hdeg (b : B) : R.degree (.inr b) ≤ if Full G b then 0 else 1 := by
    by_cases hb : Full G b
    · rw [if_pos hb]
      have hz : R.degree (.inr b) = 0 := by
        apply (SimpleGraph.degree_eq_zero_iff_notMem_support R (.inr b)).mpr
        rintro ⟨x,hx⟩
        cases x with
        | inl a => exact hx.2 hb
        | inr c => simpa [completeBipartiteGraph] using hG hx.1
      exact hz.le
    · rw [if_neg hb]
      exact (SimpleGraph.degree_le_of_le (v := .inr b) (show R ≤ G from sdiff_le)).trans
        (nonfull_degree_le_one hm hG hfull hb)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hdeg b)
  have he := (BipartiteLower.bipartite_edge_sums R (sdiff_le.trans hG)).2
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card] at hs he
  rw [← he] at hs
  simpa only [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    smul_eq_mul, mul_one, Fintype.card_subtype] using hs

lemma acyclic_of_no_full (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) (hf : ∀ b, ¬ Full G b) :
    G.IsAcyclic := by
  have hdeg (b : B) : G.degree (.inr b) ≤ 2 := by
    have hne := mt (degree_eq_three_iff_full hG b).mp (hf b)
    have hu := SimpleGraph.degree_le_of_le (v := .inr b) hG
    have hh := BipartiteLower.complete_degree_right (A := Fin 3) b
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_fin] at hne hu hh ⊢
    omega
  intro x p hp
  have hright (b : B) (hb : .inr b ∈ p.support) : False := by
    have hh := hm.cycle_vertex_degree hp hb
    have hd := hdeg b
    omega
  cases x with
  | inr b => exact hright b p.start_mem_support
  | inl a =>
    have hs := hG (p.adj_snd hp.not_nil)
    cases he : p.snd with
    | inl c => simp [he,completeBipartiteGraph] at hs
    | inr b =>
      apply hright b
      rw [← he]
      simpa using p.getVert_mem_support 1

lemma full_complement_card : Fintype.card {b : B // Full G b} +
    Fintype.card {b : B // ¬ Full G b} = Fintype.card B := by
  simpa only [Fintype.card_subtype, Finset.card_univ] using
    Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset B)) (Full G)

/-- All right vertices not belonging to the complete three-hub part are
leaves or isolated vertices, unless the whole graph is a forest. -/
lemma minimal_upper (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) :
    number G ≤ Fintype.card B + max 2 ((Fintype.card {b : B // Full G b} + 2)/3) := by
  by_cases hf : ∃ b, Full G b
  · obtain ⟨b,hb⟩ := hf
    have hsplit := number_sdiff_add_le G (fullGraph G) fullGraph_le
    have hrest := number_le_edges (G \ fullGraph G)
    have hrc := remainder_card_le hm hG hb
    have hcc := full_complement_card (G := G)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hrest
    by_cases ha : 2 ≤ Fintype.card {b : B // Full G b}
    · have hcore := fullGraph_number_le (G := G)
      have hc := upper_type {b : B // Full G b} ha
      omega
    · have hcore := number_le_edges (fullGraph G)
      have hc := fullGraph_card (G := G)
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcore
      omega
  · have ha := acyclic_of_no_full hm hG (by simpa only [not_exists] using hf)
    have he := acyclic_card_edges_lt G ha
    have hn := number_le_edges G
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_sum, Nat.card_fin] at he hn ⊢
    omega

lemma full_card_lt_of_ne (hG : G ≤ completeBipartiteGraph (Fin 3) B)
    (hne : G ≠ completeBipartiteGraph (Fin 3) B) :
    Fintype.card {b : B // Full G b} < Fintype.card B := by
  have hn : ∃ b, ¬ Full G b := by
    by_contra! hf
    apply hne
    apply le_antisymm hG
    intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl c => simpa [completeBipartiteGraph] using hxy
      | inr b => exact (hf b a).symm
    | inr b =>
      cases y with
      | inl a => exact hf b a
      | inr c => simpa [completeBipartiteGraph] using hxy
  obtain ⟨b,hb⟩ := hn
  exact Fintype.card_subtype_lt hb

lemma proper_upper (q : ℕ) (hq : 2 ≤ q)
    (H : SimpleGraph (Fin 3 ⊕ Fin (3*q+1))) (hH : H ≤ graph (3*q+1))
    (hne : H ≠ graph (3*q+1)) : number H ≤ 4*q+1 := by
  obtain ⟨R,hRH,hm,hr⟩ := exists_minimal_maximizer_all H
  have hRG := hRH.trans hH
  have hnR : R ≠ graph (3*q+1) := by
    intro he
    apply hne
    exact le_antisymm hH (he ▸ hRH)
  have ha := full_card_lt_of_ne hRG hnR
  have hb := minimal_upper hm hRG
  have hh := number_le_value H
  simp only [Fintype.card_fin] at ha hb
  omega

lemma complete_minimal (q : ℕ) (hq : 2 ≤ q) : Minimal (graph (3*q+1)) := by
  intro H hH hne
  have hh := proper_upper q hq H hH hne
  have hg := exact_number (3*q+1) (by omega)
  omega

end Erdos184Work.ThreeHubGlobalMinimal
#print axioms Erdos184Work.ThreeHubGlobalMinimal.minimal_upper
#print axioms Erdos184Work.ThreeHubGlobalMinimal.complete_minimal
