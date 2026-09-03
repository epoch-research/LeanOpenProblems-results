import Submission.ThreeHubMinimalLeaves

/-! A strictly increasing Best-singleton potential cannot justify every
cycle/core descent. The counterexample below concerns that auxiliary rule,
not the original cycle decomposition conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.StrictSingletonDescent
open Critical EdgeHull SingletonExchange ThreeHubMinimalLeaves
set_option maxHeartbeats 1400000
variable {V : Type*} [Fintype V]

noncomputable def bestForest (G : SimpleGraph V) : SimpleGraph V :=
  Classical.choose (exists_best G)
lemma bestForest_best (G : SimpleGraph V) : Best G (bestForest G) :=
  Classical.choose_spec (exists_best G)
noncomputable def singles (G : SimpleGraph V) : ℕ := Nat.card (bestForest G).edgeSet

lemma singles_eq {G F : SimpleGraph V} (h : Best G F) :
    singles G = Nat.card F.edgeSet := by
  exact Nat.le_antisymm ((bestForest_best G).2 F h.1)
    (h.2 (bestForest G) (bestForest_best G).1)

lemma singles_le (G : SimpleGraph V) : singles G ≤ Fintype.card V - 1 := by
  have h := CycleCertificates.acyclic_edge_count_pred (bestForest G)
    (bestForest_best G).1.acyclic
  simpa only [singles,SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h

/-- This hypothetical strict-increase rule is stronger than mere monotonicity.
It even allows an arbitrary smaller core, not just deletion of a chosen cycle. -/
def Property (H : SimpleGraph V) : Prop :=
  ∀ G ≤ H, Minimal G → G.Connected → ¬ G.IsAcyclic →
    ∃ R, R ≤ G ∧ Minimal R ∧ R.Connected ∧ number R + 1 = number G ∧
      singles G < singles R

lemma potential_bound {H : SimpleGraph V} (h : Property H)
    (G : SimpleGraph V) (hG : G ≤ H) (hm : Minimal G) (hc : G.Connected) :
    number G + singles G ≤ 2 * (Fintype.card V - 1) := by
  have main : ∀ k, ∀ G : SimpleGraph V, number G = k → G ≤ H →
      Minimal G → G.Connected → number G + singles G ≤ 2 * (Fintype.card V - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro G hk hG hm hc
      by_cases ha : G.IsAcyclic
      · have hn := (number_le_edges G).trans
          (CycleCertificates.acyclic_edge_count_pred G ha)
        have hs := singles_le G
        omega
      · obtain ⟨R,hRG,hmR,hcR,hn,hs⟩ := h G hG hm hc ha
        have hr := ih (number R) (by omega) R rfl (hRG.trans hG) hmR hcR
        omega
  exact main (number G) G rfl hG hm hc

abbrev Vertex := Fin 3 ⊕ Fin 19
def host : SimpleGraph Vertex := completeBipartiteGraph (Fin 3) (Fin 19)

lemma host_connected : host.Connected where
  preconnected := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        exact (show host.Adj (.inl a) (.inr 0) by simp [host,completeBipartiteGraph]).reachable.trans
          (show host.Adj (.inr 0) (.inl b) by simp [host,completeBipartiteGraph]).reachable
      | inr b => exact (show host.Adj (.inl a) (.inr b) by simp [host,completeBipartiteGraph]).reachable
    | inr a =>
      cases y with
      | inl b => exact (show host.Adj (.inr a) (.inl b) by simp [host,completeBipartiteGraph]).reachable
      | inr b =>
        exact (show host.Adj (.inr a) (.inl 0) by simp [host,completeBipartiteGraph]).reachable.trans
          (show host.Adj (.inl 0) (.inr b) by simp [host,completeBipartiteGraph]).reachable
  nonempty := inferInstance

lemma host_degree_left (a : Fin 3) : host.degree (.inl a) = 19 := by
  let f : Fin 19 → host.neighborSet (.inl a) := fun b => ⟨.inr b,by simp [host,completeBipartiteGraph]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Sum.inr.inj (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      cases x with
      | inl b => simp [host,completeBipartiteGraph] at hx
      | inr b => exact ⟨b,rfl⟩
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  simpa only [Nat.card_fin] using h.symm

lemma host_degree_right (b : Fin 19) : host.degree (.inr b) = 3 := by
  have h := degree_right_full (A := Fin 3) b
  simpa only [host,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card,Nat.card_fin] using h

lemma host_number_lower : 26 ≤ number host := by
  obtain ⟨D,hD,hdec,hn⟩ := exists_minimum host
  let A : Finset Vertex := Finset.univ.image Sum.inl
  let B : Finset Vertex := Finset.univ.image Sum.inr
  have hA : A.card = 3 := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  have hB : B.card = 19 := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    simp
  have hi : ∀ x ∈ B, ∀ y ∈ B, ¬ host.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    simpa [host,completeBipartiteGraph] using hxy
  have ho : ∀ x ∈ B, Odd (host.degree x) := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    rw [host_degree_right]
    decide
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hy
    cases hb
  have hs : (∑ v ∈ A, host.degree v) = 57 := by
    calc
      _ = ∑ _v ∈ A, 19 := Finset.sum_congr rfl (by
        intro v hv
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
        exact host_degree_left a)
      _ = _ := by simp [hA]
  have hl := ParityDegreeLower.independent_odd_degree_bound D hD hdec A B B
    (by omega) hdis hi ho ho
  rw [hs,hA,hB,hn] at hl
  omega

/-- A globally minimal connected graph whose number plus its minimum optimal
singleton count exceeds the bound that strict singleton descent would impose. -/
lemma exists_excess_core : ∃ G : SimpleGraph Vertex, G ≤ host ∧ Minimal G ∧
    G.Connected ∧ 42 < number G + singles G := by
  obtain ⟨G,hG,hm,hn⟩ := exists_minimal_maximizer_all host
  have hc := maximizer_connected hG hn host_connected
  have hk : 26 ≤ number G := by
    rw [hn]
    exact host_number_lower.trans (number_le_value host)
  have hs := optimal_singleton_lower hm hG hc (bestForest_best G).1
  change Fintype.card (Fin 19) ≤ singles G + 2 at hs
  simp only [Fintype.card_fin] at hs
  exact ⟨G,hG,hm,hc,by omega⟩

/-- Strict singleton growth is not a valid universal core-reduction rule.
This theorem is NOT a negation of the original Erdős184 conjecture. -/
lemma not_property : ¬ Property host := by
  intro h
  obtain ⟨G,hG,hm,hc,he⟩ := exists_excess_core
  have hb := potential_bound h G hG hm hc
  norm_num [Vertex] at hb
  omega

end Erdos184Work.StrictSingletonDescent
#print axioms Erdos184Work.StrictSingletonDescent.host_number_lower
#print axioms Erdos184Work.StrictSingletonDescent.exists_excess_core
#print axioms Erdos184Work.StrictSingletonDescent.not_property
