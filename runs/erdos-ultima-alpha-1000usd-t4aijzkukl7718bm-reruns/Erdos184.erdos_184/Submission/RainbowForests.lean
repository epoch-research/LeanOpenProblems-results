import Submission.ColoredIncidence

/-!
Independent colored incidence representatives form a rainbow family of forests.
This is a finite independent-transversal construction, not an absorption theorem.
-/
open SimpleGraph Module
open scoped Classical
namespace Erdos184.RainbowForests
open ColoredIncidence

variable {K V I J : Type*} [Field K] [Fintype V] [Fintype I]

noncomputable def selected (c : J → I) (u v : J → V) (i : I) : SimpleGraph V :=
  fromEdgeSet {e | ∃ j, c j = i ∧ e = s(u j, v j)}

lemma selected_adj (c : J → I) (u v : J → V) (i : I) (a b : V) :
    (selected c u v i).Adj a b ↔
      (∃ j, c j = i ∧ s(a,b) = s(u j,v j)) ∧ a ≠ b :=
  fromEdgeSet_adj _

/-- Independence of the colored incidence differences excludes a cycle in
every color, since an edge on a cycle is spanned by the other edges. -/
theorem selected_isAcyclic (c : J → I) (u v : J → V)
    (h : LinearIndependent K (fun j => boundary (K := K) (c j) (u j) (v j)))
    (i : I) : (selected c u v i).IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro a b hab
  obtain ⟨⟨p, hp, hep⟩, hne⟩ := (selected_adj c u v i a b).mp hab
  apply isBridge_iff.mpr
  refine ⟨hab, ?_⟩
  intro hpath
  let w : J → I → V → K := fun j => boundary (K := K) (c j) (u j) (v j)
  let W := Submodule.span K (w '' {p}ᶜ)
  have hW : ∀ x y, (selected c u v i \ fromEdgeSet {s(a,b)}).Adj x y →
      boundary (K := K) i x y ∈ W := by
    intro x y hxy
    obtain ⟨⟨q, hq, heq⟩, hnq⟩ := (selected_adj c u v i x y).mp hxy.1
    have hed : s(x,y) ≠ s(a,b) := by
      intro he
      exact hxy.2 ((fromEdgeSet_adj _).mpr ⟨Set.mem_singleton_iff.mpr he, hnq⟩)
    have hqp : q ≠ p := by
      intro hqp
      subst q
      exact hed (heq.trans hep.symm)
    have hmem : w q ∈ W := Submodule.subset_span ⟨q, by simpa using hqp, rfl⟩
    have hmem' : boundary (K := K) i (u q) (v q) ∈ W := by
      simpa only [w, hq] using hmem
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem'
    · rw [boundary_reverse]
      exact W.neg_mem hmem'
  have hmem := boundary_mem_of_reachable _ i W hW hpath
  have hnot : w p ∉ W := h.notMem_span p
  apply hnot
  have hmem' : boundary (K := K) i (u p) (v p) ∈ W := by
    rcases Sym2.eq_iff.mp hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem
    · rw [boundary_reverse] at hmem
      exact (W.neg_mem_iff).mp hmem
  simpa only [w, hp] using hmem'

lemma selected_le (c : J → I) (u v : J → V) (G : SimpleGraph V)
    (h : ∀ j, G.Adj (u j) (v j)) (i : I) : selected c u v i ≤ G := by
  intro a b hab
  obtain ⟨⟨j, _, hej⟩, _⟩ := (selected_adj c u v i a b).mp hab
  have he : s(u j,v j) ∈ G.edgeSet := h j
  exact (mem_edgeSet G).mp (hej.symm ▸ he)

lemma selected_contains (c : J → I) (u v : J → V)
    (h : ∀ j, u j ≠ v j) (j : J) :
    (selected c u v (c j)).Adj (u j) (v j) :=
  (selected_adj c u v (c j) (u j) (v j)).mpr ⟨⟨j, rfl, rfl⟩, h j⟩

/-- Rado's rank inequalities yield a representative edge from each family
member, colored so that each color is acyclic. -/
theorem exists_rainbow_forests [Fintype J] (G : J → SimpleGraph V)
    (h : ∀ s : Finset J, s.card ≤ Fintype.card I *
      (Fintype.card V - Fintype.card (s.sup G).ConnectedComponent)) :
    ∃ (c : J → I) (u v : J → V), (∀ j, (G j).Adj (u j) (v j)) ∧
      ∀ i, (selected c u v i).IsAcyclic := by
  obtain ⟨c, u, v, ha, hi⟩ := exists_independent_edges (I := I) G h
  exact ⟨c, u, v, ha, selected_isAcyclic c u v hi⟩

lemma selected_edgeFinset [Fintype J] (c : J → I) (u v : J → V)
    (h : ∀ j, u j ≠ v j) (i : I) :
    (selected c u v i).edgeFinset =
      (Finset.univ.filter (fun j => c j = i)).image (fun j => s(u j,v j)) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_edgeFinset]
    change (selected c u v i).Adj a b ↔ _
    constructor
    · intro hab
      obtain ⟨⟨j, hj, he⟩, _⟩ := (selected_adj c u v i a b).mp hab
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, he.symm⟩
    · intro he
      obtain ⟨j, hj, hej⟩ := Finset.mem_image.mp he
      apply (selected_adj c u v i a b).mpr
      refine ⟨⟨j, (Finset.mem_filter.mp hj).2, hej.symm⟩, ?_⟩
      rcases Sym2.eq_iff.mp hej.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h j
      · exact (h j).symm

lemma sum_selected_card [Fintype J] (c : J → I) (u v : J → V)
    (h : ∀ j, u j ≠ v j) (hi : Function.Injective (fun j => s(u j,v j))) :
    ∑ i, (selected c u v i).edgeFinset.card = Fintype.card J := by
  simp_rw [selected_edgeFinset c u v h, Finset.card_image_of_injective _ hi]
  simpa using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ c

lemma acyclic_card_le [Nonempty V] (G : SimpleGraph V) (h : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  obtain ⟨T, hGT, hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show G ≤ (⊤ : SimpleGraph V) from le_top) h
  have ht := (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hm
  have hc := ht.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

lemma tree_of_acyclic_card [Nonempty V] (G : SimpleGraph V) (h : G.IsAcyclic)
    (hc : G.edgeFinset.card = Fintype.card V - 1) : G.IsTree := by
  obtain ⟨T, hGT, hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show G ≤ (⊤ : SimpleGraph V) from le_top) h
  have ht := (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hm
  have hct := ht.card_edgeFinset
  have he : G.edgeFinset = T.edgeFinset := Finset.eq_of_subset_of_card_le
    (SimpleGraph.edgeFinset_mono hGT) (by omega)
  have hge : G = T := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simpa only [← mem_edgeFinset, he]
  exact hge.symm ▸ ht

/-- Saturating the C(n−1) capacity turns every extracted forest into a
spanning tree. Edge representatives are assumed globally distinct. -/
theorem selected_isTree_of_card [Fintype J] [Nonempty V]
    (c : J → I) (u v : J → V) (h : ∀ j, u j ≠ v j)
    (hi : Function.Injective (fun j => s(u j,v j)))
    (hf : ∀ i, (selected c u v i).IsAcyclic)
    (hc : Fintype.card J = Fintype.card I * (Fintype.card V - 1)) :
    ∀ i, (selected c u v i).IsTree := by
  have hle : ∀ i ∈ (Finset.univ : Finset I),
      (selected c u v i).edgeFinset.card ≤ Fintype.card V - 1 :=
    fun i _ => acyclic_card_le _ (hf i)
  have hsum : (∑ i, (selected c u v i).edgeFinset.card) =
      ∑ _ : I, (Fintype.card V - 1) := by
    rw [sum_selected_card c u v h hi, hc]
    simp [mul_comm]
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  intro i
  exact tree_of_acyclic_card _ (hf i) (he i (Finset.mem_univ i))

end Erdos184.RainbowForests
