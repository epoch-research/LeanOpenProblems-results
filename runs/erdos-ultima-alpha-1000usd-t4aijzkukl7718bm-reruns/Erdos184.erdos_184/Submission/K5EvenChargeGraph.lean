import Submission.K5EvenCharge

/-! Graph-level interpretation of the explicit K5 signed-charge obstruction.
This does not assume invariant cycle-partition count and does not settle
Erdos 184. -/
open SimpleGraph
open scoped BigOperators
namespace K5EvenCharge
def edge (e : E) : Sym2 V := s((endpoints e).1, (endpoints e).2)
lemma edge_injective : Function.Injective edge := by decide
lemma edge_nondiag : ∀ e, ¬ (edge e).IsDiag := by decide
lemma mem_edge (e : E) (v : V) : v ∈ edge e ↔ incident e v := by
  revert e v; decide
def graph (s : Finset E) : SimpleGraph V := fromEdgeSet (s.image edge : Set (Sym2 V))
instance (s : Finset E) : DecidableRel (graph s).Adj := by unfold graph; infer_instance
lemma graph_edgeFinset (s : Finset E) : (graph s).edgeFinset = s.image edge := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, graph, edgeSet_fromEdgeSet, Set.mem_diff,
    Finset.mem_coe, Sym2.mem_diagSet_iff_isDiag]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact edge_nondiag i
lemma graph_degree (s : Finset E) (v : V) :
    (graph s).degree v = (s.filter (fun e => incident e v)).card := by
  rw [← card_incidenceFinset_eq_degree]
  have hh : (graph s).incidenceFinset v = (s.filter (fun e => incident e v)).image edge := by
    ext e
    rw [incidenceFinset_eq_filter, graph_edgeFinset]
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hv⟩
      exact ⟨i, ⟨hi, (mem_edge i v).mp hv⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hv⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (mem_edge i v).mpr hv⟩
  rw [hh, Finset.card_image_of_injective _ edge_injective]
lemma graph_univ : graph Finset.univ = (⊤ : SimpleGraph V) := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

lemma even_graph_iff (s : Finset E) :
    EvenEdges s ↔ ∀ v, Even ((graph s).degree v) := by
  simp only [EvenEdges, graph_degree, Nat.even_iff]

noncomputable def code (H : SimpleGraph V) : Finset E :=
  open scoped Classical in Finset.univ.filter (fun e => edge e ∈ H.edgeSet)

lemma code_graph (s : Finset E) : code (graph s) = s := by
  classical
  ext e
  simp only [code, Finset.mem_filter, Finset.mem_univ, true_and,
    ← mem_edgeFinset, graph_edgeFinset, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, he⟩
    exact edge_injective he ▸ hi
  · intro he
    exact ⟨e, he, rfl⟩

lemma graph_code (H : SimpleGraph V) : graph (code H) = H := by
  classical
  apply edgeSet_injective
  ext e
  rw [← mem_edgeFinset, graph_edgeFinset]
  simp only [Finset.mem_image, code, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro he
    have ht : e ∈ (graph Finset.univ).edgeFinset := by
      rw [mem_edgeFinset, graph_univ]
      exact edgeSet_mono (show H ≤ ⊤ from le_top) he
    rw [graph_edgeFinset] at ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨i, he, rfl⟩

lemma code_bot : code ⊥ = ∅ := by
  classical
  simp [code]

lemma code_sup (H K : SimpleGraph V) : code (H ⊔ K) = code H ∪ code K := by
  classical
  ext e
  simp [code, edgeSet_sup]

lemma code_even {H : SimpleGraph V} (he : ∀ v, Even (H.degree v)) :
    EvenEdges (code H) := by
  apply (even_graph_iff _).mpr
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, graph_code] using he

lemma code_disjoint {H K : SimpleGraph V} (hd : Disjoint H.edgeSet K.edgeSet) :
    Disjoint (code H) (code K) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Set.disjoint_left.mp hd (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

noncomputable def graphCharge (H : SimpleGraph V) : ℝ := charge (code H)

lemma graphCharge_bot : graphCharge ⊥ = 0 := by
  simp [graphCharge, code_bot, charge_empty]

lemma graphCharge_add {H K : SimpleGraph V}
    (heH : ∀ v, Even (H.degree v)) (heK : ∀ v, Even (K.degree v))
    (hd : Disjoint H.edgeSet K.edgeSet) :
    graphCharge (H ⊔ K) = graphCharge H + graphCharge K := by
  unfold graphCharge
  rw [code_sup, charge_add (code_even heH) (code_even heK) (code_disjoint hd), Int.cast_add]

/-- No signed real weight on K5's edges represents this charge on all even
spanning edge subgraphs. All graphs on V are automatically subgraphs of K5. -/
theorem graphCharge_not_edge_sum :
    ¬ ∃ w : Sym2 V → ℝ, ∀ H : SimpleGraph V, (∀ v, Even (H.degree v)) →
      graphCharge H = ∑ e ∈ H.edgeFinset, w e := by
  classical
  rintro ⟨w, hw⟩
  apply not_edge_weight_sum
  refine ⟨fun i => w (edge i), fun s hs => ?_⟩
  have hh := hw (graph s) (by
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (even_graph_iff s).mp hs)
  rw [graphCharge, code_graph] at hh
  have hedges := graph_edgeFinset s
  simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hh hedges
  rw [hedges, Finset.sum_image] at hh
  · exact hh
  · intro i _ j _ hij
    exact edge_injective hij

/-- Fully graph-level counterexample to unrestricted additive-charge
extension. Invariance of cycle-partition count is NOT a hypothesis. -/
theorem graph_additive_charge_not_representable :
    graphCharge ⊥ = 0 ∧
    (∀ H K : SimpleGraph V, (∀ v, Even (H.degree v)) →
      (∀ v, Even (K.degree v)) → Disjoint H.edgeSet K.edgeSet →
      graphCharge (H ⊔ K) = graphCharge H + graphCharge K) ∧
    ¬ (∃ w : Sym2 V → ℝ, ∀ H : SimpleGraph V, (∀ v, Even (H.degree v)) →
      graphCharge H = ∑ e ∈ H.edgeFinset, w e) :=
  ⟨graphCharge_bot, fun _ _ heH heK hd => graphCharge_add heH heK hd,
    graphCharge_not_edge_sum⟩

/-- Adding the edge count also gives a positive additive charge. -/
noncomputable def positiveGraphCharge (H : SimpleGraph V) : ℝ :=
  (code H).card + graphCharge H

lemma graphCharge_lower (H : SimpleGraph V) : -1 ≤ graphCharge H := by
  unfold graphCharge charge
  split_ifs <;> norm_num

lemma evenAt_card_lower : ∀ i : Fin 64, evenAt i ≠ ∅ → 3 ≤ (evenAt i).card := by decide

lemma positiveGraphCharge_pos {H : SimpleGraph V}
    (he : ∀ v, Even (H.degree v)) (hne : H ≠ ⊥) : 0 < positiveGraphCharge H := by
  have hc : code H ≠ ∅ := by
    intro h
    apply hne
    rw [← graph_code H, h]
    simp [graph]
  have hcard : 3 ≤ (code H).card := by
    have hi := even_index (code H) (code_even he)
    have hb := evenAt_card_lower (evenIndex (code H))
    rw [hi] at hb
    exact hb hc
  have hreal : (3 : ℝ) ≤ (code H).card := by exact_mod_cast hcard
  have hb := graphCharge_lower H
  unfold positiveGraphCharge
  linarith

lemma positiveGraphCharge_bot : positiveGraphCharge ⊥ = 0 := by
  simp [positiveGraphCharge, code_bot, graphCharge_bot]

lemma positiveGraphCharge_add {H K : SimpleGraph V}
    (heH : ∀ v, Even (H.degree v)) (heK : ∀ v, Even (K.degree v))
    (hd : Disjoint H.edgeSet K.edgeSet) :
    positiveGraphCharge (H ⊔ K) = positiveGraphCharge H + positiveGraphCharge K := by
  unfold positiveGraphCharge
  rw [code_sup, Finset.card_union_of_disjoint (code_disjoint hd), Nat.cast_add,
    graphCharge_add heH heK hd]
  ring

/-- Even strict positivity does not make unrestricted additive charges
representable by signed edge weights. The charge is not constant on cycles. -/
theorem positiveGraphCharge_not_edge_sum :
    ¬ ∃ w : Sym2 V → ℝ, ∀ H : SimpleGraph V, (∀ v, Even (H.degree v)) →
      positiveGraphCharge H = ∑ e ∈ H.edgeFinset, w e := by
  classical
  rintro ⟨w, hw⟩
  apply not_edge_weight_sum
  refine ⟨fun i => w (edge i) - 1, fun s hs => ?_⟩
  have hh := hw (graph s) (by
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (even_graph_iff s).mp hs)
  rw [positiveGraphCharge, graphCharge, code_graph] at hh
  have hedges := graph_edgeFinset s
  simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hh hedges
  rw [hedges, Finset.sum_image] at hh
  · simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  · intro i _ j _ hij
    exact edge_injective hij

end K5EvenCharge
