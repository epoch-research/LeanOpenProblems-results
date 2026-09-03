import Submission.TwoForestAbsorption

/-!
An obstruction to simultaneously completing an arbitrary prescribed partition
into three forests. The graph nevertheless has a marked-hitting decomposition.
This is not a counterexample to Erdos 184 or to the general hitting assertion.
-/
open SimpleGraph
namespace Erdos184.ThreeForestObstruction

abbrev V := Fin 8
abbrev Color := Fin 3

def R : SimpleGraph V := cycleGraph 8

def blueEdges (i : Color) : Finset (Sym2 V) :=
  ![{s(0,2),s(4,6)}, {s(0,4)}, {s(2,6)}] i

def blue (i : Color) : SimpleGraph V := fromEdgeSet (blueEdges i : Set (Sym2 V))
def B : SimpleGraph V := blue 0 ⊔ blue 1 ⊔ blue 2
def G : SimpleGraph V := R ⊔ B

instance (i : Color) : DecidableRel (blue i).Adj := by unfold blue; infer_instance
instance : DecidableRel R.Adj := by unfold R; infer_instance
instance : DecidableRel B.Adj := by unfold B; infer_instance
instance : DecidableRel G.Adj := by unfold G; infer_instance

def redColor (c : V → Color) (i : Color) : SimpleGraph V where
  Adj v w := (v + 1 = w ∧ c v = i) ∨ (w + 1 = v ∧ c w = i)
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless v h := by
    have hn : v + 1 ≠ v := by fin_cases v <;> decide
    exact h.elim (fun h => hn h.1) (fun h => hn h.1)

instance (c : V → Color) (i : Color) : DecidableRel (redColor c i).Adj := by
  unfold redColor; infer_instance

lemma redColor_le (c : V → Color) (i : Color) : redColor c i ≤ R := by
  intro v w h
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · subst w
    fin_cases v <;> decide
  · subst v
    fin_cases w <;> decide

lemma redColor_degree (c : V → Color) (i : Color) (v : V) :
    (redColor c i).degree v =
      (if c (v-1) = i then 1 else 0) + (if c v = i then 1 else 0) := by
  have ha (w : V) : (redColor c i).Adj v w ↔
      (w = v-1 ∧ c (v-1) = i) ∨ (w = v+1 ∧ c v = i) := by
    constructor
    · rintro (⟨h,hc⟩ | ⟨h,hc⟩)
      · exact Or.inr ⟨h.symm,hc⟩
      · have hw : w = v-1 := eq_sub_iff_add_eq.mpr h
        exact Or.inl ⟨hw,hw ▸ hc⟩
    · rintro (⟨rfl,hc⟩ | ⟨rfl,hc⟩)
      · exact Or.inr ⟨sub_add_cancel v 1,hc⟩
      · exact Or.inl ⟨rfl,hc⟩
  have hn : (redColor c i).neighborFinset v =
      (if c (v-1) = i then {v-1} else ∅) ∪ (if c v = i then {v+1} else ∅) := by
    ext w
    simp only [mem_neighborFinset,ha,Finset.mem_union]
    by_cases hp : c (v-1) = i <;> by_cases hv : c v = i <;> simp [hp,hv]
  have hne : v-1 ≠ v+1 := (by decide : ∀ v : V, v-1 ≠ v+1) v
  rw [SimpleGraph.degree,hn]
  by_cases hp : c (v-1) = i <;> by_cases hv : c v = i <;> simp [hp,hv,Ne.symm hne]

lemma equal_of_even (a b : Color)
    (h : ∀ i : Color, Even ((if a = i then 1 else 0) + (if b = i then 1 else 0) : ℕ)) :
    a = b := by
  by_contra hn
  have hh := h a
  simp [Ne.symm hn] at hh

lemma pair_of_parity : ∀ a b x y : Color, x ≠ y →
    (∀ i : Color, Even ((if a = i then 1 else 0) + (if b = i then 1 else 0) +
      (if i = x ∨ i = y then 1 else 0) : ℕ)) →
    (a = x ∨ a = y) ∧ (b = x ∨ b = y) ∧ a ≠ b := by decide

lemma blue_degree_zero : ∀ i : Color,
    (blue i).degree 0 = if i = 0 ∨ i = 1 then 1 else 0 := by decide
lemma blue_degree_one : ∀ i : Color, (blue i).degree 1 = 0 := by decide
lemma blue_degree_two : ∀ i : Color,
    (blue i).degree 2 = if i = 0 ∨ i = 2 then 1 else 0 := by decide
lemma blue_degree_three : ∀ i : Color, (blue i).degree 3 = 0 := by decide
lemma blue_degree_four : ∀ i : Color,
    (blue i).degree 4 = if i = 0 ∨ i = 1 then 1 else 0 := by decide

/-- No coloring of the red Hamilton cycle into three classes simultaneously
completes these three specified blue forests to even graphs. -/
theorem no_simultaneous_completion :
    ¬ ∃ c : V → Color, ∀ i v, Even ((redColor c i).degree v + (blue i).degree v) := by
  rintro ⟨c,h⟩
  have h01 : c 0 = c 1 := by
    apply equal_of_even
    intro i
    have hh := h i 1
    rw [redColor_degree,blue_degree_one] at hh
    simpa using hh
  have h23 : c 2 = c 3 := by
    apply equal_of_even
    intro i
    have hh := h i 3
    rw [redColor_degree,blue_degree_three] at hh
    simpa using hh
  have h0 := pair_of_parity (c 7) (c 0) 0 1 (by decide) (by
    intro i
    have hh := h i 0
    rw [redColor_degree,blue_degree_zero] at hh
    exact hh)
  have h2 := pair_of_parity (c 1) (c 2) 0 2 (by decide) (by
    intro i
    have hh := h i 2
    rw [redColor_degree,blue_degree_two] at hh
    exact hh)
  have h4 := pair_of_parity (c 3) (c 4) 0 1 (by decide) (by
    intro i
    have hh := h i 4
    rw [redColor_degree,blue_degree_four] at hh
    exact hh)
  have hc1 : c 1 = 0 := by
    have ha := h0.2.1
    rw [h01] at ha
    rcases ha with ha | ha
    · exact ha
    · rcases h2.1 with hb | hb
      · exact hb
      · exact ((by decide : (1 : Color) ≠ 2) (ha.symm.trans hb)).elim
  have hc2 : c 2 = 0 := by
    have ha := h4.1
    rw [← h23] at ha
    rcases ha with ha | ha
    · exact ha
    · rcases h2.2.1 with hb | hb
      · exact hb
      · exact ((by decide : (1 : Color) ≠ 2) (ha.symm.trans hb)).elim
  exact h2.2.2 (hc1.trans hc2.symm)

lemma red_next : ∀ v : V, R.Adj v (v+1) := by decide
lemma red_adj_iff : ∀ v w : V, R.Adj v w ↔ v+1 = w ∨ w+1 = v := by decide

/-- Every actual partition of the red edge set is represented by one of
our colorings. No restriction on possible red parts is hidden in redColor. -/
lemma partition_is_coloring (X : Color → SimpleGraph V)
    (hsub : ∀ i, X i ≤ R)
    (hpart : ∀ v w, R.Adj v w → ∃! i, (X i).Adj v w) :
    ∃ c : V → Color, ∀ i, X i = redColor c i := by
  classical
  have hex (v : V) := hpart v (v+1) (red_next v)
  choose c hc using hex
  refine ⟨c,fun i => ?_⟩
  ext v w
  constructor
  · intro h
    rcases (red_adj_iff v w).mp (hsub i h) with hnext | hprev
    · subst w
      exact Or.inl ⟨rfl,((hc v).2 i h).symm⟩
    · subst v
      exact Or.inr ⟨rfl,((hc w).2 i h.symm).symm⟩
  · rintro (⟨rfl,hcvi⟩ | ⟨rfl,hcwi⟩)
    · exact hcvi ▸ (hc v).1
    · exact hcwi ▸ (hc w).1.symm

/-- The obstruction in a graph-partition formulation. -/
theorem no_red_partition_with_prescribed_parities :
    ¬ ∃ X : Color → SimpleGraph V,
      (∀ i, X i ≤ R) ∧
      (∀ v w, R.Adj v w → ∃! i, (X i).Adj v w) ∧
      (∀ i v, Even ((X i).degree v + (blue i).degree v)) := by
  classical
  rintro ⟨X,hsub,hpart,he⟩
  obtain ⟨c,hc⟩ := partition_is_coloring X hsub hpart
  apply no_simultaneous_completion
  refine ⟨c,fun i v => ?_⟩
  have hh := he i v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rwa [hc i] at hh

lemma blue_forests (i : Color) : (blue i).IsAcyclic := by
  apply TwoForestAbsorption.acyclic_of_degree_le_one
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using (by decide : ∀ i : Color, ∀ v : V, (blue i).degree v ≤ 1) i v

lemma blue_pairwise : Pairwise (fun i j : Color => Disjoint (blue i).edgeSet (blue j).edgeSet) := by
  intro i j hne
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | h v w => exact (by decide : ∀ i j : Color, i ≠ j → ∀ v w : V,
      (blue i).Adj v w → ¬ (blue j).Adj v w) i j hne v w

lemma red_blue_disjoint : Disjoint R.edgeSet B.edgeSet := by
  rw [Set.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | h v w => exact (by decide : ∀ v w : V, R.Adj v w → ¬ B.Adj v w) v w

lemma blue_isCycles : B.IsCycles := by
  intro v hv
  have hp := (degree_pos_iff_nonempty (G := B) (v := v)).mpr hv
  have hd := (by decide : ∀ v : V, B.degree v = 0 ∨ B.degree v = 2) v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hp hd
  omega

lemma blue_is_complement : G \ R = B := by
  ext v w
  have hd : R.Adj v w → ¬ B.Adj v w :=
    (by decide : ∀ v w : V, R.Adj v w → ¬ B.Adj v w) v w
  change ((R.Adj v w ∨ B.Adj v w) ∧ ¬R.Adj v w) ↔ B.Adj v w
  constructor
  · rintro ⟨h,hr⟩
    exact h.resolve_left hr
  · intro hb
    exact ⟨Or.inr hb,fun hr => hd hr hb⟩

/-- Despite the failed prescribed three-forest completion, the full graph
has a decomposition hitting red, by the verified two-forest absorption theorem. -/
theorem hitting_decomposition_exists :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ 8 := by
  classical
  obtain ⟨D,hc,hd,hh,hcard⟩ := TwoForestAbsorption.hitting_of_blue_cycles G R
    le_sup_left (cycleGraph_connected (n := 7))
    (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (by decide : ∀ v : V, Even (G.degree v)) v)
    (blue_is_complement.symm ▸ blue_isCycles)
  refine ⟨D,?_,hd,hh,?_⟩
  · intro H hH
    refine ⟨(hc H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc H hH).2 v
  ·
    have hRcard : R.edgeFinset.card = 8 := by
      simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_fin] using regular_two_graph_edge_card R (by
        intro v
        simpa only [R,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using (cycleGraph_degree_three_le (n := 5) (v := v)))
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcard hRcard
    omega

end Erdos184.ThreeForestObstruction
