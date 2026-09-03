import Submission.VertexHullLossReduction

/-! A selective vertex-loss bound only on large, highly connected minimal
graphs would suffice. The loss bound itself remains an explicit hypothesis. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.HighlyConnectedVertexLoss
open Critical EdgeHull VertexSeparators
set_option maxHeartbeats 1600000
universe u

/-- Only large graphs beyond the fixed separator threshold are tested. -/
def Property (k C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    Minimal G → DeletionConnected G k → 2*k+1 < Fintype.card V →
      ∃ v : V, number G ≤ value (G.induce ({v}ᶜ : Set V)) + C

lemma uniform_of_property (k B : ℕ) (hhigh : Property.{u} k B) :
    ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      number G ≤ ((2*k+1)^2 + B) * Fintype.card W := by
  let C := (2*k+1)^2 + B
  have hCsq : (2*k+1)^2 ≤ C := Nat.le_add_right _ _
  have hBC : B ≤ C := Nat.le_add_left _ _
  have main : ∀ n : ℕ, ∀ (W : Type u) [Fintype W]
      (G : SimpleGraph W), Fintype.card W = n → k < n →
      number G ≤ C*(n-k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hW hkn
      by_cases hsmall : n ≤ 2*k+1
      · have hn := number_le_square G
        rw [hW] at hn
        have hle : number G ≤ C := by nlinarith
        exact hle.trans (Nat.le_mul_of_pos_right C (by omega))
      by_cases hz : value G = 0
      · have hh := number_le_value G
        rw [hz] at hh
        exact hh.trans (Nat.zero_le _)
      obtain ⟨R,hRG,hm,hr⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
      have hGR : number G ≤ number R := (number_le_value G).trans_eq hr.symm
      apply hGR.trans
      by_cases hG : NoSmallSeparator R k
      · obtain ⟨v,hv⟩ := hhigh W R hm hG.deletionConnected (by omega)
        have hc : Fintype.card ({v}ᶜ : Set W) + 1 = n := by
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
          omega
        have hsm : Fintype.card ({v}ᶜ : Set W) < n := by omega
        have hb : value (R.induce ({v}ᶜ : Set W)) ≤
            C * (Fintype.card ({v}ᶜ : Set W) - k) := by
          apply (value_le_iff _ _).mpr
          intro S _
          exact ih _ hsm _ S rfl (by omega)
        have ha : (Fintype.card ({v}ᶜ : Set W) - k) + 1 = n-k := by omega
        have hh := congrArg (C * ·) ha
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      have hsep : ∃ A T : Set W, A ∪ T = Set.univ ∧ A ≠ Set.univ ∧
          T ≠ Set.univ ∧ Nat.card (A ∩ T : Set W) ≤ k ∧
          ∀ x ∈ A \ T, ∀ y ∈ T \ A, ¬ R.Adj x y := by
        unfold NoSmallSeparator at hG
        push_neg at hG
        exact hG
      obtain ⟨A,T,hcover,hA,hT,hint,hcross⟩ := hsep
      have ha : Fintype.card A < n := by
        obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hA
        exact (Fintype.card_subtype_lt hx).trans_eq hW
      have ht : Fintype.card T < n := by
        obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hT
        exact (Fintype.card_subtype_lt hx).trans_eq hW
      have hsum : Fintype.card A + Fintype.card T ≤ n+k := by
        have hc := Set.ncard_union_add_ncard_inter A T
        rw [hcover, Set.ncard_univ] at hc
        change Nat.card W + Nat.card (A ∩ T : Set W) = Nat.card A + Nat.card T at hc
        simp only [Nat.card_eq_fintype_card] at hc hint
        rw [hW] at hc
        omega
      obtain ⟨H,hnum⟩ := split_number R A T hcover hcross
      apply hnum.trans
      apply split_budget k C n (Fintype.card A) (Fintype.card T) _ _ hCsq
        (by omega) ha ht hsum (number_le_square _) (number_le_square _)
      · exact fun hka => ih _ ha _ (R.induce A) rfl hka
      · exact fun hkt => ih _ ht _ H rfl hkt
  intro W _ G
  change number G ≤ C * Fintype.card W
  by_cases hk : k < Fintype.card W
  · exact (main _ W G rfl hk).trans (Nat.mul_le_mul_left C (Nat.sub_le _ _))
  · have hsq := number_le_square G
    have hWC : Fintype.card W ≤ C := by dsimp [C]; nlinarith
    exact hsq.trans (by simpa only [pow_two] using
      Nat.mul_le_mul_right (Fintype.card W) hWC)

lemma asymptotic_of_property (k C : ℕ) (h : Property.{u} k C) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply asymptotic_iff_uniform.mpr
  refine ⟨(((2*k+1)^2 + C : ℕ) : ℝ), ?_⟩
  intro V _ _ G
  obtain ⟨D,hD,hd,hcard⟩ := exists_minimum G
  refine ⟨D,hD,hd,?_⟩
  have hb := uniform_of_property k C h V G
  rw [← hcard] at hb
  exact_mod_cast hb

/-- Original failure would force large highly connected globally minimal
graphs with large hull loss at EVERY vertex. No such graphs are constructed. -/
lemma obstruction_of_asymptotic_failure
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V))) (k C : ℕ) :
    ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V),
      Minimal G ∧ DeletionConnected G k ∧ 2*k+1 < Fintype.card V ∧
        ∀ v : V, value (G.induce ({v}ᶜ : Set V)) + C < number G := by
  have hn : ¬ Property.{u} k C := fun h => hbad (asymptotic_of_property k C h)
  unfold Property at hn
  push_neg at hn
  exact hn

private noncomputable def stableNumber {W : Type*} [Finite W] (H : SimpleGraph W) : ℕ :=
  @number W (Fintype.ofFinite W) H

private lemma number_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    number H = stableNumber H :=
  congrArg (fun i : Fintype W => @number W i H) (Subsingleton.elim _ _)

/-- The elementary loss bound pays for all incident edges. It does not
supply a constant independent of the vertex degree. -/
lemma number_le_induced_hull_add_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    number G ≤ value (G.induce ({v}ᶜ : Set V)) + G.degree v := by
  let M := SimpleGraph.fromEdgeSet (G.incidenceSet v)
  have hMG : M ≤ G := by
    intro x y hxy
    exact G.incidenceSet_subset v hxy.1
  have hn := number_sdiff_add_le G M hMG
  have hc : Nat.card M.edgeSet = G.degree v := by
    rw [show M.edgeSet = G.incidenceSet v from G.edgeSet_fromEdgeSet_incidenceSet v]
    rw [Nat.card_eq_fintype_card, G.card_incidenceSet_eq_degree]
  have hm := number_le_edges M
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hm
  rw [hc] at hm
  have hh := number_induce_support (G.deleteIncidenceSet v) ({v}ᶜ : Set V) (by
    intro x hx
    exact (G.support_deleteIncidenceSet_subset v hx).2)
  change number G ≤ number (G.deleteIncidenceSet v) + number M at hn
  have hi := number_le_value (G.induce ({v}ᶜ : Set V))
  simp only [number_stable] at hn hh hm hi ⊢
  rw [G.induce_deleteIncidenceSet_of_notMem (by simp)] at hh
  omega

/-- The simultaneous obstruction also has arbitrarily large minimum degree.
Again this follows only under failure of the original conjecture. -/
lemma high_minimum_degree_obstruction
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V))) (k C : ℕ) :
    ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V),
      Minimal G ∧ DeletionConnected G k ∧ 2*k+1 < Fintype.card V ∧
        (∀ v : V, C < G.degree v) ∧
        (∀ v : V, value (G.induce ({v}ᶜ : Set V)) + C < number G) := by
  obtain ⟨V,iV,G,hm,hc,hn,hv⟩ := obstruction_of_asymptotic_failure hbad k C
  letI := iV
  refine ⟨V,iV,G,hm,hc,hn,?_,hv⟩
  intro v
  have hb := number_le_induced_hull_add_degree G v
  have hh := hv v
  omega

end Erdos184Work.HighlyConnectedVertexLoss
#print axioms Erdos184Work.HighlyConnectedVertexLoss.high_minimum_degree_obstruction
#print axioms Erdos184Work.HighlyConnectedVertexLoss.uniform_of_property
#print axioms Erdos184Work.HighlyConnectedVertexLoss.obstruction_of_asymptotic_failure
