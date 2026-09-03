import Submission.CycleDualBound
import Submission.OptimalSingletonForest
import Submission.MaximizerReachability

/-! A sufficient dual-exactness criterion for the original conjecture.
The existence hypothesis is NOT proved for arbitrary globally minimal graphs. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.OptimalRemainderDualCriterion
open Critical EdgeHull SingletonExchange TightDual CycleCertificates
set_option maxHeartbeats 1000000
universe u
variable {V : Type u} [Fintype V]

def HasExactOptimalRemainder (G : SimpleGraph V) : Prop :=
  ∃ F : SimpleGraph V, Optimal G F ∧
    ∃ w : Sym2 V → ℝ, CycleUpperWeight (G \ F) w ∧
      (number (G \ F) : ℝ) ≤ ∑ e ∈ (G \ F).edgeFinset, w e

lemma number_bound {G : SimpleGraph V} (h : HasExactOptimalRemainder G) :
    number G ≤ 3 * (Fintype.card V - 1) := by
  obtain ⟨F,hF,w,hw,hex⟩ := h
  have he : ∀ v, Even (Nat.card ((G \ F).neighborSet v)) := hF.2.1
  have hd := CycleDualBound.total_le_two_card_sub_one hw (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using he)
  have hb : (number (G \ F) : ℝ) ≤ 2 * (Fintype.card V - 1 : ℕ) := by
    simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hex hd
    exact hex.trans hd
  have hbn : number (G \ F) ≤ 2 * (Fintype.card V - 1) := by exact_mod_cast hb
  have hf := acyclic_edge_count_pred F hF.acyclic
  have hn := hF.2.2
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hf hbn ⊢
  omega

lemma bound_of_minimal_exactness
    (hex : ∀ R : SimpleGraph V, Minimal R → HasExactOptimalRemainder R)
    (G : SimpleGraph V) : number G ≤ 3 * (Fintype.card V - 1) := by
  obtain ⟨R,hR,hm,hn⟩ := exists_minimal_maximizer_all G
  have hb := number_bound (hex R hm)
  have hg := number_le_value G
  omega

/-- This implication is conditional: the hypothesis is the unresolved
existence of a dual-exact optimal remainder on every globally minimal graph. -/
lemma asymptotic_of_minimal_exactness
    (hex : ∀ {W : Type u} [Fintype W] (G : SimpleGraph W),
      Minimal G → HasExactOptimalRemainder G) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
        ∃ D : Finset G.Subgraph,
          (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
          (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_uniform.mpr
  refine ⟨3,?_⟩
  intro W _ _ G
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  refine ⟨D,hD,hdec,?_⟩
  have hb := bound_of_minimal_exactness (fun R hR => hex R hR) G
  have hc : D.card ≤ 3 * Fintype.card W := by omega
  exact_mod_cast hc

/-- Failure of the conjecture would in particular refute the exactness
hypothesis, rather than contradicting the fractional bound alone. -/
lemma obstruction_of_asymptotic_failure
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
        ∃ D : Finset G.Subgraph,
          (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
          (D.card : ℝ) ≤ f (Fintype.card W))) :
    ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      Minimal G ∧ ¬ HasExactOptimalRemainder G := by
  by_contra! h
  apply hbad
  apply asymptotic_of_minimal_exactness
  intro W i G hm
  exact h W i G hm

end Erdos184Work.OptimalRemainderDualCriterion
#print axioms Erdos184Work.OptimalRemainderDualCriterion.number_bound
#print axioms Erdos184Work.OptimalRemainderDualCriterion.asymptotic_of_minimal_exactness
#print axioms Erdos184Work.OptimalRemainderDualCriterion.obstruction_of_asymptotic_failure
