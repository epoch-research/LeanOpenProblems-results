import Submission.FiniteInducedRamsey
import Submission.RamseyVectorObstruction

/-!
The uniform triangle-hitting margin -1/3 fails on a finite K4-free graph.
The formerly conditional Ramsey host is supplied by the finite partite
construction. This is an obstruction to a uniform-margin method, not a
counterexample to countable triangle-free edge covering.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PaleyRamseyMargin
open Erdos595RamseyVector

/-- Binary induced Ramsey implies the asymmetric red-H / blue-triangle
property when H contains a triangle. Both target and host are finite. -/
theorem finite_ramsey_against_triangle {A : Type} [Finite A]
    (H : SimpleGraph A) (hH : H.CliqueFree 4)
    (htri : ∃ a b d, H.Adj a b ∧ H.Adj a d ∧ H.Adj b d) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ RamseyAgainstTriangle H G := by
  classical
  obtain ⟨V,hV,G,hG,hRam⟩ :=
    Erdos595FiniteInducedRamsey.finite_induced_ramsey H hH
  refine ⟨V,hV,G,hG,?_⟩
  intro R B he hB
  let col : Sym2 V → Bool := fun e => decide (e ∈ R.edgeSet)
  obtain ⟨f,z,hf⟩ := hRam col
  cases z with
  | true =>
    refine ⟨{ toFun := f, map_rel' := ?_ }⟩
    intro a b hab
    have hh := hf a b hab
    simpa only [col,decide_eq_true_eq,SimpleGraph.mem_edgeSet] using hh
  | false =>
    have hb : ∀ a b, H.Adj a b → B.Adj (f a) (f b) := by
      intro a b hab
      have hh := hf a b hab
      have hn : ¬R.Adj (f a) (f b) := by
        exact of_decide_eq_false hh
      have hle : G ≤ R ⊔ B := le_of_eq he
      exact (hle (f.map_rel_iff.mpr hab)).resolve_left hn
    obtain ⟨a,b,d,hab,had,hbd⟩ := htri
    exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hb a b hab,hb a d had,hb b d hbd⟩)).elim

theorem exists_paley_ramsey_host :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ RamseyAgainstTriangle Erdos595Paley.G G := by
  apply finite_ramsey_against_triangle Erdos595Paley.G Erdos595Paley.G_cliqueFree
  exact ⟨0,1,2,by change Erdos595Paley.adjacent 0 1; decide +kernel,
    by change Erdos595Paley.adjacent 0 2; decide +kernel,
    by change Erdos595Paley.adjacent 1 2; decide +kernel⟩

universe u
/-- The same finite host obstructs the margin in every real Hilbert space,
including nonseparable spaces. -/
theorem exists_no_third_triangle_hit :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ¬∃ v : V → E, UnitTriangleHit G (-(1/3 : ℝ)) v := by
  obtain ⟨V,hV,G,hG,hRam⟩ := exists_paley_ramsey_host
  exact ⟨V,hV,G,hG,fun _ _ _ => no_triangle_hit_third_of_paley_ramsey G hRam⟩

#print axioms finite_ramsey_against_triangle
#print axioms exists_paley_ramsey_host
#print axioms exists_no_third_triangle_hit
end Erdos595PaleyRamseyMargin
