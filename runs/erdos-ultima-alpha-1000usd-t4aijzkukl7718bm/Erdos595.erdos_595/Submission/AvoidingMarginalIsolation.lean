import Submission.BadEdgeUltrafilter
import Submission.GenericUltrafilterUniversality

/-!
The endpoint marginal of a triangle-free-piece-avoiding edge ultrafilter
is isolated in BOTH directions of the Fubini relation. Its principal images
stay isolated at every later finite mutual-ultrafilter stage. This is a
limitation of a proposed tower argument, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595AvoidingMarginalIsolation
open Erdos595Work Erdos595BadEdge Erdos595ArcAdjoint
open Erdos595GenericUltrafilterUniversality

variable {V : Type*} (G : SimpleGraph V)

private def span (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1.ne rfl

private lemma span_triangleFree (S : Set V) (hS : (G.induce S).CliqueFree 3) :
    (span G S).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact hS _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce S).Adj ⟨a,hab.2.1⟩ ⟨b,hab.2.2⟩ ∧
      (G.induce S).Adj ⟨a,hab.2.1⟩ ⟨c,hac.2.2⟩ ∧
      (G.induce S).Adj ⟨b,hab.2.2⟩ ⟨c,hac.2.2⟩ from ⟨hab.1,hac.1,hbc.1⟩))

/-- This excludes every triangle-free induced vertex set, not just the
neighborhood of a single original vertex. No clique bound on G is needed. -/
theorem triangleFree_set_not_mem (D : Ultrafilter (Arc G)) (hD : Avoids G D)
    (S : Set V) (hS : (G.induce S).CliqueFree 3) :
    S ∉ D.map (fun e => e.val.1) := by
  intro h₁
  have h₂ : S ∈ D.map (fun e => e.val.2) := marginals_equal G D hD ▸ h₁
  apply hD (span G S) (span_triangleFree G S hS)
  exact Filter.mem_of_superset (Filter.inter_mem h₁ h₂)
    (fun e h => ⟨e.property,h.1,h.2⟩)

/-- In a K4-free base every neighborhood trace is triangle-free. The common
endpoint marginal therefore has no outgoing Fubini adjacency either. -/
theorem no_outgoing (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (q : Ultrafilter V) :
    ¬fubiniAdj G (D.map (fun e => e.val.1)) q :=
  triangleFree_set_not_mem G D hD _ (ultrafilter_trace_cliqueFree G hG q)

/-- Empty original neighborhood trace excludes the reverse direction. -/
theorem no_incoming (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (q : Ultrafilter V) :
    ¬fubiniAdj G q (D.map (fun e => e.val.1)) := by
  intro h
  obtain ⟨v,hv⟩ := Ultrafilter.nonempty_of_mem h
  exact neighborhood_not_mem G hG D hD v hv

/-- Neither symmetrization, nor any choice of orientation order, can turn
this particular marginal into a nonisolated vertex. -/
theorem both_directions (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (q : Ultrafilter V) :
    ¬(fubiniAdj G (D.map (fun e => e.val.1)) q ∨
      fubiniAdj G q (D.map (fun e => e.val.1))) :=
  fun h => h.elim (no_outgoing G hG D hD q) (no_incoming G hG D hD q)

/-- An isolated vertex remains isolated when embedded principally. -/
theorem pure_isolated (hG : G.CliqueFree 4) (v : V)
    (hv : ∀ w, ¬G.Adj v w) (q : Ultrafilter V) :
    ¬(ultrafilterGraph G hG).Adj (pure v) q := by
  intro h
  have hm : G.neighborSet v ∈ q := h.1
  obtain ⟨w,hw⟩ := Ultrafilter.nonempty_of_mem hm
  exact hv w hw

def principalIterate {A : Type*} (a : A) : (n : ℕ) → Carrier A n
  | 0 => a
  | n+1 => pure (principalIterate a n)

/-- Later stages do not revive an isolated point already introduced. -/
theorem principalIterate_isolated (hG : G.CliqueFree 4) (v : V)
    (hv : ∀ w, ¬G.Adj v w) (n : ℕ) :
    ∀ q, ¬(tower G hG n).val.Adj (principalIterate v n) q := by
  induction n with
  | zero => exact hv
  | succ n ih => exact pure_isolated (tower G hG n).val (tower G hG n).property _ ih

/-- In particular the finite-cover compactness marginal remains isolated
in every finite tower above the first extension. -/
theorem marginal_stays_isolated (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D) (n : ℕ) :
    ∀ q, ¬(tower (ultrafilterGraph G hG) (ultrafilterGraph_cliqueFree G hG) n).val.Adj
      (principalIterate (D.map (fun e => e.val.1)) n) q :=
  principalIterate_isolated _ _ _ (marginal_isolated G hG D hD) n

#print axioms triangleFree_set_not_mem
#print axioms both_directions
#print axioms marginal_stays_isolated
end Erdos595AvoidingMarginalIsolation
