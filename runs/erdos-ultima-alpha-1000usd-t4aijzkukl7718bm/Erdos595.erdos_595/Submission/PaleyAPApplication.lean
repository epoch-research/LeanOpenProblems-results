import Submission.PaleyAPObstruction

/-!
The Paley graph on 17 vertices has no edge labeling by vectors in any
rational vector space making each triangle a nonconstant arithmetic
progression. Midpoints may be chosen independently on all triangles.
This is an obstruction to one covering method, not a solution of Erdős 595.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
open SimpleGraph Set
namespace Erdos595PaleyAPApplication
open Erdos595Paley Erdos595ArithmeticProgression Erdos595PaleyAPObstruction

local instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adjacent)

lemma det_ne_zero : incidence.det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse certificate

lemma triEdges_correct : ∀ i : Fin 68,
    edges (triEdges i 0) = ((triangles i).1, (triangles i).2.1) ∧
    edges (triEdges i 1) = ((triangles i).1, (triangles i).2.2) ∧
    edges (triEdges i 2) = ((triangles i).2.1, (triangles i).2.2) := by
  decide +kernel

lemma triangles_correct : ∀ i : Fin 68,
    G.Adj (triangles i).1 (triangles i).2.1 ∧
    G.Adj (triangles i).1 (triangles i).2.2 ∧
    G.Adj (triangles i).2.1 (triangles i).2.2 := by
  decide +kernel

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

def edgeLabel (f : Sym2 (Fin 17) → E) (i : Fin 68) : E :=
  f s((edges i).1,(edges i).2)

theorem all_edges_constant (f : Sym2 (Fin 17) → E)
    (hf : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      ∃ m, defect m (f s(a,b)) (f s(a,c)) (f s(b,c)) = 0) :
    ∀ i : Fin 68, edgeLabel f i = edgeLabel f 0 := by
  classical
  have h (i : Fin 67) : ∃ m, defect m
      (edgeLabel f (triEdges i.castSucc 0))
      (edgeLabel f (triEdges i.castSucc 1))
      (edgeLabel f (triEdges i.castSucc 2)) = 0 := by
    obtain ⟨h₁,h₂,h₃⟩ := triangles_correct i.castSucc
    obtain ⟨m,hm⟩ := hf _ _ _ h₁ h₂ h₃
    refine ⟨m,?_⟩
    obtain ⟨he₁,he₂,he₃⟩ := triEdges_correct i.castSucc
    simpa only [edgeLabel,he₁,he₂,he₃] using hm
  choose m hm using h
  exact Erdos595APModularTransfer.vector_constant
    (fun i : Fin 67 => triEdges i.castSucc) det_ne_zero m (edgeLabel f) hm

theorem no_nondegenerate_AP_labeling :
    ¬∃ f : Sym2 (Fin 17) → E,
      ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
        ∃ m, defect m (f s(a,b)) (f s(a,c)) (f s(b,c)) = 0 ∧
          ¬(f s(a,b) = f s(a,c) ∧ f s(a,b) = f s(b,c)) := by
  rintro ⟨f,hf⟩
  have he := all_edges_constant f (fun a b c hab hac hbc => by
    obtain ⟨m,hm,_⟩ := hf a b c hab hac hbc
    exact ⟨m,hm⟩)
  have h₁ := he 1
  have h₂ := he 8
  change f s(0,2) = f s(0,1) at h₁
  change f s(1,2) = f s(0,1) at h₂
  obtain ⟨_,_,hn⟩ := hf 0 1 2 (by decide) (by decide) (by decide)
  exact hn ⟨h₁.symm,h₂.symm⟩

#print axioms all_edges_constant
#print axioms no_nondegenerate_AP_labeling
end Erdos595PaleyAPApplication
