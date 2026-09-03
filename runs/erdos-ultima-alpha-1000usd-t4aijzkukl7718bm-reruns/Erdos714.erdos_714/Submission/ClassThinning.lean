import Submission.EdgeAveraging
import Submission.GroupClass
import Submission.UpperBounds

/-!
The edge-transitive averaging obstruction applies to every edge thinning of the
SL(3) companion conjugacy-class hosts, not just induced vertex restrictions.
This result does not settle the balanced Zarankiewicz conjecture.
-/

open SimpleGraph Classical
open scoped MatrixGroups

set_option maxHeartbeats 1000000

namespace Erdos714ClassGraph

variable {Γ : Type*} [Group Γ]

lemma relative_transform (p q g h : Γ) :
    (p*g*q)⁻¹*(p*h*q) = q⁻¹*(g⁻¹*h)*q := by group

/-- Left and right multiplication simultaneously on the two sides. -/
def transform (a p q : Γ) : graph a ≃g graph a where
  toEquiv := Equiv.sumCongr ((Equiv.mulLeft p).trans (Equiv.mulRight q))
    ((Equiv.mulLeft p).trans (Equiv.mulRight q))
  map_rel_iff' := by
    intro x y
    have hh (g h : Γ) :
        (∃ k, (p*g*q)⁻¹*(p*h*q) = k*a*k⁻¹) ↔ ∃ k, g⁻¹*h = k*a*k⁻¹ := by
      rw [relative_transform]
      constructor
      · rintro ⟨k,hk⟩
        refine ⟨q*k, ?_⟩
        have he := congrArg (fun z : Γ => q*z*q⁻¹) hk
        simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
          mul_inv_rev, mul_inv_cancel, mul_one] using he
      · rintro ⟨k,hk⟩
        refine ⟨q⁻¹*k, ?_⟩
        rw [hk]
        group
    cases x with
    | inl g =>
      cases y with
      | inl h => rfl
      | inr h => exact hh g h
    | inr h =>
      cases y with
      | inl g => exact hh g h
      | inr g => rfl

@[simp] lemma transform_left (a p q x : Γ) :
    transform a p q (.inl x) = .inl (p*x*q) := rfl

@[simp] lemma transform_right (a p q x : Γ) :
    transform a p q (.inr x) = .inr (p*x*q) := rfl

def canonicalEdge (a : Γ) : (graph a).edgeSet :=
  ⟨s(Sum.inl 1, Sum.inr a), by
    change ∃ k : Γ, 1⁻¹*a=k*a*k⁻¹
    exact ⟨1, by simp⟩⟩

lemma cross_from_canonical (a g h : Γ) (hadj : (graph a).Adj (.inl g) (.inr h)) :
    ∃ f : graph a ≃g graph a,
      Sym2.map f (canonicalEdge a).val = s(Sum.inl g, Sum.inr h) := by
  obtain ⟨k,hk⟩ := hadj
  refine ⟨transform a (g*k) k⁻¹, ?_⟩
  change s(Sum.inl (g*k*1*k⁻¹), Sum.inr (g*k*a*k⁻¹)) = s(Sum.inl g, Sum.inr h)
  have hh : g*k*a*k⁻¹ = h := by
    rw [mul_assoc g k a, mul_assoc g (k*a) k⁻¹, ← hk]
    group
  rw [hh]
  simp

lemma from_canonical (a : Γ) (e : (graph a).edgeSet) :
    ∃ f : graph a ≃g graph a, f.mapEdgeSet (canonicalEdge a) = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    cases x with
    | inl g =>
      cases y with
      | inl h => exact False.elim he
      | inr h =>
        obtain ⟨f,hf⟩ := cross_from_canonical a g h he
        exact ⟨f, Subtype.ext hf⟩
    | inr h =>
      cases y with
      | inl g =>
        obtain ⟨f,hf⟩ := cross_from_canonical a g h he
        refine ⟨f, Subtype.ext ?_⟩
        simpa only [Sym2.eq_swap] using hf
      | inr g => exact False.elim he

/-- Every conjugacy-class bipartite Cayley graph is edge-transitive. -/
theorem edge_transitive (a : Γ) : Erdos714GraphAveraging.EdgeTransitive (graph a) := by
  intro x y
  obtain ⟨fx,hx⟩ := from_canonical a x
  obtain ⟨fy,hy⟩ := from_canonical a y
  refine ⟨fy * fx⁻¹, ?_⟩
  change (Erdos714GraphAveraging.edgeAction (graph a)) (fy*fx⁻¹) x = y
  rw [map_mul, map_inv]
  change fy.mapEdgeSet (fx.mapEdgeSet.symm x) = y
  rw [← hx, Equiv.symm_apply_apply]
  exact hy

/-- An arbitrary edge thinning is subject to the biclique averaging bound. -/
theorem thinning_bound [Fintype Γ] (a : Γ) (H : SimpleGraph (Γ ⊕ Γ)) (r t : ℕ)
    (hHG : H ≤ graph a) (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H)
    (hcopy : ¬ (completeBipartiteGraph (Fin t) (Fin t)).Free (graph a)) :
    t^2 * H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph a).edgeFinset.card := by
  obtain ⟨c⟩ := SimpleGraph.not_free.mp hcopy
  exact Erdos714GraphAveraging.biclique_bound H (graph a) r t c hHG hH (edge_transitive a)

end Erdos714ClassGraph

namespace Erdos714SL3Class

variable {F : Type*} [Field F] [Fintype F]

/-- The growing grid in the SL(3) host forbids positive-density edge repairs. -/
theorem thinning_bound (a b : F) (H : SimpleGraph (SL(3,F) ⊕ SL(3,F))) (r : ℕ)
    (hHG : H ≤ Erdos714ClassGraph.graph (center a b))
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    (Fintype.card F)^2 * H.edgeFinset.card ≤
      extremalNumber (2*Fintype.card F) (completeBipartiteGraph (Fin r) (Fin r)) *
        (Erdos714ClassGraph.graph (center a b)).edgeFinset.card := by
  apply Erdos714ClassGraph.thinning_bound (center a b) H r (Fintype.card F) hHG hH
  exact not_free a b (Fintype.equivFin F).symm.toEmbedding

end Erdos714SL3Class

#print axioms Erdos714ClassGraph.edge_transitive
#print axioms Erdos714ClassGraph.thinning_bound
#print axioms Erdos714SL3Class.thinning_bound

namespace Erdos714ClassGraph

variable {Γ : Type*} [Group Γ] [Fintype Γ]

/-- An explicit real form: a growing balanced biclique forces the retained
fraction of edges to tend to zero in every fixed forbidden-biclique case. -/
theorem thinning_real_bound (a : Γ) (H : SimpleGraph (Γ ⊕ Γ)) (r t : ℕ)
    (hr : 1 ≤ r) (hHG : H ≤ graph a)
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H)
    (hcopy : ¬ (completeBipartiteGraph (Fin t) (Fin t)).Free (graph a)) :
    (t : ℝ)^2 * H.edgeFinset.card ≤
      (((r : ℝ)-1)^(1/(r : ℝ))/2 *
        ((2*t : ℕ) : ℝ)^((2 : ℝ)-1/(r : ℝ)) +
        ((r : ℝ)-1)/2 * ((2*t : ℕ) : ℝ)) * (graph a).edgeFinset.card := by
  have h : (t : ℝ)^2 * H.edgeFinset.card ≤
      (extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) *
        (graph a).edgeFinset.card := by
    exact_mod_cast thinning_bound a H r t hHG hH hcopy
  exact h.trans (mul_le_mul_of_nonneg_right (Erdos714Upper.extremal_real_bound hr (2*t))
    (by positivity))

end Erdos714ClassGraph

#print axioms Erdos714ClassGraph.thinning_real_bound
