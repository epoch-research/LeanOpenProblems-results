import Submission.DoubleCosetOrbital
import Submission.EdgeAveraging

/-! Edge transitivity and local thinning bounds for the actual double-coset
orbital graphs. These are conditional tools, not a solution of Erdős 714. -/
noncomputable section
open SimpleGraph Classical
namespace Erdos714DoubleCoset
variable {Γ : Type*} [Group Γ]

private lemma right_related (H : Subgroup Γ) (t x y : Γ)
    (h : QuotientGroup.rightRel H x y) : QuotientGroup.rightRel H (x*t) (y*t) := by
  apply QuotientGroup.rightRel_apply.mpr
  convert QuotientGroup.rightRel_apply.mp h using 1
  group

/-- Right multiplication is well-defined on right cosets. -/
def rightPerm (H : Subgroup Γ) (t : Γ) : Cosets H ≃ Cosets H where
  toFun := Quotient.map' (fun x => x*t) (right_related H t)
  invFun := Quotient.map' (fun x => x*t⁻¹) (right_related H t⁻¹)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h x =>
      change coset H (x*t*t⁻¹) = coset H x
      congr 1
      group
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h x =>
      change coset H (x*t⁻¹*t) = coset H x
      congr 1
      group

@[simp] lemma rightPerm_coset (H : Subgroup Γ) (t x : Γ) :
    rightPerm H t (coset H x) = coset H (x*t) := rfl

lemma rightPerm_inv (H : Subgroup Γ) (t : Γ) (x : Cosets H) :
    rightPerm H t⁻¹ (rightPerm H t x) = x :=
  (rightPerm H t).symm_apply_apply x

lemma relation_right (H K : Subgroup Γ) (g t : Γ) {x : Cosets H} {y : Cosets K}
    (h : Rel H K g x y) : Rel H K g (rightPerm H t x) (rightPerm K t y) := by
  obtain ⟨s,rfl,rfl⟩ := h
  refine ⟨s*t,rfl,?_⟩
  simp only [rightPerm_coset,mul_assoc]

lemma relation_right_iff (H K : Subgroup Γ) (g t : Γ) (x : Cosets H) (y : Cosets K) :
    Rel H K g (rightPerm H t x) (rightPerm K t y) ↔ Rel H K g x y := by
  constructor
  · intro h
    have h' := relation_right H K g t⁻¹ h
    simpa only [rightPerm_inv] using h'
  · exact relation_right H K g t

/-- Every simultaneous right translation is an automorphism. -/
def rightIso (H K : Subgroup Γ) (g t : Γ) : graph H K g ≃g graph H K g where
  toEquiv := Equiv.sumCongr (rightPerm H t) (rightPerm K t)
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · rfl
    · exact relation_right_iff H K g t _ _
    · exact relation_right_iff H K g t _ _
    · rfl

def baseEdge (H K : Subgroup Γ) (g : Γ) : (graph H K g).edgeSet :=
  ⟨s(Sum.inl (coset H 1),Sum.inr (coset K g)),⟨1,rfl,by simp⟩⟩

lemma from_baseEdge (H K : Subgroup Γ) (g : Γ) (e : (graph H K g).edgeSet) :
    ∃ f : graph H K g ≃g graph H K g, f.mapEdgeSet (baseEdge H K g) = e := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | _ x y =>
    cases x with
    | inl x =>
      cases y with
      | inl y => exact False.elim he
      | inr y =>
        obtain ⟨t,ht,hy⟩ := he
        refine ⟨rightIso H K g t,Subtype.ext ?_⟩
        change s(Sum.inl (rightPerm H t (coset H 1)),
          Sum.inr (rightPerm K t (coset K g))) = s(Sum.inl x,Sum.inr y)
        simp only [rightPerm_coset,one_mul,ht,hy]
    | inr x =>
      cases y with
      | inr y => exact False.elim he
      | inl y =>
        obtain ⟨t,ht,hy⟩ := he
        refine ⟨rightIso H K g t,Subtype.ext ?_⟩
        change s(Sum.inl (rightPerm H t (coset H 1)),
          Sum.inr (rightPerm K t (coset K g))) = s(Sum.inr x,Sum.inl y)
        simp only [rightPerm_coset,one_mul,ht,hy,Sym2.eq_swap]

/-- No free-pair assumption is needed for edge transitivity. -/
theorem edge_transitive (H K : Subgroup Γ) (g : Γ) :
    Erdos714GraphAveraging.EdgeTransitive (graph H K g) := by
  intro x y
  obtain ⟨fx,hx⟩ := from_baseEdge H K g x
  obtain ⟨fy,hy⟩ := from_baseEdge H K g y
  refine ⟨fy * fx⁻¹,?_⟩
  change (Erdos714GraphAveraging.edgeAction (graph H K g)) (fy*fx⁻¹) x = y
  rw [map_mul,map_inv]
  change fy.mapEdgeSet (fx.mapEdgeSet.symm x) = y
  rw [← hx,Equiv.symm_apply_apply]
  exact hy

/-- A growing copied biclique bounds every forbidden-biclique-free edge thinning. -/
theorem biclique_thinning_bound [Fintype Γ] (H K : Subgroup Γ) (g : Γ)
    (J : SimpleGraph (Cosets H ⊕ Cosets K)) (r t : ℕ)
    (hc : Copy (completeBipartiteGraph (Fin t) (Fin t)) (graph H K g))
    (hJ : J ≤ graph H K g) (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free J) :
    t^2 * J.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph H K g).edgeFinset.card :=
  Erdos714GraphAveraging.biclique_bound J _ r t hc hJ hfree (edge_transitive H K g)

end Erdos714DoubleCoset
#print axioms Erdos714DoubleCoset.rightPerm
#print axioms Erdos714DoubleCoset.edge_transitive
#print axioms Erdos714DoubleCoset.biclique_thinning_bound
