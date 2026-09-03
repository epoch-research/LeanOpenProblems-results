import Submission.BicliquePartition

/-! Affine symmetries and subfield-kernel obstructions for weighted power
graphs. These results do not prove or disprove Erdős 714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714WeightedPower
variable {E W : Type*} [Field E] [CommGroup W]

def relation (ν : Eˣ →* W) (p q : E × W) : Prop :=
  ∃ z : Eˣ, (z : E)=p.1+q.1 ∧ ν z=p.2*q.2

def graph (ν : Eˣ →* W) : SimpleGraph ((E × W) ⊕ (E × W)) :=
  Erdos714Tensor.incidence (relation ν)

def affine (c : Eˣ) (t : E) (d : W) : E × W ≃ E × W where
  toFun p := ((c : E)*p.1+t,d*p.2)
  invFun p := ((c : E)⁻¹*(p.1-t),d⁻¹*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp; field_simp; ring
    · dsimp; simp
  right_inv p := by
    apply Prod.ext
    · dsimp; field_simp; ring
    · dsimp; simp

lemma weight_identity (c d p q : W) : c*(p*q)=(d*p)*((c/d)*q) := by
  calc
    c*(p*q)=(d*(c/d))*(p*q) := by simp
    _ = _ := by ac_rfl

lemma affine_relation (ν : Eˣ →* W) (c : Eˣ) (t : E) (d : W) (p q : E × W) :
    relation ν (affine c t d p) (affine c (-t) (ν c/d) q) ↔ relation ν p q := by
  constructor
  · rintro ⟨z,hz,hν⟩
    refine ⟨c⁻¹*z,?_,?_⟩
    · rw [Units.val_mul,Units.val_inv_eq_inv_val]
      dsimp [affine] at hz
      rw [hz]
      field_simp
      ring
    · rw [map_mul,map_inv,hν]
      dsimp only [affine,Equiv.coe_fn_mk]
      rw [← weight_identity]
      simp
  · rintro ⟨z,hz,hν⟩
    refine ⟨c*z,?_,?_⟩
    · change (c : E)*(z : E)=_
      rw [hz]
      dsimp [affine]
      ring
    · rw [map_mul,hν]
      exact weight_identity (ν c) d p.2 q.2

def automorphism (ν : Eˣ →* W) (c : Eˣ) (t : E) (d : W) : graph ν ≃g graph ν where
  toEquiv := (affine c t d).sumCongr (affine c (-t) (ν c/d))
  map_rel_iff' := by
    intro p q
    cases p <;> cases q
    · rfl
    · exact affine_relation ν c t d _ _
    · exact affine_relation ν c t d _ _
    · rfl

lemma edge_rep (ν : Eˣ →* W) (e : (graph ν).edgeSet) :
    ∃ p q : E × W, relation ν p q ∧ e.val=s(Sum.inl p,Sum.inr q) := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    cases u with
    | inl p =>
      cases v with
      | inl q => exact False.elim he
      | inr q => exact ⟨p,q,he,rfl⟩
    | inr q =>
      cases v with
      | inl p => exact ⟨p,q,he,Sym2.eq_swap⟩
      | inr p => exact False.elim he

/-- The affine transformations send the canonical edge to any chosen edge. -/
lemma sends_canonical (ν : Eˣ →* W) {p q : E × W} {z : Eˣ}
    (hz : (z : E)=p.1+q.1) (hν : ν z=p.2*q.2) :
    automorphism ν z p.1 p.2 (.inl (0,1))=Sum.inl p ∧
    automorphism ν z p.1 p.2 (.inr (1,1))=Sum.inr q := by
  constructor
  · simp [automorphism,affine]
  · change Sum.inr ((z : E)*1 + -p.1,(ν z/p.2)*1)=Sum.inr q
    rw [hz,hν]
    congr 1
    apply Prod.ext
    · dsimp; ring
    · dsimp; simp [div_eq_mul_inv,mul_assoc]

/-- No surjectivity of ν is required for edge transitivity. -/
theorem edge_transitive (ν : Eˣ →* W) : Erdos714GraphAveraging.EdgeTransitive (graph ν) := by
  intro e f
  obtain ⟨p,q,⟨z,hz,hν⟩,he⟩ := edge_rep ν e
  obtain ⟨p',q',⟨z',hz',hν'⟩,hf⟩ := edge_rep ν f
  let a := automorphism ν z p.1 p.2
  let b := automorphism ν z' p'.1 p'.2
  have ha := sends_canonical ν hz hν
  have hb := sends_canonical ν hz' hν'
  refine ⟨a.symm.trans b,?_⟩
  apply Subtype.ext
  change Sym2.map (a.symm.trans b) e.val=f.val
  rw [he,hf]
  change s(b (a.symm (.inl p)),b (a.symm (.inr q)))=s(Sum.inl p',Sum.inr q')
  have ha1 : a.symm (.inl p)=Sum.inl (0,1) := a.symm_apply_eq.mpr ha.1.symm
  have ha2 : a.symm (.inr q)=Sum.inr (1,1) := a.symm_apply_eq.mpr ha.2.symm
  rw [ha1,ha2,hb.1,hb.2]


def neighborEquiv (ν : Eˣ →* W) (p : E × W) : {q // relation ν p q} ≃ Eˣ where
  toFun q := Classical.choose q.property
  invFun z := ⟨((z : E)-p.1,ν z/p.2),z,by simp,by simp⟩
  left_inv q := by
    apply Subtype.ext
    have hz := (Classical.choose_spec q.property).1
    have hν := (Classical.choose_spec q.property).2
    apply Prod.ext
    · change ((Classical.choose q.property : Eˣ) : E)-p.1=q.1.1
      rw [hz]
      ring
    · change ν (Classical.choose q.property)/p.2=q.1.2
      rw [hν]
      simp
  right_inv z := by
    apply Units.ext
    exact (Classical.choose_spec
      (show relation ν p ((z : E)-p.1,ν z/p.2) from ⟨z,by simp,by simp⟩)).1.trans (by simp)

variable [Fintype E] [Fintype W]

lemma neighbor_card (ν : Eˣ →* W) (p : E × W) :
    (univ.filter (fun q => relation ν p q)).card=Fintype.card E-1 := by
  have h := Fintype.card_congr (neighborEquiv ν p)
  simpa only [Fintype.card_subtype,Fintype.card_units] using h

theorem edge_count (ν : Eˣ →* W) :
    (graph ν).edgeFinset.card=Fintype.card E*Fintype.card W*(Fintype.card E-1) := by
  have hg : graph ν=Erdos714Packing.incidence (fun p => univ.filter (fun q => relation ν p q)) := by
    ext p q
    cases p <;> cases q <;> simp [graph,Erdos714Tensor.incidence,Erdos714Packing.incidence]
  rw [hg,Erdos714Packing.incidence_edges]
  simp_rw [neighbor_card]
  simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_id]

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.affine_relation
#print axioms Erdos714WeightedPower.edge_transitive

#print axioms Erdos714WeightedPower.edge_count
