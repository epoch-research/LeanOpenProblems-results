import Submission.EvaluationInterchange

/-!
Reciprocal evaluation and commutator covers of arbitrary finite group actions
cannot attain the fourth-case exponent when the acted-on set grows. The bound
allows arbitrary edge thinnings. This does not settle Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Finset

namespace Erdos714ReciprocalAction

variable {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω]

/-- Edges exchange the two evaluation points. -/
abbrev graph : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)) :=
  Erdos714EvaluationInterchange.graph (fun g x => g • x) (fun h y => h • y)

/-- Every nonempty transporter fiber is a translate of the actual stabilizer. -/
def transporterEquiv (x y : Ω) (g : Γ) (hg : g • x = y) :
    {h : Γ // h • x = y} ≃ MulAction.stabilizer Γ x where
  toFun h := ⟨g⁻¹*h.val, by
    change (g⁻¹*h.val) • x = x
    rw [mul_smul, h.property, ←hg, inv_smul_smul]⟩
  invFun h := ⟨g*h.val, by
    rw [mul_smul, h.property, hg]⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv h := by apply Subtype.ext; simp

/-- The permutation cover with voltage `h⁻¹g⁻¹hg`. This convention is stated
explicitly so that the identification does not depend on commutator notation. -/
def commutatorGraph : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)) where
  Adj p q := match p,q with
    | .inl x,.inr y => y.2 = (y.1⁻¹*x.1⁻¹*y.1*x.1) • x.2
    | .inr y,.inl x => y.2 = (y.1⁻¹*x.1⁻¹*y.1*x.1) • x.2
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

def sheetGauge : Γ × Ω ≃ Γ × Ω where
  toFun p := (p.1,p.1 • p.2)
  invFun p := (p.1,p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp

lemma action_equation (g h : Γ) (a b : Ω) :
    g • (h • b) = h • (g • a) ↔ b = (h⁻¹*g⁻¹*h*g) • a := by
  constructor
  · intro he
    have hh := congrArg (fun x => h⁻¹ • (g⁻¹ • x)) he
    simpa only [inv_smul_smul, mul_smul] using hh
  · intro he
    rw [he]
    simp only [mul_smul, smul_inv_smul]

/-- This isomorphism includes all sheets and all actual graph edges. -/
def commutatorIso : commutatorGraph (Γ := Γ) (Ω := Ω) ≃g graph (Γ := Γ) (Ω := Ω) where
  toEquiv := sheetGauge.sumCongr sheetGauge
  map_rel_iff' := by
    intro p q
    cases p with
    | inl p =>
      cases q with
      | inl q => rfl
      | inr q => exact action_equation p.1 q.1 p.2 q.2
    | inr p =>
      cases q with
      | inl q => exact action_equation q.1 p.1 q.2 p.2
      | inr q => rfl

variable [Fintype Γ] [Fintype Ω]

omit [Fintype Ω] in
lemma transporter_card (x y : Ω) (h : ∃ g : Γ, g • x = y) :
    Fintype.card {g : Γ // g • x = y} = Fintype.card (MulAction.stabilizer Γ x) := by
  obtain ⟨g,hg⟩ := h
  exact Fintype.card_congr (transporterEquiv x y g hg)

/-- Orbit-stabilizer gives this bound without transitivity or faithfulness. -/
lemma group_card_bound (x : Ω) :
    Fintype.card Γ ≤ Fintype.card Ω * Fintype.card (MulAction.stabilizer Γ x) := by
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Γ x]
  exact Nat.mul_le_mul_right _
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)

lemma neighbor_card (p : Γ × Ω) :
    (univ.filter (fun q : Γ × Ω => p.1 • q.2 = q.1 • p.2)).card = Fintype.card Γ := by
  rw [←card_univ (α := Γ)]
  apply card_bij (fun q _ => q.1)
  · intro q hq
    exact mem_univ _
  · intro q hq r hr he
    have hq' := (mem_filter.mp hq).2
    have hr' := (mem_filter.mp hr).2
    rw [he] at hq'
    have hh := congrArg (fun x => p.1⁻¹ • x) (hq'.trans hr'.symm)
    exact Prod.ext he (by simpa using hh)
  · intro g hg
    refine ⟨(g,p.1⁻¹ • (g • p.2)), ?_, rfl⟩
    simp

/-- Every left vertex has exactly |Γ| neighbors, even for nontransitive actions. -/
theorem edges : (graph (Γ := Γ) (Ω := Ω)).edgeFinset.card = Fintype.card Γ ^ 2 * Fintype.card Ω := by
  have he : graph (Γ := Γ) (Ω := Ω) = Erdos714Packing.incidence
      (fun p : Γ × Ω => univ.filter (fun q : Γ × Ω => p.1 • q.2 = q.1 • p.2)) := by
    ext p q
    cases p <;> cases q <;> simp [graph, Erdos714EvaluationInterchange.graph, Erdos714Packing.incidence]
  rw [he, Erdos714Packing.incidence_edges]
  simp_rw [neighbor_card]
  simp only [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  ring

variable [Nonempty Ω]

/-- Uniform absolute bound, stronger than merely a relative-density obstruction.
The action need not be transitive or faithful. -/
theorem fourth_power_bound (H : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)))
    (hHG : H ≤ graph)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card ^ 4 ≤ 10368 * Fintype.card Γ ^ 7 * Fintype.card Ω ^ 5 := by
  obtain ⟨x,hx,hmin⟩ := exists_min_image (univ : Finset Ω)
    (fun x => Fintype.card (MulAction.stabilizer Γ x)) univ_nonempty
  let t := Fintype.card (MulAction.stabilizer Γ x)
  have ht (x' y : Ω) (h : ∃ g : Γ, g • x' = y) :
      t ≤ Fintype.card {g : Γ // g • x' = y} := by
    rw [transporter_card x' y h]
    exact hmin x' (mem_univ _)
  have hlocal := Erdos714EvaluationInterchange.fourth_density_bound
    (fun g : Γ => fun x : Ω => g • x) (fun g : Γ => fun x : Ω => g • x)
    H t ht ht hHG hfree
  change t * H.edgeFinset.card ^ 4 ≤ 10368 * (graph (Γ := Γ) (Ω := Ω)).edgeFinset.card ^ 4 at hlocal
  rw [edges] at hlocal
  have hcard : Fintype.card Γ ≤ Fintype.card Ω*t := group_card_bound x
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card Γ) ?_ (Fintype.card_pos)
  calc
    Fintype.card Γ * H.edgeFinset.card ^ 4 ≤
        (Fintype.card Ω*t)*H.edgeFinset.card ^ 4 := Nat.mul_le_mul_right _ hcard
    _ = Fintype.card Ω * (t*H.edgeFinset.card ^ 4) := by ring
    _ ≤ Fintype.card Ω * (10368*(Fintype.card Γ ^ 2 * Fintype.card Ω)^4) :=
      Nat.mul_le_mul_left _ hlocal
    _ = _ := by ring

/-- Relative to the actual total vertex count n, the loss is |Ω|^(1/2). -/
theorem normalized_bound (H : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)))
    (hHG : H ≤ graph)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card Ω ^ 2 * H.edgeFinset.card ^ 4 ≤
      81 * Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7 := by
  calc
    _ ≤ Fintype.card Ω ^ 2 * (10368 * Fintype.card Γ ^ 7 * Fintype.card Ω ^ 5) :=
      Nat.mul_le_mul_left _ (fourth_power_bound H hHG hfree)
    _ = _ := by simp only [Fintype.card_sum, Fintype.card_prod]; ring

/-- Any fixed fourth-power lower-bound constant bounds the action-set size.
Thus an unbounded sequence of action sets cannot yield the conjectured scale. -/
theorem critical_scale_budget (H : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)))
    (hHG : H ≤ graph)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (he : Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7 ≤ K*H.edgeFinset.card ^ 4) :
    Fintype.card Ω ^ 2 ≤ 81*K := by
  have hN : 0 < Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7 := pow_pos Fintype.card_pos 7
  apply Nat.le_of_mul_le_mul_right (c := Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7) ?_ hN
  calc
    _ ≤ Fintype.card Ω ^ 2 * (K*H.edgeFinset.card ^ 4) := Nat.mul_le_mul_left _ he
    _ = K*(Fintype.card Ω ^ 2 * H.edgeFinset.card ^ 4) := by ring
    _ ≤ K*(81*Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7) :=
      Nat.mul_le_mul_left _ (normalized_bound H hHG hfree)
    _ = _ := by ring

/-- The same absolute loss applies to arbitrary edge thinnings of commutator
permutation covers, not just to their full edge sets. -/
theorem commutator_normalized_bound (H : SimpleGraph ((Γ × Ω) ⊕ (Γ × Ω)))
    (hHG : H ≤ commutatorGraph)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card Ω ^ 2 * H.edgeFinset.card ^ 4 ≤
      81 * Fintype.card ((Γ × Ω) ⊕ (Γ × Ω)) ^ 7 := by
  let e := commutatorIso (Γ := Γ) (Ω := Ω)
  let K := H.comap e.symm
  have hK : K ≤ graph := by
    intro p q hpq
    have he := e.toHom.map_adj (hHG hpq)
    change graph.Adj (e.toEquiv (e.toEquiv.symm p)) (e.toEquiv (e.toEquiv.symm q)) at he
    simpa only [Equiv.apply_symm_apply] using he
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free K :=
    Erdos714GraphAveraging.free_comap _ H e.symm.toEquiv.toEmbedding hfree
  let iso : K ≃g H := ⟨e.symm.toEquiv,Iff.rfl⟩
  have hb := normalized_bound K hK hf
  rw [iso.card_edgeFinset_eq] at hb
  exact hb

#print axioms commutatorIso
#print axioms commutator_normalized_bound

#print axioms transporterEquiv
#print axioms group_card_bound
#print axioms edges
#print axioms fourth_power_bound
#print axioms normalized_bound
#print axioms critical_scale_budget

end Erdos714ReciprocalAction
