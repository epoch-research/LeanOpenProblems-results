import Submission.LabelledSumGraphs

/-!
Exact counts for a ratio-filtered weighted norm graph. The filter may take
values in a fixed finite alphabet, rather than the norm's growing base field.
These are counting and parametrization results, not graph-freeness claims.
-/
noncomputable section
open SimpleGraph Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714RatioFilteredNorm
variable {E F K : Type*} [Field E] [Field F]

abbrev Vertex (E F : Type*) [Field E] [Field F] := Eˣ × Fˣ

/-- The sum is a genuine nonzero element. The labels may be the actual norm
on units; the counting argument only needs its multiplicative homomorphism. -/
def Rel (ν : Eˣ →* Fˣ) (θ : E → K) (γ : K) (p q : Vertex E F) : Prop :=
  ∃ z : Eˣ, (z:E)=(p.1:E)+(q.1:E) ∧ ν z=p.2*q.2 ∧ θ ((p.1:E)/(z:E))=γ

def graph (ν : Eˣ →* Fˣ) (θ : E → K) (γ : K) :
    SimpleGraph (Vertex E F ⊕ Vertex E F) := Erdos714Tensor.incidence (Rel ν θ γ)

variable (ν : Eˣ →* Fˣ) (θ : E → K) (γ : K)
variable (h₀ : θ 0 ≠ γ) (h₁ : θ 1 ≠ γ)
include h₀ h₁

lemma parameter_ne (t : {t : E // θ t=γ}) : (t:E) ≠ 0 ∧ (t:E) ≠ 1 := by
  constructor
  · intro h; exact h₀ (h ▸ t.property)
  · intro h; exact h₁ (h ▸ t.property)

def next (p : Vertex E F) (t : {t : E // θ t=γ}) : Vertex E F :=
  let u := Units.mk0 (t:E) (parameter_ne θ γ h₀ h₁ t).1
  let v := Units.mk0 (1-(t:E)) (sub_ne_zero.mpr (Ne.symm (parameter_ne θ γ h₀ h₁ t).2))
  (p.1*v/u, ν (p.1/u)/p.2)

lemma next_sum (p : Vertex E F) (t : {t : E // θ t=γ}) :
    (p.1:E)+((next ν θ γ h₀ h₁ p t).1:E)=(p.1:E)/(t:E) := by
  dsimp only [next]
  simp only [Units.val_div_eq_div_val,Units.val_mul,Units.val_mk0]
  field_simp [(parameter_ne θ γ h₀ h₁ t).1]
  ring

lemma parameter_recover (p : Vertex E F) (t : {t : E // θ t=γ}) :
    (p.1:E)/((p.1:E)+((next ν θ γ h₀ h₁ p t).1:E))=(t:E) := by
  rw [next_sum]
  field_simp [p.1.ne_zero,(parameter_ne θ γ h₀ h₁ t).1]

lemma next_injective (p : Vertex E F) : Function.Injective (next ν θ γ h₀ h₁ p) := by
  intro t u h
  apply Subtype.ext
  rw [← parameter_recover ν θ γ h₀ h₁ p t,h,parameter_recover]

lemma next_rel (p : Vertex E F) (t : {t : E // θ t=γ}) :
    Rel ν θ γ p (next ν θ γ h₀ h₁ p t) := by
  let u := Units.mk0 (t:E) (parameter_ne θ γ h₀ h₁ t).1
  refine ⟨p.1/u,?_,?_,?_⟩
  · simpa only [u,Units.val_div_eq_div_val,Units.val_mk0] using
      (next_sum ν θ γ h₀ h₁ p t).symm
  · change ν (p.1/u)=p.2*(ν (p.1/u)/p.2)
    simp [div_eq_mul_inv,mul_comm]
  · simp only [Units.val_div_eq_div_val,u,Units.val_mk0]
    change θ ((p.1:E)/((p.1:E)/(t:E)))=γ
    have he : (p.1:E)/((p.1:E)/(t:E))=(t:E) := by
      field_simp [p.1.ne_zero,(parameter_ne θ γ h₀ h₁ t).1]
    rw [he]
    exact t.property

lemma exists_next (p q : Vertex E F) (h : Rel ν θ γ p q) :
    ∃ t : {t : E // θ t=γ}, next ν θ γ h₀ h₁ p t=q := by
  obtain ⟨z,hz,hw,ht⟩ := h
  let t : {t : E // θ t=γ} := ⟨(p.1:E)/(z:E),ht⟩
  let u := Units.mk0 (t:E) (parameter_ne θ γ h₀ h₁ t).1
  have he : p.1/u=z := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val,u,Units.val_mk0]
    change (p.1:E)/((p.1:E)/(z:E))=(z:E)
    field_simp [p.1.ne_zero,z.ne_zero]
  refine ⟨t,Prod.ext ?_ ?_⟩
  · apply Units.ext
    have hs := next_sum ν θ γ h₀ h₁ p t
    have hv : (p.1:E)/(t:E)=(z:E) := by
      simpa only [u,Units.val_div_eq_div_val,Units.val_mk0] using
        congrArg (fun z : Eˣ => (z:E)) he
    rw [hv,hz] at hs
    exact add_left_cancel hs
  · change ν (p.1/u)/p.2=q.2
    rw [he,hw]
    simp [div_eq_mul_inv,mul_assoc]

/-- Every permitted ratio gives exactly one neighbor, and every neighbor is
obtained. Neither surjectivity of the norm nor any generic-rank claim is used. -/
def neighborEquiv (p : Vertex E F) : {t : E // θ t=γ} ≃ {q // Rel ν θ γ p q} :=
  Equiv.ofBijective (fun t => ⟨next ν θ γ h₀ h₁ p t,next_rel ν θ γ h₀ h₁ p t⟩) (by
    constructor
    · intro t u h
      exact next_injective ν θ γ h₀ h₁ p (congrArg Subtype.val h)
    · rintro ⟨q,hq⟩
      obtain ⟨t,ht⟩ := exists_next ν θ γ h₀ h₁ p q hq
      exact ⟨t,Subtype.ext ht⟩)

variable [Fintype E] [Fintype F]

lemma neighbor_card (p : Vertex E F) :
    (univ.filter (Rel ν θ γ p)).card=Fintype.card {t : E // θ t=γ} := by
  have h := (Fintype.card_congr (neighborEquiv ν θ γ h₀ h₁ p)).symm
  simpa only [Fintype.card_subtype] using h

/-- The number of vertices on one side and the fiber size give the exact
unordered edge count of the actual bipartite relation. -/
theorem edge_count :
    (graph ν θ γ).edgeFinset.card=
      (Fintype.card E-1)*(Fintype.card F-1)*Fintype.card {t : E // θ t=γ} := by
  have hg : graph ν θ γ=Erdos714Packing.incidence
      (fun p => univ.filter (Rel ν θ γ p)) := by
    ext p q
    cases p <;> cases q <;>
      simp [graph,Erdos714Tensor.incidence,Erdos714Packing.incidence]
  rw [hg,Erdos714Packing.incidence_edges]
  simp_rw [neighbor_card ν θ γ h₀ h₁]
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_units,nsmul_eq_mul,Nat.cast_id]

omit h₀ h₁ in
/-- All fibers of a surjective additive map have the same size. -/
theorem fiber_card [AddGroup K] [Fintype K] (T : E →+ K)
    (hT : Function.Surjective T) (γ : K) :
    Fintype.card K*Fintype.card {t : E // T t=γ}=Fintype.card E := by
  have hf (a : K) : Fintype.card {t : E // T t=a}=
      Fintype.card {t : E // T t=γ} :=
    Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hT a γ)
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv T)
  rw [Fintype.card_sigma] at h
  simp_rw [hf] at h
  simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] using h

omit h₀ h₁ in
/-- Fixed-alphabet additive filtering has an exact, constant edge-density
cost. This says nothing about biclique freeness. -/
theorem additive_edge_count [AddGroup K] [Fintype K] (T : E →+ K)
    (hT : Function.Surjective T) (γ : K) (hT₀ : T 0 ≠ γ) (hT₁ : T 1 ≠ γ) :
    Fintype.card K*(graph ν T γ).edgeFinset.card=
      (Fintype.card E-1)*(Fintype.card F-1)*Fintype.card E := by
  rw [edge_count ν T γ hT₀ hT₁]
  calc
    _ = (Fintype.card E-1)*(Fintype.card F-1)*
        (Fintype.card K*Fintype.card {t : E // T t=γ}) := by ring
    _ = _ := by rw [fiber_card T hT γ]

omit h₀ h₁ [Fintype F] in
/-- The norm-on-units relation is exactly the original field-norm equation,
not merely a label surrogate. -/
theorem norm_rel_iff [Algebra F E] (p q : Vertex E F) :
    Rel (Units.map (Algebra.norm F)) θ γ p q ↔
      Algebra.norm F ((p.1:E)+(q.1:E))=(p.2:F)*(q.2:F) ∧
        θ ((p.1:E)/((p.1:E)+(q.1:E)))=γ := by
  constructor
  · rintro ⟨z,hz,hw,ht⟩
    have hn := congrArg (fun a : Fˣ => (a:F)) hw
    change Algebra.norm F (z:E)=(p.2:F)*(q.2:F) at hn
    rw [hz] at hn ht
    exact ⟨hn,ht⟩
  · rintro ⟨hn,ht⟩
    have hs : (p.1:E)+(q.1:E) ≠ 0 := Algebra.norm_ne_zero_iff.mp (by
      rw [hn]
      exact mul_ne_zero p.2.ne_zero q.2.ne_zero)
    refine ⟨Units.mk0 _ hs,rfl,?_,ht⟩
    apply Units.ext
    exact hn

omit h₀ h₁ in
/-- The two base fields need not be nested: E can have a growing norm base F
and a fixed trace alphabet K. The actual trace is surjective. -/
theorem norm_trace_edge_count [Field K] [Fintype K] [Algebra F E] [Algebra K E]
    (γ : K) (hγ₀ : γ ≠ 0) (hγ₁ : γ ≠ Algebra.trace K E 1) :
    Fintype.card K*(graph (Units.map (Algebra.norm F)) (Algebra.trace K E) γ).edgeFinset.card=
      (Fintype.card E-1)*(Fintype.card F-1)*Fintype.card E := by
  apply additive_edge_count (Units.map (Algebra.norm F))
    (Algebra.trace K E).toAddMonoidHom (Algebra.trace_surjective K E) γ
  · simpa using Ne.symm hγ₀
  · exact Ne.symm hγ₁

end Erdos714RatioFilteredNorm
#print axioms Erdos714RatioFilteredNorm.next_rel
#print axioms Erdos714RatioFilteredNorm.neighborEquiv
#print axioms Erdos714RatioFilteredNorm.edge_count

#print axioms Erdos714RatioFilteredNorm.fiber_card
#print axioms Erdos714RatioFilteredNorm.norm_rel_iff
#print axioms Erdos714RatioFilteredNorm.norm_trace_edge_count
