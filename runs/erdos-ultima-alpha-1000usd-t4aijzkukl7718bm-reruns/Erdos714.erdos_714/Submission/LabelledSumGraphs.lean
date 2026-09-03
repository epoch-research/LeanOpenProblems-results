import Submission.BicliquePartition

/-!
Weighted sum graphs need neither commutative labels nor a multiplicative
label map for their exact degrees and counts. We assume only that left
multiplication on labels is a permutation. A compatible subfield/label
embedding transfers actual graph copies. These are conditional construction
tools, not a solution of Erdős 714.
-/
noncomputable section
open SimpleGraph Classical Finset
namespace Erdos714LabelledSums
variable {E W : Type*} [Field E]

def Rel (ν : Eˣ → W) (m : W → Equiv W W) (p q : E × W) : Prop :=
  ∃ z : Eˣ, (z : E)=p.1+q.1 ∧ ν z=m p.2 q.2

def graph (ν : Eˣ → W) (m : W → Equiv W W) :
    SimpleGraph ((E × W) ⊕ (E × W)) := Erdos714Tensor.incidence (Rel ν m)

/-- The edge-sum parameter determines exactly one opposite vertex. -/
def neighborEquiv (ν : Eˣ → W) (m : W → Equiv W W) (p : E × W) :
    {q // Rel ν m p q} ≃ Eˣ where
  toFun q := Classical.choose q.property
  invFun z := ⟨((z:E)-p.1,(m p.2).symm (ν z)),z,by simp,by simp⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · change ((Classical.choose q.property : Eˣ) : E)-p.1=q.val.1
      rw [(Classical.choose_spec q.property).1]
      ring
    · exact (m p.2).symm_apply_eq.mpr (Classical.choose_spec q.property).2
  right_inv z := by
    apply Units.ext
    exact (Classical.choose_spec
      (show Rel ν m p ((z:E)-p.1,(m p.2).symm (ν z)) from
        ⟨z,by simp,by simp⟩)).1.trans (by simp)

variable [Fintype E] [Fintype W]

lemma neighbor_card (ν : Eˣ → W) (m : W → Equiv W W) (p : E × W) :
    (univ.filter (fun q => Rel ν m p q)).card=Fintype.card E-1 := by
  have h := Fintype.card_congr (neighborEquiv ν m p)
  simpa only [Fintype.card_subtype,Fintype.card_units] using h

/-- No surjectivity, associativity or multiplicativity hypothesis is omitted:
none is necessary for this count. -/
theorem edge_count (ν : Eˣ → W) (m : W → Equiv W W) :
    (graph ν m).edgeFinset.card=Fintype.card E*Fintype.card W*(Fintype.card E-1) := by
  have hg : graph ν m=Erdos714Packing.incidence
      (fun p => univ.filter (fun q => Rel ν m p q)) := by
    ext p q
    cases p <;> cases q <;>
      simp [graph,Erdos714Tensor.incidence,Erdos714Packing.incidence]
  rw [hg,Erdos714Packing.incidence_edges]
  simp_rw [neighbor_card]
  simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_id]

end Erdos714LabelledSums

namespace Erdos714LabelledSums
variable {K E U W : Type*} [Field K] [Field E]

/-- A compatible map of points and labels embeds the entire smaller graph.
The statement makes no assumption that the two label operations commute. -/
def subfieldCopy (ν : Kˣ → U) (m : U → Equiv U U)
    (μ : Eˣ → W) (n : W → Equiv W W)
    (f : K →+* E) (τ : U ↪ W)
    (hν : ∀ z, μ (Units.map f.toMonoidHom z)=τ (ν z))
    (hm : ∀ a b, τ (m a b)=n (τ a) (τ b)) :
    (graph ν m).Copy (graph μ n) := by
  let e : K × U ↪ E × W := ⟨fun p => (f p.1,τ p.2),by
    intro p q hpq
    exact Prod.ext (f.injective (congrArg Prod.fst hpq))
      (τ.injective (congrArg Prod.snd hpq))⟩
  have he (p q : K × U) (h : Rel ν m p q) : Rel μ n (e p) (e q) := by
    obtain ⟨z,hz,hh⟩ := h
    refine ⟨Units.map f.toMonoidHom z,?_,?_⟩
    · change f (z:K)=f p.1+f q.1
      rw [hz,map_add]
    · change μ (Units.map f.toMonoidHom z)=n (τ p.2) (τ q.2)
      rw [hν,hh,hm]
  refine ⟨⟨e.sumMap e,?_⟩,(e.sumMap e).injective⟩
  intro p q hpq
  cases p with
  | inl p =>
    cases q with
    | inl q => exact False.elim hpq
    | inr q => exact he p q hpq
  | inr p =>
    cases q with
    | inl q => exact he q p hpq
    | inr q => exact False.elim hpq

/-- Thus an actual biclique in the compatible smaller model transfers. -/
theorem not_free_of_subfield {r s : ℕ}
    (ν : Kˣ → U) (m : U → Equiv U U)
    (μ : Eˣ → W) (n : W → Equiv W W)
    (f : K →+* E) (τ : U ↪ W)
    (hν : ∀ z, μ (Units.map f.toMonoidHom z)=τ (ν z))
    (hm : ∀ a b, τ (m a b)=n (τ a) (τ b))
    (hf : ¬ (completeBipartiteGraph (Fin r) (Fin s)).Free (graph ν m)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin s)).Free (graph μ n) := by
  intro hfree
  apply hf
  rintro ⟨C⟩
  exact hfree ⟨(subfieldCopy ν m μ n f τ hν hm).comp C⟩

end Erdos714LabelledSums
#print axioms Erdos714LabelledSums.neighborEquiv
#print axioms Erdos714LabelledSums.edge_count
#print axioms Erdos714LabelledSums.subfieldCopy
#print axioms Erdos714LabelledSums.not_free_of_subfield
