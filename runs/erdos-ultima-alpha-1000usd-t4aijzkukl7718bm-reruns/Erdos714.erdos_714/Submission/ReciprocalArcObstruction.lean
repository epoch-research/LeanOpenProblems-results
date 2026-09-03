import Submission.BinaryLift

/-!
A periodic-fiber obstruction to a reciprocal-trace arc code.
This does not prove or disprove the conjecture in Spec.lean.
-/

noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 1000000

namespace Erdos714ReciprocalArc

variable {G C : Type*} [Ring G] [CharP G 2]

/-- A translation code with its output value included in the column. -/
def code (f : G → C) : SimpleGraph (G ⊕ (G × C)) where
  Adj u v := match u,v with
    | .inl a, .inr b => f (a+b.1)=b.2
    | .inr b, .inl a => f (a+b.1)=b.2
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- Each output fiber embeds as an actual Cayley subgraph. -/
def fiberCopy (f : G → C) (c : C) :
    Copy (Erdos714BinaryLift.cayley {x | f x=c}) (code f) where
  toHom := {
    toFun := fun v => if v.1 then .inr (v.2,c) else .inl v.2
    map_rel' := by
      rintro ⟨a,x⟩ ⟨b,y⟩ h
      cases a <;> cases b <;>
        simp_all [Erdos714BinaryLift.cayley,code,add_comm] }
  injective' := by
    rintro ⟨a,x⟩ ⟨b,y⟩ h
    cases a <;> cases b <;> simp_all

/-- A nonzero period and a fiber larger than two create an affine binary plane. -/
theorem periodic_fiber_not_free (f : G → C) (d : G) (hd : d≠0)
    (hp : ∀ x, f (x+d)=f x) (c : C) (S : Finset G)
    (hS : ∀ x∈S, f x=c) (hc : 2<S.card) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (code f) := by
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<S.card)
  obtain ⟨y,hy,hyn⟩ := exists_mem_notMem_of_card_lt_card
    ((card_le_two (a := x) (b := x+d)).trans_lt hc)
  have hn : y≠x ∧ y≠x+d := by simpa using hyn
  have hv : x+y≠0 := fun h => hn.1 (CharTwo.add_eq_zero.mp h).symm
  have hdv : d≠x+y := by
    intro he
    apply hn.2
    rw [he]
    simp
  have hplane : ∀ i, f (x+Erdos714BinaryLift.plane d (x+y) i)=c := by
    intro i
    fin_cases i
    · simpa [Erdos714BinaryLift.plane] using hS x hx
    · simpa [Erdos714BinaryLift.plane,hp] using hS x hx
    · simpa [Erdos714BinaryLift.plane,add_assoc] using hS y hy
    · simpa [Erdos714BinaryLift.plane,add_assoc,add_left_comm,add_comm]
        using (hp y).trans (hS y hy)
  intro hfree
  apply Erdos714BinaryLift.not_free_of_plane {z | f z=c} hd hv hdv hplane
  rintro ⟨g⟩
  exact hfree ⟨(fiberCopy f c).comp g⟩

/-- Pigeonhole gives a uniform obstruction, with no assumed fiber balance. -/
theorem periodic_not_free [Fintype G] [Fintype C]
    (f : G → C) (d : G) (hd : d≠0) (hp : ∀ x, f (x+d)=f x)
    (hc : Fintype.card C*2<Fintype.card G) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (code f) := by
  obtain ⟨c,hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hc
  exact periodic_fiber_not_free f d hd hp c (univ.filter (fun x => f x=c))
    (fun x hx => (mem_filter.mp hx).2) hc

section Fields
variable {E I : Type*} [Field E] [CharP E 2]

/-- Only rows outside the quadratic fixed subfield are allowed. -/
abbrev Outside (K : Subfield E) := {a : E // a∉K}

/-- The outside-subfield restriction prevents every zero denominator. -/
lemma outside_add_ne_zero (K : Subfield E) (a : Outside K) (b : K) :
    a.1+(b : E)≠0 := by
  intro h
  exact a.property ((CharTwo.add_eq_zero.mp h).symm ▸ b.property)

/-- The actual reciprocal-trace code, with arbitrary coordinate vectors `X`. -/
def arcCode (K : Subfield E) (T : E → C) (X : I → E) :
    SimpleGraph (Outside K ⊕ (K × I × C)) where
  Adj u v := match u,v with
    | .inl a, .inr b => T (X b.2.1 / (a.1+(b.1 : E)))=b.2.2
    | .inr b, .inl a => T (X b.2.1 / (a.1+(b.1 : E)))=b.2.2
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- Every coordinate contains its full translation code on every outside coset. -/
def cosetCopy (K : Subfield E) (T : E → C) (X : I → E) (t : I)
    (a : E) (ha : a∉K) :
    Copy (code (fun u : K => T (X t / (a+(u : E))))) (arcCode K T X) := by
  let L (u : K) : Outside K := ⟨a+(u : E),by
    intro h
    apply ha
    have h' := K.sub_mem h u.property
    simpa using h'⟩
  let R (v : K × C) : K × I × C := (v.1,t,v.2)
  have hL : Function.Injective L := by
    intro u v h
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val h)
  have hR : Function.Injective R := by
    intro u v h
    apply Prod.ext
    · exact congrArg (fun w : K × I × C => w.1) h
    · exact congrArg (fun w : K × I × C => w.2.2) h
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact False.elim h
    | inr v =>
      change T (X t / ((a+(u : E))+(v.1 : E)))=v.2
      simpa only [code,Subfield.coe_add,add_assoc] using h
  | inr u =>
    cases v with
    | inl v =>
      change T (X t / ((a+(v : E))+(u.1 : E)))=u.2
      simpa only [code,Subfield.coe_add,add_assoc] using h
    | inr v => exact False.elim h

/-- Quadratic conjugation gives an exact additive period of the reciprocal trace.
The map `T` only needs conjugation invariance; additivity is unnecessary. -/
theorem reciprocal_period (K : Subfield E) (σ : E →+* E)
    (hσ : ∀ x, σ (σ x)=x) (hfix : ∀ x, x∈K ↔ σ x=x)
    (T : E → C) (hT : ∀ x, T (σ x)=T x) (a : E) (ha : a∉K) :
    ∃ d : K, d≠0 ∧ ∀ u : K,
      T ((a+((u+d : K) : E))⁻¹)=T ((a+(u : E))⁻¹) := by
  let d : K := ⟨σ a+a,(hfix _).mpr (by rw [map_add,hσ]; ac_rfl)⟩
  have hd : d≠0 := by
    intro he
    have he' : σ a+a=0 := congrArg Subtype.val he
    exact ha ((hfix a).mpr (CharTwo.add_eq_zero.mp he'))
  refine ⟨d,hd,?_⟩
  intro u
  have hu : σ (u : E)=(u : E) := (hfix _).mp u.property
  have he : a+((u+d : K) : E)=σ (a+(u : E)) := by
    rw [Subfield.coe_add,map_add,hu]
    change a+((u : E)+(σ a+a))=σ a+(u : E)
    simp [add_left_comm,add_comm]
  rw [he,←map_inv₀,hT]

/-- Uniform nonfreeness of the unfiltered reciprocal-arc construction. -/
theorem arc_not_free (K : Subfield E) [Fintype K] [Fintype C]
    (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x) (hfix : ∀ x, x∈K ↔ σ x=x)
    (T : E → C) (hT : ∀ x, T (σ x)=T x) (X : I → E)
    (t : I) (ht : σ (X t)=X t) (a : E) (ha : a∉K)
    (hc : Fintype.card C*2<Fintype.card K) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (arcCode K T X) := by
  let T' (v : E) : C := T (X t*v)
  have hT' (v : E) : T' (σ v)=T' v := by
    dsimp [T']
    rw [←ht,←map_mul,hT,ht]
  obtain ⟨d,hd,hp⟩ := reciprocal_period K σ hσ hfix T' hT' a ha
  have hp' : ∀ u : K, T (X t / (a+((u+d : K) : E)))=T (X t / (a+(u : E))) := by
    intro u
    simpa only [T',div_eq_mul_inv] using hp u
  have hn := periodic_not_free (fun u : K => T (X t / (a+(u : E)))) d hd hp' hc
  intro hf
  apply hn
  rintro ⟨g⟩
  exact hf ⟨(cosetCopy K T X t a ha).comp g⟩

/-- The target sizes satisfy the needed strict pigeonhole inequality once `q>2`. -/
theorem quadratic_scale_not_free (K : Subfield E) [Fintype K] [Fintype C]
    (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x) (hfix : ∀ x, x∈K ↔ σ x=x)
    (T : E → C) (hT : ∀ x, T (σ x)=T x) (X : I → E)
    (t : I) (ht : σ (X t)=X t) (a : E) (ha : a∉K)
    (q : ℕ) (hq : 2<q) (hK : Fintype.card K=q^2) (hC : Fintype.card C=q) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (arcCode K T X) := by
  apply arc_not_free K σ hσ hfix T hT X t ht a ha
  rw [hK,hC]
  nlinarith

/-- For the actual algebraic trace, conjugation invariance is automatic. -/
theorem algebra_trace_not_free {F : Type*} [Field F] [Fintype F] [Algebra F E]
    (K : Subfield E) [Fintype K] (σ : E ≃ₐ[F] E)
    (hσ : ∀ x, σ (σ x)=x) (hfix : ∀ x, x∈K ↔ σ x=x)
    (X : I → E) (t : I) (ht : σ (X t)=X t) (a : E) (ha : a∉K)
    (q : ℕ) (hq : 2<q) (hK : Fintype.card K=q^2) (hF : Fintype.card F=q) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (arcCode K (Algebra.trace F E) X) := by
  exact quadratic_scale_not_free K σ.toRingHom hσ hfix (Algebra.trace F E)
    (Algebra.trace_eq_of_algEquiv σ) X t ht a ha q hq hK hF


end Fields
end Erdos714ReciprocalArc

#print axioms Erdos714ReciprocalArc.periodic_fiber_not_free
#print axioms Erdos714ReciprocalArc.periodic_not_free
#print axioms Erdos714ReciprocalArc.cosetCopy
#print axioms Erdos714ReciprocalArc.reciprocal_period
#print axioms Erdos714ReciprocalArc.arc_not_free
#print axioms Erdos714ReciprocalArc.quadratic_scale_not_free

#print axioms Erdos714ReciprocalArc.outside_add_ne_zero
#print axioms Erdos714ReciprocalArc.algebra_trace_not_free
