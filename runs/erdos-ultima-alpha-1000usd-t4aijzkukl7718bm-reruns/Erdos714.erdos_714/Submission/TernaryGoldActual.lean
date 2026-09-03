import Submission.TernaryGoldAffinePlane

/-! Actual finite-field semantics for the trace-one filtered Gold-quartic obstruction. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714TernaryGoldActual
open Erdos714TernaryGoldPlane

lemma exists_eighth_root_neg_one {E : Type*} [Field E] [Fintype E] [CharP E 3]
    (hcard : Fintype.card E%16=1) (hlarge : 1<Fintype.card E) :
    ∃ u : E, u^8= -1 := by
  let N := Nat.card Eˣ
  have hN : N=Fintype.card E-1 := by simp [N,Nat.card_eq_fintype_card,Fintype.card_units]
  have hNpos : 0<N := by rw [hN]; omega
  have hdvd : 16∣N := by rw [hN]; apply Nat.dvd_of_mod_eq_zero; omega
  obtain ⟨g,hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Eˣ)).mp inferInstance
  have hp : IsPrimitiveRoot (g : E) N := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hg)
  obtain ⟨k,hk⟩ := hdvd
  have hroot : IsPrimitiveRoot ((g : E)^k) 16 := hp.pow hNpos (by omega)
  refine ⟨(g : E)^k,?_⟩
  have hh : (((g : E)^k)^8)^2=1^2 := by
    rw [← pow_mul]
    norm_num only [show 8*2=16 by decide,one_pow]
    exact hroot.pow_eq_one
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h | h
  · have hd := (hroot.pow_eq_one_iff_dvd 8).mp h
    norm_num at hd
  · exact h

variable {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
variable [CharP F 3] [Algebra F E]

/-- The graph is defined using the actual relative and absolute algebra traces. -/
def graph : SimpleGraph (E ⊕ E) := by
  letI : CharP E 3 := CharP.of_ringHom_of_ne_zero (algebraMap F E) 3 (by decide)
  letI := ZMod.algebra E 3
  exact
    { Adj := fun x y => match x,y with
        | .inl a,.inr b => Algebra.trace F E ((a+b)^4)=1 ∧ Algebra.trace (ZMod 3) E (a+b)=1
        | .inr b,.inl a => Algebra.trace F E ((a+b)^4)=1 ∧ Algebra.trace (ZMod 3) E (a+b)=1
        | _,_ => False
      symm := by intro x y; cases x <;> cases y <;> simp_all
      loopless := by intro x; cases x <;> simp }

/-- Uniformly in every odd-degree ternary base field and its quartic extension,
the asymmetric absolute-trace-one restriction still contains an actual K44. -/
theorem not_free (m : ℕ) (hodd : Odd m) (hcard : Fintype.card F=3^m)
    (hdegree : Module.finrank F E=4) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  letI : CharP E 3 := CharP.of_ringHom_of_ne_zero (algebraMap F E) 3 (by decide)
  letI := ZMod.algebra F 3
  letI := ZMod.algebra E 3
  letI : IsScalarTower (ZMod 3) F E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let τₐ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  let τ := τₐ.toRingHom
  let L := (Algebra.trace (ZMod 3) E).toAddMonoidHom
  have hτ (x : E) : τ x=x^(3^m) := by
    change τₐ x=x^(3^m)
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,hcard]
  have hL (x : E) : L (τ x)=L x :=
    Algebra.trace_eq_of_algEquiv (τₐ.restrictScalars (ZMod 3)) x
  have hmod4 : 3^m%4=3 := by
    obtain ⟨k,hk⟩ := hodd
    rw [hk,pow_add,pow_mul]
    norm_num [Nat.pow_mod,Nat.mul_mod]
  have hmod16 : (3^m)^2%16=9 := by
    obtain ⟨k,hk⟩ := hodd
    have he : (2*k+1)*2=4*k+2 := by omega
    rw [hk,← pow_mul,he,pow_add,pow_mul]
    norm_num [Nat.pow_mod,Nat.mul_mod]
  have hE : Fintype.card E=(3^m)^4 := by rw [Module.card_eq_pow_finrank (K := F) (V := E),hdegree,hcard]
  have hE16 : Fintype.card E%16=1 := by
    rw [hE,show (3^m)^4=(3^4)^m by rw [← pow_mul,← pow_mul,Nat.mul_comm]]
    norm_num [Nat.pow_mod]
  obtain ⟨u,hu8⟩ := exists_eighth_root_neg_one (E := E) hE16 (Fintype.one_lt_card (α := E))
  let i := u^4
  have hi : i^2= -1 := by dsimp [i]; rw [← pow_mul]; exact hu8
  have hu16 : u^16=1 := by
    calc
      _ = (u^8)^2 := by ring
      _ = 1 := by rw [hu8]; ring
  have hi4 : i^4=1 := by calc
    _ = (i^2)^2 := by ring
    _ = 1 := by rw [hi]; ring
  have hti : τ i= -i := by
    rw [hτ]
    conv_lhs => rw [← Nat.mod_add_div (3^m) 4]
    rw [pow_add,pow_mul,hi4,one_pow,mul_one,hmod4]
    calc
      i^3 = i^2*i := by ring
      _ = -i := by rw [hi]; ring
  have htu : τ (τ u)= -u := by
    rw [hτ,hτ,← pow_mul,← pow_two]
    conv_lhs => rw [← Nat.mod_add_div ((3^m)^2) 16]
    rw [pow_add,pow_mul,hu16,one_pow,mul_one,hmod16]
    calc
      u^9 = u^8*u := by ring
      _ = -u := by rw [hu8]; ring
  obtain ⟨a,b,hab,hLa⟩ := Erdos714QuarticCircleTrace.exists_actual_trace_one
    (F := F) (by rw [hcard]; exact hmod4)
  have hLa' : L (algebraMap F E a)=1 := by
    change Algebra.trace (ZMod 3) E (algebraMap F E a)=1
    rw [← Algebra.trace_trace (R := ZMod 3) (S := F),Algebra.trace_algebraMap,hdegree,map_nsmul,hLa]
    norm_num
    decide
  have hnot := not_free_four (algebraMap (ZMod 3) E) τ L hL hi (show u^4=i from rfl) hti htu
    (τₐ.commutes a) (τₐ.commutes b)
    (by simpa only [← map_pow,← map_add,map_one] using congrArg (algebraMap F E) hab) hLa'
  have ht (x : E) : algebraMap F E (Algebra.trace F E x)=trace4 τ x := by
    rw [FiniteField.algebraMap_trace_eq_sum_pow,hdegree]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.card_eq_fintype_card,hcard,
      trace4,hτ,← pow_mul]
    ring_nf
  have he : graph (F := F) (E := E)=Erdos714TernaryGoldPlane.graph τ L := by
    ext x y
    cases x <;> cases y
    · rfl
    · change (Algebra.trace F E ((_+_)^4)=1 ∧ _) ↔ (trace4 τ ((_+_)^4)=1 ∧ _)
      rw [← ht]
      simp only [← map_one (algebraMap F E),(algebraMap F E).injective.eq_iff]
      rfl
    · change (Algebra.trace F E ((_+_)^4)=1 ∧ _) ↔ (trace4 τ ((_+_)^4)=1 ∧ _)
      rw [← ht]
      simp only [← map_one (algebraMap F E),(algebraMap F E).injective.eq_iff]
      rfl
    · rfl
  rwa [he]

#print axioms exists_eighth_root_neg_one
#print axioms not_free
end Erdos714TernaryGoldActual
