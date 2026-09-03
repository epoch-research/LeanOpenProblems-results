import Submission.ProfiledTranslation

/-! The full cubic norm-product additive model fails over every finite binary
base field. Arbitrary edge thinnings are not addressed. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000

namespace Erdos714NormProductAdditive
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- A lower bound suffices, without computing an explicit norm-one element. -/
lemma norm_one_large (hE : Fintype.card E=Fintype.card F^3) :
    Fintype.card F^2 < (univ.filter (fun x : E => Algebra.norm F x=1)).card := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hc : Fintype.card Fˣ*q^2 < Fintype.card Eˣ := by
    simp only [Fintype.card_units,hE]
    change (q-1)*q^2 < q^3-1
    have h1 : q-1+1=q := Nat.sub_add_cancel (by omega)
    have h3 : q^3-1+1=q^3 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
    nlinarith [congrArg (fun x : ℕ => x*q^2) h1]
  let f := Units.map (Algebra.norm F (S := E))
  obtain ⟨c,hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hc
  have he : (univ.filter (fun x => f x=c)).card =
      (univ.filter (fun x => f x=1)).card :=
    MonoidHom.card_fiber_eq_of_mem_range f
      (FiniteField.unitsMap_norm_surjective F E c) ⟨1,map_one f⟩
  rw [he] at hc
  refine hc.trans_le (card_le_card_of_injOn (fun x : Eˣ => (x : E)) ?_ ?_)
  · intro x hx
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    exact congrArg (fun u : Fˣ => (u : F)) (mem_filter.mp hx).2
  · intro x _ y _ h
    exact Units.ext h

variable [CharP E 2]

def graph : SimpleGraph ((E × F) ⊕ (E × F)) :=
  Erdos714ProfiledTranslation.graph (Algebra.norm F)
    (fun c z => c*Algebra.norm F z)

omit [Field F] [Field E] [Algebra F E] [CharP E 2] in
lemma vertex_count (hE : Fintype.card E=Fintype.card F^3) :
    Fintype.card ((E × F) ⊕ (E × F))=2*Fintype.card F^4 := by
  simp only [Fintype.card_sum,Fintype.card_prod,hE]
  ring

omit [CharP E 2] in
lemma edge_count (hE : Fintype.card E=Fintype.card F^3) :
    (graph (F := F) (E := E)).edgeFinset.card=Fintype.card F^7 := by
  rw [graph,Erdos714ProfiledTranslation.edge_count,hE]
  ring

/-- Every finite binary cubic extension fails, including q=2. The row-profile
fiber bound is applied to the actual algebraic norm. -/
theorem not_free (hE : Fintype.card E=Fintype.card F^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  intro hfree
  let q := Fintype.card F
  let m := (univ.filter (fun x : E => Algebra.norm F x=1)).card
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hm : q^2 < m := norm_one_large hE
  have hb := Erdos714ProfiledTranslation.fiber_bound (Algebra.norm F)
    (fun c z => c*Algebra.norm F z) hfree 1
  change m*(m-1) ≤ 2*Fintype.card E at hb
  rw [hE] at hb
  change m*(m-1) ≤ 2*q^3 at hb
  have hmprod : (q^2+1)*q^2 ≤ m*(m-1) := Nat.mul_le_mul (by omega) (by omega)
  have hlt : 2*q^3 < (q^2+1)*q^2 := by
    nlinarith [Nat.mul_le_mul_left (q^2) (show 2*q ≤ q^2 by nlinarith)]
  omega

end Erdos714NormProductAdditive
#print axioms Erdos714NormProductAdditive.norm_one_large
#print axioms Erdos714NormProductAdditive.not_free

#print axioms Erdos714NormProductAdditive.vertex_count
#print axioms Erdos714NormProductAdditive.edge_count
