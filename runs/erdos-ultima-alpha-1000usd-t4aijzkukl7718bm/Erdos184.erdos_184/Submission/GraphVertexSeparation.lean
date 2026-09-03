import Submission.GraphCircuitCode
import Submission.CircuitSeparation

/-! A one-vertex interface separates graphical circuit codes. Cycle numbers
add across it; even minimality and cycle rigidity factor independently.
No assertion about arbitrary minimal cores is made. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphVertexSeparation
open Critical EvenCore Rigidity GraphCircuitCode Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two supports may meet only at the specified vertex. -/
def TouchAt (A B : SimpleGraph V) (v : V) : Prop :=
  ∀ x, x ∈ A.support → x ∈ B.support → x = v

lemma TouchAt.symm {A B : SimpleGraph V} {v : V} (h : TouchAt A B v) : TouchAt B A v :=
  fun x hx hy => h x hy hx

lemma TouchAt.edge_disjoint {A B : SimpleGraph V} {v : V} (h : TouchAt A B v) :
    Disjoint A.edgeSet B.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heA heB
  induction e using Sym2.ind with | h x y =>
    have hxyA : A.Adj x y := heA
    have hxyB : B.Adj x y := heB
    have hx := h x ⟨y,hxyA⟩ ⟨y,hxyB⟩
    have hy := h y ⟨x,hxyA.symm⟩ ⟨x,hxyB.symm⟩
    exact hxyA.ne (hx.trans hy.symm)

lemma inf_bot_of_edge_disjoint {A B : SimpleGraph V} (h : Disjoint A.edgeSet B.edgeSet) :
    A ⊓ B = ⊥ := by
  apply SimpleGraph.edgeSet_injective
  rw [SimpleGraph.edgeSet_inf,Set.disjoint_iff_inter_eq_empty.mp h]
  simp

lemma even_sup_of_disjoint {A B : SimpleGraph V}
    (h : Disjoint A.edgeSet B.edgeSet)
    (hA : ∀ x, Even (A.degree x)) (hB : ∀ x, Even (B.degree x)) :
    ∀ x, Even ((A ⊔ B).degree x) := by
  intro x
  have hd := Vertex.degree_sup_inf A B x
  have he := (hA x).add (hB x)
  have hb := inf_bot_of_edge_disjoint h
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd he ⊢
  rw [hb] at hd
  have hd' : Nat.card ((A ⊔ B).neighborSet x) = Nat.card (A.neighborSet x) + Nat.card (B.neighborSet x) := by
    simpa [SimpleGraph.neighborSet] using hd
  rw [hd']
  exact he

lemma even_at_of_even_elsewhere (R : SimpleGraph V) (v : V)
    (h : ∀ x, x ≠ v → Even (R.degree x)) : Even (R.degree v) := by
  by_contra hv
  obtain ⟨w,hw,ho⟩ := R.exists_ne_odd_degree_of_exists_odd_degree v (Nat.not_even_iff_odd.mp hv)
  have he := Nat.even_iff.mp (h w hw)
  have ho' := Nat.odd_iff.mp ho
  omega

lemma inf_even {A B R : SimpleGraph V} {v : V} (h : TouchAt A B v)
    (hR : R ≤ A ⊔ B) (he : ∀ x, Even (R.degree x)) :
    ∀ x, Even ((R ⊓ A).degree x) := by
  have hother (x : V) (hxv : x ≠ v) : Even ((R ⊓ A).degree x) := by
    by_cases hxA : x ∈ A.support
    · have hxB : x ∉ B.support := fun hb => hxv (h x hxA hb)
      have hN : (R ⊓ A).neighborSet x = R.neighborSet x := by
        ext y
        constructor
        · exact fun hy => hy.1
        · intro hy
          refine ⟨hy,?_⟩
          rcases hR hy with hA | hB
          · exact hA
          · exact (hxB ⟨y,hB⟩).elim
      have hv := he x
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv ⊢
      rw [hN]
      exact hv
    · have hz : (R ⊓ A).degree x = 0 :=
        (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
          (fun hx => hxA (SimpleGraph.support_mono inf_le_right hx))
      rw [hz]
      exact ⟨0,rfl⟩
  intro x
  by_cases hx : x = v
  · subst x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      even_at_of_even_elsewhere (R ⊓ A) v (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hother)
  · exact hother x hx

lemma even_sup_iff {A B : SimpleGraph V} {v : V} (h : TouchAt A B v) :
    (∀ x, Even ((A ⊔ B).degree x)) ↔
      (∀ x, Even (A.degree x)) ∧ (∀ x, Even (B.degree x)) := by
  constructor
  · intro he
    have hL := inf_even h (R := A ⊔ B) le_rfl (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
    have hR := inf_even h.symm (R := A ⊔ B) (by rw [sup_comm]) (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hL hR ⊢
    simpa only [inf_eq_right.mpr (le_sup_left : A ≤ A ⊔ B),
      inf_eq_right.mpr (le_sup_right : B ≤ A ⊔ B)] using And.intro hL hR
  · rintro ⟨hA,hB⟩
    exact even_sup_of_disjoint h.edge_disjoint hA hB

lemma code_separation {A B : SimpleGraph V} {v : V} (h : TouchAt A B v) :
    Separation (code (A ⊔ B)) A.edgeFinset B.edgeFinset := by
  have hdis : Disjoint A.edgeFinset B.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact Set.disjoint_left.mp h.edge_disjoint
      (SimpleGraph.mem_edgeFinset.mp heA) (SimpleGraph.mem_edgeFinset.mp heB)
  refine ⟨hdis,?_⟩
  intro u hu
  constructor
  · rintro ⟨R,hRG,hRe,rfl⟩
    constructor
    · refine ⟨R ⊓ A,inf_le_left.trans hRG,?_,?_⟩
      · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using inf_even h hRG hRe
      · ext e; simp
    · refine ⟨R ⊓ B,inf_le_left.trans hRG,?_,?_⟩
      · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
          inf_even h.symm (by simpa only [sup_comm] using hRG) hRe
      · ext e; simp
  · rintro ⟨⟨L,hLG,hLe,hL⟩,⟨R,hRG,hRe,hR⟩⟩
    have hLR : Disjoint L.edgeSet R.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e heL heR
      have heL' : e ∈ u ∩ A.edgeFinset := hL ▸ SimpleGraph.mem_edgeFinset.mpr heL
      have heR' : e ∈ u ∩ B.edgeFinset := hR ▸ SimpleGraph.mem_edgeFinset.mpr heR
      exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp heL').2 (Finset.mem_inter.mp heR').2
    refine ⟨L ⊔ R,sup_le hLG hRG,?_,?_⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using even_sup_of_disjoint hLR hLe hRe
    · have hf : (L ⊔ R).edgeFinset = u := by
        rw [SimpleGraph.edgeFinset_sup,hL,hR,← Finset.inter_union_distrib_left,Finset.inter_eq_left.mpr hu]
      simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using hf

lemma number_sup {A B : SimpleGraph V} {v : V} (h : TouchAt A B v)
    (hA : ∀ x, Even (A.degree x)) (hB : ∀ x, Even (B.degree x)) :
    number (A ⊔ B) = number A + number B := by
  have he := even_sup_of_disjoint h.edge_disjoint hA hB
  apply (hasNumber_iff (G := A ⊔ B) (R := A ⊔ B) le_rfl (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he) _).mp
  have hh := (code_separation h).hasNumber_add (hasNumber le_sup_left hA) (hasNumber le_sup_right hB)
  rw [← SimpleGraph.edgeFinset_sup] at hh
  simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using hh

lemma minimal_sup_iff {A B : SimpleGraph V} {v : V} (h : TouchAt A B v)
    (hA : ∀ x, Even (A.degree x)) (hB : ∀ x, Even (B.degree x)) :
    EvenMinimal (A ⊔ B) ↔ EvenMinimal A ∧ EvenMinimal B := by
  have he := even_sup_of_disjoint h.edge_disjoint hA hB
  have hn := number_sup h hA hB
  have hh := (code_separation h).minimalCore_iff
    (valid_edgeFinset le_sup_left hA) (valid_edgeFinset le_sup_right hB)
    (hasNumber le_sup_left hA) (hasNumber le_sup_right hB)
  rw [← SimpleGraph.edgeFinset_sup] at hh
  have hg := GraphCircuitCode.minimalCore_iff (G := A ⊔ B) le_rfl (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he) (number A + number B)
  have hl := GraphCircuitCode.minimalCore_iff (G := A ⊔ B) le_sup_left hA (number A)
  have hr := GraphCircuitCode.minimalCore_iff (G := A ⊔ B) le_sup_right hB (number B)
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hh hg hl hr
  rw [hg,hl,hr] at hh
  simpa only [hn,eq_self_iff_true,and_true] using hh

lemma rigid_sup_iff {A B : SimpleGraph V} {v : V} (h : TouchAt A B v)
    (hA : ∀ x, Even (A.degree x)) (hB : ∀ x, Even (B.degree x)) :
    CycleRigid (A ⊔ B) ↔ CycleRigid A ∧ CycleRigid B := by
  have he := even_sup_of_disjoint h.edge_disjoint hA hB
  have hn := number_sup h hA hB
  have hh := (code_separation h).rigid_iff (hasNumber le_sup_left hA) (hasNumber le_sup_right hB)
  rw [← SimpleGraph.edgeFinset_sup,← hn] at hh
  have hg := GraphCircuitCode.rigid_iff (G := A ⊔ B) le_rfl (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
  have hl := GraphCircuitCode.rigid_iff (G := A ⊔ B) le_sup_left hA
  have hr := GraphCircuitCode.rigid_iff (G := A ⊔ B) le_sup_right hB
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hh hg hl hr
  rw [hg,hl,hr] at hh
  exact hh

lemma nonrigid_minimal_sup_factor {A B : SimpleGraph V} {v : V} (h : TouchAt A B v)
    (he : ∀ x, Even ((A ⊔ B).degree x))
    (hm : EvenMinimal (A ⊔ B)) (hn : ¬ CycleRigid (A ⊔ B)) :
    ((∀ x, Even (A.degree x)) ∧ EvenMinimal A ∧ ¬ CycleRigid A) ∨
    ((∀ x, Even (B.degree x)) ∧ EvenMinimal B ∧ ¬ CycleRigid B) := by
  obtain ⟨heA,heB⟩ := (even_sup_iff h).mp he
  obtain ⟨hmA,hmB⟩ := (minimal_sup_iff h heA heB).mp hm
  by_cases hr : CycleRigid A
  · exact Or.inr ⟨heB,hmB,fun hB => hn ((rigid_sup_iff h heA heB).mpr ⟨hr,hB⟩)⟩
  · exact Or.inl ⟨heA,hmA,hr⟩

#print axioms code_separation
#print axioms number_sup
#print axioms minimal_sup_iff
#print axioms rigid_sup_iff
#print axioms nonrigid_minimal_sup_factor
end Erdos184Work.GraphVertexSeparation
