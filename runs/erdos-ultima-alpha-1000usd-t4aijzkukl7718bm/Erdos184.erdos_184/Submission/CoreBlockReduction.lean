import Submission.GraphVertexSeparation
import Submission.IrreducibleBound

/-! A hypothetical nonrigid minimal core of least optimum has neither a
nontrivial one-vertex separation nor a branch-separating two-edge cut.
This is a reduction, not an existence claim or a rigidity theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CoreBlockReduction
open Critical EvenCore Rigidity GraphVertexSeparation GraphTwoCut GraphBranchCount
  GraphCoreIrreducible IrreducibleBound
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- No nontrivial edge partition across a one-vertex support interface. -/
def VertexIrreducible (G : SimpleGraph V) : Prop :=
  ∀ A B : SimpleGraph V, ∀ v : V, TouchAt A B v → A ⊔ B = G → A = ⊥ ∨ B = ⊥

lemma number_ge_two_of_branches_pos (G : SimpleGraph V) (hb : 0 < branches G) :
    2 ≤ number G := by
  by_contra hn
  have hd (v : V) : G.degree v ≤ 2 := by
    have hv := StarCore.number_degree_bound G v
    omega
  have hz : branches G = 0 := by
    unfold branches
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (not_lt_of_ge (hd v))
  omega

lemma nonrigid_vertex_factor_number_lt {A B : SimpleGraph V} {v : V}
    (h : TouchAt A B v) (he : ∀ x, Even ((A ⊔ B).degree x))
    (hm : EvenMinimal (A ⊔ B)) (hn : ¬ CycleRigid (A ⊔ B))
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    ((∀ x, Even (A.degree x)) ∧ EvenMinimal A ∧ ¬ CycleRigid A ∧ number A < number (A ⊔ B)) ∨
    ((∀ x, Even (B.degree x)) ∧ EvenMinimal B ∧ ¬ CycleRigid B ∧ number B < number (A ⊔ B)) := by
  obtain ⟨heA,heB⟩ := (even_sup_iff h).mp he
  have hsum := number_sup h heA heB
  have hposA : 0 < number A := by
    have hne := mt (StarCharacterization.number_eq_zero_iff A).mp hA
    omega
  have hposB : 0 < number B := by
    have hne := mt (StarCharacterization.number_eq_zero_iff B).mp hB
    omega
  rcases nonrigid_minimal_sup_factor h he hm hn with hL | hR
  · exact Or.inl ⟨hL.1,hL.2.1,hL.2.2,by omega⟩
  · exact Or.inr ⟨hR.1,hR.2.1,hR.2.2,by omega⟩

lemma nonrigid_two_cut_smaller_number (G : SimpleGraph V) (S : Set V)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G)
    (hc : (crossPairs G S).card = 2)
    (hL : ∃ x : S, 2 < G.degree x.val) (hR : ∃ x : (Sᶜ : Set V), 2 < G.degree x.val) :
    ∃ a b : S, ∃ c d : (Sᶜ : Set V),
      ((∀ x, Even ((closure (G.induce S) a b).degree x)) ∧
        EvenMinimal (closure (G.induce S) a b) ∧ ¬ CycleRigid (closure (G.induce S) a b) ∧
        number (closure (G.induce S) a b) < number G) ∨
      ((∀ x, Even ((closure (G.induce Sᶜ) c d).degree x)) ∧
        EvenMinimal (closure (G.induce Sᶜ) c d) ∧ ¬ CycleRigid (closure (G.induce Sᶜ) c d) ∧
        number (closure (G.induce Sᶜ) c d) < number G) := by
  obtain ⟨a,b,c,d,hsep,hcut⟩ := exists_cut_endpoints G S hc
  obtain ⟨hbL,hbR⟩ := closures_branches_pos G S a b c d hsep hcut hL hR
  have hkL := number_ge_two_of_branches_pos _ hbL
  have hkR := number_ge_two_of_branches_pos _ hbR
  have hsum := number_two_edge_cut G S a b c d hsep hcut he
  obtain ⟨heL,heR⟩ := partition_closures_even G S a b c d hsep hcut he
  refine ⟨a,b,c,d,?_⟩
  rcases nonrigid_minimal_two_edge_cut_factor G S a b c d hsep hcut he hm hn with h | h
  · exact Or.inl ⟨heL,h.1,h.2,by omega⟩
  · exact Or.inr ⟨heR,h.1,h.2,by omega⟩

lemma least_number_vertexIrreducible (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G)
    (hmin : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → ¬ CycleRigid R → number G ≤ number R) :
    VertexIrreducible G := by
  intro A B v ht heq
  have heAB : ∀ x, Even ((A ⊔ B).degree x) := by
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he ⊢
    rw [heq]
    exact he
  have hmAB : EvenMinimal (A ⊔ B) := heq.symm ▸ hm
  have hnAB : ¬ CycleRigid (A ⊔ B) := heq.symm ▸ hn
  by_cases hA : A = ⊥
  · exact Or.inl hA
  by_cases hB : B = ⊥
  · exact Or.inr hB
  rcases nonrigid_vertex_factor_number_lt ht heAB hmAB hnAB hA hB with h | h
  · have hlt : number A < number G := by simpa only [heq] using h.2.2.2
    exact (not_lt_of_ge (hmin A h.1 h.2.1 h.2.2.1) hlt).elim
  · have hlt : number B < number G := by simpa only [heq] using h.2.2.2
    exact (not_lt_of_ge (hmin B h.1 h.2.1 h.2.2.1) hlt).elim

lemma least_number_branchCutIrreducible (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G)
    (hmin : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → ¬ CycleRigid R → number G ≤ number R) :
    BranchCutIrreducible G := by
  intro S hc
  by_cases hL : ∀ x : S, G.degree x.val ≤ 2
  · exact Or.inl hL
  right
  intro x
  by_contra hx
  have hLe : ∃ y : S, 2 < G.degree y.val := by push_neg at hL; exact hL
  have hRe : ∃ y : (Sᶜ : Set V), 2 < G.degree y.val := ⟨x,Nat.lt_of_not_ge hx⟩
  obtain ⟨a,b,c,d,h⟩ := nonrigid_two_cut_smaller_number G S he hm hn hc hLe hRe
  rcases h with h | h
  · exact not_lt_of_ge (hmin (closure (G.induce S) a b) h.1 h.2.1 h.2.2.1) h.2.2.2
  · exact not_lt_of_ge (hmin (closure (G.induce Sᶜ) c d) h.1 h.2.1 h.2.2.1) h.2.2.2

/-- Conditional existence reduction, with least optimum chosen internally. -/
lemma exists_irreducible_block_of_nonrigid_core
    (hbad : ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H ∧
      VertexIrreducible H ∧ BranchCutIrreducible H := by
  let P : ℕ → Prop := fun n => ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H ∧ number H = n
  have hP : ∃ n, P n := by
    obtain ⟨W,iW,dW,H,he,hm,hn⟩ := hbad
    exact ⟨@number W iW H,W,iW,dW,H,he,hm,hn,rfl⟩
  obtain ⟨W,iW,dW,H,he,hm,hn,hnum⟩ := Nat.find_spec hP
  letI := iW
  letI := dW
  have hmin : ∀ {U : Type u} [Fintype U] [DecidableEq U] (R : SimpleGraph U),
      (∀ x, Even (R.degree x)) → EvenMinimal R → ¬ CycleRigid R → number H ≤ number R := by
    intro U _ _ R hRe hRm hRn
    have hle := Nat.find_min' hP ⟨U,inferInstance,inferInstance,R,hRe,hRm,hRn,rfl⟩
    rw [← hnum] at hle
    exact hle
  exact ⟨W,iW,dW,H,he,hm,hn,least_number_vertexIrreducible H he hm hn hmin,
    least_number_branchCutIrreducible H he hm hn hmin⟩

lemma nonrigid_three_irreducible (he : ∀ x, Even (G.degree x))
    (hm : EvenMinimal G) (hn : ¬ CycleRigid G) (hk : number G = 3) :
    VertexIrreducible G ∧ BranchCutIrreducible G := by
  have hmin : ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      (∀ x, Even (R.degree x)) → EvenMinimal R → ¬ CycleRigid R → number G ≤ number R := by
    intro W _ _ R hRe hRm hRn
    by_contra h
    have hr : number R ≤ 2 := by omega
    exact hRn (rigid_of_evenMinimal_number_le_two hRe hRm hr)
  exact ⟨least_number_vertexIrreducible G he hm hn hmin,
    least_number_branchCutIrreducible G he hm hn hmin⟩

#print axioms nonrigid_two_cut_smaller_number
#print axioms exists_irreducible_block_of_nonrigid_core
#print axioms nonrigid_three_irreducible
end Erdos184Work.CoreBlockReduction
