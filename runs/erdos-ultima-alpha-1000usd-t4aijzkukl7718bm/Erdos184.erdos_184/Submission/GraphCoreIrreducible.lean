import Submission.GraphCutBranch

/-! Reducing a hypothetical nonrigid minimal core to one with no two-edge cut
separating branch vertices. Existence of such a core is not asserted. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphCoreIrreducible
open GraphTwoCut GraphBranchCount Critical EvenCore Rigidity
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every two-edge cut has a side without any branch vertex. -/
def BranchCutIrreducible (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (crossPairs G S).card = 2 →
    (∀ x : S, G.degree x.val ≤ 2) ∨ (∀ x : (Sᶜ : Set V), G.degree x.val ≤ 2)

lemma branchMinimal_irreducible (G : SimpleGraph V)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G)
    (hmin : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      (∀ x, Even (H.degree x)) → EvenMinimal H → ¬ CycleRigid H → branches G ≤ branches H) :
    BranchCutIrreducible G := by
  intro S hc
  by_cases hL : ∀ x : S, G.degree x.val ≤ 2
  · exact Or.inl hL
  · right
    intro x
    by_contra hx
    have hLe : ∃ y : S, 2 < G.degree y.val := by
      push_neg at hL
      exact hL
    have hRe : ∃ y : (Sᶜ : Set V), 2 < G.degree y.val := ⟨x,Nat.lt_of_not_ge hx⟩
    obtain ⟨a,b,c,d,h⟩ := nonrigid_minimal_two_cut_smaller G S he hm hn hc hLe hRe
    rcases h with h | h
    · have hb := hmin (closure (G.induce S) a b) h.2.2.1 h.1 h.2.1
      exact (not_lt_of_ge hb) h.2.2.2
    · have hb := hmin (closure (G.induce Sᶜ) c d) h.2.2.1 h.1 h.2.1
      exact (not_lt_of_ge hb) h.2.2.2

lemma exists_irreducible_of_nonrigid_core
    (hbad : ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H ∧ BranchCutIrreducible H := by
  let P : ℕ → Prop := fun n => ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    (∀ x, Even (H.degree x)) ∧ EvenMinimal H ∧ ¬ CycleRigid H ∧ branches H = n
  have hP : ∃ n, P n := by
    obtain ⟨W,iW,dW,H,he,hm,hn⟩ := hbad
    exact ⟨@branches W iW H,W,iW,dW,H,he,hm,hn,rfl⟩
  obtain ⟨W,iW,dW,H,he,hm,hn,hb⟩ := Nat.find_spec hP
  letI := iW
  letI := dW
  refine ⟨W,iW,dW,H,he,hm,hn,?_⟩
  apply branchMinimal_irreducible H he hm hn
  intro U _ _ R hRe hRm hRn
  have hle : Nat.find hP ≤ branches R := Nat.find_min' hP ⟨U,inferInstance,inferInstance,R,hRe,hRm,hRn,rfl⟩
  rw [← hb] at hle
  exact hle

#print axioms branchMinimal_irreducible
#print axioms exists_irreducible_of_nonrigid_core
end Erdos184Work.GraphCoreIrreducible
