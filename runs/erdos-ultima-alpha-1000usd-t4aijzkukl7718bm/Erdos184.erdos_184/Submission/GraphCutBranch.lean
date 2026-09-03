import Submission.GraphCutPartition
import Submission.GraphBranchCount

/-! Two-edge-cut extraction and strict descent when both sides contain a
vertex of degree greater than two. The irreducible core theorem remains open. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphTwoCut
open GraphBranchCount GraphIsoCore Critical EvenCore Rigidity
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Crossing edges, oriented from the chosen side to its complement. -/
noncomputable def crossPairs (G : SimpleGraph V) (S : Set V) : Finset (S × (Sᶜ : Set V)) :=
  Finset.univ.filter fun p => G.Adj p.1.val p.2.val

lemma exists_cut_endpoints (G : SimpleGraph V) (S : Set V) (hc : (crossPairs G S).card = 2) :
    ∃ a b : S, ∃ c d : (Sᶜ : Set V), (a ≠ b ∨ c ≠ d) ∧
      ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
        (x = a ∧ y = c) ∨ (x = b ∧ y = d) := by
  obtain ⟨p,q,hpq,he⟩ := Finset.card_eq_two.mp hc
  refine ⟨p.1,q.1,p.2,q.2,?_,?_⟩
  · by_cases h : p.1 = q.1
    · exact Or.inr (fun h' => hpq (Prod.ext h h'))
    · exact Or.inl h
  · intro x y
    have hmem : (x,y) ∈ crossPairs G S ↔ (x,y) = p ∨ (x,y) = q := by rw [he]; simp
    simpa only [crossPairs,Finset.mem_filter,Finset.mem_univ,true_and,
      Prod.ext_iff] using hmem

lemma partition_branches_left (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d)) :
    branches (closure (G.induce S) a b) = ∑ x : S, if 2 < G.degree x.val then 1 else 0 := by
  rw [branches_closure_left _ _ hsep]
  apply Finset.sum_congr rfl
  intro x _
  have h := (partitionIso G S a b c d hcut).degree_eq (.inl x)
  change G.degree x.val = _ at h
  rw [h]

lemma partition_branches_right (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d)) :
    branches (closure (G.induce Sᶜ) c d) = ∑ x : (Sᶜ : Set V), if 2 < G.degree x.val then 1 else 0 := by
  rw [branches_closure_right _ _ hsep]
  apply Finset.sum_congr rfl
  intro x _
  have h := (partitionIso G S a b c d hcut).degree_eq (.inr x)
  change G.degree x.val = _ at h
  rw [h]

lemma nonrigid_minimal_two_cut_smaller (G : SimpleGraph V) (S : Set V)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G)
    (hc : (crossPairs G S).card = 2)
    (hL : ∃ x : S, 2 < G.degree x.val) (hR : ∃ x : (Sᶜ : Set V), 2 < G.degree x.val) :
    ∃ a b : S, ∃ c d : (Sᶜ : Set V),
      (EvenMinimal (closure (G.induce S) a b) ∧ ¬ CycleRigid (closure (G.induce S) a b) ∧
        (∀ x, Even ((closure (G.induce S) a b).degree x)) ∧
        branches (closure (G.induce S) a b) < branches G) ∨
      (EvenMinimal (closure (G.induce Sᶜ) c d) ∧ ¬ CycleRigid (closure (G.induce Sᶜ) c d) ∧
        (∀ x, Even ((closure (G.induce Sᶜ) c d).degree x)) ∧
        branches (closure (G.induce Sᶜ) c d) < branches G) := by
  obtain ⟨a,b,c,d,hsep,hcut⟩ := exists_cut_endpoints G S hc
  refine ⟨a,b,c,d,?_⟩
  have e := partitionIso G S a b c d hcut
  have hj := even_iso e.symm he
  have hL' : 0 < branches (closure (G.induce S) a b) := by
    rw [partition_branches_left G S a b c d hsep hcut]
    obtain ⟨x,hx⟩ := hL
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x,Finset.mem_univ _,by simp [hx]⟩
  have hR' : 0 < branches (closure (G.induce Sᶜ) c d) := by
    rw [partition_branches_right G S a b c d hsep hcut]
    obtain ⟨x,hx⟩ := hR
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x,Finset.mem_univ _,by simp [hx]⟩
  have hb := branches_iso e
  have hmi := (minimal_iso_iff e).mpr hm
  have hni : ¬ CycleRigid (join (G.induce S) (G.induce Sᶜ) a b c d) :=
    fun hr => hn ((rigid_iso_iff e hj).mp hr)
  obtain ⟨hGe,hHe⟩ := partition_closures_even G S a b c d hsep hcut he
  rcases nonrigid_minimal_join_smaller _ _ hsep hj hmi hni hL' hR' with h | h
  · exact Or.inl ⟨h.1,h.2.1,hGe,by simpa only [hb] using h.2.2⟩
  · exact Or.inr ⟨h.1,h.2.1,hHe,by simpa only [hb] using h.2.2⟩

#print axioms exists_cut_endpoints
#print axioms partition_branches_left
#print axioms partition_branches_right
#print axioms nonrigid_minimal_two_cut_smaller
end Erdos184Work.GraphTwoCut
