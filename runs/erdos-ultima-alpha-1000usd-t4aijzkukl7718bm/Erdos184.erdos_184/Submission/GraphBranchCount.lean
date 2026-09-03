import Submission.GraphTwoCutTheory

/-! A subdivision-invariant size measure and strict two-cut reductions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphBranchCount
open GraphSubdivision GraphTwoCut GraphIsoCore Critical EvenCore Rigidity
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Number of vertices of degree greater than two. -/
noncomputable def branches (G : SimpleGraph V) : ℕ := ∑ v, if 2 < G.degree v then 1 else 0

lemma branches_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : branches G = branches H := by
  unfold branches
  calc
    _ = ∑ v, if 2 < H.degree (e v) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [e.degree_eq]
    _ = _ := Equiv.sum_comp e.toEquiv (fun w : W => if 2 < H.degree w then (1 : ℕ) else 0)

lemma branches_split (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) :
    branches (split G {()} a b) = branches G := by
  have hm : G.Adj a b ↔ () ∈ ({()} : Finset Unit) := by simp [hp]
  have hn := degree_subdivide_new G hp
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hn
  rw [subdivide_eq_split G hp] at hn
  have hn' : (split G {()} a b).degree (.inr ()) = 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hn
  unfold branches
  rw [Fintype.sum_sum_type]
  simp_rw [degree_old_of_match G {()} hp.ne hm]
  simp only [Fintype.sum_unique,hn',lt_self_iff_false,if_false,add_zero]

lemma branches_expanded (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) : branches (expanded G H a b c d) = branches (join G H a b c d) :=
  (branches_split _ (port₄ G H a b c d)).trans
    ((branches_split _ (port₃ G H hsep)).trans
      ((branches_split _ (port₂ G H a b c d)).trans (branches_split _ (port₁ G H a b c d))))

lemma branches_switch (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hp : G.Adj a b) (hq : H.Adj c d) :
    branches (GraphSerial.switch G H a b c d) = branches G + branches H := by
  have hm := iff_of_true hp hq
  unfold branches
  rw [Fintype.sum_sum_type]
  simp_rw [GraphSerial.degree_left_of_match G H hp.ne hm,
    GraphSerial.degree_right_of_match G H hq.ne hm]

lemma branches_join (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) :
    branches (join G H a b c d) = branches (closure G a b) + branches (closure H c d) := by
  calc
    _ = branches (expanded G H a b c d) := (branches_expanded G H hsep).symm
    _ = branches (switched G H a b c d) := branches_iso (expansionIso G H hsep)
    _ = _ := branches_switch _ _ (closure_port G a b) (closure_port H c d)

lemma split_degree_old (G : SimpleGraph V) {a b : V} (hp : G.Adj a b) (x : V) :
    (split G {()} a b).degree (.inl x) = G.degree x :=
  degree_old_of_match G {()} hp.ne (by simp [hp]) x

lemma expanded_degree_old (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (x : V ⊕ W) :
    (expanded G H a b c d).degree (.inl (.inl (.inl (.inl x)))) = (join G H a b c d).degree x := by
  exact (split_degree_old _ (port₄ G H a b c d) _).trans
    ((split_degree_old _ (port₃ G H hsep) _).trans
      ((split_degree_old _ (port₂ G H a b c d) _).trans (split_degree_old _ (port₁ G H a b c d) x)))

lemma closure_degree_left (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (x : V) :
    (closure G a b).degree (.inl x) = (join G H a b c d).degree (.inl x) := by
  have hi := (expansionIso G H hsep).degree_eq (.inl (.inl (.inl (.inl (.inl x)))))
  change (switched G H a b c d).degree (.inl (.inl x)) = _ at hi
  rw [GraphSerial.degree_left_of_match _ _ (closure_port G a b).ne
    (iff_of_true (closure_port G a b) (closure_port H c d))] at hi
  exact hi.trans (expanded_degree_old G H hsep (.inl x))

lemma closure_degree_right (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (x : W) :
    (closure H c d).degree (.inl x) = (join G H a b c d).degree (.inr x) := by
  have hi := (expansionIso G H hsep).degree_eq (.inl (.inl (.inl (.inl (.inr x)))))
  change (switched G H a b c d).degree (.inr (.inl x)) = _ at hi
  rw [GraphSerial.degree_right_of_match _ _ (closure_port H c d).ne
    (iff_of_true (closure_port G a b) (closure_port H c d))] at hi
  exact hi.trans (expanded_degree_old G H hsep (.inr x))

lemma closure_degree_new (G : SimpleGraph V) (a b : V) (u : Bool) :
    (closure G a b).degree (.inr u) = 2 := by
  cases u with
  | false =>
    have he : (closure G a b).neighborFinset (.inr false) = {Sum.inl a,Sum.inr true} := by
      ext x
      cases x with
      | inl x => simp [SimpleGraph.mem_neighborFinset,GraphTwoCut.closure]
      | inr u => cases u <;> simp [SimpleGraph.mem_neighborFinset,GraphTwoCut.closure]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
    simp
  | true =>
    have he : (closure G a b).neighborFinset (.inr true) = {Sum.inl b,Sum.inr false} := by
      ext x
      cases x with
      | inl x => simp [SimpleGraph.mem_neighborFinset,GraphTwoCut.closure]
      | inr u => cases u <;> simp [SimpleGraph.mem_neighborFinset,GraphTwoCut.closure]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
    simp

lemma branches_closure_left (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) :
    branches (closure G a b) = ∑ x : V, if 2 < (join G H a b c d).degree (.inl x) then 1 else 0 := by
  unfold branches
  rw [Fintype.sum_sum_type]
  simp_rw [closure_degree_left G H hsep,closure_degree_new]
  simp

lemma branches_closure_right (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) :
    branches (closure H c d) = ∑ x : W, if 2 < (join G H a b c d).degree (.inr x) then 1 else 0 := by
  unfold branches
  rw [Fintype.sum_sum_type]
  simp_rw [closure_degree_right G H hsep,closure_degree_new]
  simp

lemma nonrigid_minimal_join_smaller (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hsep : a ≠ b ∨ c ≠ d) (he : ∀ x, Even ((join G H a b c d).degree x))
    (hm : EvenMinimal (join G H a b c d)) (hn : ¬ CycleRigid (join G H a b c d))
    (hL : 0 < branches (closure G a b)) (hR : 0 < branches (closure H c d)) :
    (EvenMinimal (closure G a b) ∧ ¬ CycleRigid (closure G a b) ∧
      branches (closure G a b) < branches (join G H a b c d)) ∨
    (EvenMinimal (closure H c d) ∧ ¬ CycleRigid (closure H c d) ∧
      branches (closure H c d) < branches (join G H a b c d)) := by
  have hsum := branches_join G H hsep
  rcases nonrigid_minimal_join_factor G H hsep he hm hn with h | h
  · exact Or.inl ⟨h.1,h.2,by omega⟩
  · exact Or.inr ⟨h.1,h.2,by omega⟩

#print axioms branches_iso
#print axioms branches_split
#print axioms branches_join
#print axioms nonrigid_minimal_join_smaller
end Erdos184Work.GraphBranchCount
