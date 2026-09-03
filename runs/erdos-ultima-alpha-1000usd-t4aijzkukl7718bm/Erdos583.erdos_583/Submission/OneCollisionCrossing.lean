import Submission.ReindexedCoreArms

/-! The valid crossing for a repeated-port pair. The selected repeated
endpoint stays fixed while the other endpoint is swapped with the opposite
slot of a compatible partner pair. -/
namespace Erdos583OneCollisionCrossingDevelopment
open SimpleGraph Erdos583Work
open Erdos583ReindexedCoreArmsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma repaired_pair_unique_nil {I V : Type*} [DecidableEq I]
    (a : I × Bool → V) (u : V) (e : I × Bool)
    (hb : Function.Bijective (fun z ↦ if z=e then u else a z))
    (i : I) (hi : a (i,true)=a (i,false)) : i=e.1 := by
  by_contra hie
  have ht : (i,true) ≠ e := fun h ↦ hie (congrArg Prod.fst h)
  have hf : (i,false) ≠ e := fun h ↦ hie (congrArg Prod.fst h)
  have hh := hb.injective (a₁ := (i,true)) (a₂ := (i,false))
    (by simpa only [if_neg ht,if_neg hf] using hi)
  cases congrArg Prod.snd hh

lemma cross_pairs_compatible {I V : Type*} [DecidableEq I]
    (F : I × Bool → Set V) (j l : I) (hjl : j ≠ l) (c : Bool)
    (hother : ∀ i, i ≠ j → i ≠ l → Disjoint (F (i,true)) (F (i,false)))
    (htrue : Disjoint (F (j,true)) (F (l,true)))
    (hfalse : Disjoint (F (j,false)) (F (l,false))) :
    ∀ i, Disjoint (F (Equiv.swap (j,!c) (l,c) (i,true)))
      (F (Equiv.swap (j,!c) (l,c) (i,false))) := by
  intro i
  by_cases hij : i=j
  · subst i
    cases c
    · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl] using hfalse.symm
    · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl] using htrue
  by_cases hil : i=l
  · subst i
    cases c
    · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl] using htrue.symm
    · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl] using hfalse
  cases c <;> simpa [Equiv.swap_apply_def,hij,hil] using hother i hij hil

lemma cross_fixes_selected {I : Type*} [DecidableEq I]
    (j l : I) (hjl : j ≠ l) (c : Bool) :
    (Equiv.swap (j,!c) (l,c)).symm (j,c)=(j,c) := by
  cases c <;> simp [Equiv.swap_apply_def,hjl]

lemma cross_selected_pair_distinct {I V : Type*} [DecidableEq I]
    (a : I × Bool → V) (v : V) (j l : I) (hjl : j ≠ l) (c : Bool)
    (hjt : a (j,true)=v) (hjf : a (j,false)=v)
    (hl : ∀ b, a (l,b) ≠ v) :
    a (Equiv.swap (j,!c) (l,c) (j,true)) ≠
      a (Equiv.swap (j,!c) (l,c) (j,false)) := by
  cases c
  · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl,hjf] using hl false
  · simpa [Equiv.swap_apply_def,hjl,Ne.symm hjl,hjt] using Ne.symm (hl true)

lemma other_pair_avoids_repeated_label {I V : Type*} [DecidableEq I]
    (a : I × Bool → V) (u v : V) (j l : I) (hjl : j ≠ l) (c : Bool)
    (hjt : a (j,true)=v) (hjf : a (j,false)=v)
    (hb : Function.Bijective (fun z ↦ if z=(j,c) then u else a z)) :
    ∀ b, a (l,b) ≠ v := by
  intro b hbad
  have hl : (l,b) ≠ (j,c) := fun h ↦ hjl (congrArg Prod.fst h).symm
  have hj : (j,!c) ≠ (j,c) := by cases c <;> simp
  have hmate : a (j,!c)=v := by cases c <;> assumption
  have hh := hb.injective (a₁ := (l,b)) (a₂ := (j,!c))
    (by simp only [if_neg hl,if_neg hj,hbad,hmate])
  exact hjl (congrArg Prod.fst hh).symm

lemma near_complete_splice_one_collision {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a : Fin k × Bool → S) (x : Fin k × Bool → V)
    (P : ∀ z, G.Walk (x z) (a z).val)
    (hp : ∀ z, (P z).IsPath)
    (hPS : ∀ z, ∀ v ∈ (P z).support, v ∈ S → v=(a z).val)
    (hd : Pairwise (fun z w ↦ Disjoint (P z).toSubgraph.edgeSet (P w).toSubgraph.edgeSet))
    (hc : (BridgeGlue.within G S).edgeSet ∪ (⋃ z, (P z).toSubgraph.edgeSet)=G.edgeSet)
    (u v : S) (huv : u ≠ v)
    (hnear : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(u,v)})
    (e : Fin k × Bool) (he : a e=v)
    (hbij : Function.Bijective (fun z ↦ if z=e then u else a z))
    (hcompat : ∀ i, a (i,true) ≠ a (i,false) →
      Disjoint {w | w ∈ (P (i,true)).support} {w | w ∈ (P (i,false)).support})
    (hcross : a (e.1,true)=a (e.1,false) → ∃ l, e.1 ≠ l ∧
      Disjoint {w | w ∈ (P (e.1,true)).support} {w | w ∈ (P (l,true)).support} ∧
      Disjoint {w | w ∈ (P (e.1,false)).support} {w | w ∈ (P (l,false)).support}) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  by_cases hnil : a (e.1,true)=a (e.1,false)
  · obtain ⟨l,hel,ht,hf⟩ := hcross hnil
    have het : a (e.1,true)=v := by rcases e with ⟨i,c⟩; cases c <;> simp_all
    have hef : a (e.1,false)=v := hnil.symm.trans het
    let π := Equiv.swap (e.1,!e.2) (l,e.2)
    have hfix : π.symm e=e := by
      simpa only [Prod.mk.eta] using cross_fixes_selected e.1 l hel e.2
    have hne := cross_selected_pair_distinct a v e.1 l hel e.2 het hef
      (other_pair_avoids_repeated_label a u v e.1 l hel e.2 het hef hbij)
    have hnew := cross_pairs_compatible (fun z ↦ {w | w ∈ (P z).support}) e.1 l hel e.2
      (fun i hie _ ↦ hcompat i (fun hh ↦ hie (repaired_pair_unique_nil a u e hbij i hh))) ht hf
    apply reindexed_near_complete_splice S a x P hp hPS hd hc u v huv hnear e he hbij π
      (by rw [hfix]; exact hne)
    intro i w hw1 hw2
    exact Set.disjoint_left.mp (hnew i) hw1 hw2
  · apply reindexed_near_complete_splice S a x P hp hPS hd hc u v huv hnear e he hbij
      (Equiv.refl _) hnil
    intro i w hw1 hw2
    have hi : a (i,true) ≠ a (i,false) := by
      intro hh
      have hie := repaired_pair_unique_nil a u e hbij i hh
      exact hnil (hie ▸ hh)
    exact Set.disjoint_left.mp (hcompat i hi) hw1 hw2

end Erdos583OneCollisionCrossingDevelopment
