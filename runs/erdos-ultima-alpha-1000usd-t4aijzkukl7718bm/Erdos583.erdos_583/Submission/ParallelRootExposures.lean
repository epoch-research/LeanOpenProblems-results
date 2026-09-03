import Submission.Work

/-! Distinct root-edge seeds for different root tails are followed using one
common successor map. Exposures are separate realizations, but their labels
are proved distinct before any rearrangement is performed. -/
namespace Erdos583ParallelRootExposuresDevelopment
open SimpleGraph Erdos583Work Erdos583Work.DistinctTails
open Erdos583Work.DoubleEscape
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma parallel_root_exposures {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    {G : SimpleGraph V} {v : V} {B : Finset V} (R : I → TailFamily G v B)
    (ht : ∀ i j (w : B), w.val ≠ v → (R i).tail w=(R j).tail w)
    (hd : Pairwise fun i j ↦
      Disjoint ((R i).tail ⟨v,(R i).root_mem⟩).toSubgraph.edgeSet
        ((R j).tail ⟨v,(R j).root_mem⟩).toSubgraph.edgeSet) :
    ∃ E : Finset V,
      E.card=∑ i, (((R i).tail ⟨v,(R i).root_mem⟩).toSubgraph.neighborSet v).ncard ∧
      ∀ z ∈ E, z ∉ B ∧ ∃ (i : I) (S : TailFamily G v B),
        Rearranged S (R i) ∧ (S.tail ⟨v,S.root_mem⟩).snd=z := by
  classical
  let i₀ : I := Classical.choice ‹Nonempty I›
  let A := B.erase v
  let N (i : I) := ((R i).tail ⟨v,(R i).root_mem⟩).toSubgraph.neighborSet v
  obtain ⟨f,hf,htf,_,_⟩ := successor_data (R i₀)
  have htf' (i : I) (w : B) (hw : w.val ≠ v) :
      f w.val=((R i).tail w).penultimate := by
    rw [←ht i₀ i w hw]
    exact htf w hw
  have hstart (z : Σ i, N i) : z.2.val ∉ A.image f :=
    neighbor_outside_successor_image (R z.1) f (htf' z.1) z.2.val z.2.property
  have hseed : Function.Injective (fun z : Σ i, N i ↦ z.2.val) := by
    intro z w he
    change z.2.val=w.2.val at he
    have hi : z.1=w.1 := by
      by_contra hn
      have hz : s(v,z.2.val) ∈ ((R z.1).tail ⟨v,(R z.1).root_mem⟩).toSubgraph.edgeSet := z.2.property
      have hw : s(v,w.2.val) ∈ ((R w.1).tail ⟨v,(R w.1).root_mem⟩).toSubgraph.edgeSet := w.2.property
      rw [he] at hz
      exact Set.disjoint_left.mp (hd hn) hz hw
    rcases z with ⟨i,z⟩
    rcases w with ⟨j,w⟩
    dsimp at hi he
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext he)
  have hex (z : Σ i, N i) :
      ∃ n : ℕ, f^[n] z.2.val ∉ A ∧ ∀ m < n, f^[m] z.2.val ∈ A :=
    exists_first_exit_of_injective_successor A f hf z.2.val (hstart z)
  choose n hn hprev using hex
  let exit (z : Σ i, N i) := f^[n z] z.2.val
  have hinj : Function.Injective exit := by
    intro z w he
    exact hseed (starts_eq_of_iterate_eq A f hf z.2.val w.2.val (hstart z) (hstart w)
      (n z) (n w) (hprev z) (hprev w) he)
  have hreach (z : Σ i, N i) : exit z ∉ B ∧ ∃ S : TailFamily G v B,
      Rearranged S (R z.1) ∧ (S.tail ⟨v,S.root_mem⟩).snd=exit z := by
    obtain ⟨C,hC,hCe,hCn,hCz⟩ := MultipleEscape.closed_trail_first_at_neighbor
      ((R z.1).tail ⟨v,(R z.1).root_mem⟩) ((R z.1).trail _) z.2.property
    obtain ⟨R',hR',hroot,htail⟩ := replace_root (R z.1) C hC hCe hCn
    have hfirst : (R'.tail ⟨v,R'.root_mem⟩).snd=z.2.val := by rw [hroot,hCz]
    have htf'' (w : B) (hw : w.val ≠ v) : f w.val=(R'.tail w).penultimate := by
      rw [htail w hw]
      exact htf' z.1 w hw
    obtain ⟨S,hS,hSfirst,hSout⟩ := realize_escape_orbit R' f hf htf''
      (by rw [hfirst]; exact hstart z) (n z) (by rw [hfirst]; exact hn z)
      (by rw [hfirst]; exact hprev z)
    have hsnd : (S.tail ⟨v,S.root_mem⟩).snd=exit z := by rw [hSfirst,hfirst]
    exact ⟨hsnd ▸ hSout,S,rearranged_trans hS hR',hsnd⟩
  refine ⟨Finset.univ.image exit,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.card_eq_fintype_card.symm
  · intro z hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw,S,hS,hs⟩ := hreach w
    exact ⟨hw,w.1,S,hS,hs⟩

end Erdos583ParallelRootExposuresDevelopment
