import Submission.AdaptiveHitSelectionExplore
import Submission.AdaptivePacketChoiceExplore

/-! Coordinated finite packet repair. Sequential exclusion of used assignment
cells avoids the quadratic collision union bound, while a common potential
controls the entire signed collateral, not a sum of separate repair bounds. -/
namespace Erdos66AdaptiveAssignedRepair
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66AdaptivePacketAlgebra Erdos66AdaptivePacketChoice Erdos66AdaptiveHitSelection
open scoped Classical
set_option maxHeartbeats 4000000

noncomputable def occurrences (n : ℕ → ℕ) (k z : ℕ) : ℕ :=
  ∑ i∈Finset.range k, if n i=z then 1 else 0

lemma occurrences_succ (n : ℕ → ℕ) (k z : ℕ) :
    occurrences n (k+1) z=occurrences n k z+(if n k=z then 1 else 0) := by
  exact Finset.sum_range_succ _ _

lemma occurrences_zero_off (n : ℕ → ℕ) (m : ℕ) (C : Finset ℕ)
    (hC : ∀ k < m, n k∈C) (z : ℕ) (hz : z∉C) : occurrences n m z=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hn : n k≠z := fun he ↦ hz (he ▸ hC k (Finset.mem_range.mp hk))
  simp only [hn,if_false]

/-- The candidate alphabet is fixed, but centers and endpoint maps can vary
with the step. No independence assumption is made on the selected choices. -/
theorem exists_adaptive_assigned_repair {α : Type*} [Fintype α]
    (A C : Finset ℕ) (assign : ℕ → ℕ) (n : ℕ → ℕ) (x : ℕ → α → ℕ) (m H : ℕ)
    (hC : ∀ k < m, n k∈C)
    (hinj : ∀ k < m, ∀ b, Function.Injective (endpoint (n k) (x k) b))
    (hhalf : ∀ k < m, ∀ a, 2*x k a<n k)
    (hmem : ∀ k < m, ∀ b a, assign (endpoint (n k) (x k) b a)∈A)
    (hsep : ∀ k < m, ∀ a, Function.Injective (fun b ↦ assign (endpoint (n k) (x k) b a)))
    (hfiber : ∀ k < m, ∀ b r,
      (Finset.univ.filter (fun a ↦ assign (endpoint (n k) (x k) b a)=r)).card ≤ H)
    (B Kc : ℝ) (K : ℕ → ℝ)
    (hB : ∀ k < m, ((Erdos66AssignedPacketRepair.badChoices A assign (n k) (x k)).card : ℝ) ≤ B)
    (hKc : ∀ k < m, ∀ z∈C,
      ((Erdos66AssignedPacketRepair.swapHits A assign (n k) (x k) z).card : ℝ) ≤ Kc)
    (T : Finset ℕ) (q t : ℝ) (R : ℕ → ℝ) (hq : 0<q) (ht : 0<t)
    (hK : ∀ k < m, ∀ z∈T,
      ((Erdos66AssignedPacketRepair.swapHits A assign (n k) (x k) z).card : ℝ) ≤ K z)
    (havailable : q+B+4*H*m+C.card*(Kc+4*m+2) ≤ Fintype.card α)
    (hsmall : (∑ z∈T, Real.exp ((m : ℝ)*(Real.exp t*(K z+4*m+2)/q)-t*R z))<1) :
    ∃ D F : Finset ℕ, D ⊆ A ∧ Disjoint A F ∧ D.card=2*m ∧ F.card=2*m ∧
      D=F.image assign ∧ Set.InjOn assign (F : Set ℕ) ∧
      (∀ u∈F, ∃ k < m, ∃ a, u∈packet (n k) (x k) a) ∧
      (∀ z∈C, sumRep (swapped A D F : Set ℕ) z=sumRep (A : Set ℕ) z+2*occurrences n m z) ∧
      (∀ z∈T, z∉C → |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z|<14*R z) := by
  let Inv (k : ℕ) (s : ℕ × Finset ℕ) : Prop :=
    s.1=k ∧ s.2.card=2*k ∧ Disjoint A s.2 ∧ s.2.image assign ⊆ A ∧
    Set.InjOn assign (s.2 : Set ℕ) ∧
    (∀ u∈s.2, ∃ j < k, ∃ a, u∈packet (n j) (x j) a) ∧
    ∀ z∈C, pairs s.2 A z=0 ∧ pairs (s.2.image assign) A z=0 ∧
      sumRep (s.2 : Set ℕ) z=2*occurrences n k z
  let choices (k : ℕ) (s : ℕ × Finset ℕ) := available A s.2 C assign (n k) (x k)
  let next (k : ℕ) (s : ℕ × Finset ℕ) (a : α) : ℕ × Finset ℕ := (k+1,s.2∪packet (n k) (x k) a)
  let load (s : ℕ × Finset ℕ) (z : ℕ) : ℝ :=
    (energy A s.2 assign z-2*(occurrences n s.1 z : ℝ))/14
  let hit (k : ℕ) (s : ℕ × Finset ℕ) (z : ℕ) := jointHits A s.2 assign (n k) (x k) z
  let b (z : ℕ) : ℝ := Real.exp t*(K z+4*m+2)/q
  have hinit : Inv 0 (0,∅) := by
    simp [Inv,occurrences,pairs,sumRep_def]
  have hzinit : ∀ z∈T, load (0,∅) z=0 := by
    intro z hz
    simp [load,energy,occurrences,pairs,sumRep_def]
  have hchoices : ∀ k < m, ∀ s, Inv k s → q ≤ (choices k s).card := by
    intro k hk s hs
    apply available_card A s.2 C assign (n k) (x k) (hinj k hk) H m
      (by rw [hs.2.1]; omega) (hfiber k hk) B Kc q (hB k hk) (hKc k hk) havailable
  have hnext : ∀ k < m, ∀ s, Inv k s → ∀ a∈choices k s, Inv (k+1) (next k s a) := by
    intro k hk s hs a ha
    obtain ⟨hsk,hcard,hAF,hDA,hiF,hpoints,hcent⟩ := hs
    obtain ⟨hAP,hFP,hDP,havoid⟩ := available_properties A s.2 C assign (n k) (x k) a ha
    have hP : (packet (n k) (x k) a).image assign ⊆ A := by
      intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨bb,rfl⟩ := (mem_packet_iff (n k) (x k) a v).mp hv
      exact hmem k hk bb a
    refine ⟨rfl,?_,Finset.disjoint_union_right.mpr ⟨hAF,hAP⟩,?_,?_,?_,?_⟩
    · dsimp only [next]
      rw [Finset.card_union_of_disjoint hFP,hcard,packet_card _ _ _ (hhalf k hk a)]
      omega
    · dsimp only [next]
      rw [Finset.image_union]
      exact Finset.union_subset hDA hP
    · exact injOn_union_disjoint_image s.2 (packet (n k) (x k) a) assign hiF
        (assigned_packet_injOn assign (n k) (x k) a (hsep k hk a)) hDP
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨j,hj,a',ha'⟩ := hpoints u hu
        exact ⟨j,by omega,a',ha'⟩
      · exact ⟨k,by omega,a,hu⟩
    · intro z hz
      obtain ⟨hf,hd,hr⟩ := energy_center_step A s.2 assign (n k) (x k) a (hhalf k hk a) z (havoid z hz) hFP hDP
      obtain ⟨hc₁,hc₂,hc₃⟩ := hcent z hz
      refine ⟨hf.trans hc₁,hd.trans hc₂,?_⟩
      dsimp only [next]
      rw [hr,hc₃,occurrences_succ]
      omega
  have hhit : ∀ k < m, ∀ s, Inv k s → ∀ z∈T, ((hit k s z).card : ℝ) ≤ K z+4*m+2 := by
    intro k hk s hs z hz
    have hh := jointHits_card A s.2 assign (n k) (x k) (hinj k hk) z (K z) (hK k hk z hz)
    have hc : (s.2.card : ℝ)=2*k := by exact_mod_cast hs.2.1
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk.le
    change ((jointHits A s.2 assign (n k) (x k) z).card : ℝ) ≤ _
    linarith
  have hload : ∀ k < m, ∀ s, Inv k s → ∀ a∈choices k s, ∀ z∈T,
      load (next k s a) z ≤ load s z+(if a∈hit k s z then 1 else 0) := by
    intro k hk s hs a ha z hz
    obtain ⟨hAP,hFP,hDP,havoid⟩ := available_properties A s.2 C assign (n k) (x k) a ha
    have he := energy_step A s.2 assign (n k) (x k) a (hhalf k hk a) hFP hDP z
    dsimp only [load,next,hit]
    rw [hs.1,occurrences_succ]
    push_cast
    linarith
  obtain ⟨s,hs,hsload⟩ := exists_adaptive_small_hits m (0,∅) Inv choices next load hit T q t
    (fun z ↦ K z+4*m+2) b R hq ht hinit hzinit hchoices hnext hhit hload
    (fun _ _ ↦ le_rfl) hsmall
  obtain ⟨hsm,hcard,hAF,hDA,hiF,hpoints,hcent⟩ := hs
  refine ⟨s.2.image assign,s.2,hDA,hAF,?_,hcard,rfl,hiF,hpoints,?_,?_⟩
  · rw [Finset.card_image_of_injOn hiF,hcard]
  · intro z hz
    obtain ⟨hf,hd,hr⟩ := hcent z hz
    rw [swapped_no_old_hits A (s.2.image assign) s.2 hDA hAF z hd hf,hr]
  · intro z hz hzC
    have ho := occurrences_zero_off n m C hC z hzC
    have hh := hsload z hz
    dsimp only [load] at hh
    rw [hsm,ho] at hh
    have he := swapped_error_le_energy A s.2 assign hDA hAF z
    push_cast at hh
    linarith

end Erdos66AdaptiveAssignedRepair
