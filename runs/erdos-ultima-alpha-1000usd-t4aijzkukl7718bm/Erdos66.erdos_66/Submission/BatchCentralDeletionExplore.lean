import Submission.CentralEndpointResetExplore

/-! Simultaneous central deletions: a union is charged only once, with each
center's own decrement separated from the other centers' triple incidences. -/
namespace Erdos66BatchCentralDeletion
open AdditiveCombinatorics Erdos66CentralTripleDeletion Erdos66CentralTripleCounts
  Erdos66CentralEndpointReset Erdos66Explore
open scoped Classical
set_option maxHeartbeats 2500000

lemma union_hits_bound (A : Set ℕ) (T : Finset ℕ) (N : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hD : ∀ n∈T, D n ⊆ endpoints A (N n) n) (z : ℕ) :
    (hits A (T.biUnion D) z).card ≤ ∑ n∈T, (fiber A (N n) n z).card := by
  have hsub : hits A (T.biUnion D) z ⊆ T.biUnion (fun n ↦ fiber A (N n) n z) := by
    intro a ha
    obtain ⟨ha,haz,hza⟩ := Finset.mem_filter.mp ha
    obtain ⟨n,hn,ha⟩ := Finset.mem_biUnion.mp ha
    have hh := mem_endpoints.mp (hD n hn ha)
    exact Finset.mem_biUnion.mpr ⟨n,hn,mem_fiber.mpr
      ⟨hh.1,hh.2.1,hh.2.2.1,haz,hh.2.2.2.1,hh.2.2.2.2,hza⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma union_deletion_loss (A : Set ℕ) (T : Finset ℕ) (N : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hD : ∀ n∈T, D n ⊆ endpoints A (N n) n) (z : ℕ) :
    sumRep A z ≤ sumRep (A\(T.biUnion D : Set ℕ)) z+
      2*∑ n∈T, (fiber A (N n) n z).card := by
  have hh := deletion_inside_host A A (T.biUnion D) (Set.Subset.refl A) z
  have hc := union_hits_bound A T N D hD z
  omega

lemma center_core_bounds (A : Set ℕ) (T : Finset ℕ) (N : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hD : ∀ n∈T, D n ⊆ upperEndpoints A (N n) n) (n : ℕ) (hn : n∈T) :
    sumRep (A\(T.biUnion D : Set ℕ)) n ≤ sumRep A n-2*(D n).card ∧
      sumRep A n-2*(D n).card ≤ sumRep (A\(T.biUnion D : Set ℕ)) n+
        2*∑ m∈T.erase n, (fiber A (N m) m n).card := by
  have hself := upper_target_exact A (D n) (N n) n (hD n hn)
  have hmono := sumRep_mono (show A\(T.biUnion D : Set ℕ) ⊆ A\(D n : Set ℕ) from by
    intro a ha
    exact ⟨ha.1,fun hd ↦ ha.2 (Finset.mem_biUnion.mpr ⟨n,hn,hd⟩)⟩) n
  have hdecomp : A\(T.biUnion D : Set ℕ)=
      (A\(D n : Set ℕ))\((T.erase n).biUnion D : Set ℕ) := by
    ext a
    simp only [Set.mem_diff,Finset.mem_coe,Finset.mem_biUnion,Finset.mem_erase]
    constructor
    · rintro ⟨ha,hnot⟩
      exact ⟨⟨ha,fun hd ↦ hnot ⟨n,hn,hd⟩⟩,fun ⟨m,hm,hmd⟩ ↦ hnot ⟨m,hm.2,hmd⟩⟩
    · rintro ⟨⟨ha,han⟩,hrest⟩
      refine ⟨ha,?_⟩
      rintro ⟨m,hm,hmd⟩
      by_cases he : m=n
      · subst m
        exact han hmd
      · exact hrest ⟨m,⟨he,hm⟩,hmd⟩
  have hother := deletion_inside_host A (A\(D n : Set ℕ)) ((T.erase n).biUnion D)
    Set.diff_subset n
  rw [←hdecomp] at hother
  have hcount := union_hits_bound A (T.erase n) N D
    (fun m hm ↦ (hD m (Finset.mem_erase.mp hm).2).trans (Finset.filter_subset _ _)) n
  omega

end Erdos66BatchCentralDeletion
