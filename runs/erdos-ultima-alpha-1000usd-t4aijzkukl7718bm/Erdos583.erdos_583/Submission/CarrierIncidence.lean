import Submission.Work
import Submission.CarrierCount

/-! The carrier exchanges preserve incidence at every fixed cycle vertex. -/
namespace Erdos583CarrierIncidenceDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails
open Erdos583CarrierCountDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def PreservesIncidence (T U : TrailFamily G k) (S : Set V) : Prop :=
  ∀ x ∈ S, carrierCount U {x}=carrierCount T {x}

lemma preserves_refl (T : TrailFamily G k) (S : Set V) : PreservesIncidence T T S := fun _ _ ↦ rfl

lemma preserves_trans {T U Z : TrailFamily G k} {S : Set V}
    (hTU : PreservesIncidence T U S) (hUZ : PreservesIncidence U Z S) : PreservesIncidence T Z S :=
  fun x hx ↦ (hUZ x hx).trans (hTU x hx)

lemma touches_mono {S R : Set V} {H : G.Subgraph} (hSR : S ⊆ R) (h : Touches S H) : Touches R H := by
  obtain ⟨x,hx,y,hxy⟩ := h
  exact ⟨x,hSR hx,y,hxy⟩

lemma untouched_group_preserves (T U : TrailFamily G k) (S : Set V) (F : Finset (Fin k))
    (hrest : ∀ l, l ∉ F → (U.walk l).toSubgraph=(T.walk l).toSubgraph)
    (hTF : ∀ l ∈ F, ¬Touches S (T.walk l).toSubgraph)
    (hUF : ∀ l ∈ F, ¬Touches S (U.walk l).toSubgraph) : PreservesIncidence T U S := by
  intro x hx
  apply carrierCount_congr
  intro l
  by_cases hl : l ∈ F
  · have hsub : ({x} : Set V) ⊆ S := Set.singleton_subset_iff.mpr hx
    exact iff_of_false (fun hh ↦ hUF l hl (touches_mono hsub hh)) (fun hh ↦ hTF l hl (touches_mono hsub hh))
  · rw [hrest l hl]

lemma carrierCount_two_balance (T U : TrailFamily G k) (S : Set V) (j m : Fin k) (hjm : j ≠ m)
    (hpair : (if Touches S (U.walk j).toSubgraph then 1 else 0)+(if Touches S (U.walk m).toSubgraph then 1 else 0) =
      (if Touches S (T.walk j).toSubgraph then 1 else 0)+(if Touches S (T.walk m).toSubgraph then 1 else 0))
    (hrest : ∀ l, l ≠ j → l ≠ m → (Touches S (U.walk l).toSubgraph ↔ Touches S (T.walk l).toSubgraph)) :
    carrierCount U S=carrierCount T S := by
  classical
  have hsum : ∑ l ∈ (Finset.univ.erase j).erase m, (if Touches S (U.walk l).toSubgraph then 1 else 0 : ℕ) =
      ∑ l ∈ (Finset.univ.erase j).erase m, (if Touches S (T.walk l).toSubgraph then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hlm,hlj⟩ := Finset.mem_erase.mp hl
    rw [hrest l (Finset.mem_erase.mp hlj).1 hlm]
  unfold carrierCount
  rw [NormalTrailSystem.sum_extract_two (fun l ↦ if Touches S (U.walk l).toSubgraph then 1 else 0) j m hjm,
    NormalTrailSystem.sum_extract_two (fun l ↦ if Touches S (T.walk l).toSubgraph then 1 else 0) j m hjm,hsum]
  omega

lemma carrier_cut_preserves (T U : TrailFamily G k) (S : Set V) (j m : Fin k) (hjm : j ≠ m)
    {a z b d : V} (A : G.Walk a z) (B : G.Walk z b) (Q : G.Walk z d)
    (hAB : (A.append B).IsPath) (hz : z ∉ S) (hQ : ¬Touches S Q.toSubgraph)
    (hTj : (T.walk j).toSubgraph=(A.append B).toSubgraph) (hTm : (T.walk m).toSubgraph=Q.toSubgraph)
    (hUj : (U.walk j).toSubgraph=B.toSubgraph) (hUm : (U.walk m).toSubgraph=(A.append Q).toSubgraph)
    (hrest : ∀ l, l ≠ j → l ≠ m → (U.walk l).toSubgraph=(T.walk l).toSubgraph) :
    PreservesIncidence T U S := by
  classical
  intro x hx
  apply carrierCount_two_balance T U {x} j m hjm
  · have hQx : ¬Touches ({x} : Set V) Q.toSubgraph := fun hh ↦
      hQ (touches_mono (Set.singleton_subset_iff.mpr hx) hh)
    have hboth : ¬(Touches ({x} : Set V) A.toSubgraph ∧ Touches ({x} : Set V) B.toSubgraph) := by
      rintro ⟨⟨y,hy,w,hyw⟩,⟨z',hz',v,hzv⟩⟩
      have hyx : y=x := hy
      have hzx : z'=x := hz'
      subst y z'
      have hxz : x ≠ z := fun he ↦ hz (he ▸ hx)
      exact hAB.ne_of_mem_support_of_append hxz (Walk.mem_support_of_adj_toSubgraph hyw)
        (Walk.mem_support_of_adj_toSubgraph hzv) rfl
    rw [hUj,hUm,hTj,hTm,touches_append,touches_append]
    by_cases ha : Touches ({x} : Set V) A.toSubgraph <;> by_cases hb : Touches ({x} : Set V) B.toSubgraph
    · exact (hboth ⟨ha,hb⟩).elim
    all_goals simp [ha,hb,hQx]
  · intro l hlj hlm
    rw [hrest l hlj hlm]

end Erdos583CarrierIncidenceDevelopment
