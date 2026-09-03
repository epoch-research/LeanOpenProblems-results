import Submission.MatchingPartitionExplore
import Submission.BoundedConflictExplore
import Submission.MultiPacketSelectionExplore

/-! Unintended sums of injectively labelled packets have bounded coordinate
incidence. A matching partition function controls them without requiring
Sidon uniqueness. -/
namespace Erdos66PacketMatching
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66MatchingPartition
  Erdos66BoundedConflict Erdos66HeterogeneousSelection Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1400000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Edge (ι : Type*) := (ι × Bool) × (ι × Bool)

def support (p : Edge ι) : Finset ι := {p.1.1,p.2.1}

noncomputable def sumEvents : Finset (Edge ι) :=
  Finset.univ.filter (fun p ↦ ¬ Designated p.1 p.2)

lemma support_nonempty (p : Edge ι) : (support p).Nonempty := by
  exact ⟨p.1.1,by simp [support]⟩

lemma sum_fiber (n : ι → ℤ) (u v : ι × Bool) (hnd : ¬ Designated u v)
    (z : ℤ) (i : ι) (hi : i = u.1 ∨ i = v.1) :
    ∀ f : ι → ℤ, ∀ a b : ℤ,
      point n (Function.update f i a) u + point n (Function.update f i a) v = z →
      point n (Function.update f i b) u + point n (Function.update f i b) v = z → a = b := by
  obtain ⟨j,s⟩ := u
  obtain ⟨k,t⟩ := v
  dsimp only [Prod.fst,Prod.snd] at hi
  rcases hi with hi | hi
  all_goals
    subst i
    intro f a b ha hb
    by_cases hjk : j = k
    · subst k
      cases s <;> cases t <;> simp [Designated] at hnd
      all_goals simp only [point,Prod.fst,Prod.snd,Bool.false_eq_true,if_false,if_true,Function.update_self] at ha hb
      all_goals omega
    · cases s <;> cases t <;>
        simp only [point,Bool.false_eq_true,if_false,if_true,Function.update_self,
          Function.update_of_ne hjk,Function.update_of_ne (Ne.symm hjk)] at ha hb <;> omega

lemma incident_card (n x : ι → ℤ) (hinj : Function.Injective (point n x))
    (z : ℤ) (S : Finset (Edge ι))
    (hS : ∀ p ∈ S, point n x p.1 + point n x p.2 = z) (i : ι) :
    (S.filter (fun p ↦ i ∈ support p)).card ≤ 4 := by
  let T := S.filter (fun p ↦ i ∈ support p)
  let tag (p : Edge ι) : Bool × Bool :=
    if p.1.1 = i then (false,p.1.2) else (true,p.2.2)
  have hin : ∀ p ∈ T, p.1.1 = i ∨ p.2.1 = i := by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    simpa [support,eq_comm] using hh
  have htag : Set.InjOn tag (T : Set (Edge ι)) := by
    intro p hp q hq he
    have hpz := hS p (Finset.mem_filter.mp hp).1
    have hqz := hS q (Finset.mem_filter.mp hq).1
    by_cases hp₁ : p.1.1 = i <;> by_cases hq₁ : q.1.1 = i
    · have hh : p.1.2 = q.1.2 := by simpa [tag,hp₁,hq₁] using congrArg Prod.snd he
      have h₁ : p.1 = q.1 := Prod.ext (hp₁.trans hq₁.symm) hh
      have h₂ : p.2 = q.2 := hinj (by rw [h₁] at hpz; linarith)
      exact Prod.ext h₁ h₂
    · have hh := congrArg Prod.fst he
      simp [tag,hp₁,hq₁] at hh
    · have hh := congrArg Prod.fst he
      simp [tag,hp₁,hq₁] at hh
    · have hp₂ := (hin p hp).resolve_left hp₁
      have hq₂ := (hin q hq).resolve_left hq₁
      have hh : p.2.2 = q.2.2 := by simpa [tag,hp₁,hq₁] using congrArg Prod.snd he
      have h₂ : p.2 = q.2 := Prod.ext (hp₂.trans hq₂.symm) hh
      have h₁ : p.1 = q.1 := hinj (by rw [h₂] at hpz; linarith)
      exact Prod.ext h₁ h₂
  calc
    T.card = (T.image tag).card := (Finset.card_image_of_injOn htag).symm
    _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by decide

lemma conflict_card (n x : ι → ℤ) (hinj : Function.Injective (point n x))
    (z : ℤ) (S : Finset (Edge ι))
    (hS : ∀ p ∈ S, point n x p.1 + point n x p.2 = z) (p : Edge ι) :
    (S.filter (fun q ↦ ¬ Disjoint (support p) (support q))).card ≤ 8 := by
  have hsub : S.filter (fun q ↦ ¬ Disjoint (support p) (support q)) ⊆
      S.filter (fun q ↦ p.1.1 ∈ support q) ∪ S.filter (fun q ↦ p.2.1 ∈ support q) := by
    intro q hq
    obtain ⟨hq,hd⟩ := Finset.mem_filter.mp hq
    have hh : p.1.1 ∈ support q ∨ p.2.1 ∈ support q := by
      simpa only [support,Finset.disjoint_insert_left,Finset.disjoint_singleton_left,
        not_and_or,not_not] using hd
    rcases hh with hh | hh
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq,hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq,hh⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h₁ := incident_card n x hinj z S hS p.1.1
  have h₂ := incident_card n x hinj z S hS p.2.1
  omega

variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

noncomputable def sumIndicator (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (z : ℤ) (p : Edge ι) (ω : ∀ i, α i) : ℝ :=
  if point n (chosen x ω) p.1 + point n (chosen x ω) p.2 = z then 1 else 0

noncomputable def offPairs (n : ι → ℤ) (x : ∀ i, α i → ℤ)
    (z : ℤ) (ω : ∀ i, α i) : Finset (Edge ι) :=
  sumEvents.filter (fun p ↦ point n (chosen x ω) p.1 + point n (chosen x ω) p.2 = z)

lemma sumIndicator_nonneg (n : ι → ℤ) (x : ∀ i, α i → ℤ) (z : ℤ) (p : Edge ι) (ω : ∀ i, α i) :
    0 ≤ sumIndicator n x z p ω := by unfold sumIndicator; split_ifs <;> norm_num

lemma sumIndicator_depends (n : ι → ℤ) (x : ∀ i, α i → ℤ) (z : ℤ) (p : Edge ι) :
    DependsOn (sumIndicator n x z p) (support p) := by
  intro ω η he
  have h₁ := he p.1.1 (by simp [support])
  have h₂ := he p.2.1 (by simp [support])
  simp only [sumIndicator,point,chosen,h₁,h₂]

lemma offPairs_exp_le (n : ι → ℤ) (x : ∀ i, α i → ℤ) (z : ℤ)
    (ω : ∀ i, α i) (hinj : Function.Injective (point n (chosen x ω))) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t * (offPairs n x z ω).card) ≤
      partition sumEvents support (sumIndicator n x z) (8*t) ω := by
  let S := offPairs n x z ω
  have hS : ∀ p ∈ S, point n (chosen x ω) p.1 + point n (chosen x ω) p.2 = z :=
    fun p hp ↦ (Finset.mem_filter.mp hp).2
  obtain ⟨M,hMS,hM,hcard⟩ := exists_large_disjoint S support 8
    (fun p _ ↦ support_nonempty p) (fun p _ ↦ conflict_card n (chosen x ω) hinj z S hS p)
  have hreal : ∀ p ∈ M, sumIndicator n x z p ω = 1 := by
    intro p hp
    simp only [sumIndicator,if_pos (hS p (hMS hp))]
  have hcard' : (S.card : ℝ) ≤ 8*(M.card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ Real.exp ((8*t)*M.card) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := exp_card_le_partition sumEvents M support (sumIndicator n x z) (8*t)
      (by positivity) ω (fun p _ ↦ sumIndicator_nonneg n x z p ω)
      (hMS.trans (Finset.filter_subset _ _)) hM hreal

end Erdos66PacketMatching
