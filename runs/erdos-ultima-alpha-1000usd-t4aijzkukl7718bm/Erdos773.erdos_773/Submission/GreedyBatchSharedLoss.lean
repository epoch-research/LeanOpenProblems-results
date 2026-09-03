import Submission.GreedyBatchGraphLoss
import Submission.RegularizationSharedLinks

/-! Graph-neighborhood loss and concentration for old shared rank-three
links. The shared-link family has vertex degree controlled by the original
pair codegree; no regularity of that family is assumed. -/
namespace Erdos773.GreedyBatchSharedLoss
open Finset HypergraphDegreeTrim UniformLayerRegularization
open GreedyBatchGraphLoss GreedyBatchState RegularizationSharedLinks
open RegularizationCommonNeighbors (common)
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma vertex_incidence (H : Finset (Finset α)) (x y : α) (P : ℕ)
    (hP : ∀ a, x≠a → pairDegree H x a≤P) (a : α) :
    ((links H x y).filter (fun A => a∈A)).card≤P := by
  by_cases hax : a=x
  · subst a
    have he : (links H x y).filter (fun A => x∈A)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact (mem_links.mp (mem_filter.mp hA).1).2.1 (mem_filter.mp hA).2
    rw [he,card_empty]
    exact Nat.zero_le _
  · apply (show ((links H x y).filter (fun A => a∈A)).card≤
        (H.filter (fun e => x∈e ∧ a∈e)).card from ?_).trans (hP a (Ne.symm hax))
    apply card_le_card_of_injOn (insert x)
    · intro A hA
      obtain ⟨hA,ha⟩ := mem_filter.mp hA
      exact mem_filter.mpr ⟨(mem_links.mp hA).2.2.2.1,mem_insert_self _ _,mem_insert_of_mem ha⟩
    · intro A hA B hB he
      have hxA := (mem_links.mp (mem_filter.mp hA).1).2.1
      have hxB := (mem_links.mp (mem_filter.mp hB).1).2.1
      have hh := congrArg (fun S : Finset α => S.erase x) he
      simpa only [erase_insert hxA,erase_insert hxB] using hh

lemma kill_size (H : Finset (Finset α)) (x y : α) (D : ℕ)
    (hD : ∀ z, (neighbors H z).card≤D) (A : Finset α) (hA : A∈links H x y) :
    (kills H x A).card≤2*D := by
  obtain ⟨hc,hx,_⟩ := mem_links.mp hA
  have hh := kills_card_upper H D hD x A
  rwa [erase_eq_of_notMem hx,hc] at hh

lemma kill_incidence (H : Finset (Finset α)) (x y : α) (D P : ℕ)
    (hD : ∀ z, (neighbors H z).card≤D) (hP : ∀ a, x≠a → pairDegree H x a≤P) (a : α) :
    ((links H x y).filter (fun A => a∈kills H x A)).card≤D*P := by
  have hs : (links H x y).filter (fun A => a∈kills H x A)⊆
      (neighbors H a).biUnion (fun z => (links H x y).filter (fun A => z∈A)) := by
    intro A hA
    obtain ⟨hA,ha⟩ := mem_filter.mp hA
    obtain ⟨z,hz,ha⟩ := mem_biUnion.mp ha
    exact mem_biUnion.mpr ⟨z,neighbors_symm (mem_erase.mp ha).2,
      mem_filter.mpr ⟨hA,(mem_erase.mp hz).2⟩⟩
  calc
    _ ≤ ((neighbors H a).biUnion (fun z => (links H x y).filter (fun A => z∈A))).card := card_le_card hs
    _ ≤ ∑ z∈neighbors H a, ((links H x y).filter (fun A => z∈A)).card := card_biUnion_le
    _ ≤ ∑ _z∈neighbors H a, P := sum_le_sum (fun z hz => vertex_incidence H x y P hP z)
    _ = (neighbors H a).card*P := by simp
    _ ≤ _ := Nat.mul_le_mul_right P (hD a)

def oldCount (H : Finset (Finset α)) (x y : α) (R : Finset α) : ℕ :=
  ((links H x y).filter (fun A => A⊆carrier H R)).card

/-- Upper tail for the number of old shared links surviving in Q. -/
theorem old_survival_tail (H : Finset (Finset α)) (x y : α) (D P q : ℕ)
    (hD : ∀ z, (neighbors H z).card≤D) (hP : ∀ a, x≠a → pairDegree H x a≤P)
    (hDP : 0<D*P) (p η L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) (hL : 0<L) :
    (∑ f : α → Bool, if (count H x y:ℝ)-
      (1-η)*(p*∑ A∈links H x y, ((kills H x A).card:ℝ))+L≤(oldCount H x y (selected f):ℝ)
      then trialWeight p f else 0) ≤
      Real.exp (-η^2*(p*∑ A∈links H x y, ((kills H x A).card:ℝ))/(2*(D*P:ℕ)))+
        (IndexedBernoulliMoments.budget 2 q
          (BernoulliHitCounts.overlapCaps (count H x y) (2*D) (D*P)) p/L)^q := by
  apply le_trans ?_ (BernoulliHitCounts.lower_tail (links H x y) (kills H x) (2*D) (D*P) q p η L
    (kill_size H x y D hD) (kill_incidence H x y D P hD hP) hDP hp hp1 hη hL)
  apply sum_le_sum
  intro f hf
  split_ifs with h0 h1
  all_goals try exact le_refl _
  all_goals try exact trialWeight_nonneg hp hp1 f
  have hb : (oldCount H x y (selected f):ℝ)+
      (BernoulliHitCounts.hitCount (links H x y) (kills H x) (selected f):ℝ)≤count H x y := by
    exact_mod_cast GreedyBatchGraphLoss.old_survival_balance H (links H x y) (selected f) x
  exact (h1 (by linarith only [h0,hb])).elim

/-- The old-link mean loses nearly two graph-degree factors. -/
lemma kill_mean_lower (H : Finset (Finset α)) (x y : α) (D C : ℕ)
    (hD : ∀ z, D≤(neighbors H z).card) (hC : ∀ z w, z≠w → common H z w≤C)
    (p : ℝ) (hp : 0≤p) :
    p*count H x y*(2*D:ℕ) ≤ (p*∑ A∈links H x y, ((kills H x A).card:ℝ))+
      p*count H x y*(2+C:ℕ) := by
  have hrow (A : Finset α) (hA : A∈links H x y) : 2*D≤(kills H x A).card+2+C := by
    obtain ⟨hc,hx,_⟩ := mem_links.mp hA
    have hh := kills_card_lower H D C hD hC x A
    simpa only [erase_eq_of_notMem hx,hc,Nat.choose_self,Nat.one_mul] using hh
  have hs := sum_le_sum (s := links H x y) hrow
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at hs
  have hs' : (count H x y:ℝ)*(2*D:ℕ)≤(∑ A∈links H x y, ((kills H x A).card:ℝ))+
      count H x y*2+count H x y*C := by exact_mod_cast hs
  have hh := mul_le_mul_of_nonneg_left hs' hp
  push_cast at *
  nlinarith only [hh]

#print axioms vertex_incidence
#print axioms kill_incidence
#print axioms old_survival_tail
#print axioms kill_mean_lower
end
end Erdos773.GreedyBatchSharedLoss
