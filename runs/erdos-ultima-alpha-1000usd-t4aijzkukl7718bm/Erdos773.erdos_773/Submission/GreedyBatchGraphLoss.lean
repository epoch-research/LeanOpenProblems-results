import Submission.GreedyBatchState
import Submission.BernoulliHitCounts
import Submission.RegularizationCommonNeighbors
import Submission.GreedyLinearDrift

/-! Graph-neighborhood hitting inputs for a short batch. This module counts
losses of old edges; promotions and the joint profile iteration are separate. -/
namespace Erdos773.GreedyBatchGraphLoss
open Finset HypergraphDegreeTrim UniformLayerRegularization
open RegularizationCommonNeighbors GreedyBatchState
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 2500000
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

def neighbors (H : Finset (Finset α)) (x : α) : Finset α := univ.filter (Adj H x)

lemma mem_neighbors {H : Finset (Finset α)} {x y : α} :
    y∈neighbors H x ↔ x≠y ∧ ({x,y}:Finset α)∈H := by simp [neighbors,Adj]

lemma neighbors_symm {H : Finset (Finset α)} {x y : α}
    (h : y∈neighbors H x) : x∈neighbors H y := by
  obtain ⟨hne,he⟩ := mem_neighbors.mp h
  exact mem_neighbors.mpr ⟨hne.symm,by simpa only [pair_comm] using he⟩

lemma neighbors_card (H : Finset (Finset α)) (x : α) :
    (neighbors H x).card=degree (layer H 2) x := by
  have he : (neighbors H x).image (fun y => ({x,y}:Finset α))=(layer H 2).filter (fun e => x∈e) := by
    ext e
    constructor
    · intro he
      obtain ⟨y,hy,rfl⟩ := mem_image.mp he
      obtain ⟨hxy,he⟩ := mem_neighbors.mp hy
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,card_pair hxy⟩,by simp⟩
    · intro he
      obtain ⟨he,hx⟩ := mem_filter.mp he
      obtain ⟨he,hcard⟩ := mem_filter.mp he
      obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hcard
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_image.mpr ⟨b,mem_neighbors.mpr ⟨hab,he⟩,rfl⟩
      · exact mem_image.mpr ⟨a,mem_neighbors.mpr ⟨hab.symm,by simpa only [pair_comm] using he⟩,pair_comm _ _⟩
  have hinj : Set.InjOn (fun y => ({x,y}:Finset α)) (neighbors H x) := by
    intro y hy z hz he
    dsimp only at he
    have hm : y∈({x,z}:Finset α) := by rw [← he]; simp
    exact mem_singleton.mp ((mem_insert.mp hm).resolve_left (mem_neighbors.mp hy).1.symm)
  unfold degree
  rw [← he,card_image_of_injOn hinj]

lemma common_eq (H : Finset (Finset α)) (x y : α) :
    (neighbors H x∩neighbors H y).card=common H x y := by
  congr 1
  ext z
  simp [neighbors,both]

/-- The tracked endpoint is omitted from each killing set, avoiding its
large and irrelevant linear weight when it is itself marked. -/
def kills (H : Finset (Finset α)) (x : α) (e : Finset α) : Finset α :=
  (e.erase x).biUnion (fun z => (neighbors H z).erase x)

lemma kills_card_upper (H : Finset (Finset α)) (D : ℕ)
    (hD : ∀ z, (neighbors H z).card≤D) (x : α) (e : Finset α) :
    (kills H x e).card≤(e.erase x).card*D := by
  calc
    _ ≤ ∑ z∈e.erase x, ((neighbors H z).erase x).card := card_biUnion_le
    _ ≤ ∑ _z∈e.erase x, D := sum_le_sum (fun z hz => (card_erase_le).trans (hD z))
    _ = _ := by simp

lemma kills_card_lower (H : Finset (Finset α)) (D C : ℕ)
    (hD : ∀ z, D≤(neighbors H z).card)
    (hC : ∀ z w, z≠w → common H z w≤C) (x : α) (e : Finset α) :
    (e.erase x).card*D ≤ (kills H x e).card+(e.erase x).card+
      (e.erase x).card.choose 2*C := by
  have hi : ∀ z∈e.erase x, ∀ w∈e.erase x, z≠w →
      (((neighbors H z).erase x)∩((neighbors H w).erase x)).card≤C := by
    intro z hz w hw hzw
    apply (card_le_card (inter_subset_inter (erase_subset _ _) (erase_subset _ _))).trans
    rw [common_eq]
    exact hC z w hzw
  have hu := GreedyLinearDrift.union_card_lower (e.erase x) (fun z => (neighbors H z).erase x) C hi
  have hd (z : α) : D≤((neighbors H z).erase x).card+1 := by
    have hh := hD z
    by_cases hx : x∈neighbors H z
    · rw [card_erase_of_mem hx]
      have hp := card_pos.mpr ⟨x,hx⟩
      omega
    · rw [erase_eq_of_notMem hx]
      omega
  have hs := sum_le_sum (s := e.erase x) (fun z _ => hd z)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id] at hs
  change (∑ z∈e.erase x, ((neighbors H z).erase x).card)≤
    (kills H x e).card+(e.erase x).card.choose 2*C at hu
  omega

/-- The number of old incident edges that one mark can kill is bounded
using pair codegrees. This retains original edge indices. -/
lemma kills_incidence (H T : Finset (Finset α)) (hT : T⊆H) (x : α)
    (hx : ∀ e∈T, x∈e) (D P : ℕ) (hD : ∀ z, (neighbors H z).card≤D)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) (a : α) :
    (T.filter (fun e => a∈kills H x e)).card≤D*P := by
  have hs : T.filter (fun e => a∈kills H x e) ⊆
      (neighbors H a).biUnion (fun z => T.filter (fun e => z∈e.erase x)) := by
    intro e he
    obtain ⟨he,ha⟩ := mem_filter.mp he
    obtain ⟨z,hz,ha⟩ := mem_biUnion.mp ha
    exact mem_biUnion.mpr ⟨z,neighbors_symm (mem_erase.mp ha).2,mem_filter.mpr ⟨he,hz⟩⟩
  have hc (z : α) : (T.filter (fun e => z∈e.erase x)).card≤P := by
    by_cases hzx : z=x
    · subst z
      simp
    · apply (card_le_card (show T.filter (fun e => z∈e.erase x)⊆
        H.filter (fun e => x∈e ∧ z∈e) from ?_)).trans (hP x z (Ne.symm hzx))
      intro e he
      obtain ⟨he,hz⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨hT he,hx e he,(mem_erase.mp hz).2⟩
  calc
    _ ≤ ((neighbors H a).biUnion (fun z => T.filter (fun e => z∈e.erase x))).card := card_le_card hs
    _ ≤ ∑ z∈neighbors H a, (T.filter (fun e => z∈e.erase x)).card := card_biUnion_le
    _ ≤ ∑ _z∈neighbors H a, P := sum_le_sum (fun z _ => hc z)
    _ = (neighbors H a).card*P := by simp
    _ ≤ _ := Nat.mul_le_mul_right P (hD a)

/-- Rank-two old edges have the sharper common-neighbor incidence cap,
not the much larger D*P bound. -/
lemma kills_two_incidence (H T : Finset (Finset α)) (hT : T⊆H) (x : α)
    (hx : ∀ e∈T, x∈e) (h2 : ∀ e∈T, e.card=2) (C : ℕ)
    (hC : ∀ a, x≠a → common H x a≤C) (a : α) :
    (T.filter (fun e => a∈kills H x e)).card≤C := by
  by_cases hax : a=x
  · subst a
    have he : T.filter (fun e => x∈kills H x e)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨z,hz,ha⟩ := mem_biUnion.mp (mem_filter.mp he).2
      exact notMem_erase x (neighbors H z) ha
    rw [he,card_empty]
    exact Nat.zero_le _
  · have hb : (T.filter (fun e => a∈kills H x e)).card≤
        ((neighbors H x∩neighbors H a).powersetCard 1).card := by
      apply card_le_card_of_injOn (fun e : Finset α => e.erase x)
      · intro e he
        obtain ⟨he,ha⟩ := mem_filter.mp he
        have hc : (e.erase x).card=1 := by rw [card_erase_of_mem (hx e he),h2 e he]
        obtain ⟨z,hz,ha⟩ := mem_biUnion.mp ha
        have hze : e.erase x={z} := (card_eq_one.mp hc).elim (fun b hb => by
          have hzb : z=b := mem_singleton.mp (hb ▸ hz)
          simpa only [hzb] using hb)
        have heq : e=({x,z}:Finset α) := by rw [← insert_erase (hx e he),hze]
        have hzx : z∈neighbors H x := mem_neighbors.mpr ⟨(mem_erase.mp hz).1.symm,heq ▸ hT he⟩
        refine mem_powersetCard.mpr ⟨?_,hc⟩
        dsimp only
        rw [hze]
        exact singleton_subset_iff.mpr (mem_inter.mpr ⟨hzx,neighbors_symm (mem_erase.mp ha).2⟩)
      · intro e he f hf hef
        dsimp only at hef
        rw [← insert_erase (hx e (mem_filter.mp he).1),← insert_erase (hx f (mem_filter.mp hf).1),hef]
    rw [card_powersetCard,Nat.choose_one_right,common_eq] at hb
    exact hb.trans (hC a (Ne.symm hax))

/-- An old edge lying wholly in the new carrier cannot have been hit by
any graph-neighborhood killing mark. -/
lemma surviving_unhit (H : Finset (Finset α)) (R : Finset α) (x : α) (e : Finset α)
    (he : e⊆carrier H R) : Disjoint (kills H x e) R := by
  apply disjoint_left.mpr
  intro a ha haR
  obtain ⟨z,hz,ha⟩ := mem_biUnion.mp ha
  obtain ⟨hza,hpair⟩ := mem_neighbors.mp (mem_erase.mp ha).2
  apply (mem_carrier.mp (he (mem_erase.mp hz).2)).2
  refine mem_closed.mpr ⟨{z,a},hpair,by simp,?_⟩
  have he : ({z,a}:Finset α).erase z={a} := by simp [hza]
  rw [he]
  exact singleton_subset_iff.mpr haR

lemma old_survival_balance (H T : Finset (Finset α)) (R : Finset α) (x : α) :
    (T.filter (fun e => e⊆carrier H R)).card+
      BernoulliHitCounts.hitCount T (kills H x) R≤T.card := by
  have hd : Disjoint (T.filter (fun e => e⊆carrier H R))
      (T.filter (fun e => (kills H x e∩R).Nonempty)) := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha⟩ := (mem_filter.mp hf).2
    exact disjoint_left.mp (surviving_unhit H R x e (mem_filter.mp he).2)
      (mem_inter.mp ha).1 (mem_inter.mp ha).2
  unfold BernoulliHitCounts.hitCount
  rw [← card_union_of_disjoint hd]
  exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))

/-- Actual upper tail for the number of uncontracted old edges remaining
in the conservative carrier. The mean uses the proved killing sets. -/
theorem old_survival_tail (H T : Finset (Finset α)) (x : α) (j D M q : ℕ)
    (hx : ∀ e∈T, x∈e) (hj : ∀ e∈T, e.card=j)
    (hD : ∀ z, (neighbors H z).card≤D)
    (hM : ∀ a, (T.filter (fun e => a∈kills H x e)).card≤M) (hMpos : 0<M)
    (p η L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) (hL : 0<L) :
    (∑ f : α → Bool, if (T.card:ℝ)-(1-η)*(p*∑ e∈T, ((kills H x e).card:ℝ))+L ≤
      ((T.filter (fun e => e⊆carrier H (selected f))).card:ℝ) then trialWeight p f else 0) ≤
      Real.exp (-η^2*(p*∑ e∈T, ((kills H x e).card:ℝ))/(2*M))+
        (IndexedBernoulliMoments.budget 2 q
          (BernoulliHitCounts.overlapCaps T.card ((j-1)*D) M) p/L)^q := by
  have hs (e : Finset α) (he : e∈T) : (kills H x e).card≤(j-1)*D := by
    have hh := kills_card_upper H D hD x e
    rwa [card_erase_of_mem (hx e he),hj e he] at hh
  apply le_trans ?_ (BernoulliHitCounts.lower_tail T (kills H x) ((j-1)*D) M q p η L
    hs hM hMpos hp hp1 hη hL)
  apply sum_le_sum
  intro f hf
  split_ifs with h0 h1
  all_goals try exact le_refl _
  all_goals try exact trialWeight_nonneg hp hp1 f
  have hb : ((T.filter (fun e => e⊆carrier H (selected f))).card:ℝ)+
      (BernoulliHitCounts.hitCount T (kills H x) (selected f):ℝ)≤T.card := by
    exact_mod_cast old_survival_balance H T (selected f) x
  exact (h1 (by linarith only [h0,hb])).elim

/-- A deterministic lower bound for the mean number of killing marks.
Only pairwise graph common-neighbor control is used. -/
lemma kill_mean_lower (H T : Finset (Finset α)) (x : α) (j D C : ℕ)
    (hx : ∀ e∈T, x∈e) (hj : ∀ e∈T, e.card=j)
    (hD : ∀ z, D≤(neighbors H z).card) (hC : ∀ z w, z≠w → common H z w≤C)
    (p : ℝ) (hp : 0≤p) :
    p*T.card*((j-1)*D:ℕ) ≤ (p*∑ e∈T, ((kills H x e).card:ℝ))+
      p*T.card*((j-1)+(j-1).choose 2*C:ℕ) := by
  have hrow (e : Finset α) (he : e∈T) : (j-1)*D≤(kills H x e).card+(j-1)+(j-1).choose 2*C := by
    have hh := kills_card_lower H D C hD hC x e
    rwa [card_erase_of_mem (hx e he),hj e he] at hh
  have hs := sum_le_sum (s := T) hrow
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at hs
  have hs' : (T.card:ℝ)*((j-1)*D:ℕ)≤(∑ e∈T, ((kills H x e).card:ℝ))+
      T.card*(j-1:ℕ)+T.card*((j-1).choose 2*C:ℕ) := by exact_mod_cast hs
  have hh := mul_le_mul_of_nonneg_left hs' hp
  push_cast at *
  nlinarith only [hh]

#print axioms neighbors_card
#print axioms kills_card_lower
#print axioms kills_incidence
#print axioms kills_two_incidence
#print axioms surviving_unhit
#print axioms old_survival_balance
#print axioms old_survival_tail
#print axioms kill_mean_lower
end
end Erdos773.GreedyBatchGraphLoss
