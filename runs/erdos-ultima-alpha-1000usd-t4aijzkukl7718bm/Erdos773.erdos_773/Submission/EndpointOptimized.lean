import FormalConjecturesUtil

/-!
# Erdős Problem 773

Single-file consolidation of the proved two-thirds endpoint.
This file proves only the two-thirds endpoint, not the near-linear conjecture.
-/

set_option Elab.async false
set_option linter.all false
set_option linter.unusedSectionVars false

-- Begin HypergraphDegreeTrim.lean
section EndpointModule000

/- Removing vertices of high incidence degree from a finite four-uniform hypergraph. -/
namespace Erdos773.HypergraphDegreeTrim
open Finset
set_option maxHeartbeats 1000000
variable {α : Type*} [DecidableEq α]

def degree (H : Finset (Finset α)) (a : α) : ℕ :=
  (H.filter (fun e => a ∈ e)).card

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.HypergraphDegreeTrim
end EndpointModule000
-- End HypergraphDegreeTrim.lean

-- Begin FourUniformRegularization.lean
section EndpointModule001

/-
A finite regularization construction. Copies of a hypergraph are supplemented
by affine-line edges between copies of the same original vertex. The added
edges have pair codegree at most one. This is preparatory work, not an
independent-set lower bound or a proof of Erdős 773.
-/
namespace Erdos773.FourUniformRegularization
open Finset HypergraphDegreeTrim
set_option maxHeartbeats 1500000
noncomputable section
variable {α F : Type*} [Fintype α] [DecidableEq α]
  [Field F] [Fintype F] [DecidableEq F]

-- Unused development declaration omitted.
-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

def pairDegree {β : Type*} [DecidableEq β] (H : Finset (Finset β)) (x y : β) : ℕ :=
  (H.filter (fun e => x ∈ e ∧ y ∈ e)).card

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.FourUniformRegularization
end EndpointModule001
-- End FourUniformRegularization.lean

-- Begin GreedyHypergraphState.lean
section EndpointModule002

/-
Exact states and updates for greedy hypergraph independence. Residual edges
are indexed by their ORIGINAL edges; different contractions are not silently
identified. These identities do not constitute a random-greedy lower bound.
-/
namespace Erdos773.GreedyHypergraphState
open Finset FourUniformRegularization
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def Independent (H : Finset (Finset α)) (I : Finset α) : Prop :=
  ∀ e ∈ H, ¬e ⊆ I

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyHypergraphState
end EndpointModule002
-- End GreedyHypergraphState.lean

-- Begin Hypergraph.lean
section EndpointModule003

/- Finite alteration lemmas for the Sidon-subset problem. -/

namespace Erdos773

lemma delete_forbidden_edges {α : Type*} [DecidableEq α]
    (A : Finset α) (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty) :
    ∃ B ⊆ A, A.card ≤ B.card + H.card ∧ ∀ e ∈ H, ¬e ⊆ B := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨A, Finset.Subset.refl A, by simp, by simp⟩
  | @insert e H he ih =>
    obtain ⟨B, hBA, hcard, havoid⟩ := ih (fun f hf => hH f (Finset.mem_insert_of_mem hf))
    obtain ⟨a, ha⟩ := hH e (Finset.mem_insert_self e H)
    refine ⟨B.erase a, (Finset.erase_subset a B).trans hBA, ?_, ?_⟩
    · have hc : B.card ≤ (B.erase a).card + 1 := by
        by_cases hab : a ∈ B
        · rw [Finset.card_erase_of_mem hab]
          have : 0 < B.card := Finset.card_pos.mpr ⟨a, hab⟩
          omega
        · simp [Finset.erase_eq_of_notMem hab]
      rw [Finset.card_insert_of_notMem he]
      omega
    · intro f hf hfB
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Finset.notMem_erase a B (hfB ha)
      · exact havoid f hf (hfB.trans (Finset.erase_subset a B))

section Bernoulli

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def trialWeight (p : ℝ) (f : α → Bool) : ℝ :=
  ∏ i, if f i then p else 1 - p

def selected (f : α → Bool) : Finset α := univ.filter (fun i => f i)

lemma trialWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : α → Bool) :
    0 ≤ trialWeight p f := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> linarith

lemma sum_trialWeight (p : ℝ) : ∑ f : α → Bool, trialWeight p f = 1 := by
  unfold trialWeight
  rw [← Fintype.prod_sum (fun (_ : α) (b : Bool) => if b then p else 1 - p)]
  simp

lemma sum_trialWeight_contains (p : ℝ) (e : Finset α) :
    (∑ f : α → Bool, if e ⊆ selected f then trialWeight p f else 0) = p ^ e.card := by
  have hterm (f : α → Bool) :
      (if e ⊆ selected f then trialWeight p f else 0) =
        ∏ i, if i ∈ e then (if f i then p else 0) else (if f i then p else 1 - p) := by
    by_cases h : e ⊆ selected f
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hie : i ∈ e
      · have hf : f i = true := by simpa [selected] using h hie
        simp [hie, hf]
      · simp [hie]
    · rw [if_neg h]
      obtain ⟨i, hie, hi⟩ := Finset.not_subset.mp h
      have hf : f i = false := by simpa [selected] using hi
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hie, hf]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : α) (b : Bool) =>
    if i ∈ e then (if b then p else 0) else (if b then p else 1 - p))]
  simp

lemma sum_trialWeight_card (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f * ((selected f).card : ℝ)) = p * Fintype.card α := by
  calc
    _ = ∑ f : α → Bool, ∑ i : α,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [Finset.singleton_subset_iff, Finset.sum_ite_mem, mul_comm]
    _ = ∑ i : α, ∑ f : α → Bool,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = p * Fintype.card α := by
      simp_rw [sum_trialWeight_contains]
      simp [mul_comm]

lemma sum_trialWeight_edgeCount (p : ℝ) (H : Finset (Finset α)) :
    (∑ f : α → Bool, trialWeight p f * ((H.filter (· ⊆ selected f)).card : ℝ)) =
      ∑ e ∈ H, p ^ e.card := by
  calc
    _ = ∑ f : α → Bool, ∑ e ∈ H,
        if e ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.sum_filter, mul_comm]
    _ = ∑ e ∈ H, ∑ f : α → Bool,
        if e ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = ∑ e ∈ H, p ^ e.card := by simp_rw [sum_trialWeight_contains]

-- Unused development declaration omitted.

end Bernoulli

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.


end Erdos773
end EndpointModule003
-- End Hypergraph.lean

-- Begin GreedyBatchState.lean
section EndpointModule004

/- A conservative batched greedy state. Rejected marked vertices remain
outside the next carrier. This prevents alteration from reopening constraints.
The expectation identities here do not assert local profile concentration. -/
namespace Erdos773.GreedyBatchState
open Finset GreedyHypergraphState
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

def discarded (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  (H.filter (·⊆R)).biUnion id

def chosen (H : Finset (Finset α)) (R : Finset α) : Finset α := R \ discarded H R

def closed (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  H.biUnion (fun e => e.filter (fun v => e.erase v⊆R))

def discardCost (H : Finset (Finset α)) (R : Finset α) : ℕ :=
  ∑ e∈H, if e⊆R then e.card else 0

def closureCost (H : Finset (Finset α)) (R : Finset α) : ℕ :=
  ∑ e∈H, (e.filter (fun v => e.erase v⊆R)).card

lemma chosen_subset (H : Finset (Finset α)) (R : Finset α) : chosen H R⊆R := sdiff_subset

lemma mem_closed {H : Finset (Finset α)} {R : Finset α} {x : α} :
    x∈closed H R ↔ ∃ e∈H, x∈e ∧ e.erase x⊆R := by
  simp [closed]

/-- All vertices of any fully marked edge are rejected. -/
lemma chosen_independent (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.Nonempty) : Independent H (chosen H R) := by
  intro e he hesub
  obtain ⟨x,hx⟩ := hH e he
  have hxJ := hesub hx
  have hxD : x∈discarded H R := mem_biUnion.mpr
    ⟨e,mem_filter.mpr ⟨he,hesub.trans (chosen_subset H R)⟩,hx⟩
  exact (mem_sdiff.mp hxJ).2 hxD

lemma chosen_card (H : Finset (Finset α)) (R : Finset α) :
    R.card≤(chosen H R).card+discardCost H R := by
  have hs : R⊆chosen H R∪discarded H R := by
    intro a ha
    by_cases hd : a∈discarded H R
    · exact mem_union_right _ hd
    · exact mem_union_left _ (mem_sdiff.mpr ⟨ha,hd⟩)
  have hc : (discarded H R).card≤discardCost H R := by
    have hh := card_biUnion_le (s := H.filter (·⊆R)) (t := id)
    simpa only [discardCost,sum_filter] using hh
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left hc _))

variable [Fintype α]

def carrier (H : Finset (Finset α)) (R : Finset α) : Finset α :=
  univ \ (R∪closed H R)

lemma mem_carrier {H : Finset (Finset α)} {R : Finset α} {x : α} :
    x∈carrier H R ↔ x∉R ∧ x∉closed H R := by simp [carrier]

lemma carrier_disjoint (H : Finset (Finset α)) (R : Finset α) : Disjoint (carrier H R) R :=
  disjoint_left.mpr (fun _ hx hxR => (mem_carrier.mp hx).1 hxR)

lemma carrier_card (H : Finset (Finset α)) (R : Finset α) :
    Fintype.card α≤(carrier H R).card+R.card+closureCost H R := by
  have hh := card_sdiff_add_card_eq_card (subset_univ (R∪closed H R))
  rw [card_univ] at hh
  have hc : (closed H R).card≤closureCost H R := card_biUnion_le
  have hu := card_union_le R (closed H R)
  change (carrier H R).card+(R∪closed H R).card=Fintype.card α at hh
  omega

/-- Empty residuals are omitted: they are already dealt with by alteration.
Singleton residuals cannot meet the conservative carrier. -/
def next (H : Finset (Finset α)) (R : Finset α) : Finset (Finset α) :=
  (H.filter (fun e => 2≤(e \ R).card ∧ e \ R⊆carrier H R)).image (fun e => e \ R)

lemma next_subset {H : Finset (Finset α)} {R f : Finset α} (hf : f∈next H R) :
    f⊆carrier H R := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact (mem_filter.mp he).2.2

lemma next_rank {H : Finset (Finset α)} {R : Finset α} (hH : ∀ e∈H, e.card≤4)
    {f : Finset α} (hf : f∈next H R) : 2≤f.card ∧ f.card≤4 := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  obtain ⟨he,hlo,hQ⟩ := mem_filter.mp he
  exact ⟨hlo,(card_le_card sdiff_subset).trans (hH e he)⟩

/-- A sufficient residual system for genuine extensions. The tentative
mark set itself need not be independent. -/
theorem extension {H : Finset (Finset α)} (R : Finset α)
    (hH : ∀ e∈H, e.Nonempty) {A : Finset α} (hA : A⊆carrier H R)
    (hi : Independent (next H R) A) : Independent H (chosen H R∪A) := by
  intro e he hesub
  have hres : e \ R⊆A := by
    intro x hx
    rcases mem_union.mp (hesub (mem_sdiff.mp hx).1) with hxJ | hxA
    · exact ((mem_sdiff.mp hx).2 (chosen_subset H R hxJ)).elim
    · exact hxA
  have hnon : (e \ R).Nonempty := by
    apply sdiff_nonempty.mpr
    intro heR
    apply chosen_independent H R hH e he
    intro x hx
    rcases mem_union.mp (hesub hx) with hxJ | hxA
    · exact hxJ
    · exact ((mem_carrier.mp (hA hxA)).1 (heR hx)).elim
  have hnotone : (e \ R).card≠1 := by
    intro h1
    obtain ⟨x,hx⟩ := card_eq_one.mp h1
    have hxe : x∈e \ R := by rw [hx]; simp
    have hxQ := hA (hres hxe)
    apply (mem_carrier.mp hxQ).2
    apply mem_closed.mpr
    refine ⟨e,he,(mem_sdiff.mp hxe).1,?_⟩
    intro y hy
    by_contra hyR
    have hm : y∈e \ R := mem_sdiff.mpr ⟨(mem_erase.mp hy).2,hyR⟩
    rw [hx] at hm
    exact (mem_erase.mp hy).1 (mem_singleton.mp hm)
  have hlo : 2≤(e \ R).card := by have := card_pos.mpr hnon; omega
  exact hi (e \ R) (mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hlo,hres.trans hA⟩,rfl⟩) hres

lemma extension_card (H : Finset (Finset α)) (R : Finset α) {A : Finset α}
    (hA : A⊆carrier H R) : (chosen H R∪A).card=(chosen H R).card+A.card := by
  apply card_union_of_disjoint
  exact ((carrier_disjoint H R).mono hA (chosen_subset H R)).symm

lemma discardCost_expectation (H : Finset (Finset α)) (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f*(discardCost H (selected f):ℝ)) =
      ∑ e∈H, (e.card:ℝ)*p^e.card := by
  simp only [discardCost,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  calc
    _ = (e.card:ℝ)*(∑ f : α → Bool, if e⊆selected f then trialWeight p f else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> ring
    _ = _ := by rw [sum_trialWeight_contains]

lemma closureCost_expectation (H : Finset (Finset α)) (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f*(closureCost H (selected f):ℝ)) =
      ∑ e∈H, (e.card:ℝ)*p^(e.card-1) := by
  simp only [closureCost,Nat.cast_sum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hc (f : α → Bool) : ((e.filter (fun v => e.erase v⊆selected f)).card:ℝ)=
      ∑ v∈e, if e.erase v⊆selected f then (1:ℝ) else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [hc,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ v∈e, p^(e.erase v).card := by
      apply sum_congr rfl
      intro v hv
      have hh := sum_trialWeight_contains p (e.erase v)
      convert hh using 1
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ = ∑ _v∈e, p^(e.card-1) := sum_congr rfl (fun v hv => by rw [card_erase_of_mem hv])
    _ = _ := by simp

/-- Expected reward for one batched stage followed by a hypothetical
residual density δ. The local-profile and subsequent density bounds are
not asserted by this lemma. -/
theorem reward_expectation (H : Finset (Finset α)) (p δ : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hδ : 0≤δ) :
    p*Fintype.card α-(∑ e∈H, (e.card:ℝ)*p^e.card)+
      δ*((1-p)*Fintype.card α-∑ e∈H, (e.card:ℝ)*p^(e.card-1)) ≤
      ∑ f : α → Bool, trialWeight p f*
        ((chosen H (selected f)).card+δ*(carrier H (selected f)).card) := by
  have hpoint (f : α → Bool) :
      ((selected f).card:ℝ)-(discardCost H (selected f):ℝ)+
        δ*(Fintype.card α-(selected f).card-(closureCost H (selected f):ℝ)) ≤
        (chosen H (selected f)).card+δ*(carrier H (selected f)).card := by
    have hJ : ((selected f).card:ℝ)≤(chosen H (selected f)).card+(discardCost H (selected f):ℝ) := by
      exact_mod_cast chosen_card H (selected f)
    have hQ : (Fintype.card α:ℝ)≤(carrier H (selected f)).card+(selected f).card+
        (closureCost H (selected f):ℝ) := by exact_mod_cast carrier_card H (selected f)
    nlinarith only [hJ,mul_le_mul_of_nonneg_left hQ hδ]
  have hh := sum_le_sum (s := (univ : Finset (α → Bool)))
    (fun f _ => mul_le_mul_of_nonneg_left (hpoint f) (trialWeight_nonneg hp hp1 f))
  apply le_trans (le_of_eq ?_) hh
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
  rw [sum_trialWeight_card,discardCost_expectation]
  have hdelta : (∑ f : α → Bool, trialWeight p f*(δ*(Fintype.card α-(selected f).card-
      (closureCost H (selected f):ℝ)))) =
      δ*((1-p)*Fintype.card α-∑ e∈H, (e.card:ℝ)*p^(e.card-1)) := by
    simp only [mul_sub,sum_sub_distrib]
    simp_rw [mul_left_comm (trialWeight p _) δ]
    rw [← mul_sum,← mul_sum,← mul_sum,← sum_mul,sum_trialWeight,one_mul,
      sum_trialWeight_card,closureCost_expectation]
    ring
  simp only [mul_sub,sum_sub_distrib] at hdelta
  nlinarith only [hdelta]

end
end Erdos773.GreedyBatchState
end EndpointModule004
-- End GreedyBatchState.lean

-- Begin HypergraphSamplingMoments.lean
section EndpointModule005

/- Finite high-moment bounds for induced edge counts under independent
vertex sampling. No asymptotic or concentration assumption is used. -/
namespace Erdos773.HypergraphSamplingMoments
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

lemma touching_card (H : Finset (Finset α)) (U : Finset α) (K : ℕ)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (H.filter (fun e => ¬Disjoint U e)).card ≤ U.card*K := by
  classical
  have hs : H.filter (fun e => ¬Disjoint U e) ⊆
      U.biUnion (fun a => H.filter (fun e => a ∈ e)) := by
    intro e he
    obtain ⟨he,hn⟩ := mem_filter.mp he
    rw [Finset.disjoint_left] at hn
    push_neg at hn
    obtain ⟨a,ha,hae⟩ := hn
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨he,hae⟩⟩
  calc
    _ ≤ (U.biUnion (fun a => H.filter (fun e => a ∈ e))).card := card_le_card hs
    _ ≤ ∑ a ∈ U, (H.filter (fun e => a ∈ e)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ U, K := sum_le_sum (fun a _ => hK a)
    _ = _ := by simp

lemma union_step (H : Finset (Finset α)) (U : Finset α) (r K : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (∑ e ∈ H, p^(U∪e).card) ≤ p^U.card*(p^r*H.card+U.card*K) := by
  classical
  have ht (e : Finset α) (he : e ∈ H) : p^(U∪e).card ≤
      p^U.card*p^r+(if ¬Disjoint U e then p^U.card else 0) := by
    by_cases hd : Disjoint U e
    · rw [card_union_of_disjoint hd,hr e he,pow_add,if_neg (not_not.mpr hd),add_zero]
    · rw [if_pos hd]
      have hh : p^(U∪e).card ≤ p^U.card :=
        pow_le_pow_of_le_one hp hp1 (card_le_card subset_union_left)
      have hz : 0 ≤ p^U.card*p^r := by positivity
      linarith only [hh,hz]
  have hc : ((H.filter (fun e => ¬Disjoint U e)).card:ℝ) ≤ (U.card:ℝ)*K := by
    exact_mod_cast touching_card H U K hK
  calc
    _ ≤ ∑ e ∈ H, (p^U.card*p^r+(if ¬Disjoint U e then p^U.card else 0)) :=
      sum_le_sum ht
    _ = p^U.card*(p^r*H.card+(H.filter (fun e => ¬Disjoint U e)).card) := by
      rw [sum_add_distrib,← sum_filter]
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (pow_nonneg hp _)

/-- Ordered edge tuples, weighted by the size of their union with U. -/
def jointMoment (H : Finset (Finset α)) (p : ℝ) : ℕ → Finset α → ℝ
  | 0,U => p^U.card
  | k+1,U => ∑ e ∈ H, jointMoment H p k (U∪e)

lemma jointMoment_bound (H : Finset (Finset α)) (r K q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    ∀ k U, U.card+r*k ≤ r*q → jointMoment H p k U ≤
      p^U.card*(p^r*H.card+(r*q:ℕ)*K)^k := by
  intro k
  induction k with
  | zero => intro U hU; simp [jointMoment]
  | succ k ih =>
    intro U hU
    simp only [Nat.mul_succ] at hU
    have hbase : (0:ℝ) ≤ p^r*H.card+(r*q:ℕ)*K := by positivity
    have hrec (e : Finset α) (he : e ∈ H) : (U∪e).card+r*k ≤ r*q := by
      have hh := card_union_le U e
      rw [hr e he] at hh
      omega
    have hstep := union_step H U r K p hp hp1 hr hK
    have hU' : (U.card:ℝ)*K ≤ ((r*q:ℕ):ℝ)*K := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show U.card ≤ r*q by omega))
        (Nat.cast_nonneg K)
    have hstep' := hstep.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hU') (pow_nonneg hp _))
    calc
      _ ≤ ∑ e ∈ H, p^(U∪e).card*(p^r*H.card+(r*q:ℕ)*K)^k :=
        sum_le_sum (fun e he => ih (U∪e) (hrec e he))
      _ = (∑ e ∈ H, p^(U∪e).card)*(p^r*H.card+(r*q:ℕ)*K)^k := (sum_mul _ _ _).symm
      _ ≤ (p^U.card*(p^r*H.card+(r*q:ℕ)*K))*(p^r*H.card+(r*q:ℕ)*K)^k :=
        mul_le_mul_of_nonneg_right hstep' (pow_nonneg hbase _)
      _ = _ := by rw [pow_succ]; ring

section Expectation
variable [Fintype α]

/-- The recursive union polynomial is the actual Bernoulli mixed moment. -/
lemma jointMoment_expectation (H : Finset (Finset α)) (p : ℝ) (k : ℕ) (U : Finset α) :
    jointMoment H p k U = ∑ f : α → Bool,
      if U ⊆ selected f then trialWeight p f*((H.filter (· ⊆ selected f)).card:ℝ)^k else 0 := by
  classical
  induction k generalizing U with
  | zero => simpa only [jointMoment,pow_zero,mul_one] using (sum_trialWeight_contains p U).symm
  | succ k ih =>
    simp only [jointMoment,ih]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    by_cases hU : U ⊆ selected f
    · simp only [union_subset_iff,hU,true_and,if_true]
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul,pow_succ]
      ring
    · simp only [union_subset_iff,hU,false_and,if_false,sum_const_zero]

/-- High moments of an induced r-uniform edge count. The error uses only
    the original maximum vertex degree K, not a sampled-degree hypothesis. -/
theorem moment_bound (H : Finset (Finset α)) (r K q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (∑ f : α → Bool, trialWeight p f*((H.filter (· ⊆ selected f)).card:ℝ)^q) ≤
      (p^r*H.card+(r*q:ℕ)*K)^q := by
  have hb := jointMoment_bound H r K q p hp hp1 hr hK q ∅ (by simp)
  rw [jointMoment_expectation] at hb
  simpa only [empty_subset,if_true,card_empty,pow_zero,one_mul] using hb

-- Unused development declaration omitted.

end Expectation

end
end Erdos773.HypergraphSamplingMoments
end EndpointModule005
-- End HypergraphSamplingMoments.lean

-- Begin IndexedBernoulliMoments.lean
section EndpointModule006

/- High moments of indexed uniform witness counts, retaining every overlap
rank. Repeated supports are allowed. Unlike a maximum-degree-only bound,
a one-vertex overlap in an r-witness still pays p^(r-1). -/
namespace Erdos773.IndexedBernoulliMoments
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def incidence (T : Finset β) (C : β → Finset α) (U : Finset α) : ℕ :=
  (T.filter (fun i => U⊆C i)).card

def budget (r q : ℕ) (K : ℕ → ℕ) (p : ℝ) : ℝ :=
  ∑ k∈range (r+1), ((r*q).choose k:ℝ)*K k*p^(r-k)

lemma budget_nonneg (r q : ℕ) (K : ℕ → ℕ) {p : ℝ} (hp : 0≤p) : 0≤budget r q K p := by
  apply sum_nonneg
  intro k hk
  positivity

lemma union_exponent {U V : Finset α} {r : ℕ} (hV : V.card=r) :
    (U∪V).card=U.card+(r-(U∩V).card) := by
  have hh := card_union_add_card_inter U V
  have hi := card_le_card (inter_subset_right : U∩V⊆V)
  omega

/-- An explicit overlap-stratified one-step estimate. -/
lemma union_step (T : Finset β) (C : β → Finset α) (U : Finset α)
    (r q : ℕ) (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p)
    (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card)
    (hU : U.card≤r*q) :
    (∑ i∈T, p^(U∪C i).card) ≤ p^U.card*budget r q K p := by
  have hpoint (i : β) (hi : i∈T) :
      p^(U∪C i).card ≤ p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, if S⊆C i then p^(r-k) else 0) := by
    let S := U∩C i
    have hSr : S.card≤r := (card_le_card inter_subset_right).trans_eq (hr i hi)
    have hSmem : S∈U.powersetCard S.card := mem_powersetCard.mpr ⟨inter_subset_left,rfl⟩
    have hs1 : p^(r-S.card) ≤ ∑ A∈U.powersetCard S.card,
        if A⊆C i then p^(r-S.card) else 0 := by
      have hh := single_le_sum (s := U.powersetCard S.card)
        (f := fun A => if A⊆C i then p^(r-S.card) else 0)
        (fun A hA => by dsimp only; split_ifs <;> positivity) hSmem
      simpa only [show S⊆C i from inter_subset_right,if_true] using hh
    have hs2 : (∑ A∈U.powersetCard S.card, if A⊆C i then p^(r-S.card) else 0) ≤
        ∑ k∈range (r+1), ∑ A∈U.powersetCard k, if A⊆C i then p^(r-k) else 0 := by
      apply single_le_sum (f := fun k => ∑ A∈U.powersetCard k, if A⊆C i then p^(r-k) else 0) (a := S.card)
      · intro k hk
        apply sum_nonneg
        intro A hA
        split_ifs <;> positivity
      · exact mem_range.mpr (by omega)
    rw [union_exponent (hr i hi),pow_add]
    exact mul_le_mul_of_nonneg_left (hs1.trans hs2) (pow_nonneg hp _)
  have hb (k : ℕ) (hk : k∈range (r+1)) :
      (∑ S∈U.powersetCard k, ∑ i∈T, if S⊆C i then p^(r-k) else 0) ≤
        ((r*q).choose k:ℝ)*K k*p^(r-k) := by
    have hk' : k≤r := by simpa only [mem_range,Nat.lt_succ_iff] using hk
    calc
      _ = ∑ S∈U.powersetCard k, (incidence T C S:ℝ)*p^(r-k) := by
        apply sum_congr rfl
        intro S hS
        rw [← sum_filter]
        simp [incidence]
      _ ≤ ∑ _S∈U.powersetCard k, (K k:ℝ)*p^(r-k) := by
        apply sum_le_sum
        intro S hS
        have hSc := (mem_powersetCard.mp hS).2
        have hh := hK S (hSc.trans_le hk')
        rw [hSc] at hh
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (pow_nonneg hp _)
      _ = (U.card.choose k:ℝ)*K k*p^(r-k) := by
        simp only [sum_const,nsmul_eq_mul,card_powersetCard]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast Nat.choose_le_choose k hU
  calc
    _ ≤ ∑ i∈T, p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, if S⊆C i then p^(r-k) else 0) := sum_le_sum hpoint
    _ = p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, ∑ i∈T, if S⊆C i then p^(r-k) else 0) := by
      rw [← mul_sum,sum_comm]
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum hb) (pow_nonneg hp _)

def jointMoment (T : Finset β) (C : β → Finset α) (p : ℝ) : ℕ → Finset α → ℝ
  | 0,U => p^U.card
  | k+1,U => ∑ i∈T, jointMoment T C p k (U∪C i)

lemma jointMoment_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p) (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    ∀ k U, U.card+r*k≤r*q → jointMoment T C p k U≤p^U.card*(budget r q K p)^k := by
  intro k
  induction k with
  | zero => intro U hU; simp [jointMoment]
  | succ k ih =>
    intro U hU
    have hrec (i : β) (hi : i∈T) : (U∪C i).card+r*k≤r*q := by
      have hh := card_union_le U (C i)
      rw [hr i hi] at hh
      simp only [Nat.mul_succ] at hU
      omega
    calc
      _ ≤ ∑ i∈T, p^(U∪C i).card*(budget r q K p)^k :=
        sum_le_sum (fun i hi => ih (U∪C i) (hrec i hi))
      _ = (∑ i∈T, p^(U∪C i).card)*(budget r q K p)^k := (sum_mul _ _ _).symm
      _ ≤ (p^U.card*budget r q K p)*(budget r q K p)^k :=
        mul_le_mul_of_nonneg_right (union_step T C U r q K p hp hr hK (by omega))
          (pow_nonneg (budget_nonneg r q K hp) _)
      _ = _ := by rw [pow_succ]; ring

section Expectation
variable [Fintype α]

lemma jointMoment_expectation (T : Finset β) (C : β → Finset α) (p : ℝ)
    (k : ℕ) (U : Finset α) :
    jointMoment T C p k U = ∑ f : α → Bool,
      if U⊆selected f then trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^k else 0 := by
  induction k generalizing U with
  | zero => simpa only [jointMoment,pow_zero,mul_one] using (sum_trialWeight_contains p U).symm
  | succ k ih =>
    simp only [jointMoment,ih]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    by_cases hU : U⊆selected f
    · simp only [union_subset_iff,hU,true_and,if_true]
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul,pow_succ]
      ring
    · simp only [union_subset_iff,hU,false_and,if_false,sum_const_zero]

/-- The complete indexed moment bound, with every overlap rank retained. -/
theorem moment_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p) (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    (∑ f : α → Bool, trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^q) ≤
      (budget r q K p)^q := by
  have hh := jointMoment_bound T C r q K p hp hr hK q ∅ (by simp)
  rw [jointMoment_expectation] at hh
  simpa only [empty_subset,if_true,card_empty,pow_zero,one_mul] using hh

/-- Markov tail with the same overlap-sensitive budget. -/
theorem tail_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L)
    (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    (∑ f : α → Bool, if L≤((T.filter (fun i => C i⊆selected f)).card:ℝ)
      then trialWeight p f else 0) ≤ (budget r q K p/L)^q := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hL q)).mpr
  calc
    _ = ∑ f : α → Bool, if L≤((T.filter (fun i => C i⊆selected f)).card:ℝ)
        then trialWeight p f*L^q else 0 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ ≤ ∑ f : α → Bool, trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^q := by
      apply sum_le_sum
      intro f hf
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le h q) (trialWeight_nonneg hp hp1 f)
      · exact mul_nonneg (trialWeight_nonneg hp hp1 f) (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := moment_bound T C r q K p hp hr hK
end Expectation

end
end Erdos773.IndexedBernoulliMoments
end EndpointModule006
-- End IndexedBernoulliMoments.lean

-- Begin UniformLayerRegularization.lean
section EndpointModule007

/-
A finite regularization construction. Copies of a hypergraph are supplemented
by affine-line edges between copies of the same original vertex. The added
edges have pair codegree at most one. This is preparatory work, not an
independent-set lower bound or a proof of Erdős 773.
-/
namespace Erdos773.UniformLayerRegularization
open Finset HypergraphDegreeTrim
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 1500000
noncomputable section
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

abbrev Copy (ρ F : Type*) := ρ × F
abbrev Vertex (α ρ F : Type*) := α × Copy ρ F

def copyEdge (e : Finset α) (c : Copy ρ F) : Finset (Vertex α ρ F) :=
  e.image (fun a => (a,c))

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma mem_copyEdge {e : Finset α} {c : Copy ρ F} {x : Vertex α ρ F} :
    x ∈ copyEdge e c ↔ x.1 ∈ e ∧ x.2 = c := by
  rcases x with ⟨a,b⟩
  simp [copyEdge,eq_comm]

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copyEdge_injective (c : Copy ρ F) :
    Function.Injective (fun e : Finset α => copyEdge e c) := by
  intro e f he
  ext a
  have hh := congrArg (fun t : Finset (Vertex α ρ F) => (a,c) ∈ t) he
  simpa only [mem_copyEdge,and_true] using hh.to_iff

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copyEdge_card (e : Finset α) (c : Copy ρ F) : (copyEdge e c).card = e.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

def line (h : ρ → F) (a : α) (s t : F) : Finset (Vertex α ρ F) :=
  univ.image (fun i => (a,(i,t+s*h i)))

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma mem_line {h : ρ → F} {a : α} {s t : F} {x : Vertex α ρ F} :
    x ∈ line h a s t ↔ x.1 = a ∧ x.2.2 = t+s*h x.2.1 := by
  rcases x with ⟨a',i,y⟩
  simp [line,eq_comm]

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_card (h : ρ → F) (a : α) (s t : F) :
    (line h a s t).card = Fintype.card ρ := by
  rw [line,card_image_of_injective _ (fun i j he => congrArg (fun x => x.2.1) he)]
  simp

omit [Fintype α] [Fintype F] in
lemma line_parameters {h : ρ → F} (hh : Function.Injective h)
    {a b : α} {s t u v : F} (he : line h a s t = line h b u v) :
    a = b ∧ s = u ∧ t = v := by
  obtain ⟨i,j,hij⟩ := exists_pair_ne ρ
  have h0 : (a,(i,t+s*h i)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  have h1 : (a,(j,t+s*h j)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  obtain ⟨hab,h0⟩ := mem_line.mp h0
  have h1 := (mem_line.mp h1).2
  have hne : h i - h j ≠ 0 := sub_ne_zero.mpr (fun he => by
    have := hh he
    exact hij this)
  have hmul : (s-u)*(h i-h j) = 0 := by linear_combination h0-h1
  have hsu := (mul_eq_zero.mp hmul).resolve_right hne
  have hsu : s = u := sub_eq_zero.mp hsu
  refine ⟨hab,hsu,?_⟩
  rw [hsu] at h0
  exact add_right_cancel h0

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_pair_unique {h : ρ → F} (hh : Function.Injective h)
    {x y : Vertex α ρ F} (hxy : x ≠ y)
    {a b : α} {s t u v : F}
    (hx : x ∈ line h a s t) (hy : y ∈ line h a s t)
    (hx' : x ∈ line h b u v) (hy' : y ∈ line h b u v) :
    line h a s t = line h b u v := by
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hya,hy⟩ := mem_line.mp hy
  obtain ⟨hxb,hx'⟩ := mem_line.mp hx'
  obtain ⟨hyb,hy'⟩ := mem_line.mp hy'
  have hij : x.2.1 ≠ y.2.1 := by
    intro he
    apply hxy
    apply Prod.ext (hxa.trans hya.symm)
    apply Prod.ext he
    rw [hx,hy,he]
  have hne : h x.2.1-h y.2.1 ≠ 0 := sub_ne_zero.mpr (fun he => hij (hh he))
  have hmul : (s-u)*(h x.2.1-h y.2.1)=0 := by
    linear_combination hx'-hx-hy'+hy
  have hsu : s=u := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hne)
  have htv : t=v := by rw [hsu] at hx; linear_combination hx'-hx
  rw [hxa.symm.trans hxb,hsu,htv]

def oldEdges (H : Finset (Finset α)) : Finset (Finset (Vertex α ρ F)) :=
  (H ×ˢ (univ : Finset (Copy ρ F))).image (fun p => copyEdge p.1 p.2)

def newEdges (h : ρ → F) (S : α → Finset F) : Finset (Finset (Vertex α ρ F)) :=
  ((univ : Finset (α × F × F)).filter (fun p => p.2.1 ∈ S p.1)).image
    (fun p => line h p.1 p.2.1 p.2.2)

def regularized (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F) :=
  oldEdges (F := F) H ∪ newEdges h S

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma mem_oldEdges {H : Finset (Finset α)} {e : Finset (Vertex α ρ F)} :
    e ∈ oldEdges H ↔ ∃ f ∈ H, ∃ c : Copy ρ F, copyEdge f c = e := by
  simp [oldEdges]

omit [Nontrivial ρ] in
lemma mem_newEdges {h : ρ → F} {S : α → Finset F}
    {e : Finset (Vertex α ρ F)} :
    e ∈ newEdges h S ↔ ∃ a : α, ∃ s ∈ S a, ∃ t : F, line h a s t = e := by
  simp [newEdges]

lemma old_new_disjoint (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F) :
    Disjoint (oldEdges H) (newEdges h S) := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  obtain ⟨a,s,hs,t,he⟩ := mem_newEdges.mp hf
  have hc (i : ρ) : i = c.1 := by
    have hm : (a,(i,t+s*h i)) ∈ copyEdge f c := by
      rw [← he]
      exact mem_line.mpr ⟨rfl,rfl⟩
    exact congrArg Prod.fst (mem_copyEdge.mp hm).2
  obtain ⟨i,j,hij⟩ := exists_pair_ne ρ
  exact hij ((hc i).trans (hc j).symm)

-- Unused development declaration omitted.

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_incident (H : Finset (Finset α)) (x : Vertex α ρ F) :
    (oldEdges H).filter (fun e => x ∈ e) =
      (H.filter (fun e => x.1 ∈ e)).image (fun e => copyEdge e x.2) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx⟩ := mem_filter.mp he
    obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨hx',hc⟩ := mem_copyEdge.mp hx
    subst c
    exact mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hx'⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,hx⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_oldEdges.mpr ⟨f,hf,x.2,rfl⟩,mem_copyEdge.mpr ⟨hx,rfl⟩⟩

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_degree (H : Finset (Finset α)) (x : Vertex α ρ F) :
    degree (oldEdges H) x = degree H x.1 := by
  rw [degree,old_incident,card_image_of_injective _ (copyEdge_injective _)]
  rfl

omit [Nontrivial ρ] in
lemma new_incident (h : ρ → F) (S : α → Finset F) (x : Vertex α ρ F) :
    (newEdges h S).filter (fun e => x ∈ e) =
      (S x.1).image (fun s => line h x.1 s (x.2.2-s*h x.2.1)) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx⟩ := mem_filter.mp he
    obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨hxa,hx⟩ := mem_line.mp hx
    have ht : t=x.2.2-s*h x.2.1 := by linear_combination -hx
    subst a
    subst t
    exact mem_image.mpr ⟨s,hs,rfl⟩
  · intro he
    obtain ⟨s,hs,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨mem_newEdges.mpr ⟨x.1,s,hs,_,rfl⟩,
      mem_line.mpr ⟨rfl,by ring⟩⟩

lemma new_degree (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x : Vertex α ρ F) :
    degree (newEdges h S) x = (S x.1).card := by
  rw [degree,new_incident,card_image_of_injective]
  intro s t he
  exact (line_parameters hh he).2.1

lemma regularized_degree (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (x : Vertex α ρ F) :
    degree (regularized H h S) x = degree H x.1+(S x.1).card := by
  unfold regularized degree
  rw [filter_union,card_union_of_disjoint
    ((old_new_disjoint H h S).mono (filter_subset _ _) (filter_subset _ _))]
  exact congrArg₂ (·+·) (old_degree H x) (new_degree h hh S x)

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_incident (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 = y.2) :
    (oldEdges H).filter (fun e => x ∈ e ∧ y ∈ e) =
      (H.filter (fun e => x.1 ∈ e ∧ y.1 ∈ e)).image (fun e => copyEdge e x.2) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx,hy⟩ := mem_filter.mp he
    obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨hx',hc⟩ := mem_copyEdge.mp hx
    have hy' := (mem_copyEdge.mp hy).1
    subst c
    exact mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hx',hy'⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_oldEdges.mpr ⟨f,hf,x.2,rfl⟩,
      mem_copyEdge.mpr ⟨hx,rfl⟩,mem_copyEdge.mpr ⟨hy,hxy.symm⟩⟩

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_degree (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 = y.2) :
    pairDegree (oldEdges H) x y = pairDegree H x.1 y.1 := by
  rw [pairDegree,old_pair_incident H x y hxy,
    card_image_of_injective _ (copyEdge_injective _)]
  rfl

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_empty (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 ≠ y.2) :
    (oldEdges H).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  exact hxy ((mem_copyEdge.mp hx).2.trans (mem_copyEdge.mp hy).2.symm)

omit [Nontrivial ρ] in
lemma new_pair_empty (h : ρ → F) (S : α → Finset F) (x y : Vertex α ρ F)
    (hxy : x.1 ≠ y.1) :
    (newEdges h S).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact hxy ((mem_line.mp hx).1.trans (mem_line.mp hy).1.symm)

omit [Nontrivial ρ] in
lemma new_pair_degree (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x y : Vertex α ρ F) (hxy : x ≠ y) :
    pairDegree (newEdges h S) x y ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨hf,hx',hy'⟩ := mem_filter.mp hf
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
  exact line_pair_unique hh hxy hx hy hx' hy'

omit [Nontrivial ρ] in
/-- No pair-codegree loss, provided the old bound is at least one. -/
theorem regularized_pair_degree (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (K : ℕ) (hK : 1 ≤ K)
    (hcode : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    ∀ x y : Vertex α ρ F, x ≠ y → pairDegree (regularized H h S) x y ≤ K := by
  intro x y hxy
  by_cases hc : x.2 = y.2
  · have ha : x.1 ≠ y.1 := fun he => hxy (Prod.ext he hc)
    unfold pairDegree regularized
    rw [filter_union,new_pair_empty h S x y ha,union_empty]
    exact (old_pair_degree H x y hc).trans_le (hcode _ _ ha)
  · unfold pairDegree regularized
    rw [filter_union,old_pair_empty H x y hc,empty_union]
    exact (new_pair_degree h hh S x y hxy).trans hK

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copy_inter_same (e f : Finset α) (c : Copy ρ F) :
    copyEdge e c ∩ copyEdge f c = copyEdge (e ∩ f) c := by
  ext x
  simp only [mem_inter,mem_copyEdge]
  tauto

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copy_inter_distinct (e f : Finset α) (c d : Copy ρ F) (hcd : c ≠ d) :
    copyEdge e c ∩ copyEdge f d = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hy⟩ := mem_inter.mp hx
  exact hcd ((mem_copyEdge.mp hx).2.symm.trans (mem_copyEdge.mp hy).2)

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma copy_line_inter_card (e : Finset α) (c : Copy ρ F)
    (h : ρ → F) (a : α) (s t : F) :
    (copyEdge e c ∩ line h a s t).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxc,hxl⟩ := mem_inter.mp hx
  obtain ⟨hyc,hyl⟩ := mem_inter.mp hy
  exact Prod.ext ((mem_line.mp hxl).1.trans (mem_line.mp hyl).1.symm)
    ((mem_copyEdge.mp hxc).2.trans (mem_copyEdge.mp hyc).2.symm)

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_inter_card (h : ρ → F) (hh : Function.Injective h)
    (a b : α) (s t u v : F) (hne : line h a s t ≠ line h b u v) :
    (line h a s t ∩ line h b u v).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hx,hx'⟩ := mem_inter.mp hx
  obtain ⟨hy,hy'⟩ := mem_inter.mp hy
  exact hne (line_pair_unique hh hxy hx hy hx' hy')

omit [Nontrivial ρ] in
/-- Edge-intersection bounds at least one are preserved as well. In particular,
    distinct edges with three common vertices cannot be newly introduced. -/
theorem regularized_intersections (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (k : ℕ) (hk : 1 ≤ k)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ k) :
    ∀ e ∈ regularized H h S, ∀ f ∈ regularized H h S,
      e ≠ f → (e ∩ f).card ≤ k := by
  intro e he f hf hne
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,hb,d,rfl⟩ := mem_oldEdges.mp hf
    by_cases hcd : c = d
    · subst d
      have hab : a ≠ b := fun he => hne (congrArg (fun t => copyEdge t c) he)
      rw [copy_inter_same,copyEdge_card]
      exact hinter a ha b hb hab
    · rw [copy_inter_distinct a b c d hcd]
      simp
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,s,hs,t,rfl⟩ := mem_newEdges.mp hf
    exact (copy_line_inter_card a c h b s t).trans hk
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,hb,c,rfl⟩ := mem_oldEdges.mp hf
    rw [inter_comm]
    exact (copy_line_inter_card b c h a s t).trans hk
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
    exact (line_inter_card h hh a b s t u v hne).trans hk

/-- Original vertices retained in one fixed copy. -/
def slice (B : Finset (Vertex α ρ F)) (c : Copy ρ F) : Finset α :=
  univ.filter (fun a => (a,c) ∈ B)

omit [Field F] [Nontrivial ρ] in
lemma sum_slice_card (B : Finset (Vertex α ρ F)) :
    ∑ c : Copy ρ F, (slice B c).card = B.card := by
  simp only [slice,card_filter]
  rw [sum_comm,← Fintype.sum_prod_type (fun p : Vertex α ρ F => if p ∈ B then (1:ℕ) else 0)]
  simp

/-- Averaging independent sets back to the original hypergraph incurs exactly
    the number-of-copies factor, not an additional density loss. -/
theorem independent_slice (H : Finset (Finset α)) (h : ρ → F)
    (S : α → Finset F) (B : Finset (Vertex α ρ F))
    (hB : ∀ e ∈ regularized H h S, ¬e ⊆ B) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧
      B.card ≤ (Fintype.card ρ * Fintype.card F) * A.card := by
  obtain ⟨c,hc,hmax⟩ := exists_max_image (univ : Finset (Copy ρ F))
    (fun c => (slice B c).card) univ_nonempty
  refine ⟨slice B c,?_,?_⟩
  · intro e he hsub
    apply hB (copyEdge e c) (mem_union_left _ (mem_oldEdges.mpr ⟨e,he,c,rfl⟩))
    intro x hx
    obtain ⟨hx',hcopy⟩ := mem_copyEdge.mp hx
    have hmem := (mem_filter.mp (hsub hx')).2
    simpa only [← hcopy,Prod.mk.eta] using hmem
  · calc
      B.card = ∑ d : Copy ρ F, (slice B d).card := (sum_slice_card B).symm
      _ ≤ ∑ _d : Copy ρ F, (slice B c).card := sum_le_sum (fun d hd => hmax d hd)
      _ = _ := by simp [Copy,Fintype.card_prod]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

omit [Fintype α] [Field F] [DecidableEq F] in
lemma exists_slopes (H : Finset (Finset α)) (D : ℕ)
    (hD : D ≤ Fintype.card F) :
    ∃ S : α → Finset F, ∀ a : α, (S a).card = D-degree H a := by
  have hs (a : α) : ∃ s : Finset F, s.card = D-degree H a := by
    obtain ⟨s,hs,hcard⟩ := exists_subset_card_eq
      (show D-degree H a ≤ (univ : Finset F).card by simpa using (Nat.sub_le D _).trans hD)
    exact ⟨s,hcard⟩
  choose S hS using hs
  exact ⟨S,hS⟩


/-- The original constraints of one specified size. -/
def layer {β : Type*} [DecidableEq β] (H : Finset (Finset β)) (k : ℕ) : Finset (Finset β) :=
  H.filter (fun e => e.card=k)

omit [Fintype α] [Nontrivial ρ] [Field F] in
lemma layer_old (H : Finset (Finset α)) (k : ℕ) :
    layer (oldEdges (ρ := ρ) (F := F) H) k=oldEdges (layer H k) := by
  ext e
  simp only [layer,mem_filter,mem_oldEdges]
  constructor
  · rintro ⟨⟨f,hf,c,rfl⟩,hc⟩
    exact ⟨f,⟨hf,by simpa only [copyEdge_card] using hc⟩,c,rfl⟩
  · rintro ⟨f,⟨hf,hfc⟩,c,rfl⟩
    exact ⟨⟨f,hf,c,rfl⟩,by simpa only [copyEdge_card] using hfc⟩

omit [Nontrivial ρ] in
lemma layer_new_same (h : ρ → F) (S : α → Finset F) :
    layer (newEdges h S) (Fintype.card ρ)=newEdges h S := by
  apply filter_eq_self.mpr
  intro e he
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact line_card h a s t

omit [Nontrivial ρ] in
lemma layer_new_other (h : ρ → F) (S : α → Finset F) {k : ℕ} (hk : k≠Fintype.card ρ) :
    layer (newEdges h S) k=∅ := by
  apply filter_eq_empty_iff.mpr
  intro e he hc
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact hk (hc.symm.trans (line_card h a s t))

lemma layer_union {β : Type*} [DecidableEq β] (H G : Finset (Finset β)) (k : ℕ) :
    layer (H∪G) k=layer H k∪layer G k := filter_union _ _ _

omit [Nontrivial ρ] in
/-- Only the selected rank is changed. All the other degree layers are
copied exactly, including already-shortened constraints. -/
lemma degree_layer_other (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    {k : ℕ} (hk : k≠Fintype.card ρ) (x : Vertex α ρ F) :
    degree (layer (regularized H h S) k) x=degree (layer H k) x.1 := by
  rw [regularized,layer_union,layer_old,layer_new_other h S hk,union_empty,old_degree]

lemma degree_layer_same (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x : Vertex α ρ F) :
    degree (layer (regularized H h S) (Fintype.card ρ)) x=
      degree (layer H (Fintype.card ρ)) x.1+(S x.1).card := by
  rw [regularized,layer_union,layer_old,layer_new_same]
  exact regularized_degree (layer H (Fintype.card ρ)) h hh S x

omit [Nontrivial ρ] in
lemma rank_range (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hρ : 2≤Fintype.card ρ ∧ Fintype.card ρ≤4) :
    ∀ e ∈ regularized H h S, 2≤e.card ∧ e.card≤4 := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    simpa only [copyEdge_card] using hH f hf
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    simpa only [line_card] using hρ

omit [Fintype α] [Field F] [Fintype F] [DecidableEq F] in
/-- An arbitrary large enough slope reservoir can fill every degree deficit;
using a Sidon reservoir will additionally control graph common neighbors. -/
lemma exists_slopes_subset (H : Finset (Finset α)) (D : ℕ) (T : Finset F) (hT : D≤T.card) :
    ∃ S : α → Finset F, (∀ a, S a⊆T) ∧ (∀ a, (S a).card=D-degree H a) := by
  have hs (a : α) : ∃ s ⊆ T, s.card=D-degree H a :=
    exists_subset_card_eq ((Nat.sub_le D _).trans hT)
  choose S hS hcard using hs
  exact ⟨S,hS,hcard⟩


end
end Erdos773.UniformLayerRegularization
end EndpointModule007
-- End UniformLayerRegularization.lean

-- Begin GreedyBatchPromotions.lean
section EndpointModule008

/- Indexed batched promotion witnesses and their overlap-sensitive tails.
The selected supports retain their original edge indices. -/
namespace Erdos773.GreedyBatchPromotions
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def incidentLayer (H : Finset (Finset α)) (r : ℕ) (x : α) : Finset (Finset α) :=
  (layer H r).filter (fun e => x∈e)

def family (H : Finset (Finset α)) (x : α) (r k : ℕ) : Finset (Σ _ : Finset α, Finset α) :=
  (incidentLayer H r x).sigma (fun e => (e.erase x).powersetCard k)

def cost (H : Finset (Finset α)) (x : α) (r k : ℕ) (R : Finset α) : ℕ :=
  ((family H x r k).filter (fun i => i.2⊆R)).card

lemma family_card (H : Finset (Finset α)) (x : α) (r k : ℕ) :
    (family H x r k).card=degree (layer H r) x*(r-1).choose k := by
  rw [family,card_sigma]
  have he (e : Finset α) (he : e∈incidentLayer H r x) : ((e.erase x).powersetCard k).card=(r-1).choose k := by
    obtain ⟨he,hx⟩ := mem_filter.mp he
    rw [card_powersetCard,card_erase_of_mem hx,(mem_filter.mp he).2]
  rw [sum_congr rfl he]
  simp [degree,incidentLayer]

lemma positive_incidence (H : Finset (Finset α)) (x : α) (r k P : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P)
    (S : Finset α) (hS : S.Nonempty) :
    IndexedBernoulliMoments.incidence (family H x r k) (fun i => i.2) S≤8*P := by
  by_cases hxS : x∈S
  · have he : (family H x r k).filter (fun i => S⊆i.2)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨e,A⟩ hi
      obtain ⟨hi,hSA⟩ := mem_filter.mp hi
      have hAe := (mem_powersetCard.mp (mem_sigma.mp hi).2).1
      exact notMem_erase x e (hAe (hSA hxS))
    simp [IndexedBernoulliMoments.incidence,he]
  · obtain ⟨a,ha⟩ := hS
    have hxa : x≠a := fun he => hxS (he.symm ▸ ha)
    let E := (layer H r).filter (fun e => x∈e ∧ a∈e)
    have hs : (family H x r k).filter (fun i => S⊆i.2) ⊆
        E.sigma (fun e => (e.erase x).powersetCard k) := by
      rintro ⟨e,A⟩ hi
      obtain ⟨hi,hSA⟩ := mem_filter.mp hi
      obtain ⟨he,hA⟩ := mem_sigma.mp hi
      obtain ⟨he,hx⟩ := mem_filter.mp he
      have hae := (mem_erase.mp ((mem_powersetCard.mp hA).1 (hSA ha))).2
      exact mem_sigma.mpr ⟨mem_filter.mpr ⟨he,hx,hae⟩,hA⟩
    have hEc : E.card≤P := by
      apply (card_le_card (show E⊆H.filter (fun e => x∈e ∧ a∈e) from ?_)).trans (hP a hxa)
      intro e he
      obtain ⟨he,hx,ha⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,hx,ha⟩
    have hcount (e : Finset α) (he : e∈E) : ((e.erase x).powersetCard k).card≤8 := by
      obtain ⟨he,hx,ha⟩ := mem_filter.mp he
      have hc := (mem_filter.mp he).2
      rw [card_powersetCard,card_erase_of_mem hx,hc]
      apply (Nat.choose_le_two_pow _ _).trans
      exact (Nat.pow_le_pow_right (by omega : 0<2) (by omega : r-1≤3))
    calc
      _ ≤ (E.sigma (fun e => (e.erase x).powersetCard k)).card := card_le_card hs
      _ = ∑ e∈E, ((e.erase x).powersetCard k).card := card_sigma _ _
      _ ≤ ∑ _e∈E, 8 := sum_le_sum hcount
      _ = 8*E.card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left 8 hEc

def overlapCaps (m P : ℕ) (i : ℕ) : ℕ := if i=0 then m else 8*P

lemma incidence_bound (H : Finset (Finset α)) (x : α) (r k P : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P) (S : Finset α) :
    IndexedBernoulliMoments.incidence (family H x r k) (fun i => i.2) S≤
      overlapCaps (degree (layer H r) x*(r-1).choose k) P S.card := by
  by_cases hS : S.card=0
  · have he := card_eq_zero.mp hS
    subst S
    simp [IndexedBernoulliMoments.incidence,overlapCaps,family_card]
  · rw [overlapCaps,if_neg hS]
    exact positive_incidence H x r k P hr hP S (card_pos.mp (by omega))

/-- Tail for all k-mark promotion witnesses of a rank-r original link. -/
theorem cost_tail (H : Finset (Finset α)) (x : α) (r k P q : ℕ) (hr : r≤4)
    (hP : ∀ a, x≠a → pairDegree H x a≤P) (p L : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(cost H x r k (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget k q
        (overlapCaps (degree (layer H r) x*(r-1).choose k) P) p/L)^q := by
  exact IndexedBernoulliMoments.tail_bound (family H x r k) (fun i => i.2) k q
    (overlapCaps (degree (layer H r) x*(r-1).choose k) P) p L hp hp1 hL
    (fun i hi => (mem_powersetCard.mp (mem_sigma.mp hi).2).2)
    (fun S _ => incidence_bound H x r k P hr hP S)

/-- Every actual contraction has the required marked witness, including
contractions from rank four directly to rank two. -/
lemma contraction_count (H : Finset (Finset α)) (R : Finset α) (x : α) (j k : ℕ) :
    ((layer H (j+k)).filter (fun e => x∈e \ R ∧ (e \ R).card=j)).card ≤
      cost H x (j+k) k R := by
  apply card_le_card_of_injOn (fun e : Finset α => (⟨e,e∩R⟩ : Σ _ : Finset α, Finset α))
  · intro e he
    obtain ⟨he,hx,hj⟩ := mem_filter.mp he
    have her := (mem_filter.mp he).2
    have hcard : (e∩R).card=k := by
      have hh := card_sdiff_add_card_inter e R
      omega
    have hs : e∩R⊆e.erase x := by
      intro a ha
      obtain ⟨hae,haR⟩ := mem_inter.mp ha
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hx).2 (he ▸ haR),hae⟩
    exact mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_filter.mpr ⟨he,(mem_sdiff.mp hx).1⟩,
      mem_powersetCard.mpr ⟨hs,hcard⟩⟩,inter_subset_right⟩
  · intro e he f hf hef
    exact congrArg Sigma.fst hef

end
end Erdos773.GreedyBatchPromotions
end EndpointModule008
-- End GreedyBatchPromotions.lean

-- Begin WeightedBernoulliLowerTail.lean
section EndpointModule009

/- A finite weighted Bernoulli lower-tail bound. Its variance scale is
maximum weight times mean, rather than ambient cardinality times squared
maximum weight. All expectations are the explicit finite product law. -/
namespace Erdos773.WeightedBernoulliLowerTail
open Finset
set_option maxHeartbeats 2500000
noncomputable section

lemma exp_neg_quadratic {x : ℝ} (hx : 0≤x) : Real.exp (-x)≤1-x+x^2/2 := by
  have hd (z : ℝ) : HasDerivAt (fun y : ℝ => 1-y+y^2/2-Real.exp (-y))
      (-1+z+Real.exp (-z)) z := by
    convert (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).add
      (((hasDerivAt_id z).pow 2).div_const 2)).sub ((hasDerivAt_id z).neg.exp) using 1 <;> simp only [id_eq,Pi.neg_apply] <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun z => by
    change (0:ℝ)≤-1+z+Real.exp (-z)
    have hh := Real.add_one_le_exp (-z)
    linarith only [hh])
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

variable {α : Type*} [Fintype α] [DecidableEq α]

def value (w : α → ℝ) (f : α → Bool) : ℝ := ∑ a : α, if f a then w a else 0

def mean (w : α → ℝ) (p : ℝ) : ℝ := p*∑ a : α, w a

lemma laplace_identity (w : α → ℝ) (p t : ℝ) :
    (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f)) =
      ∏ a : α, (1-p+p*Real.exp (-t*w a)) := by
  have hterm (f : α → Bool) : trialWeight p f*Real.exp (-t*value w f)=
      ∏ a : α, if f a then p*Real.exp (-t*w a) else 1-p := by
    have he : -t*value w f=∑ a : α, if f a then -t*w a else 0 := by
      unfold value
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      split_ifs <;> ring
    rw [he,Real.exp_sum,trialWeight,← prod_mul_distrib]
    apply prod_congr rfl
    intro a ha
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (a : α) (b : Bool) => if b then p*Real.exp (-t*w a) else 1-p)]
  simp [add_comm]

lemma laplace_bound (w : α → ℝ) (W p t : ℝ)
    (hw : ∀ a, 0≤w a) (hW : ∀ a, w a≤W)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0≤t) :
    (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f)) ≤
      Real.exp (-t*mean w p+t^2*W*mean w p/2) := by
  rw [laplace_identity]
  have hfac (a : α) : 1-p+p*Real.exp (-t*w a) ≤
      Real.exp (-p*t*w a+p*t^2*(w a)^2/2) := by
    have hh := mul_le_mul_of_nonneg_left (exp_neg_quadratic (mul_nonneg ht (hw a))) hp
    have he := Real.add_one_le_exp (-p*t*w a+p*t^2*(w a)^2/2)
    simp only [← neg_mul] at hh
    nlinarith only [hh,he]
  have hb : (∏ a : α, (1-p+p*Real.exp (-t*w a))) ≤
      ∏ a : α, Real.exp (-p*t*w a+p*t^2*(w a)^2/2) := by
    apply prod_le_prod
    · intro a ha
      exact add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
    · intro a ha
      exact hfac a
  apply hb.trans
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hs : (∑ a : α, (w a)^2)≤W*∑ a : α, w a := by
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    nlinarith only [mul_le_mul_of_nonneg_right (hW a) (hw a)]
  have hh := mul_le_mul_of_nonneg_left hs (show 0≤p*t^2/2 by positivity)
  simp only [sum_add_distrib,← sum_div,← mul_sum]
  unfold mean
  nlinarith only [hh]

/-- Unoptimized exponential Markov bound for the lower deviation event. -/
theorem lower_tail_parameter (w : α → ℝ) (W p t a : ℝ)
    (hw : ∀ i, 0≤w i) (hW : ∀ i, w i≤W)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0≤t) :
    (∑ f : α → Bool, if value w f≤ mean w p-a then trialWeight p f else 0) ≤
      Real.exp (-t*a+t^2*W*mean w p/2) := by
  have hpoint (f : α → Bool) :
      (if value w f≤ mean w p-a then trialWeight p f else 0)*Real.exp (-t*(mean w p-a)) ≤
      trialWeight p f*Real.exp (-t*value w f) := by
    split_ifs with h
    · apply mul_le_mul_of_nonneg_left _ (trialWeight_nonneg hp hp1 f)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left h (by linarith)
    · simp only [zero_mul]
      exact mul_nonneg (trialWeight_nonneg hp hp1 f) (Real.exp_pos _).le
  have hh := sum_le_sum (s := (univ : Finset (α → Bool))) (fun f _ => hpoint f)
  rw [← sum_mul] at hh
  calc
    _ ≤ (∑ f : α → Bool, trialWeight p f*Real.exp (-t*value w f))/Real.exp (-t*(mean w p-a)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hh
    _ ≤ Real.exp (-t*mean w p+t^2*W*mean w p/2)/Real.exp (-t*(mean w p-a)) :=
      div_le_div_of_nonneg_right (laplace_bound w W p t hw hW hp hp1 ht) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- Multiplicative lower tail with the correct maximum-weight/mean scale.
No independence of hypergraph edge indicators is assumed: only the original
vertex marks are independent. -/
theorem relative_lower_tail (w : α → ℝ) (W p η : ℝ)
    (hw : ∀ i, 0≤w i) (hW : ∀ i, w i≤W) (hWpos : 0<W)
    (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) :
    (∑ f : α → Bool, if value w f≤(1-η)*mean w p then trialWeight p f else 0) ≤
      Real.exp (-η^2*mean w p/(2*W)) := by
  have hh := lower_tail_parameter w W p (η/W) (η*mean w p) hw hW hp hp1 (div_nonneg hη hWpos.le)
  have ht : -(η/W)*(η*mean w p)+(η/W)^2*W*mean w p/2=-η^2*mean w p/(2*W) := by
    field_simp
    ring
  rw [ht] at hh
  have hm : mean w p-η*mean w p=(1-η)*mean w p := by ring
  rwa [hm] at hh

end
end Erdos773.WeightedBernoulliLowerTail
end EndpointModule009
-- End WeightedBernoulliLowerTail.lean

-- Begin BernoulliHitCounts.lean
section EndpointModule010

/- Lower concentration for the number of indexed sets hit by independent
vertex marks. The linear hit multiplicity is corrected by an indexed
selected-pair count; pair multiplicities are not discarded. -/
namespace Erdos773.BernoulliHitCounts
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def hitCount (T : Finset β) (D : β → Finset α) (R : Finset α) : ℕ :=
  (T.filter (fun i => (D i∩R).Nonempty)).card

def linearCount (T : Finset β) (D : β → Finset α) (R : Finset α) : ℕ :=
  ∑ i∈T, (D i∩R).card

def pairFamily (T : Finset β) (D : β → Finset α) : Finset (Σ _ : β, Finset α) :=
  T.sigma (fun i => (D i).powersetCard 2)

def pairCost (T : Finset β) (D : β → Finset α) (R : Finset α) : ℕ :=
  ((pairFamily T D).filter (fun x => x.2⊆R)).card

lemma pairCost_eq (T : Finset β) (D : β → Finset α) (R : Finset α) :
    pairCost T D R=∑ i∈T, (D i∩R).card.choose 2 := by
  have he : (pairFamily T D).filter (fun x => x.2⊆R)=
      T.sigma (fun i => (D i∩R).powersetCard 2) := by
    ext ⟨i,A⟩
    simp only [pairFamily,mem_filter,mem_sigma,mem_powersetCard,subset_inter_iff]
    tauto
  unfold pairCost
  rw [he,card_sigma]
  simp only [card_powersetCard]

lemma nat_hit_bound (k : ℕ) : k≤(if 0<k then 1 else 0)+k.choose 2 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [if_pos (Nat.succ_pos _)]
    have hh : (k+1).choose 2=k.choose 1+k.choose 2 := Nat.choose_succ_succ k 1
    rw [hh,Nat.choose_one_right]
    omega

lemma hit_lower (T : Finset β) (D : β → Finset α) (R : Finset α) :
    linearCount T D R≤hitCount T D R+pairCost T D R := by
  have hh := sum_le_sum (s := T) (fun i _ => nat_hit_bound (D i∩R).card)
  rw [sum_add_distrib,← pairCost_eq] at hh
  have he : (∑ i∈T, if 0<(D i∩R).card then (1:ℕ) else 0)=hitCount T D R := by
    simp [card_pos,hitCount]
  rwa [he] at hh

lemma pairs_vertex_card (A : Finset α) (a : α) :
    ((A.powersetCard 2).filter (fun S => a∈S)).card≤A.card := by
  have hh : ((A.powersetCard 2).filter (fun S => a∈S)).card≤(A.powersetCard 1).card := by
    apply card_le_card_of_injOn (fun S : Finset α => S.erase a)
    · intro S hS
      obtain ⟨hS,ha⟩ := mem_filter.mp hS
      obtain ⟨hSA,hSc⟩ := mem_powersetCard.mp hS
      exact mem_powersetCard.mpr ⟨(erase_subset a S).trans hSA,by rw [card_erase_of_mem ha,hSc]⟩
    · intro S hS V hV he
      dsimp only at he
      rw [← insert_erase (mem_filter.mp hS).2,← insert_erase (mem_filter.mp hV).2,he]
  simpa only [card_powersetCard,Nat.choose_one_right] using hh

lemma pairFamily_card (T : Finset β) (D : β → Finset α) (s : ℕ)
    (hs : ∀ i∈T, (D i).card≤s) :
    (pairFamily T D).card≤T.card*s.choose 2 := by
  rw [pairFamily,card_sigma]
  calc
    _ ≤ ∑ _i∈T, s.choose 2 := sum_le_sum (fun i hi => by
      rw [card_powersetCard]
      exact Nat.choose_le_choose 2 (hs i hi))
    _ = _ := by simp

lemma pairFamily_vertex (T : Finset β) (D : β → Finset α) (s M : ℕ)
    (hs : ∀ i∈T, (D i).card≤s)
    (hM : ∀ a, (T.filter (fun i => a∈D i)).card≤M) (a : α) :
    ((pairFamily T D).filter (fun x => a∈x.2)).card≤s*M := by
  have he : (pairFamily T D).filter (fun x => a∈x.2)=
      (T.filter (fun i => a∈D i)).sigma (fun i => ((D i).powersetCard 2).filter (fun S => a∈S)) := by
    ext ⟨i,A⟩
    simp only [pairFamily,mem_filter,mem_sigma,mem_powersetCard]
    constructor
    · rintro ⟨⟨hi,hA,hcard⟩,ha⟩
      exact ⟨⟨hi,hA ha⟩,⟨hA,hcard⟩,ha⟩
    · rintro ⟨⟨hi,haD⟩,⟨hA,hcard⟩,ha⟩
      exact ⟨⟨hi,hA,hcard⟩,ha⟩
  rw [he,card_sigma]
  calc
    _ ≤ ∑ _i∈T.filter (fun i => a∈D i), s := sum_le_sum (fun i hi =>
      (pairs_vertex_card (D i) a).trans (hs i (mem_filter.mp hi).1))
    _ = s*(T.filter (fun i => a∈D i)).card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left s (hM a)

lemma pairFamily_pair (T : Finset β) (D : β → Finset α) (M : ℕ)
    (hM : ∀ a, (T.filter (fun i => a∈D i)).card≤M)
    (S : Finset α) (hS : S.card=2) :
    IndexedBernoulliMoments.incidence (pairFamily T D) (fun x => x.2) S≤M := by
  obtain ⟨a,ha⟩ := card_pos.mp (by rw [hS]; decide : 0<S.card)
  apply (show IndexedBernoulliMoments.incidence (pairFamily T D) (fun x => x.2) S≤
      (T.filter (fun i => a∈D i)).card from ?_).trans (hM a)
  apply card_le_card_of_injOn Sigma.fst
  · rintro ⟨i,A⟩ hx
    obtain ⟨hx,hSA⟩ := mem_filter.mp hx
    obtain ⟨hi,hA⟩ := mem_sigma.mp hx
    exact mem_filter.mpr ⟨hi,(mem_powersetCard.mp hA).1 (hSA ha)⟩
  · rintro ⟨i,A⟩ hx ⟨j,B⟩ hy he
    have hA := (mem_powersetCard.mp (mem_sigma.mp (mem_filter.mp hx).1).2).2
    have hB := (mem_powersetCard.mp (mem_sigma.mp (mem_filter.mp hy).1).2).2
    change A.card=2 at hA
    change B.card=2 at hB
    have hSA : S=A := eq_of_subset_of_card_le (mem_filter.mp hx).2 (by omega)
    have hSB : S=B := eq_of_subset_of_card_le (mem_filter.mp hy).2 (by omega)
    change i=j at he
    subst j
    rw [← hSA,← hSB]

def overlapCaps (m s M : ℕ) : ℕ → ℕ
  | 0 => m*s.choose 2
  | 1 => s*M
  | _ => M

lemma pairFamily_incidence (T : Finset β) (D : β → Finset α) (s M : ℕ)
    (hs : ∀ i∈T, (D i).card≤s)
    (hM : ∀ a, (T.filter (fun i => a∈D i)).card≤M)
    (S : Finset α) (hS : S.card≤2) :
    IndexedBernoulliMoments.incidence (pairFamily T D) (fun x => x.2) S≤
      overlapCaps T.card s M S.card := by
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc | hc | hc
  · have he := card_eq_zero.mp hc
    subst S
    simpa [IndexedBernoulliMoments.incidence,overlapCaps] using pairFamily_card T D s hs
  · obtain ⟨a,ha⟩ := card_eq_one.mp hc
    subst S
    simpa only [IndexedBernoulliMoments.incidence,card_singleton,overlapCaps,singleton_subset_iff]
      using pairFamily_vertex T D s M hs hM a
  · rw [hc]
    exact pairFamily_pair T D M hM S hc

variable [Fintype α]

def weight (T : Finset β) (D : β → Finset α) (a : α) : ℝ :=
  (T.filter (fun i => a∈D i)).card

lemma linear_value (T : Finset β) (D : β → Finset α) (f : α → Bool) :
    (linearCount T D (selected f):ℝ)=WeightedBernoulliLowerTail.value (weight T D) f := by
  have he (i : β) : D i∩selected f=(selected f).filter (fun a => a∈D i) := by
    ext a
    simp only [mem_inter,mem_filter,and_comm]
  have hh := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := selected f) (fun i a => a∈D i)
  simp only [bipartiteAbove,bipartiteBelow] at hh
  simp_rw [← he] at hh
  unfold linearCount
  rw [hh,Nat.cast_sum]
  simp only [WeightedBernoulliLowerTail.value,weight,selected,sum_filter]

lemma weight_sum (T : Finset β) (D : β → Finset α) :
    (∑ a : α, weight T D a)=∑ i∈T, ((D i).card:ℝ) := by
  have hh := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := (univ : Finset α)) (fun i a => a∈D i)
  simp only [bipartiteAbove,bipartiteBelow,filter_mem_eq_inter,univ_inter] at hh
  unfold weight
  exact_mod_cast hh.symm

/-- Pair-correction tail with every overlap rank accounted for. -/
theorem pair_tail (T : Finset β) (D : β → Finset α) (s M q : ℕ) (p L : ℝ)
    (hs : ∀ i∈T, (D i).card≤s)
    (hM : ∀ a, (T.filter (fun i => a∈D i)).card≤M)
    (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(pairCost T D (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget 2 q (overlapCaps T.card s M) p/L)^q := by
  exact IndexedBernoulliMoments.tail_bound (pairFamily T D) (fun x => x.2) 2 q
    (overlapCaps T.card s M) p L hp hp1 hL
    (fun i hi => (mem_powersetCard.mp (mem_sigma.mp hi).2).2)
    (pairFamily_incidence T D s M hs hM)

/-- Lower concentration of the actual hit count. The two terms pay for a
weighted linear lower deviation and for multiple hits of the same index. -/
theorem lower_tail (T : Finset β) (D : β → Finset α) (s M q : ℕ) (p η L : ℝ)
    (hs : ∀ i∈T, (D i).card≤s)
    (hM : ∀ a, (T.filter (fun i => a∈D i)).card≤M) (hMpos : 0<M)
    (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) (hL : 0<L) :
    (∑ f : α → Bool, if (hitCount T D (selected f):ℝ)≤
      (1-η)*(p*∑ i∈T, ((D i).card:ℝ))-L then trialWeight p f else 0) ≤
      Real.exp (-η^2*(p*∑ i∈T, ((D i).card:ℝ))/(2*M))+
        (IndexedBernoulliMoments.budget 2 q (overlapCaps T.card s M) p/L)^q := by
  let μ : ℝ := p*∑ i∈T, ((D i).card:ℝ)
  have hm : WeightedBernoulliLowerTail.mean (weight T D) p=μ := by
    rw [WeightedBernoulliLowerTail.mean,weight_sum]
  have hlinear := WeightedBernoulliLowerTail.relative_lower_tail (weight T D) (M:ℝ) p η
    (fun a => Nat.cast_nonneg _) (fun a => by dsimp [weight]; exact_mod_cast hM a)
    (by exact_mod_cast hMpos) hp hp1 hη
  rw [hm] at hlinear
  have hpair := pair_tail T D s M q p L hs hM hp hp1 hL
  have hcover (f : α → Bool) (hf : (hitCount T D (selected f):ℝ)≤(1-η)*μ-L) :
      WeightedBernoulliLowerTail.value (weight T D) f≤(1-η)*μ ∨
        L≤(pairCost T D (selected f):ℝ) := by
    by_contra! hh
    have hl : (linearCount T D (selected f):ℝ)≤
        (hitCount T D (selected f):ℝ)+(pairCost T D (selected f):ℝ) := by
      exact_mod_cast hit_lower T D (selected f)
    rw [linear_value] at hl
    linarith only [hf,hh.1,hh.2,hl]
  have hpoint (f : α → Bool) :
      (if (hitCount T D (selected f):ℝ)≤(1-η)*μ-L then trialWeight p f else 0) ≤
        (if WeightedBernoulliLowerTail.value (weight T D) f≤(1-η)*μ then trialWeight p f else 0)+
        (if L≤(pairCost T D (selected f):ℝ) then trialWeight p f else 0) := by
    have hn := trialWeight_nonneg hp hp1 f
    split_ifs with hb hl hpa
    all_goals try linarith only [hn]
    have hh := hcover f (by assumption)
    tauto
  have hh := sum_le_sum (s := (univ : Finset (α → Bool))) (fun f _ => hpoint f)
  rw [sum_add_distrib] at hh
  exact hh.trans (add_le_add hlinear hpair)

end
end Erdos773.BernoulliHitCounts
end EndpointModule010
-- End BernoulliHitCounts.lean

-- Begin PolynomialSidonSlopes.lean
section EndpointModule011

/- A polynomial-size finite cyclic carrier for Sidon slope labels. This is
an ordinary Sidon construction, not a Sidon subset of square values. -/
namespace Erdos773.PolynomialSidonSlopes
open Finset
set_option maxHeartbeats 2000000
noncomputable section

def value (D : ℕ) (i : Fin D) : ℕ := i.val+(2*D+1)*i.val^2
def height (D : ℕ) : ℕ := 3*(D+1)^3

def seed (D p : ℕ) : Finset (ZMod p) := univ.image (fun i : Fin D => (value D i : ZMod p))

lemma value_lt (D : ℕ) (i : Fin D) : value D i<height D := by
  have hi := i.isLt
  have hi2 := Nat.pow_le_pow_left hi.le 2
  have hm := Nat.mul_le_mul_left (2*D+1) hi2
  unfold value height
  nlinarith only [hm,hi]

lemma value_mod (D : ℕ) (i : Fin D) : value D i%(2*D+1)=i.val := by
  have hi : i.val<2*D+1 := by have hh := i.isLt; omega
  simp [value,Nat.add_mod,Nat.mod_eq_of_lt hi]

lemma value_injective (D : ℕ) : Function.Injective (value D) := by
  intro i j hij
  apply Fin.ext
  have hh := congrArg (fun n => n%(2*D+1)) hij
  simpa only [value_mod] using hh

lemma sum_sq_matching (a b c d : ℕ) (hs : a+b=c+d) (hq : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hsZ : (a:ℤ)+b=c+d := by exact_mod_cast hs
  have hqZ : (a:ℤ)^2+b^2=c^2+d^2 := by exact_mod_cast hq
  have hp : (a:ℤ)*b=c*d := by
    have hh := congrArg (fun z : ℤ => z^2) hsZ
    nlinarith only [hh,hqZ]
  have hf : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by
    linear_combination (a:ℤ)*hsZ-hp
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hh : a=c := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh,by omega⟩
  · right
    have hh : a=d := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh,by omega⟩

lemma value_pair_matching (D : ℕ) (a b c d : Fin D)
    (he : value D a+value D b=value D c+value D d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hab : a.val+b.val<2*D+1 := by have ha := a.isLt; have hb := b.isLt; omega
  have hcd : c.val+d.val<2*D+1 := by have hc := c.isLt; have hd := d.isLt; omega
  have he' : a.val+b.val+(2*D+1)*(a.val^2+b.val^2)=
      c.val+d.val+(2*D+1)*(c.val^2+d.val^2) := by
    dsimp only [value] at he
    nlinarith only [he]
  have hs := congrArg (fun n => n%(2*D+1)) he'
  simp only [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hab,
    Nat.mod_eq_of_lt hcd] at hs
  have hm : (2*D+1)*(a.val^2+b.val^2)=(2*D+1)*(c.val^2+d.val^2) := by omega
  have hq := Nat.eq_of_mul_eq_mul_left (by omega : 0<2*D+1) hm
  rcases sum_sq_matching a b c d hs hq with h | h
  · exact Or.inl ⟨Fin.ext h.1,Fin.ext h.2⟩
  · exact Or.inr ⟨Fin.ext h.1,Fin.ext h.2⟩

lemma cast_injective (D p : ℕ) (hp : 2*height D<p) :
    Function.Injective (fun i : Fin D => (value D i:ZMod p)) := by
  intro i j hij
  apply value_injective D
  have hi : value D i<p := (value_lt D i).trans (by omega)
  have hj : value D j<p := (value_lt D j).trans (by omega)
  have hh := (ZMod.natCast_eq_natCast_iff' (value D i) (value D j) p).mp hij
  simpa only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hh

lemma seed_card (D p : ℕ) (hp : 2*height D<p) : (seed D p).card=D := by
  rw [seed,card_image_of_injective _ (cast_injective D p hp)]
  simp

lemma seed_sidon (D p : ℕ) (hp : 2*height D<p) : IsSidon (seed D p : Set (ZMod p)) := by
  intro a ha b hb c hc d hd he
  simp only [seed,Finset.mem_coe] at ha hb hc hd
  obtain ⟨i,_,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := mem_image.mp hb
  obtain ⟨k,_,rfl⟩ := mem_image.mp hc
  obtain ⟨l,_,rfl⟩ := mem_image.mp hd
  have hik : value D i+value D k<p := by have hi := value_lt D i; have hk := value_lt D k; omega
  have hjl : value D j+value D l<p := by have hj := value_lt D j; have hl := value_lt D l; omega
  have he' : ((value D i+value D k:ℕ):ZMod p)=((value D j+value D l:ℕ):ZMod p) := by
    push_cast
    exact he
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ p).mp he'
  rw [Nat.mod_eq_of_lt hik,Nat.mod_eq_of_lt hjl] at hh
  rcases value_pair_matching D i k j l hh with h | h
  · left; simp only [h.1,h.2,and_self]
  · right; simp only [h.1,h.2,and_self]

/-- Distinct equal directed differences of Sidon labels determine their
ordered endpoints. No multiplicative or square-Sidon property is asserted. -/
lemma difference_unique {G : Type*} [AddCommGroup G] {T : Set G} (hT : IsSidon T)
    {a b c d : G} (ha : a∈T) (hb : b∈T) (hc : c∈T) (hd : d∈T)
    (hab : a≠b) (he : a-b=c-d) : a=c ∧ b=d := by
  have hs : a+d=c+b := sub_eq_sub_iff_add_eq_add.mp he
  rcases hT a ha c hc d hd b hb hs with h | h
  · exact ⟨h.1,h.2.symm⟩
  · exact False.elim (hab h.1)

end
end Erdos773.PolynomialSidonSlopes
end EndpointModule011
-- End PolynomialSidonSlopes.lean

-- Begin RegularizationCommonNeighbors.lean
section EndpointModule012

/- Common-neighbor control for regularizing an already mixed residual
hypergraph. Its graph layer is preserved by higher-rank regularization;
Sidon slopes bound the extra common neighbors in rank two. -/
namespace Erdos773.RegularizationCommonNeighbors
open Finset UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section
attribute [local instance] Classical.propDecidable

section Graph
variable {β : Type*} [Fintype β] [DecidableEq β]

def Adj (H : Finset (Finset β)) (x y : β) : Prop := x≠y ∧ ({x,y}:Finset β)∈H

def both (H K : Finset (Finset β)) (x y : β) : Finset β :=
  univ.filter (fun z => Adj H x z ∧ Adj K y z)

def common (H : Finset (Finset β)) (x y : β) : ℕ := (both H H x y).card

lemma mem_both {H K : Finset (Finset β)} {x y z : β} :
    z∈both H K x y ↔ Adj H x z ∧ Adj K y z := by simp [both]

omit [Fintype β] in
lemma adj_union (H K : Finset (Finset β)) (x y : β) :
    Adj (H∪K) x y ↔ Adj H x y ∨ Adj K x y := by simp [Adj,and_or_left]

lemma both_swap (H K : Finset (Finset β)) (x y : β) : both H K x y=both K H y x := by
  ext z
  simp only [mem_both,and_comm]

lemma common_union (H K : Finset (Finset β)) (x y : β) :
    common (H∪K) x y ≤ common H x y+(both H K x y).card+
      (both K H x y).card+common K x y := by
  have he : both (H∪K) (H∪K) x y=
      (both H H x y∪both H K x y)∪(both K H x y∪both K K x y) := by
    ext z
    simp only [mem_both,mem_union,adj_union]
    tauto
  unfold common
  rw [he]
  have h1 := card_union_le (both H H x y∪both H K x y) (both K H x y∪both K K x y)
  have h2 := card_union_le (both H H x y) (both H K x y)
  have h3 := card_union_le (both K H x y) (both K K x y)
  omega
end Graph

section Copies
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_adj (H : Finset (Finset α)) (x y : Vertex α ρ F) :
    Adj (oldEdges H) x y ↔ x.2=y.2 ∧ Adj H x.1 y.1 := by
  constructor
  · rintro ⟨hne,he⟩
    obtain ⟨f,hf,c,hfc⟩ := mem_oldEdges.mp he
    have hx : x∈copyEdge f c := by rw [hfc]; simp
    have hy : y∈copyEdge f c := by rw [hfc]; simp
    have hxc := (mem_copyEdge.mp hx).2
    have hyc := (mem_copyEdge.mp hy).2
    have hxy := hxc.trans hyc.symm
    have hab : x.1≠y.1 := fun h => hne (Prod.ext h hxy)
    have hec : copyEdge ({x.1,y.1}:Finset α) c=({x,y}:Finset (Vertex α ρ F)) := by
      simp only [copyEdge,image_insert,image_singleton]
      have hx' : (x.1,c)=x := by rw [← hxc]
      have hy' : (y.1,c)=y := by rw [← hyc]
      rw [hx',hy']
    have hfe := copyEdge_injective c (hfc.trans hec.symm)
    exact ⟨hxy,hab,by rwa [← hfe]⟩
  · rintro ⟨hxy,hab,hpair⟩
    refine ⟨fun h => hab (congrArg Prod.fst h),mem_oldEdges.mpr ⟨_,hpair,x.2,?_⟩⟩
    simp only [copyEdge,image_insert,image_singleton,Prod.mk.eta]
    rw [hxy]

omit [Nontrivial ρ] in
lemma new_adj_witness (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) :
    ∃ a s, s∈S a ∧ ∃ t, x∈line h a s t ∧ y∈line h a s t := by
  obtain ⟨a,s,hs,t,he⟩ := mem_newEdges.mp hxy.2
  exact ⟨a,s,hs,t,by rw [he]; simp,by rw [he]; simp⟩

omit [Nontrivial ρ] in
lemma new_adj_label (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) : x.1=y.1 := by
  obtain ⟨a,s,hs,t,hx,hy⟩ := new_adj_witness h S hxy
  exact (mem_line.mp hx).1.trans (mem_line.mp hy).1.symm

omit [Nontrivial ρ] in
lemma new_adj_row (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) : x.2.1≠y.2.1 := by
  obtain ⟨a,s,hs,t,hx,hy⟩ := new_adj_witness h S hxy
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hya,hy⟩ := mem_line.mp hy
  intro he
  apply hxy.1
  refine Prod.ext (hxa.trans hya.symm) (Prod.ext he ?_)
  rw [hx,hy,he]

omit [Field F] in
lemma old_common_bound (H : Finset (Finset α)) (C : ℕ)
    (hC : ∀ a b, a≠b → common H a b≤C) (x y : Vertex α ρ F) (hxy : x≠y) :
    common (oldEdges H) x y≤C := by
  by_cases hc : x.2=y.2
  · have hab : x.1≠y.1 := fun h => hxy (Prod.ext h hc)
    have hb : (both (oldEdges H) (oldEdges H) x y).card≤(both H H x.1 y.1).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro z hz
        obtain ⟨hx,hy⟩ := mem_both.mp hz
        exact mem_both.mpr ⟨((old_adj H x z).mp hx).2,((old_adj H y z).mp hy).2⟩
      · intro z hz w hw he
        have hzc := ((old_adj H x z).mp (mem_both.mp hz).1).1
        have hwc := ((old_adj H x w).mp (mem_both.mp hw).1).1
        exact Prod.ext he (hzc.symm.trans hwc)
    exact hb.trans (hC _ _ hab)
  · have he : both (oldEdges H) (oldEdges H) x y=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hx,hy⟩ := mem_both.mp hz
      exact hc (((old_adj H x z).mp hx).1.trans ((old_adj H y z).mp hy).1.symm)
    simp only [common,he,card_empty,Nat.zero_le]

/-- An old-edge/new-edge common neighbor is determined by one original
label and one copy coordinate, so there is at most one. -/
lemma mixed_common_bound (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (x y : Vertex α ρ F) : (both (oldEdges H) (newEdges h S) x y).card≤1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨hxz,hyz⟩ := mem_both.mp hz
  obtain ⟨hxw,hyw⟩ := mem_both.mp hw
  have hzc := ((old_adj H x z).mp hxz).1
  have hwc := ((old_adj H x w).mp hxw).1
  have hza := new_adj_label h S hyz
  have hwa := new_adj_label h S hyw
  exact Prod.ext (hza.symm.trans hwa) (hzc.symm.trans hwc)

omit [Nontrivial ρ] in
lemma adj_regularized_other (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hρ : Fintype.card ρ≠2) (x y : Vertex α ρ F) :
    Adj (regularized H h S) x y ↔ Adj (oldEdges H) x y := by
  rw [regularized,adj_union]
  have hn : ¬Adj (newEdges h S) x y := by
    rintro ⟨hne,he⟩
    obtain ⟨a,s,hs,t,hline⟩ := mem_newEdges.mp he
    have hh := congrArg Finset.card hline
    rw [line_card,card_pair hne] at hh
    exact hρ hh
  simp only [hn,or_false]

/-- Adding only higher-rank constraints leaves the graph layer unchanged
inside each old copy. -/
lemma higher_common_bound (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hρ : Fintype.card ρ≠2) (C : ℕ) (hC : ∀ a b, a≠b → common H a b≤C)
    (x y : Vertex α ρ F) (hxy : x≠y) : common (regularized H h S) x y≤C := by
  have he : both (regularized H h S) (regularized H h S) x y=
      both (oldEdges H) (oldEdges H) x y := by
    ext z
    simp only [mem_both,adj_regularized_other H h S hρ]
  unfold common
  rw [he]
  exact old_common_bound H C hC x y hxy
end Copies

section TwoRows
variable {α F : Type*} [Fintype α] [DecidableEq α]
  [Field F] [Fintype F] [DecidableEq F]

lemma two_eq_of_ne (a b c : Fin 2) (hac : a≠c) (hbc : b≠c) : a=b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have ha' : a.val≠c.val := fun h => hac (Fin.ext h)
  have hb' : b.val≠c.val := fun h => hbc (Fin.ext h)
  omega

/-- Sidon slope labels forbid a four-cycle entirely among newly added
rank-two edges. This controls common neighbors, not just pair codegrees. -/
lemma new_common_bound (h : Fin 2 → F) (hh : Function.Injective h)
    (S : α → Finset F) (T : Finset F) (hST : ∀ a, S a⊆T) (hT : IsSidon (T:Set F))
    (x y : Vertex α (Fin 2) F) (hxy : x≠y) : common (newEdges h S) x y≤1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨hxz,hyz⟩ := mem_both.mp hz
  obtain ⟨hxw,hyw⟩ := mem_both.mp hw
  have hrowxy : x.2.1=y.2.1 := two_eq_of_ne _ _ _ (new_adj_row h S hxz) (new_adj_row h S hyz)
  have hrowzw : z.2.1=w.2.1 := two_eq_of_ne _ _ _ (new_adj_row h S hxz).symm (new_adj_row h S hxw).symm
  obtain ⟨a,s,hs,t,hx,hz⟩ := new_adj_witness h S hxz
  obtain ⟨b,u,hu,v,hy,hz'⟩ := new_adj_witness h S hyz
  obtain ⟨c,s',hs',t',hx',hw⟩ := new_adj_witness h S hxw
  obtain ⟨d,u',hu',v',hy',hw'⟩ := new_adj_witness h S hyw
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hza,hz⟩ := mem_line.mp hz
  obtain ⟨hyb,hy⟩ := mem_line.mp hy
  obtain ⟨hzb,hz'⟩ := mem_line.mp hz'
  obtain ⟨hxc,hx'⟩ := mem_line.mp hx'
  obtain ⟨hwc,hw⟩ := mem_line.mp hw
  obtain ⟨hyd,hy'⟩ := mem_line.mp hy'
  obtain ⟨hwd,hw'⟩ := mem_line.mp hw'
  have hxa' : x.1=y.1 := hxa.trans (hza.symm.trans (hzb.trans hyb.symm))
  have hvxy : x.2.2≠y.2.2 := fun he => hxy (Prod.ext hxa' (Prod.ext hrowxy he))
  have hdelta : h z.2.1-h x.2.1≠0 :=
    sub_ne_zero.mpr (fun he => (new_adj_row h S hxz).symm (hh he))
  have hslope : (s-u)*(h z.2.1-h x.2.1)=(s'-u')*(h z.2.1-h x.2.1) := by
    rw [← hrowxy] at hy hy'
    rw [← hrowzw] at hw hw'
    linear_combination -hz+hx+hz'-hy+hw-hx'-hw'+hy'
  have he : s-u=s'-u' := mul_right_cancel₀ hdelta hslope
  have hsu : s≠u := by
    intro he
    rw [← hrowxy] at hy
    have ht : t=v := by rw [he] at hz; linear_combination hz'-hz
    apply hvxy
    rw [hx,hy,he,ht]
  have hss := PolynomialSidonSlopes.difference_unique hT
    (hST a hs) (hST b hu) (hST c hs') (hST d hu') hsu he
  have htt : t=t' := by rw [hss.1] at hx; linear_combination hx'-hx
  refine Prod.ext (hza.trans (hxa.symm.trans (hxc.trans hwc.symm))) (Prod.ext hrowzw ?_)
  rw [hz,hw,htt,hss.1,hrowzw]

/-- The graph common-neighbor cap grows by at most three. The original
constraints are all retained, and no density-transfer assertion is needed
for this local structural estimate. -/
theorem two_common_bound (H : Finset (Finset α)) (h : Fin 2 → F) (hh : Function.Injective h)
    (S : α → Finset F) (T : Finset F) (hST : ∀ a, S a⊆T) (hT : IsSidon (T:Set F))
    (C : ℕ) (hC : ∀ a b, a≠b → common H a b≤C)
    (x y : Vertex α (Fin 2) F) (hxy : x≠y) : common (regularized H h S) x y≤C+3 := by
  have h1 := common_union (oldEdges H) (newEdges h S) x y
  have h2 := old_common_bound H C hC x y hxy
  have h3 := mixed_common_bound H h S x y
  have h4 := mixed_common_bound H h S y x
  rw [both_swap] at h4
  have h5 := new_common_bound h hh S T hST hT x y hxy
  change common (oldEdges H∪newEdges h S) x y≤C+3
  omega
end TwoRows

end
end Erdos773.RegularizationCommonNeighbors
end EndpointModule012
-- End RegularizationCommonNeighbors.lean

-- Begin StoppedGreedyMoments.lean
section EndpointModule013

/-
Finite averages for a stopped greedy process. The inclusion bound is a
configuration-counting tool; it does not establish a long running time.
-/
namespace Erdos773.StoppedGreedyMoments
open Finset GreedyHypergraphState
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.
-- Unused development declaration omitted.
-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.StoppedGreedyMoments
end EndpointModule013
-- End StoppedGreedyMoments.lean

-- Begin GreedyConfigurationTails.lean
section EndpointModule014

/-
Witness and disjoint-configuration tail bounds for the stopped greedy process.
No assertion that the process reaches the proposed stopping time is made.
-/
namespace Erdos773.GreedyConfigurationTails
open Finset GreedyHypergraphState StoppedGreedyMoments
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyConfigurationTails
end EndpointModule014
-- End GreedyConfigurationTails.lean

-- Begin GreedyWitnessPacking.lean
section EndpointModule015

/-
Packing intersecting witnesses before applying inclusion bounds. The conclusion
continues to concern the stopped process, not a guarantee of its running time.
-/
namespace Erdos773.GreedyWitnessPacking
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
set_option maxHeartbeats 2000000
noncomputable section

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

variable [Fintype α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyWitnessPacking
end EndpointModule015
-- End GreedyWitnessPacking.lean

-- Begin GreedyCommonNeighbors.lean
section EndpointModule016

/-
Common-neighbor witnesses in the residual two-graph. Original edge pairs are
kept as indices, so repeated witnesses are counted with their multiplicity.
-/
namespace Erdos773.GreedyCommonNeighbors
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
open GreedyWitnessPacking FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

abbrev Pattern (α : Type*) := Finset α × α × Finset α

def extensions (H E : Finset (Finset α)) (v : α) (W : Finset α → Finset α) :
    Finset (Pattern α) :=
  E.biUnion (fun e => (W e).biUnion (fun w =>
    (H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f))))

lemma mem_extensions {H E : Finset (Finset α)} {v : α}
    {W : Finset α → Finset α} {e f : Finset α} {w : α} :
    (e,w,f) ∈ extensions H E v W ↔ e ∈ E ∧ w ∈ W e ∧ f ∈ H ∧ v ∈ f ∧ w ∈ f := by
  simp only [extensions, mem_biUnion, mem_image, mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨e', he', w', hw', f', ⟨hf', hv', hwf'⟩, he, hw, hf⟩
    subst e'; subst w'; subst f'
    exact ⟨he', hw', hf', hv', hwf'⟩
  · rintro ⟨he, hw, hf, hvf, hwf⟩
    exact ⟨e, he, w, hw, f, ⟨hf, hvf, hwf⟩, rfl, rfl, rfl⟩

lemma extensions_card_le (H E : Finset (Finset α)) (v : α)
    (W : Finset α → Finset α) (r K : ℕ)
    (hsize : ∀ e ∈ E, (W e).card ≤ r)
    (hne : ∀ e ∈ E, ∀ w ∈ W e, v ≠ w)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (extensions H E v W).card ≤ E.card*r*K := by
  calc
    _ ≤ ∑ e ∈ E, ((W e).biUnion (fun w =>
      (H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f)))).card := card_biUnion_le
    _ ≤ ∑ e ∈ E, ∑ w ∈ W e,
      ((H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f))).card :=
      sum_le_sum (fun _ _ => card_biUnion_le)
    _ ≤ ∑ e ∈ E, ∑ _w ∈ W e, K := by
      apply sum_le_sum
      intro e he
      apply sum_le_sum
      intro w hw
      exact card_image_le.trans (hK v w (hne e he w hw))
    _ = ∑ e ∈ E, (W e).card*K := by simp
    _ ≤ ∑ _e ∈ E, r*K := sum_le_sum (fun e he => Nat.mul_le_mul_right K (hsize e he))
    _ = _ := by simp [mul_assoc]

/-- e contains u,w, f contains v,w, and neither edge contains the opposite
    designated endpoint. -/
def patterns (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (extensions H (H.filter (fun e => u ∈ e)) v (fun e => e \ {u,v})).filter
    (fun x => v ∉ x.1 ∧ u ∉ x.2.2)

lemma mem_patterns {H : Finset (Finset α)} {u v w : α} {e f : Finset α} :
    (e,w,f) ∈ patterns H u v ↔
      e ∈ H ∧ f ∈ H ∧ u ∈ e ∧ v ∈ f ∧ w ∈ e ∧ w ∈ f ∧
        w ≠ u ∧ w ≠ v ∧ v ∉ e ∧ u ∉ f := by
  simp only [patterns, mem_filter, mem_extensions, mem_sdiff, mem_insert, mem_singleton]
  tauto

lemma pattern_swap {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (h : (e,w,f) ∈ patterns H u v) : (f,w,e) ∈ patterns H v u := by
  simp only [mem_patterns] at *
  tauto

-- Unused development declaration omitted.

def witness (u v : α) (x : Pattern α) : Finset α :=
  (x.1 \ {u,x.2.1}) ∪ (x.2.2 \ {v,x.2.1})

-- Unused development declaration omitted.

lemma pattern_residual_cards {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) {u v w : α} {e f : Finset α}
    (h : (e,w,f) ∈ patterns H u v) :
    (e \ {u,w}).card = 2 ∧ (f \ {v,w}).card = 2 := by
  obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, _⟩ := mem_patterns.mp h
  have hp : ({u,w} : Finset α) ⊆ e := by simp [insert_subset_iff, hu, hw]
  have hq : ({v,w} : Finset α) ⊆ f := by simp [insert_subset_iff, hv, hwf]
  constructor
  · rw [card_sdiff_of_subset hp, h4 e he]
    simp [hwu.symm]
  · rw [card_sdiff_of_subset hq, h4 f hf]
    simp [hwv.symm]

lemma witness_card_bounds {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {u v : α} {x : Pattern α} (hx : x ∈ patterns H u v) :
    3 ≤ (witness u v x).card ∧ (witness u v x).card ≤ 4 := by
  rcases x with ⟨e,w,f⟩
  obtain ⟨hc, hd⟩ := pattern_residual_cards h4 hx
  obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, hve, huf⟩ := mem_patterns.mp hx
  have hef : e ≠ f := by rintro rfl; exact huf hu
  let A := (e \ {u,w}) ∩ (f \ {v,w})
  have hwa : w ∉ A := by simp [A]
  have hsub : insert w A ⊆ e ∩ f := by
    apply insert_subset_iff.mpr
    refine ⟨mem_inter.mpr ⟨hw, hwf⟩, ?_⟩
    intro a ha
    exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp ha).1).1,
      (mem_sdiff.mp (mem_inter.mp ha).2).1⟩
  have hi := (card_le_card hsub).trans (h2 e he f hf hef)
  rw [card_insert_of_notMem hwa] at hi
  have hh := card_union_add_card_inter (e \ {u,w}) (f \ {v,w})
  rw [hc, hd] at hh
  change 3 ≤ ((e \ {u,w}) ∪ (f \ {v,w})).card ∧
    ((e \ {u,w}) ∪ (f \ {v,w})).card ≤ 4
  dsimp [A] at hi
  omega

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

variable [Fintype α]

-- Unused development declaration omitted.

def patternCost (H : Finset (Finset α)) (u v : α) (I : Finset α) : ℕ :=
  ((patterns H u v).filter (fun x => witness u v x ⊆ I)).card

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyCommonNeighbors
end EndpointModule016
-- End GreedyCommonNeighbors.lean

-- Begin GreedyLinearDrift.lean
section EndpointModule017

/-
First-moment drift bounds for a linear hypergraph. Newly closed vertices are
included in edge losses. These identities are not a running-time theorem.
-/
namespace Erdos773.GreedyLinearDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors FourUniformRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A finite Bonferroni bound with only a uniform intersection hypothesis. -/
theorem union_card_lower (S : Finset β) (C : β → Finset α) (K : ℕ) :
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → (C i ∩ C j).card ≤ K) →
      (∑ i ∈ S, (C i).card) ≤ (S.biUnion C).card + S.card.choose 2*K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    intro hK
    have hi := ih (fun i hi j hj hij => hK i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hinter : C a ∩ S.biUnion C = S.biUnion (fun i => C a ∩ C i) := by
      ext x
      simp only [mem_inter, mem_biUnion]
      aesop
    have hc : (C a ∩ S.biUnion C).card ≤ S.card*K := by
      rw [hinter]
      calc
        _ ≤ ∑ i ∈ S, (C a ∩ C i).card := card_biUnion_le
        _ ≤ ∑ _i ∈ S, K := sum_le_sum (fun i hi => hK a (mem_insert_self _ _)
          i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
        _ = _ := by simp
    have hu := card_union_add_card_inter (C a) (S.biUnion C)
    rw [sum_insert ha, biUnion_insert, card_insert_of_notMem ha]
    have hchoose : (S.card+1).choose 2 = S.card.choose 2 + S.card := by
      rw [Nat.choose_succ_succ]
      simp [Nat.add_comm]
    rw [hchoose, Nat.add_mul]
    omega

variable [Fintype α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyLinearDrift
end EndpointModule017
-- End GreedyLinearDrift.lean

-- Begin GreedyBatchGraphLoss.lean
section EndpointModule018

/- Graph-neighborhood hitting inputs for a short batch. This module counts
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

end
end Erdos773.GreedyBatchGraphLoss
end EndpointModule018
-- End GreedyBatchGraphLoss.lean

-- Begin GreedyBatchDegreeStep.lean
section EndpointModule019

/- Deterministic simultaneous residual-rank accounting for a conservative
batch. Old-edge losses and every higher-rank promotion are retained. -/
namespace Erdos773.GreedyBatchDegreeStep
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open GreedyBatchPromotions
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def sources (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) : Finset (Finset α) :=
  H.filter (fun e => e \ R⊆carrier H R ∧ (e \ R).card=j ∧ x∈e \ R)

def oldCount (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) : ℕ :=
  ((incidentLayer H j x).filter (fun e => e⊆carrier H R)).card

lemma degree_le_sources (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) :
    degree (layer (next H R) j) x≤(sources H R j x).card := by
  have hs : (layer (next H R) j).filter (fun e => x∈e) ⊆
      (sources H R j x).image (fun e => e \ R) := by
    intro f hf
    obtain ⟨hf,hx⟩ := mem_filter.mp hf
    obtain ⟨hf,hj⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    obtain ⟨he,hlo,hQ⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hQ,hj,hx⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma same_rank_le_old (H : Finset (Finset α)) (R : Finset α) (j : ℕ) (x : α) :
    ((sources H R j x).filter (fun e => e.card=j)).card≤oldCount H R j x := by
  apply card_le_card
  intro e he
  obtain ⟨he,her⟩ := mem_filter.mp he
  obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
  have heq : e \ R=e := eq_of_subset_of_card_le sdiff_subset (by omega)
  rw [heq] at hQ hx
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨he,her⟩,hx⟩,hQ⟩

lemma higher_rank_le_cost (H : Finset (Finset α)) (R : Finset α) (j r : ℕ) (x : α)
    (hjr : j≤r) :
    ((sources H R j x).filter (fun e => e.card=r)).card≤cost H x r (r-j) R := by
  have heq : j+(r-j)=r := Nat.add_sub_of_le hjr
  have hs : (sources H R j x).filter (fun e => e.card=r) ⊆
      (layer H (j+(r-j))).filter (fun e => x∈e \ R ∧ (e \ R).card=j) := by
    intro e he
    obtain ⟨he,her⟩ := mem_filter.mp he
    obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,by rwa [heq]⟩,hx,hj⟩
  have hh := (card_le_card hs).trans (contraction_count H R x j (r-j))
  rwa [heq] at hh

lemma lower_rank_empty (H : Finset (Finset α)) (R : Finset α) (j r : ℕ) (x : α)
    (hrj : r<j) : (sources H R j x).filter (fun e => e.card=r)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,her⟩ := mem_filter.mp he
  obtain ⟨he,hQ,hj,hx⟩ := mem_filter.mp he
  have hh := card_le_card (sdiff_subset : e \ R⊆e)
  omega

def rankBudget (H : Finset (Finset α)) (R : Finset α) (x : α) (j r : ℕ) : ℕ :=
  if r=j then oldCount H R j x else if j<r then cost H x r (r-j) R else 0

/-- A finite update inequality, without any asserted typical profile. -/
theorem degree_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) (j : ℕ) :
    degree (layer (next H R) j) x≤∑ r∈range 5, rankBudget H R x j r := by
  apply (degree_le_sources H R j x).trans
  have he := card_eq_sum_card_fiberwise (s := sources H R j x) (t := range 5)
    (f := Finset.card) (fun e he => mem_range.mpr (by have := hH e (mem_filter.mp he).1; omega))
  rw [he]
  apply sum_le_sum
  intro r hr
  unfold rankBudget
  split_ifs with hrj hjr
  · subst r
    exact same_rank_le_old H R j x
  · exact higher_rank_le_cost H R j r x hjr.le
  · rw [lower_rank_empty H R j r x (by omega),card_empty]

/-- Rank four to rank two is charged with a two-mark witness. -/
theorem degree_two (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 2) x≤oldCount H R 2 x+cost H x 3 1 R+cost H x 4 2 R := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 2

theorem degree_three (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 3) x≤oldCount H R 3 x+cost H x 4 1 R := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 3

theorem degree_four (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x : α) :
    degree (layer (next H R) 4) x≤oldCount H R 4 x := by
  simpa [sum_range_succ,rankBudget] using degree_step H R hH x 4

end
end Erdos773.GreedyBatchDegreeStep
end EndpointModule019
-- End GreedyBatchDegreeStep.lean

-- Begin RegularizationSharedLinks.lean
section EndpointModule020

/- Affine padding introduces no new two-vertex shared links. This controls
a structural source of one-selected-vertex common-neighbor witnesses in a
mixed restart. No stochastic profile estimate is assumed or concluded. -/
namespace Erdos773.RegularizationSharedLinks
open Finset UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section

section Definition
variable {β : Type*} [Fintype β] [DecidableEq β]

def links (H : Finset (Finset β)) (x y : β) : Finset (Finset β) :=
  univ.filter (fun A => A.card=2 ∧ x∉A ∧ y∉A ∧ insert x A∈H ∧ insert y A∈H)

def count (H : Finset (Finset β)) (x y : β) : ℕ := (links H x y).card

lemma mem_links {H : Finset (Finset β)} {x y : β} {A : Finset β} :
    A∈links H x y ↔ A.card=2 ∧ x∉A ∧ y∉A ∧ insert x A∈H ∧ insert y A∈H := by
  simp [links]

omit [Fintype β] in
lemma insert_inter {A : Finset β} {x y : β} (hxy : x≠y) :
    insert x A∩insert y A=A := by
  ext a
  simp only [mem_inter,mem_insert]
  constructor
  · rintro ⟨h,h'⟩
    rcases h with rfl | h
    · exact h'.resolve_left hxy
    · exact h
  · intro h
    exact ⟨Or.inr h,Or.inr h⟩

omit [Fintype β] in
lemma insert_distinct {A : Finset β} {x y : β} (hxy : x≠y) (hx : x∉A) :
    insert x A≠insert y A := by
  intro he
  have hm : x∈insert y A := he ▸ mem_insert_self x A
  exact (mem_insert.mp hm).elim hxy hx
end Definition

section Copies
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Field F] [Fintype F] [DecidableEq F]

/-- Any distinct edges with at least two common vertices lie together in
one old copy. All new/new and old/new overlaps have size at most one. -/
lemma overlap_rigid (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {e f : Finset (Vertex α ρ F)}
    (he : e∈regularized H h S) (hf : f∈regularized H h S)
    (hne : e≠f) (hi : 1<(e∩f).card) :
    ∃ a∈H, ∃ b∈H, ∃ c : Copy ρ F, e=copyEdge a c ∧ f=copyEdge b c := by
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,hb,d,rfl⟩ := mem_oldEdges.mp hf
    have hcd : c=d := by
      by_contra hcd
      rw [copy_inter_distinct a b c d hcd,card_empty] at hi
      omega
    exact ⟨a,ha,b,hb,c,rfl,by rw [hcd]⟩
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,s,hs,t,rfl⟩ := mem_newEdges.mp hf
    exact (not_lt_of_ge (copy_line_inter_card a c h b s t) hi).elim
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,hb,c,rfl⟩ := mem_oldEdges.mp hf
    rw [inter_comm] at hi
    exact (not_lt_of_ge (copy_line_inter_card b c h a s t) hi).elim
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
    exact (not_lt_of_ge (line_inter_card h hh a b s t u v hne) hi).elim

/-- A shared link forces its endpoints, and the whole link, into a common
copy coordinate. -/
lemma link_coordinates (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {x y : Vertex α ρ F} (hxy : x≠y)
    {A : Finset (Vertex α ρ F)} (hA : A∈links (regularized H h S) x y) :
    x.2=y.2 ∧ ∀ z∈A, z.2=x.2 := by
  obtain ⟨hcard,hx,hy,he,hf⟩ := mem_links.mp hA
  obtain ⟨a,ha,b,hb,c,he,hf⟩ := overlap_rigid H h hh S he hf
    (insert_distinct hxy hx) (by rw [insert_inter hxy,hcard]; decide)
  have hxc : x.2=c := (mem_copyEdge.mp (he ▸ mem_insert_self x A)).2
  have hyc : y.2=c := (mem_copyEdge.mp (hf ▸ mem_insert_self y A)).2
  exact ⟨hxc.trans hyc.symm,fun z hz =>
    ((mem_copyEdge.mp (he ▸ mem_insert_of_mem hz)).2).trans hxc.symm⟩

/-- Projecting a shared link gives a genuine old link. -/
lemma project_link (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {x y : Vertex α ρ F} (hxy : x≠y)
    {A : Finset (Vertex α ρ F)} (hA : A∈links (regularized H h S) x y) :
    A.image Prod.fst∈links H x.1 y.1 := by
  have hc := link_coordinates H h hh S hxy hA
  obtain ⟨hcard,hx,hy,he,hf⟩ := mem_links.mp hA
  obtain ⟨a,ha,b,hb,c,he,hf⟩ := overlap_rigid H h hh S he hf
    (insert_distinct hxy hx) (by rw [insert_inter hxy,hcard]; decide)
  have hinj : Set.InjOn (Prod.fst : Vertex α ρ F → α) (A:Set (Vertex α ρ F)) := by
    intro z hz w hw he
    exact Prod.ext he ((hc.2 z hz).trans (hc.2 w hw).symm)
  have hc' : (A.image Prod.fst).card=2 := (card_image_iff.mpr hinj).trans hcard
  have hx' : x.1∉A.image Prod.fst := by
    intro hx'
    obtain ⟨z,hz,hzx⟩ := mem_image.mp hx'
    have hez : z=x := Prod.ext hzx (hc.2 z hz)
    exact hx (hez ▸ hz)
  have hy' : y.1∉A.image Prod.fst := by
    intro hy'
    obtain ⟨z,hz,hzy⟩ := mem_image.mp hy'
    have hez : z=y := Prod.ext hzy ((hc.2 z hz).trans hc.1)
    exact hy (hez ▸ hz)
  have project (a : Finset α) (c : Copy ρ F) : (copyEdge a c).image Prod.fst=a := by
    simp only [copyEdge,image_image]
    exact image_id
  have hpa := congrArg (fun e : Finset (Vertex α ρ F) => e.image Prod.fst) he
  have hpb := congrArg (fun e : Finset (Vertex α ρ F) => e.image Prod.fst) hf
  dsimp only at hpa hpb
  rw [image_insert,project] at hpa hpb
  exact mem_links.mpr ⟨hc',hx',hy',hpa.symm ▸ ha,hpb.symm ▸ hb⟩

/-- Shared-link bounds are preserved, with no additive deterioration. -/
theorem count_bound (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (B : ℕ) (hB : ∀ a b, a≠b → count H a b≤B)
    (x y : Vertex α ρ F) (hxy : x≠y) : count (regularized H h S) x y≤B := by
  by_cases hc : x.2=y.2
  · have hab : x.1≠y.1 := fun he => hxy (Prod.ext he hc)
    apply (show count (regularized H h S) x y≤count H x.1 y.1 from ?_).trans (hB _ _ hab)
    apply card_le_card_of_injOn (fun A : Finset (Vertex α ρ F) => A.image Prod.fst)
    · exact fun A hA => project_link H h hh S hxy hA
    · intro A hA B hB he
      dsimp only at he
      have hAc := (link_coordinates H h hh S hxy hA).2
      have hBc := (link_coordinates H h hh S hxy hB).2
      ext z
      constructor
      · intro hz
        have hz' : z.1∈B.image Prod.fst := he ▸ mem_image_of_mem Prod.fst hz
        obtain ⟨w,hw,hwz⟩ := mem_image.mp hz'
        have hwz' : w=z := Prod.ext hwz ((hBc w hw).trans (hAc z hz).symm)
        exact hwz' ▸ hw
      · intro hz
        have hz' : z.1∈A.image Prod.fst := he.symm ▸ mem_image_of_mem Prod.fst hz
        obtain ⟨w,hw,hwz⟩ := mem_image.mp hz'
        have hwz' : w=z := Prod.ext hwz ((hAc w hw).trans (hBc z hz).symm)
        exact hwz' ▸ hw
  · have he : links (regularized H h S) x y=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact hc (link_coordinates H h hh S hxy hA).1
    simp [count,he]
end Copies

end
end Erdos773.RegularizationSharedLinks
end EndpointModule020
-- End RegularizationSharedLinks.lean

-- Begin GreedyBatchSharedLoss.lean
section EndpointModule021

/- Graph-neighborhood loss and concentration for old shared rank-three
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

end
end Erdos773.GreedyBatchSharedLoss
end EndpointModule021
-- End GreedyBatchSharedLoss.lean

-- Begin GreedyBatchSharedWitnesses.lean
section EndpointModule022

/- Indexed creation witnesses for shared rank-three links in a mixed batch.
The one-mark and two-mark cases keep their true support sizes and original
edge multiplicities. No asymptotic restart theorem is asserted. -/
namespace Erdos773.GreedyBatchSharedWitnesses
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Index (α : Type*) := Σ _ : Finset α, Σ _ : Finset α, Finset α

def firstEdges (H : Finset (Finset α)) (x y : α) (r : ℕ) :=
  (layer H r).filter (fun e => x∈e ∧ y∉e)

def mates (H : Finset (Finset α)) (x y : α) (s : ℕ) (A : Finset α) :=
  (layer H s).filter (fun f => insert y A⊆f ∧ x∉f)

def family (H : Finset (Finset α)) (x y : α) (r s : ℕ) : Finset (Index α) :=
  (firstEdges H x y r).sigma (fun e => (e.erase x).powersetCard 2 |>.sigma (mates H x y s))

structure Data (H : Finset (Finset α)) (x y : α) (r s : ℕ)
    (e A f : Finset α) : Prop where
  e_mem : e∈H
  f_mem : f∈H
  e_card : e.card=r
  f_card : f.card=s
  x_mem : x∈e
  y_mem : y∈f
  y_not : y∉e
  x_not : x∉f
  A_card : A.card=2
  A_e : A⊆e
  A_f : A⊆f
  x_A : x∉A
  y_A : y∉A

lemma data_of_mem {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (hi : (⟨e,A,f⟩:Index α)∈family H x y r s) : Data H x y r s e A f := by
  obtain ⟨he,hi⟩ := mem_sigma.mp hi
  obtain ⟨hA,hf⟩ := mem_sigma.mp hi
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨he,hr⟩ := mem_filter.mp he
  obtain ⟨hAs,hAc⟩ := mem_powersetCard.mp hA
  obtain ⟨hf,hsub,hxf⟩ := mem_filter.mp hf
  obtain ⟨hf,hs⟩ := mem_filter.mp hf
  exact ⟨he,hf,hr,hs,hx,hsub (mem_insert_self _ _),hy,hxf,hAc,
    hAs.trans (erase_subset _ _),(subset_insert _ _).trans hsub,
    fun h => notMem_erase x e (hAs h),fun h => hy ((hAs.trans (erase_subset _ _)) h)⟩

lemma mem_of_data {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (h : Data H x y r s e A f) : (⟨e,A,f⟩:Index α)∈family H x y r s := by
  refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨h.e_mem,h.e_card⟩,h.x_mem,h.y_not⟩,
    mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨?_,h.A_card⟩,
      mem_filter.mpr ⟨mem_filter.mpr ⟨h.f_mem,h.f_card⟩,insert_subset h.y_mem h.A_f,h.x_not⟩⟩⟩
  intro a ha
  exact mem_erase.mpr ⟨fun he => h.x_A (he ▸ ha),h.A_e ha⟩

lemma Data.swap {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (h : Data H x y r s e A f) : Data H y x s r f A e :=
  ⟨h.f_mem,h.e_mem,h.f_card,h.e_card,h.y_mem,h.x_mem,h.x_not,h.y_not,
    h.A_card,h.A_f,h.A_e,h.y_A,h.x_A⟩

lemma mates_card (H : Finset (Finset α)) (x y : α) (s P : ℕ)
    (hP : ∀ a, y≠a → pairDegree H y a≤P)
    (A : Finset α) (hA : A.Nonempty) (hy : y∉A) : (mates H x y s A).card≤P := by
  obtain ⟨a,ha⟩ := hA
  have hya : y≠a := fun he => hy (he.symm ▸ ha)
  apply (card_le_card (show mates H x y s A⊆H.filter (fun f => y∈f ∧ a∈f) from ?_)).trans (hP a hya)
  intro f hf
  obtain ⟨hf,hsub,hx⟩ := mem_filter.mp hf
  exact mem_filter.mpr ⟨(mem_filter.mp hf).1,hsub (mem_insert_self _ _),hsub (mem_insert_of_mem ha)⟩

lemma family_card (H : Finset (Finset α)) (x y : α) (r s P : ℕ)
    (hP : ∀ a, y≠a → pairDegree H y a≤P) :
    (family H x y r s).card≤degree (layer H r) x*(r-1).choose 2*P := by
  rw [family,card_sigma]
  have hrow (e : Finset α) (he : e∈firstEdges H x y r) :
      (((e.erase x).powersetCard 2).sigma (mates H x y s)).card≤(r-1).choose 2*P := by
    obtain ⟨he,hx,hy⟩ := mem_filter.mp he
    have hrc := (mem_filter.mp he).2
    rw [card_sigma]
    calc
      _ ≤ ∑ _A∈(e.erase x).powersetCard 2, P := by
        apply sum_le_sum
        intro A hA
        obtain ⟨hAe,hAc⟩ := mem_powersetCard.mp hA
        exact mates_card H x y s P hP A (card_pos.mp (by rw [hAc]; decide))
          (fun h => hy ((erase_subset x e) (hAe h)))
      _ = _ := by simp [card_erase_of_mem hx,hrc]
  calc
    _ ≤ ∑ _e∈firstEdges H x y r, (r-1).choose 2*P := sum_le_sum hrow
    _ = (firstEdges H x y r).card*((r-1).choose 2*P) := by simp
    _ ≤ degree (layer H r) x*((r-1).choose 2*P) := by
      apply Nat.mul_le_mul_right
      apply card_le_card
      intro e he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨he,hx⟩
    _ = _ := by ring

def witness (x y : α) (i : Index α) : Finset α :=
  (i.1 \ insert x i.2.1)∪(i.2.2 \ insert y i.2.1)

def cost (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) : ℕ :=
  ((family H x y r s).filter (fun i => witness x y i⊆R)).card

lemma witness_card {H : Finset (Finset α)} {x y : α} {r s : ℕ} {i : Index α}
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2) (hi : i∈family H x y r s) :
    (witness x y i).card=(r-3)+(s-3) := by
  rcases i with ⟨e,A,f⟩
  have h := data_of_mem hi
  have hef : e≠f := fun he => h.x_not (he ▸ h.x_mem)
  have hAe : insert x A⊆e := insert_subset h.x_mem h.A_e
  have hAf : insert y A⊆f := insert_subset h.y_mem h.A_f
  have hAc : (insert x A).card=3 := by rw [card_insert_of_notMem h.x_A,h.A_card]
  have hBc : (insert y A).card=3 := by rw [card_insert_of_notMem h.y_A,h.A_card]
  have hcommon : A=e∩f := eq_of_subset_of_card_le (subset_inter h.A_e h.A_f)
    (by rw [h.A_card]; exact hI e h.e_mem f h.f_mem hef)
  have hd : Disjoint (e \ insert x A) (f \ insert y A) := by
    apply disjoint_left.mpr
    intro a ha hb
    have hm : a∈A := hcommon.symm ▸ mem_inter.mpr ⟨(mem_sdiff.mp ha).1,(mem_sdiff.mp hb).1⟩
    exact (mem_sdiff.mp ha).2 (mem_insert_of_mem hm)
  change ((e \ insert x A)∪(f \ insert y A)).card=_
  rw [card_union_of_disjoint hd,card_sdiff_of_subset hAe,card_sdiff_of_subset hAf,h.e_card,h.f_card,hAc,hBc]

/-- Once a first-role mark a is fixed, the shared two-set is determined
by the original first edge, since its rank is at most four. -/
lemma first_role_link {H : Finset (Finset α)} {x y a : α} {r s : ℕ} {e A f : Finset α}
    (hr : r≤4) (hi : (⟨e,A,f⟩:Index α)∈family H x y r s)
    (ha : a∈e \ insert x A) : A=e \ {x,a} := by
  have h := data_of_mem hi
  have hxa : x≠a := fun he => (mem_sdiff.mp ha).2 (by simp [he])
  have hpair : ({x,a}:Finset α)⊆e := by simp [insert_subset_iff,h.x_mem,(mem_sdiff.mp ha).1]
  have hs : A⊆e \ {x,a} := by
    intro b hb
    refine mem_sdiff.mpr ⟨h.A_e hb,?_⟩
    simp only [mem_insert,mem_singleton]
    rintro (rfl | rfl)
    · exact h.x_A hb
    · exact (mem_sdiff.mp ha).2 (mem_insert_of_mem hb)
  apply eq_of_subset_of_card_le hs
  rw [card_sdiff_of_subset hpair,h.e_card,card_pair hxa,h.A_card]
  omega

lemma first_role_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1)).card≤P^2 := by
  by_cases hax : a=x
  · subst a
    have he : (family H x y r s).filter (fun i => x∈i.1 \ insert x i.2.1)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (mem_sdiff.mp (mem_filter.mp hi).2).2 (mem_insert_self _ _)
    rw [he,card_empty]
    exact Nat.zero_le _
  · let E := (firstEdges H x y r).filter (fun e => a∈e)
    have hE : E.card≤P := by
      apply (card_le_card (show E⊆H.filter (fun e => x∈e ∧ a∈e) from ?_)).trans (hP x a (Ne.symm hax))
      intro e he
      obtain ⟨he,ha⟩ := mem_filter.mp he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,hx,ha⟩
    have hc (e : Finset α) (he : e∈E) : (mates H x y s (e \ {x,a})).card≤P := by
      obtain ⟨he,ha⟩ := mem_filter.mp he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      have hecard := (mem_filter.mp he).2
      apply mates_card H x y s P (hP y) (e \ {x,a})
      · apply card_pos.mp
        rw [card_sdiff_of_subset (by simp [insert_subset_iff,hx,ha]),hecard,card_pair (Ne.symm hax)]
        omega
      · exact fun h => hy (mem_sdiff.mp h).1
    have hb : ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1)).card≤
        (E.sigma (fun e => mates H x y s (e \ {x,a}))).card := by
      apply card_le_card_of_injOn (fun i : Index α => (⟨i.1,i.2.2⟩ : Σ _ : Finset α, Finset α))
      · rintro ⟨e,A,f⟩ hi
        obtain ⟨hi,ha⟩ := mem_filter.mp hi
        have h := data_of_mem hi
        have hA := first_role_link hr.2 hi ha
        refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_filter.mpr ⟨h.e_mem,h.e_card⟩,h.x_mem,h.y_not⟩,(mem_sdiff.mp ha).1⟩,?_⟩
        rw [← hA]
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨h.f_mem,h.f_card⟩,insert_subset h.y_mem h.A_f,h.x_not⟩
      · rintro ⟨e,A,f⟩ hi ⟨e',A',f'⟩ hi' he
        have he' : e=e' := congrArg Sigma.fst he
        have hf' : f=f' := congrArg (fun i : Σ _ : Finset α, Finset α => i.2) he
        subst e'; subst f'
        have hA := first_role_link hr.2 (mem_filter.mp hi).1 (mem_filter.mp hi).2
        have hA' := first_role_link hr.2 (mem_filter.mp hi').1 (mem_filter.mp hi').2
        rw [hA,hA']
    apply hb.trans
    rw [card_sigma]
    calc
      _ ≤ ∑ _e∈E, P := sum_le_sum hc
      _ = E.card*P := by simp
      _ ≤ P*P := Nat.mul_le_mul_right P hE
      _ = _ := by ring

lemma second_role_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hs : 3≤s ∧ s≤4) (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1)).card≤P^2 := by
  apply (show _≤((family H y x s r).filter (fun i => a∈i.1 \ insert y i.2.1)).card from ?_).trans
    (first_role_incidence H y x a s r P hs hP)
  apply card_le_card_of_injOn (fun i : Index α => (⟨i.2.2,i.2.1,i.1⟩ : Index α))
  · rintro ⟨e,A,f⟩ hi
    obtain ⟨hi,ha⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_of_data (data_of_mem hi).swap,ha⟩
  · rintro ⟨e,A,f⟩ hi ⟨e',A',f'⟩ hi' he
    have hf : f=f' := congrArg Sigma.fst he
    have hA : A=A' := congrArg (fun i : Index α => i.2.1) he
    have hh : e=e' := congrArg (fun i : Index α => i.2.2) he
    subst e'; subst A'; subst f'
    rfl

lemma witness_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈witness x y i)).card≤2*P^2 := by
  have he : (family H x y r s).filter (fun i => a∈witness x y i)=
      ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1))∪
      ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1)) := by
    ext i
    simp only [mem_filter,witness,mem_union]
    tauto
  rw [he]
  have hh := card_union_le
    ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1))
    ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1))
  have h1 := first_role_incidence H x y a r s P hr hP
  have h2 := second_role_incidence H x y a r s P hs hP
  omega

def swap (i : Index α) : Index α := ⟨i.2.2,i.2.1,i.1⟩

lemma swap_swap (i : Index α) : swap (swap i)=i := by cases i; rfl

lemma witness_swap (x y : α) (i : Index α) : witness y x (swap i)=witness x y i := union_comm _ _

lemma cost_le_swap (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    cost H x y r s R≤cost H y x s r R := by
  apply card_le_card_of_injOn swap
  · rintro ⟨e,A,f⟩ hi
    obtain ⟨hi,hR⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_of_data (data_of_mem hi).swap,by rwa [witness_swap]⟩
  · intro i hi j hj he
    have hh := congrArg swap he
    simpa only [swap_swap] using hh

lemma cost_swap (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    cost H x y r s R=cost H y x s r R :=
  Nat.le_antisymm (cost_le_swap H x y r s R) (cost_le_swap H y x s r R)

def overlapCaps (m P : ℕ) (k : ℕ) : ℕ := if k=0 then m else 2*P^2

lemma incidence_bound (H : Finset (Finset α)) (x y : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P) (A : Finset α) :
    IndexedBernoulliMoments.incidence (family H x y r s) (witness x y) A≤
      overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P A.card := by
  by_cases hA : A.card=0
  · have he := card_eq_zero.mp hA
    subst A
    simpa [IndexedBernoulliMoments.incidence,overlapCaps] using family_card H x y r s P (hP y)
  · rw [overlapCaps,if_neg hA]
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<A.card)
    apply (card_le_card (show (family H x y r s).filter (fun i => A⊆witness x y i)⊆
      (family H x y r s).filter (fun i => a∈witness x y i) from ?_)).trans
      (witness_incidence H x y a r s P hr hs hP)
    intro i hi
    obtain ⟨hi,hA⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,hA ha⟩

/-- Mixed shared-link creation tails: (3,4) uses one mark, while (4,4)
uses two. The latter relies on the original intersection cap of two. -/
theorem cost_tail (H : Finset (Finset α)) (x y : α) (r s P q : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(cost H x y r s (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget ((r-3)+(s-3)) q
        (overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P) p/L)^q := by
  exact IndexedBernoulliMoments.tail_bound (family H x y r s) (witness x y) ((r-3)+(s-3)) q
    (overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P) p L hp hp1 hL
    (fun i hi => witness_card hI hi) (fun A _ => incidence_bound H x y r s P hr hs hP A)

end
end Erdos773.GreedyBatchSharedWitnesses
end EndpointModule022
-- End GreedyBatchSharedWitnesses.lean

-- Begin BernoulliEvents.lean
section EndpointModule023

/- Finite event probabilities and indexed union bounds for the actual
Bernoulli product weights. -/
namespace Erdos773.BernoulliEvents
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def prob (p : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ f : α → Bool, if P (selected f) then trialWeight p f else 0

-- Unused development declaration omitted.

lemma mono (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (P Q : Finset α → Prop)
    (h : ∀ R, P R → Q R) : prob p P≤prob p Q := by
  apply sum_le_sum
  intro f hf
  split_ifs with hP hQ
  all_goals try exact le_refl _
  all_goals try exact trialWeight_nonneg hp hp1 f
  exact (hQ (h _ hP)).elim

/-- An indexed covering bound, valid with dependent or repeated events. -/
theorem cover_bound (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (S : Finset β)
    (P : β → Finset α → Prop) (Bad : Finset α → Prop)
    (hcover : ∀ R, Bad R → ∃ i∈S, P i R) : prob p Bad≤∑ i∈S, prob p (P i) := by
  have hpoint (f : α → Bool) : (if Bad (selected f) then trialWeight p f else 0)≤
      ∑ i∈S, if P i (selected f) then trialWeight p f else 0 := by
    by_cases hb : Bad (selected f)
    · obtain ⟨i,hi,hP⟩ := hcover _ hb
      have hh := single_le_sum (s := S) (f := fun i => if P i (selected f) then trialWeight p f else 0)
        (fun i hi => by dsimp only; split_ifs; exact trialWeight_nonneg hp hp1 f; exact le_refl _) hi
      simpa only [if_pos hb,if_pos hP] using hh
    · rw [if_neg hb]
      apply sum_nonneg
      intro i hi
      split_ifs
      · exact trialWeight_nonneg hp hp1 f
      · exact le_refl _
  have hh := sum_le_sum (s := (univ : Finset (α → Bool))) (fun f _ => hpoint f)
  rw [sum_comm] at hh
  exact hh

lemma union_bound (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (P Q : Finset α → Prop) :
    prob p (fun R => P R ∨ Q R)≤prob p P+prob p Q := by
  have hh := cover_bound p hp hp1 (univ : Finset Bool) (fun b => if b then P else Q) (fun R => P R ∨ Q R) (by
    intro R h
    rcases h with h | h
    · exact ⟨true,mem_univ _,h⟩
    · exact ⟨false,mem_univ _,h⟩)
  simpa [add_comm] using hh

/-- A deterministic upper cap makes a mean-dependent exponential term
uniform in small families. If mu<L, the stated upper-tail event is empty. -/
theorem capped_exponential_tail (p : ℝ) (X : Finset α → ℝ) (n μ η L M E : ℝ)
    (hX : ∀ R, X R≤n) (hμ : 0≤μ) (hη : 0≤η) (hM : 0<M) (hE : 0≤E)
    (htail : prob p (fun R => n-(1-η)*μ+L≤X R)≤Real.exp (-η^2*μ/(2*M))+E) :
    prob p (fun R => n-(1-η)*μ+L≤X R)≤Real.exp (-η^2*L/(2*M))+E := by
  by_cases hLμ : L≤μ
  · apply htail.trans
    apply add_le_add _ le_rfl
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : 0≤2*M)
    have hh := mul_le_mul_of_nonneg_left hLμ (sq_nonneg η)
    nlinarith only [hh]
  · have hbad (R : Finset α) : ¬n-(1-η)*μ+L≤X R := by
      have hh := hX R
      have hz := mul_nonneg hη hμ
      intro he
      linarith only [hh,hz,he,lt_of_not_ge hLμ]
    simp only [prob,if_neg (hbad _),sum_const_zero]
    exact add_nonneg (Real.exp_pos _).le hE

end
end Erdos773.BernoulliEvents
end EndpointModule023
-- End BernoulliEvents.lean

-- Begin GreedyBatchScalarTails.lean
section EndpointModule024

/- Uniform scalar tails for old-edge survival and new residual witnesses.
The estimates use actual Bernoulli weights, not a survival-law assumption. -/
namespace Erdos773.GreedyBatchScalarTails
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchGraphLoss
open GreedyBatchPromotions BernoulliEvents
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (common)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma budget_mono (r q : ℕ) (K K' : ℕ → ℕ) (p : ℝ) (hp : 0≤p)
    (hK : ∀ k, K k≤K' k) :
    IndexedBernoulliMoments.budget r q K p≤IndexedBernoulliMoments.budget r q K' p := by
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast hK k) (Nat.cast_nonneg _)) (pow_nonneg hp _)

lemma moment_mono (r q : ℕ) (K K' : ℕ → ℕ) (p L : ℝ) (hp : 0≤p) (hL : 0≤L)
    (hK : ∀ k, K k≤K' k) :
    (IndexedBernoulliMoments.budget r q K p/L)^q≤
      (IndexedBernoulliMoments.budget r q K' p/L)^q := by
  apply pow_le_pow_left₀
  · exact div_nonneg (IndexedBernoulliMoments.budget_nonneg r q K hp) hL
  · exact div_le_div_of_nonneg_right (budget_mono r q K K' p hp hK) hL

lemma hitCaps_mono (n n' s M : ℕ) (hn : n≤n') (k : ℕ) :
    BernoulliHitCounts.overlapCaps n s M k≤BernoulliHitCounts.overlapCaps n' s M k := by
  rcases k with _ | (_ | k)
  · exact Nat.mul_le_mul_right _ hn
  · exact le_rfl
  · exact le_rfl

def hitError (n s M q : ℕ) (p η L : ℝ) : ℝ :=
  Real.exp (-η^2*L/(2*M))+
    (IndexedBernoulliMoments.budget 2 q (BernoulliHitCounts.overlapCaps n s M) p/L)^q

def retention (j D C : ℕ) (p η : ℝ) : ℝ :=
  1-(1-η)*p*((((j-1)*D:ℕ):ℝ)-((j-1+(j-1).choose 2*C:ℕ):ℝ))

def oldIncidence (j D P C : ℕ) : ℕ := if j=2 then C else D*P

lemma incident_subset (H : Finset (Finset α)) (j : ℕ) (x : α) : incidentLayer H j x⊆H :=
  fun _ he => (mem_filter.mp (mem_filter.mp he).1).1

lemma incident_mem (H : Finset (Finset α)) (j : ℕ) (x : α) : ∀ e∈incidentLayer H j x, x∈e :=
  fun _ he => (mem_filter.mp he).2

lemma incident_card (H : Finset (Finset α)) (j : ℕ) (x : α) : ∀ e∈incidentLayer H j x, e.card=j :=
  fun _ he => (mem_filter.mp (mem_filter.mp he).1).2

/-- Survival of old rank-j incident edges, with the sharper graph incidence
C for j=2 and D*P for j=3,4. The exponential term is uniform in the mean. -/
theorem old_degree_tail (H : Finset (Finset α)) (x : α) (j D Dj P C q : ℕ)
    (hD : ∀ z, degree (layer H 2) z=D) (hDj : degree (layer H j) x=Dj)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P)
    (hC : ∀ u v, u≠v → common H u v≤C)
    (hDP : 0<D*P) (hCpos : 0<C) (p η L : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) (hη1 : η≤1) (hL : 0<L) :
    prob p (fun R => (Dj:ℝ)*retention j D C p η+L≤
      (GreedyBatchDegreeStep.oldCount H R j x:ℝ))≤
      hitError Dj ((j-1)*D) (oldIncidence j D P C) q p η L := by
  let T := incidentLayer H j x
  let M := oldIncidence j D P C
  let μ : ℝ := p*∑ e∈T, ((kills H x e).card:ℝ)
  have hn : T.card=Dj := hDj
  have hd (z : α) : (neighbors H z).card=D := (neighbors_card H z).trans (hD z)
  have hMpos : 0<M := by dsimp [M,oldIncidence]; split_ifs <;> assumption
  have hM (a : α) : (T.filter (fun e => a∈kills H x e)).card≤M := by
    dsimp [M,oldIncidence]
    split_ifs with hj
    · subst j
      exact kills_two_incidence H T (incident_subset H 2 x) x (incident_mem H 2 x)
        (incident_card H 2 x) C (hC x) a
    · exact kills_incidence H T (incident_subset H j x) x (incident_mem H j x) D P
        (fun z => (hd z).le) hP a
  have ht := GreedyBatchGraphLoss.old_survival_tail H T x j D M q (incident_mem H j x)
    (incident_card H j x) (fun z => (hd z).le) hM hMpos p η L hp hp1 hη hL
  change prob p (fun R => (T.card:ℝ)-(1-η)*μ+L≤
    (GreedyBatchDegreeStep.oldCount H R j x:ℝ))≤_ at ht
  have hμ : 0≤μ := by dsimp [μ]; positivity
  have he := capped_exponential_tail p (fun R => (GreedyBatchDegreeStep.oldCount H R j x:ℝ))
    T.card μ η L M
    ((IndexedBernoulliMoments.budget 2 q (BernoulliHitCounts.overlapCaps T.card ((j-1)*D) M) p/L)^q)
    (by
      intro R
      change ((T.filter (fun e => e⊆GreedyBatchState.carrier H R)).card:ℝ)≤T.card
      exact_mod_cast card_filter_le T (fun e => e⊆GreedyBatchState.carrier H R))
    hμ hη (by exact_mod_cast hMpos)
    (pow_nonneg (div_nonneg (IndexedBernoulliMoments.budget_nonneg _ _ _ hp) hL.le) _) ht
  have hm := GreedyBatchGraphLoss.kill_mean_lower H T x j D C (incident_mem H j x)
    (incident_card H j x) (fun z => (hd z).ge) hC p hp
  change p*T.card*((j-1)*D:ℕ)≤μ+p*T.card*((j-1)+(j-1).choose 2*C:ℕ) at hm
  have hm' : p*Dj*((((j-1)*D:ℕ):ℝ)-((j-1+(j-1).choose 2*C:ℕ):ℝ))≤μ := by
    rw [hn] at hm
    nlinarith only [hm]
  have hthr : (T.card:ℝ)-(1-η)*μ+L≤(Dj:ℝ)*retention j D C p η+L := by
    have hh := mul_le_mul_of_nonneg_left hm' (sub_nonneg.mpr hη1)
    rw [hn]
    dsimp [retention]
    nlinarith only [hh]
  apply (mono p hp hp1 _ _ (fun R h => hthr.trans h)).trans
  simpa only [hn,M,hitError] using he

/-- Uniform old shared-link tail. Nonnegative retention permits replacing
the actual family size by the scalar cap B. -/
theorem old_shared_tail (H : Finset (Finset α)) (x y : α) (D P C B q : ℕ)
    (hD : ∀ z, degree (layer H 2) z=D)
    (hP : ∀ a, x≠a → pairDegree H x a≤P)
    (hC : ∀ u v, u≠v → common H u v≤C)
    (hB : RegularizationSharedLinks.count H x y≤B) (hDP : 0<D*P)
    (p η L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hη : 0≤η) (hη1 : η≤1) (hL : 0<L)
    (hr : 0≤retention 3 D C p η) :
    prob p (fun R => (B:ℝ)*retention 3 D C p η+L≤
      (GreedyBatchSharedLoss.oldCount H x y R:ℝ))≤
      hitError B (2*D) (D*P) q p η L := by
  let n := RegularizationSharedLinks.count H x y
  let μ : ℝ := p*∑ A∈RegularizationSharedLinks.links H x y, ((kills H x A).card:ℝ)
  have hd (z : α) : (neighbors H z).card=D := (neighbors_card H z).trans (hD z)
  have ht := GreedyBatchSharedLoss.old_survival_tail H x y D P q
    (fun z => (hd z).le) hP hDP p η L hp hp1 hη hL
  change prob p (fun R => (n:ℝ)-(1-η)*μ+L≤(GreedyBatchSharedLoss.oldCount H x y R:ℝ))≤_ at ht
  have hμ : 0≤μ := by dsimp [μ]; positivity
  have he := capped_exponential_tail p (fun R => (GreedyBatchSharedLoss.oldCount H x y R:ℝ))
    n μ η L (D*P:ℕ)
    ((IndexedBernoulliMoments.budget 2 q (BernoulliHitCounts.overlapCaps n (2*D) (D*P)) p/L)^q)
    (by
      intro R
      change (((RegularizationSharedLinks.links H x y).filter
        (fun A => A⊆GreedyBatchState.carrier H R)).card:ℝ)≤(RegularizationSharedLinks.links H x y).card
      exact_mod_cast card_filter_le (RegularizationSharedLinks.links H x y)
        (fun A => A⊆GreedyBatchState.carrier H R))
    hμ hη (by exact_mod_cast hDP)
    (pow_nonneg (div_nonneg (IndexedBernoulliMoments.budget_nonneg _ _ _ hp) hL.le) _) ht
  have hm := GreedyBatchSharedLoss.kill_mean_lower H x y D C (fun z => (hd z).ge) hC p hp
  change p*n*(2*D:ℕ)≤μ+p*n*(2+C:ℕ) at hm
  have hthr : (n:ℝ)-(1-η)*μ+L≤(B:ℝ)*retention 3 D C p η+L := by
    have hm' : p*n*((2*D:ℕ)-(2+C:ℕ):ℝ)≤μ := by nlinarith only [hm]
    have hh := mul_le_mul_of_nonneg_left hm' (sub_nonneg.mpr hη1)
    have hb := mul_le_mul_of_nonneg_right (show (n:ℝ)≤B by exact_mod_cast hB) hr
    norm_num [retention] at hb ⊢
    push_cast at hh
    nlinarith only [hh,hb]
  apply (mono p hp hp1 _ _ (fun R h => hthr.trans h)).trans
  apply he.trans
  apply add_le_add le_rfl
  exact moment_mono 2 q _ _ p L hp hL.le (hitCaps_mono n B (2*D) (D*P) hB)

def promotionError (r k Dr P q : ℕ) (p L : ℝ) : ℝ :=
  (IndexedBernoulliMoments.budget k q
    (GreedyBatchPromotions.overlapCaps (Dr*(r-1).choose k) P) p/L)^q

lemma promotion_tail (H : Finset (Finset α)) (x : α) (r k Dr P q : ℕ) (hr : r≤4)
    (hDr : degree (layer H r) x≤Dr) (hP : ∀ a, x≠a → pairDegree H x a≤P)
    (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    prob p (fun R => L≤(GreedyBatchPromotions.cost H x r k R:ℝ))≤promotionError r k Dr P q p L := by
  apply (GreedyBatchPromotions.cost_tail H x r k P q hr hP p L hp hp1 hL).trans
  apply moment_mono k q _ _ p L hp hL.le
  intro i
  unfold GreedyBatchPromotions.overlapCaps
  split_ifs
  · exact Nat.mul_le_mul_right _ hDr
  · exact le_rfl

def sharedError (r s Dr P q : ℕ) (p L : ℝ) : ℝ :=
  (IndexedBernoulliMoments.budget ((r-3)+(s-3)) q
    (GreedyBatchSharedWitnesses.overlapCaps (Dr*(r-1).choose 2*P) P) p/L)^q

lemma shared_creation_tail (H : Finset (Finset α)) (x y : α) (r s Dr P q : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4) (hDr : degree (layer H r) x≤Dr)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    prob p (fun R => L≤(GreedyBatchSharedWitnesses.cost H x y r s R:ℝ))≤sharedError r s Dr P q p L := by
  apply (GreedyBatchSharedWitnesses.cost_tail H x y r s P q hr hs hP hI p L hp hp1 hL).trans
  apply moment_mono _ q _ _ p L hp hL.le
  intro i
  unfold GreedyBatchSharedWitnesses.overlapCaps
  split_ifs
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hDr)
  · exact le_rfl

end
end Erdos773.GreedyBatchScalarTails
end EndpointModule024
-- End GreedyBatchScalarTails.lean

-- Begin GreedyBatchMomentBounds.lean
section EndpointModule025

/- Elementary scalar bounds for the explicit indexed moment budgets. -/
namespace Erdos773.GreedyBatchMomentBounds
open Finset IndexedBernoulliMoments GreedyBatchScalarTails
set_option maxHeartbeats 2500000
noncomputable section

/-- Separate the leading mean from an overlap error. The cap M applies only
to positive overlaps, not to the rank-zero family mass. -/
theorem budget_uniform (r q n M : ℕ) (K : ℕ → ℕ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (h0 : K 0≤n) (hK : ∀ k, 1≤k → k≤r → K k≤M) :
    budget r q K p≤(n:ℝ)*p^r+(r:ℝ)*M*((r*q+1:ℕ):ℝ)^r := by
  rw [budget,sum_range_succ']
  have hfirst : ((r*q).choose 0:ℝ)*K 0*p^(r-0)≤(n:ℝ)*p^r := by
    simpa only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero] using
      mul_le_mul_of_nonneg_right (show (K 0:ℝ)≤n by exact_mod_cast h0) (pow_nonneg hp r)
  have hrow (k : ℕ) (hk : k∈range r) :
      ((r*q).choose (k+1):ℝ)*K (k+1)*p^(r-(k+1))≤(M:ℝ)*((r*q+1:ℕ):ℝ)^r := by
    have hkr : k+1≤r := by have := mem_range.mp hk; omega
    have hchoose : (r*q).choose (k+1)≤(r*q+1)^r :=
      ((Nat.choose_le_pow (r*q) (k+1)).trans (Nat.pow_le_pow_left (by omega : r*q≤r*q+1) _)).trans
        (Nat.pow_le_pow_right (by omega : 0<r*q+1) hkr)
    have hc : ((r*q).choose (k+1):ℝ)≤((r*q+1:ℕ):ℝ)^r := by exact_mod_cast hchoose
    have hcap : (K (k+1):ℝ)≤M := by exact_mod_cast hK (k+1) (by omega) hkr
    have hm := mul_le_mul hc hcap (Nat.cast_nonneg _) (by positivity)
    have hpow : p^(r-(k+1))≤1 := pow_le_one₀ hp hp1
    calc
      _ ≤ ((r*q).choose (k+1):ℝ)*K (k+1) := by
        exact mul_le_of_le_one_right (by positivity) hpow
      _ ≤ _ := by nlinarith only [hm]
  have hs := sum_le_sum hrow
  simp only [sum_const,card_range,nsmul_eq_mul] at hs
  linarith only [hfirst,hs]

/-- The old-hit correction retains its p factor in the one-overlap term;
dropping it would be too expensive at large mixed degrees. -/
theorem hit_budget (n s M q : ℕ) (p : ℝ) (hp : 0≤p) :
    budget 2 q (BernoulliHitCounts.overlapCaps n s M) p≤
      (n:ℝ)*s^2*p^2/2+2*q*s*M*p+2*(q:ℝ)^2*M := by
  have hs : (s.choose 2:ℝ)≤(s:ℝ)^2/2 := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) 2 s)
  have hq : ((2*q).choose 2:ℝ)≤2*(q:ℝ)^2 := by
    have hh := Nat.choose_le_pow_div (α := ℝ) 2 (2*q)
    norm_num at hh
    push_cast at hh
    nlinarith only [hh]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) (sq_nonneg p)
  have h2 := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg M)
  norm_num [budget,sum_range_succ,BernoulliHitCounts.overlapCaps]
  nlinarith only [h1,h2]

/-- A near-mean budget bound yields an exponential moment tail. -/
theorem moment_exponential (r q : ℕ) (K : ℕ → ℕ) (p L u : ℝ)
    (hp : 0≤p) (hL : 0<L) (hu : 0≤u) (hu1 : u≤1)
    (hbudget : budget r q K p≤(1-u)*L) :
    (budget r q K p/L)^q≤Real.exp (-(q:ℝ)*u) := by
  have hb : budget r q K p/L≤1-u := (div_le_iff₀ hL).mpr hbudget
  have he : 1-u≤Real.exp (-u) := by simpa only [neg_add_eq_sub,add_comm] using Real.add_one_le_exp (-u)
  have hpw := pow_le_pow_left₀ (div_nonneg (budget_nonneg r q K hp) hL.le) (hb.trans he) q
  simpa only [← Real.exp_nat_mul,mul_neg,neg_mul] using hpw

/-- Matching exponential and moment errors for old-hit survival. -/
theorem hit_exponential (n s M q : ℕ) (p η L u : ℝ)
    (hp : 0≤p) (hL : 0<L) (hu : 0≤u) (hu1 : u≤1)
    (hexp : (q:ℝ)*u≤η^2*L/(2*M))
    (hbudget : budget 2 q (BernoulliHitCounts.overlapCaps n s M) p≤(1-u)*L) :
    hitError n s M q p η L≤2*Real.exp (-(q:ℝ)*u) := by
  have h1 : Real.exp (-η^2*L/(2*M))≤Real.exp (-(q:ℝ)*u) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hexp using 1 <;> ring
  have h2 := moment_exponential 2 q _ p L u hp hL hu hu1 hbudget
  dsimp [hitError]
  linarith only [h1,h2]

/-- The proposed moment order m^10 resolves relative errors of order m^-2
with an exp(-m^7) bound, uniformly for m>=20. -/
lemma shrinking_scale (m : ℕ) (hm : 20≤ m) :
    Real.exp (-((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2)))≤Real.exp (-(m:ℝ)^7) := by
  have hmR : (20:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hmne : (m:ℝ)≠0 := ne_of_gt hm0
  have he : ((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))=(m:ℝ)^8/20 := by
    push_cast
    field_simp
  rw [show -((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))= -(((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))) by ring,he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hmR (pow_nonneg hm0.le 7)
  nlinarith only [hh]

end
end Erdos773.GreedyBatchMomentBounds
end EndpointModule025
-- End GreedyBatchMomentBounds.lean

-- Begin GreedyBatchScaleTails.lean
section EndpointModule026

/- Uniform shrinking-batch moment bounds under coarse scalar scale
conditions. These conditions do not yet assert any degree trajectory. -/
namespace Erdos773.GreedyBatchScaleTails
open IndexedBernoulliMoments GreedyBatchScalarTails GreedyBatchMomentBounds
set_option maxHeartbeats 3000000
noncomputable section

def u (m : ℕ) : ℝ := 1/(20*(m:ℝ)^2)
def failure (m : ℕ) : ℝ := 2*Real.exp (-(m:ℝ)^7)

lemma u_nonneg (m : ℕ) : 0≤u m := by unfold u; positivity
lemma u_le_quarter (m : ℕ) (hm : 1≤ m) : u m≤1/4 := by
  have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
  have hm2 : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hmR
  unfold u
  apply (div_le_iff₀ (by positivity : (0:ℝ)<20*(m:ℝ)^2)).mpr
  nlinarith only [hm2]

/-- A rank-at-most-four overlap error is negligible at the proposed scale. -/
lemma overlap_error (m r M : ℕ) (hm : 100≤ m) (hr : r≤4) (hM : M≤8*m^2) :
    r*M*(r*m^10+1)^r≤ m^46 := by
  have hm1 : 1≤ m := by omega
  have hm10 : 1≤ m^10 := one_le_pow₀ hm1
  have hh := Nat.mul_le_mul_right (m^10) hr
  have hb : r*m^10+1≤5*m^10 := by omega
  have hp : 0<5*m^10 := by omega
  have hbig : 20000≤ m^4 := by
    have hh := Nat.pow_le_pow_left hm 4
    norm_num at hh
    omega
  calc
    _ ≤ 4*(8*m^2)*(5*m^10)^4 := Nat.mul_le_mul (Nat.mul_le_mul hr hM)
      ((Nat.pow_le_pow_left hb r).trans (Nat.pow_le_pow_right hp hr))
    _ = 20000*m^42 := by ring
    _ ≤ m^4*m^42 := Nat.mul_le_mul_right _ hbig
    _ = _ := by ring

lemma budget_scale (m r q n : ℕ) (K : ℕ → ℕ) (p : ℝ)
    (hm : 100≤ m) (hr : r≤4) (hq : q=m^10)
    (hp : 0≤p) (hp1 : p≤1) (h0 : K 0≤n)
    (hK : ∀ k, 1≤k → k≤r → K k≤8*m^2) :
    budget r q K p≤(n:ℝ)*p^r+(m:ℝ)^46 := by
  subst q
  have hh := budget_uniform r (m^10) n (8*m^2) K p hp hp1 h0 hK
  have he : (r:ℝ)*(8*m^2:ℕ)*((r*m^10+1:ℕ):ℝ)^r≤(m:ℝ)^46 := by
    exact_mod_cast overlap_error m r (8*m^2) hm hr le_rfl
  linarith only [hh,he]

/-- A margin S/m^4 absorbs the overlap error without multiplying the leading
mean by a fixed constant. -/
lemma near_mean_margin (m : ℕ) (S μ : ℝ) (hm : 100≤ m) (hS : (m:ℝ)^52≤S)
    (hμ : μ≤10*S/(m:ℝ)^2) :
    μ+(m:ℝ)^46≤(1-u m)*(μ+S/(m:ℝ)^4) := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hS0 : 0≤S := (pow_nonneg hm0.le 52).trans hS
  have hm2 : (4:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hE : (m:ℝ)^46≤S/(4*(m:ℝ)^4) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(m:ℝ)^4)).mpr
    have hh := mul_le_mul_of_nonneg_right hm2 (pow_nonneg hm0.le 50)
    nlinarith only [hh,hS]
  have h42 : (m:ℝ)^2≤(m:ℝ)^4 := pow_le_pow_right₀ hm1 (by decide)
  have hmargin : S/(m:ℝ)^4≤S/(m:ℝ)^2 :=
    div_le_div_of_nonneg_left hS0 (by positivity) h42
  have hL : μ+S/(m:ℝ)^4≤11*S/(m:ℝ)^2 := by
    ring_nf at hμ hmargin ⊢
    linarith only [hμ,hmargin]
  have huL : u m*(μ+S/(m:ℝ)^4)≤11*S/(20*(m:ℝ)^4) := by
    calc
      _ ≤ u m*(11*S/(m:ℝ)^2) := mul_le_mul_of_nonneg_left hL (u_nonneg m)
      _ = _ := by unfold u; field_simp
  have hmarg : 0≤S/(m:ℝ)^4 := div_nonneg hS0 (pow_nonneg hm0.le 4)
  have hE' : (m:ℝ)^46≤(1/4)*(S/(m:ℝ)^4) := by convert hE using 1 <;> ring
  have hU' : u m*(μ+S/(m:ℝ)^4)≤(11/20)*(S/(m:ℝ)^4) := by convert huL using 1 <;> ring
  nlinarith only [hE',hU',hmarg]

lemma loose_margin (m : ℕ) (μ L : ℝ) (hm : 1≤ m) (hL : 0≤L)
    (hμ : μ≤L/4) (hE : (m:ℝ)^46≤L/4) :
    μ+(m:ℝ)^46≤(1-u m)*L := by
  have hh := mul_le_mul_of_nonneg_right (u_le_quarter m hm) hL
  nlinarith only [hμ,hE,hh,hL]

lemma scaled_moment (m r n : ℕ) (K : ℕ → ℕ) (p L : ℝ)
    (hm : 100≤ m) (hr : r≤4) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L)
    (h0 : K 0≤n) (hK : ∀ k, 1≤k → k≤r → K k≤8*m^2)
    (hmargin : (n:ℝ)*p^r+(m:ℝ)^46≤(1-u m)*L) :
    (budget r (m^10) K p/L)^(m^10)≤Real.exp (-(m:ℝ)^7) := by
  have ht := moment_exponential r (m^10) K p L (u m) hp hL (u_nonneg m)
    ((u_le_quarter m (by omega)).trans (by norm_num))
    ((budget_scale m r (m^10) n K p hm hr rfl hp hp1 h0 hK).trans hmargin)
  exact ht.trans (shrinking_scale m (by omega))

/-- Four old-survival tests share this one scalar calculation. The family
mass n is allowed to be a cap rather than an attained cardinality. -/
theorem old_scaled (m n s D M : ℕ) (p : ℝ) (hm : 100≤ m) (hM : 0<M)
    (hn : m^30*M≤n) (hs : s≤3*D) (hp : 0≤p) (hDp : (D:ℝ)*p≤4/(m:ℝ)^2) :
    hitError n s M (m^10) p (1/(m:ℝ)^2) (100*n/(m:ℝ)^4)≤failure m := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hnR : (m:ℝ)^30*M≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := (mul_pos (pow_pos hm0 30) hMr).trans_le hnR
  have hL : 0<100*(n:ℝ)/(m:ℝ)^4 := by positivity
  have hsp : (s:ℝ)*p≤12/(m:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right (show (s:ℝ)≤3*D by exact_mod_cast hs) hp
    ring_nf at hh hDp ⊢
    nlinarith only [hh,hDp]
  have hterm1 : (n:ℝ)*s^2*p^2/2≤72*n/(m:ℝ)^4 := by
    have h0 : (0:ℝ)≤(s:ℝ)*p := by positivity
    have hh := pow_le_pow_left₀ h0 hsp 2
    have he : (12/(m:ℝ)^2)^2=144/(m:ℝ)^4 := by ring
    rw [he] at hh
    have hm := mul_le_mul_of_nonneg_left hh hn0.le
    ring_nf at hm ⊢
    linarith only [hm]
  have hterm2 : 2*((m^10:ℕ):ℝ)*s*M*p≤24*(m:ℝ)^8*M := by
    have hh := mul_le_mul_of_nonneg_left hsp (show (0:ℝ)≤2*(m:ℝ)^10*M by positivity)
    have he : 2*(m:ℝ)^10*M*(12/(m:ℝ)^2)=24*(m:ℝ)^8*M := by field_simp; norm_num
    rw [he] at hh
    push_cast
    nlinarith only [hh]
  have hp820 : (m:ℝ)^8≤(m:ℝ)^20 := pow_le_pow_right₀ hm1 (by decide)
  have htwos : 2*((m^10:ℕ):ℝ)*s*M*p+2*(((m^10:ℕ):ℝ))^2*M≤26*(m:ℝ)^20*M := by
    have hh := mul_le_mul_of_nonneg_right hp820 hMr.le
    push_cast at hterm2 ⊢
    nlinarith only [hterm2,hh]
  have hsmall : 26*(m:ℝ)^20*M≤(n:ℝ)/(m:ℝ)^4 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)^4)).mpr
    have hm6 : (26:ℝ)≤(m:ℝ)^6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤100) hmR 6
      norm_num at hh
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hm6 (show (0:ℝ)≤(m:ℝ)^24*M by positivity)
    nlinarith only [hh,hnR]
  have hbudget : budget 2 (m^10) (BernoulliHitCounts.overlapCaps n s M) p≤
      (1-u m)*(100*n/(m:ℝ)^4) := by
    have hh := hit_budget n s M (m^10) p hp
    have hu := mul_le_mul_of_nonneg_right (u_le_quarter m (by omega)) hL.le
    ring_nf at hh hterm1 htwos hsmall hu hL ⊢
    nlinarith only [hh,hterm1,htwos,hsmall,hu,hL]
  have hexp : ((m^10:ℕ):ℝ)*u m≤(1/(m:ℝ)^2)^2*(100*n/(m:ℝ)^4)/(2*M) := by
    have hpow : (m:ℝ)^16≤(m:ℝ)^30 := pow_le_pow_right₀ hm1 (by decide)
    have hh := mul_le_mul_of_nonneg_right hpow hMr.le
    have hbound : M*(m:ℝ)^16≤1000*(n:ℝ) := by nlinarith only [hh,hnR,hn0]
    have heL : ((m^10:ℕ):ℝ)*u m=(m:ℝ)^8/20 := by
      unfold u
      push_cast
      field_simp
    have heR : (1/(m:ℝ)^2)^2*(100*n/(m:ℝ)^4)/(2*M)=50*n/(M*(m:ℝ)^8) := by
      field_simp
      ring
    rw [heL,heR]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<M*(m:ℝ)^8)).mpr
    nlinarith only [hbound]
  have ht := hit_exponential n s M (m^10) p (1/(m:ℝ)^2) (100*n/(m:ℝ)^4) (u m)
    hp hL (u_nonneg m) ((u_le_quarter m (by omega)).trans (by norm_num)) hexp hbudget
  exact ht.trans (mul_le_mul_of_nonneg_left (shrinking_scale m (by omega)) (by norm_num))

end
end Erdos773.GreedyBatchScaleTails
end EndpointModule026
-- End GreedyBatchScaleTails.lean

-- Begin GreedyBatchSharedStep.lean
section EndpointModule027

/- Actual shared-link update for the conservative mixed batch. Every new
link is charged to the correct one- or two-mark original-edge witness. -/
namespace Erdos773.GreedyBatchSharedStep
open Finset GreedyBatchState RegularizationSharedLinks GreedyBatchSharedWitnesses
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma data_of_residuals {H : Finset (Finset α)} {R A e f : Finset α} {x y : α}
    (hxy : x≠y) (hA : A.card=2) (hxA : x∉A) (hyA : y∉A)
    (hxR : x∉R) (hyR : y∉R) (he : e∈H) (hf : f∈H)
    (heq : e \ R=insert x A) (hfq : f \ R=insert y A) :
    Data H x y e.card f.card e A f ∧ witness x y (⟨e,A,f⟩:Index α)⊆R := by
  have hxe : x∈e := (mem_sdiff.mp (heq.symm ▸ mem_insert_self x A)).1
  have hyf : y∈f := (mem_sdiff.mp (hfq.symm ▸ mem_insert_self y A)).1
  have hye : y∉e := by
    intro hy
    have hh : y∈insert x A := heq ▸ mem_sdiff.mpr ⟨hy,hyR⟩
    exact (mem_insert.mp hh).elim hxy.symm hyA
  have hxf : x∉f := by
    intro hx
    have hh : x∈insert y A := hfq ▸ mem_sdiff.mpr ⟨hx,hxR⟩
    exact (mem_insert.mp hh).elim hxy hxA
  have hAe : A⊆e := fun a ha => (mem_sdiff.mp (heq.symm ▸ mem_insert_of_mem ha)).1
  have hAf : A⊆f := fun a ha => (mem_sdiff.mp (hfq.symm ▸ mem_insert_of_mem ha)).1
  refine ⟨⟨he,hf,rfl,rfl,hxe,hyf,hye,hxf,hA,hAe,hAf,hxA,hyA⟩,?_⟩
  intro a ha
  by_contra haR
  rcases mem_union.mp ha with ha | ha
  · exact (mem_sdiff.mp ha).2 (heq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)
  · exact (mem_sdiff.mp ha).2 (hfq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)

lemma next_link_sources (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y)
    (A : Finset α) (hA : A∈links (next H R) x y) :
    ∃ e f, (3≤e.card ∧ e.card≤4) ∧ (3≤f.card ∧ f.card≤4) ∧
      Data H x y e.card f.card e A f ∧
      witness x y (⟨e,A,f⟩:Index α)⊆R ∧ A⊆carrier H R := by
  obtain ⟨hAc,hxA,hyA,hx,hy⟩ := mem_links.mp hA
  have hxQ := next_subset hx (mem_insert_self _ _)
  have hyQ := next_subset hy (mem_insert_self _ _)
  have hAQ : A⊆carrier H R := (subset_insert _ _).trans (next_subset hx)
  obtain ⟨e,he,heq⟩ := mem_image.mp hx
  obtain ⟨f,hf,hfq⟩ := mem_image.mp hy
  have heH := (mem_filter.mp he).1
  have hfH := (mem_filter.mp hf).1
  have he3 : 3≤e.card := by
    have hh := card_le_card (sdiff_subset : e \ R⊆e)
    rw [heq,card_insert_of_notMem hxA,hAc] at hh
    exact hh
  have hf3 : 3≤f.card := by
    have hh := card_le_card (sdiff_subset : f \ R⊆f)
    rw [hfq,card_insert_of_notMem hyA,hAc] at hh
    exact hh
  obtain ⟨hd,hw⟩ := data_of_residuals hxy hAc hxA hyA
    (mem_carrier.mp hxQ).1 (mem_carrier.mp hyQ).1 heH hfH heq hfq
  exact ⟨e,f,⟨he3,hH e heH⟩,⟨hf3,hH f hfH⟩,hd,hw,hAQ⟩

def created (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) : Finset (Finset α) :=
  ((family H x y r s).filter (fun i => witness x y i⊆R)).image (fun i => i.2.1)

lemma created_card (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    (created H x y r s R).card≤cost H x y r s R := card_image_le

lemma old_of_three {H : Finset (Finset α)} {x y : α} {e A f : Finset α}
    (h : Data H x y 3 3 e A f) : A∈links H x y := by
  have he : insert x A=e := eq_of_subset_of_card_le (insert_subset h.x_mem h.A_e)
    (by rw [card_insert_of_notMem h.x_A,h.A_card,h.e_card])
  have hf : insert y A=f := eq_of_subset_of_card_le (insert_subset h.y_mem h.A_f)
    (by rw [card_insert_of_notMem h.y_A,h.A_card,h.f_card])
  exact mem_links.mpr ⟨h.A_card,h.x_A,h.y_A,he.symm ▸ h.e_mem,hf.symm ▸ h.f_mem⟩

lemma next_link_cover (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    links (next H R) x y⊆
      (((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)∪created H x y 4 3 R)∪
        created H x y 4 4 R := by
  intro A hA
  obtain ⟨e,f,he,hf,hd,hw,hAQ⟩ := next_link_sources H R hH x y hxy A hA
  have her : e.card=3 ∨ e.card=4 := by omega
  have hfr : f.card=3 ∨ f.card=4 := by omega
  rcases her with her | her <;> rcases hfr with hfr | hfr
  · have hd' : Data H x y 3 3 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨old_of_three hd',hAQ⟩)))
  · have hd' : Data H x y 3 4 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩)))
  · have hd' : Data H x y 4 3 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_right _
      (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩))
  · have hd' : Data H x y 4 4 e A f := by simpa only [her,hfr] using hd
    exact mem_union_right _ (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩)

/-- Full shared-link update: an old-link survivor term, two one-mark
creation terms, and one two-mark creation term. -/
theorem shared_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    count (next H R) x y≤GreedyBatchSharedLoss.oldCount H x y R+
      cost H x y 3 4 R+cost H y x 3 4 R+cost H x y 4 4 R := by
  have h0 := card_le_card (next_link_cover H R hH x y hxy)
  have h1 := card_union_le
    (((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)∪created H x y 4 3 R)
    (created H x y 4 4 R)
  have h2 := card_union_le
    ((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)
    (created H x y 4 3 R)
  have h3 := card_union_le ((links H x y).filter (fun A => A⊆carrier H R)) (created H x y 3 4 R)
  have hc1 := created_card H x y 3 4 R
  have hc2 := created_card H x y 4 3 R
  have hc3 := created_card H x y 4 4 R
  rw [cost_swap H x y 4 3 R] at hc2
  unfold count GreedyBatchSharedLoss.oldCount
  omega

end
end Erdos773.GreedyBatchSharedStep
end EndpointModule027
-- End GreedyBatchSharedStep.lean

-- Begin GreedyWeightedDissipation.lean
section EndpointModule028

/-
Symmetric nonnegative pair weights give a dissipative signless operator.
The result applies to arbitrary odd monotone test functions, not just
quadratic energy, and requires no graph expansion hypothesis.
-/
namespace Erdos773.GreedyWeightedDissipation
open Finset
set_option maxHeartbeats 1000000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.GreedyWeightedDissipation
end EndpointModule028
-- End GreedyWeightedDissipation.lean

-- Begin GreedyPowerYoung.lean
section EndpointModule029

/-
Natural-power Young inequalities for symmetric neighbor operators. The
exponent can be any fixed natural number, which avoids relying solely on
a global quadratic moment when controlling many local degree records.
-/
namespace Erdos773.GreedyPowerYoung
open Finset
set_option maxHeartbeats 2500000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.GreedyPowerYoung
end EndpointModule029
-- End GreedyPowerYoung.lean

-- Begin GreedyTargetHazard.lean
section EndpointModule030

/-
A finite survival-aware target potential. Selection probabilities are charged
only while every remaining target is available. The one-step certificate uses
closure hazards and their pairwise overlaps, not a uniform lower bound on the
number of available vertices over the whole run.
-/
namespace Erdos773.GreedyTargetHazard
open Finset GreedyHypergraphState GreedyLinearDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyTargetHazard
end EndpointModule030
-- End GreedyTargetHazard.lean

-- Begin FiniteKernelCrossing.lean
section EndpointModule031

/-
Finite time-inhomogeneous transition kernels, first-crossing probabilities,
and a nonnegative supermartingale crossing bound. No independence of
successive choices is assumed.
-/
namespace Erdos773.FiniteKernelCrossing
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {σ : Type*} [Fintype σ]

-- Unused development declaration omitted.

namespace Kernel

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Kernel

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.FiniteKernelCrossing
end EndpointModule031
-- End FiniteKernelCrossing.lean

-- Begin FiniteKilledKernel.lean
section EndpointModule032

/-
Killing a finite kernel AFTER its guard fails. A transition from a good state
still visits its actual destination, including a first bad state or an
overshoot. Only the following transition goes to the cemetery. This makes
first-guard-crossing probabilities invariant under killing.
-/
namespace Erdos773.FiniteKilledKernel
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ : Type*} [Fintype σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.FiniteKilledKernel
end EndpointModule032
-- End FiniteKilledKernel.lean

-- Begin FiniteKernelChoices.lean
section EndpointModule033

/- Kernels obtained from uniform finite choices, with noninjective next-state
maps permitted. Repeated next states have their correct multiplicity. -/
namespace Erdos773.FiniteKernelChoices
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2000000
noncomputable section
variable {σ β : Type*} [Fintype σ] [DecidableEq σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.FiniteKernelChoices
end EndpointModule033
-- End FiniteKernelChoices.lean

-- Begin GreedyFiniteKernel.lean
section EndpointModule034

/-
The stopped greedy average as a genuine finite kernel. A lifting interface
permits finite auxiliary memory without silently altering the selected-set
process. No tracked-memory implementation or long-running-time bound is
asserted in this file.
-/
namespace Erdos773.GreedyFiniteKernel
open Finset GreedyHypergraphState StoppedGreedyMoments FiniteKernelCrossing FiniteKernelChoices
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

section Lift
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Lift
end
end Erdos773.GreedyFiniteKernel
end EndpointModule034
-- End GreedyFiniteKernel.lean

-- Begin GreedySurvivalTargets.lean
section EndpointModule035

/-
First-hitting bounds for specified selected targets, up to the first failed
guard and including the failure state itself. The finite-memory kernel may
be arbitrary provided its guarded carrier projection is the actual uniform
greedy step. Numerical hazard and availability profiles remain hypotheses.
-/
namespace Erdos773.GreedySurvivalTargets
open Finset GreedyHypergraphState GreedyTargetHazard
open FiniteKernelCrossing FiniteKilledKernel
set_option maxHeartbeats 2500000
noncomputable section
variable {α σ : Type*} [Fintype α] [DecidableEq α] [Fintype σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedySurvivalTargets
end EndpointModule035
-- End GreedySurvivalTargets.lean

-- Begin FiniteWitnessCrossing.lean
section EndpointModule036

/-
Configuration and witness bounds for finite first-hitting probabilities.
Only specified-target hitting bounds are assumed, so these lemmas apply to
guarded survival kernels without claiming an unrestricted inclusion law.
-/
namespace Erdos773.FiniteWitnessCrossing
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ α β : Type*} [Fintype σ] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.FiniteWitnessCrossing
end EndpointModule036
-- End FiniteWitnessCrossing.lean

-- Begin GreedySurvivalWitnesses.lean
section EndpointModule037

/-
Witness packing with a capped survival-aware target law. All events are
first crossings in the lifted state space. The target-size cap is explicit,
so the common-neighbor correction in the hazard profile is not forgotten
when many individual witnesses are packed together.
-/
namespace Erdos773.GreedySurvivalWitnesses
open Finset FiniteKernelCrossing FiniteKilledKernel GreedySurvivalTargets
set_option maxHeartbeats 2500000
noncomputable section
variable {α σ β : Type*} [DecidableEq α] [Fintype σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedySurvivalWitnesses
end EndpointModule037
-- End GreedySurvivalWitnesses.lean

-- Begin GreedyMixedCommonTails.lean
section EndpointModule038

/- Common-neighbor first-crossing tails for mixed hypergraphs of rank at
most four. Short-edge witnesses are charged at their actual support size;
zero-support witnesses are retained as a deterministic initial cost. -/
namespace Erdos773.GreedyMixedCommonTails
open Finset GreedyHypergraphState GreedyCommonNeighbors
open HypergraphDegreeTrim FourUniformRegularization
open FiniteKernelCrossing FiniteKilledKernel GreedySurvivalWitnesses
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Witnesses of the first role have at most 2 K² occurrences at each vertex. -/
lemma first_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1})).card ≤ 2*K^2 := by
  by_cases hau : a = u
  · subst a
    simp
  have hsub : (patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1}) ⊆
      extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) v (fun e => e \ {u,v,a}) := by
    rintro ⟨e,w,f⟩ hx
    obtain ⟨hx, ha⟩ := mem_filter.mp hx
    obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, _⟩ := mem_patterns.mp hx
    obtain ⟨ha, hna⟩ := mem_sdiff.mp ha
    have haw : a ≠ w := by intro h; exact hna (by simp [h])
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨he, hu, ha⟩,
      mem_sdiff.mpr ⟨hw, by simpa only [mem_insert, mem_singleton, not_or] using
        (And.intro hwu (And.intro hwv haw.symm))⟩, hf, hv, hwf⟩
  have hs (e : Finset α) (he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e)) :
      (e \ {u,v,a}).card ≤ 2 := by
    obtain ⟨he, hu, ha⟩ := mem_filter.mp he
    have hp : ({u,a} : Finset α) ⊆ e := by simp [insert_subset_iff, hu, ha]
    have hh : e \ {u,v,a} ⊆ e \ {u,a} := by
      intro b hb
      simp only [mem_sdiff, mem_insert, mem_singleton] at *
      tauto
    have hh := card_le_card hh
    rw [card_sdiff_of_subset hp] at hh
    have hc := h4 e he
    have hpc : ({u,a} : Finset α).card=2 := by simp [Ne.symm hau]
    rw [hpc] at hh
    omega
  have hn (e : Finset α) (_he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e))
      (w : α) (hw : w ∈ e \ {u,v,a}) : v ≠ w := by
    intro hvw
    exact (mem_sdiff.mp hw).2 (by simp [hvw])
  calc
    _ ≤ (extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) v
        (fun e => e \ {u,v,a})).card := card_le_card hsub
    _ ≤ (H.filter (fun e => u ∈ e ∧ a ∈ e)).card*2*K :=
      extensions_card_le H _ v _ 2 K hs hn hK
    _ ≤ K*2*K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right 2 (hK u a (Ne.symm hau)))
    _ = _ := by ring

lemma second_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1})).card ≤ 2*K^2 := by
  calc
    _ ≤ ((patterns H v u).filter (fun x => a ∈ x.1 \ {v,x.2.1})).card := by
      apply card_le_card_of_injOn (fun x : Pattern α => (x.2.2,x.2.1,x.1))
      · rintro ⟨e,w,f⟩ hx
        obtain ⟨hx, ha⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨pattern_swap hx, ha⟩
      · rintro ⟨e,w,f⟩ _ ⟨e',w',f'⟩ _ h
        simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using h
    _ ≤ _ := first_role_incidence h4 v u a K hK

lemma witness_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ witness u v x)).card ≤ 4*K^2 := by
  have heq : (patterns H u v).filter (fun x => a ∈ witness u v x) =
      ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1})) ∪
      ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1})) := by
    ext x
    simp only [mem_filter, witness, mem_union]
    tauto
  rw [heq]
  have hh := card_union_le
    ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1}))
    ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1}))
  have h1 := first_role_incidence h4 u v a K hK
  have h2 := second_role_incidence h4 u v a K hK
  omega

lemma witness_card_le {H : Finset (Finset α)}
    (h4 : ∀ e∈H, e.card≤4) {u v : α} {x : Pattern α} (hx : x∈patterns H u v) :
    (witness u v x).card≤4 := by
  rcases x with ⟨e,w,f⟩
  obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
  have hp : ({u,w} : Finset α)⊆e := by simp [insert_subset_iff,hu,hw]
  have hq : ({v,w} : Finset α)⊆f := by simp [insert_subset_iff,hv,hwf]
  have hc : (e \ {u,w}).card≤2 := by
    rw [card_sdiff_of_subset hp]
    simp only [card_pair hwu.symm]
    have := h4 e he
    omega
  have hd : (f \ {v,w}).card≤2 := by
    rw [card_sdiff_of_subset hq]
    simp only [card_pair hwv.symm]
    have := h4 f hf
    omega
  change ((e \ {u,w})∪(f \ {v,w})).card≤4
  exact (card_union_le _ _).trans (by omega)

def supportLayer (H : Finset (Finset α)) (u v : α) (r : ℕ) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => (witness u v x).card=r)
def selectedCost (H : Finset (Finset α)) (u v : α) (r : ℕ) (I : Finset α) : ℕ :=
  ((supportLayer H u v r).filter (fun x => witness u v x⊆I)).card

lemma layer_incidence {H : Finset (Finset α)} (h4 : ∀ e∈H, e.card≤4)
    (u v a : α) (r K : ℕ) (hK : ∀ b c : α, b≠c → pairDegree H b c≤K) :
    ((supportLayer H u v r).filter (fun x => a∈witness u v x)).card≤4*K^2 := by
  apply (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
  exact witness_incidence h4 u v a K hK

-- Unused development declaration omitted.

lemma zero_cost (H : Finset (Finset α)) (u v : α) (I : Finset α) :
    selectedCost H u v 0 I=(supportLayer H u v 0).card := by
  unfold selectedCost
  congr 1
  apply filter_true_of_mem
  intro x hx
  have hc := (mem_filter.mp hx).2
  rw [card_eq_zero.mp hc]
  exact empty_subset I

lemma cost_decomposition {H : Finset (Finset α)} (h4 : ∀ e∈H, e.card≤4)
    (u v : α) (I : Finset α) :
    patternCost H u v I = (supportLayer H u v 0).card +
      ∑ r∈Icc 1 4, selectedCost H u v r I := by
  have hh := card_eq_sum_card_fiberwise (s := (patterns H u v).filter (fun x => witness u v x⊆I))
    (t := Icc 0 4) (f := fun x => (witness u v x).card)
    (fun x hx => mem_Icc.mpr ⟨Nat.zero_le _,witness_card_le h4 (mem_filter.mp hx).1⟩)
  have he (r : ℕ) : ((patterns H u v).filter (fun x => witness u v x⊆I)).filter
      (fun x => (witness u v x).card=r) =
      (supportLayer H u v r).filter (fun x => witness u v x⊆I) := by
    ext x
    simp only [supportLayer,mem_filter]
    tauto
  simp_rw [he] at hh
  change patternCost H u v I=∑ r∈Icc 0 4, selectedCost H u v r I at hh
  have hIcc : Icc 0 4=insert 0 (Icc 1 4) := by ext r; simp only [mem_Icc,mem_insert]; omega
  rw [hIcc,sum_insert (by simp),zero_cost] at hh
  exact hh

lemma empty_witness_edges {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (hx : (e,w,f)∈patterns H u v) (h0 : (witness u v (e,w,f)).card=0) :
    e={u,w} ∧ f={v,w} := by
  obtain ⟨he,hf,hu,hv,hw,hwf,_⟩ := mem_patterns.mp hx
  have hz := card_eq_zero.mp h0
  change (e \ {u,w})∪(f \ {v,w})=∅ at hz
  obtain ⟨hz1,hz2⟩ := union_eq_empty.mp hz
  exact ⟨Subset.antisymm (sdiff_eq_empty_iff_subset.mp hz1) (by simp [insert_subset_iff,hu,hw]),
    Subset.antisymm (sdiff_eq_empty_iff_subset.mp hz2) (by simp [insert_subset_iff,hv,hwf])⟩

lemma zero_le_initial_common [Fintype α] (H : Finset (Finset α)) (u v : α) :
    (supportLayer H u v 0).card≤RegularizationCommonNeighbors.common H u v := by
  apply card_le_card_of_injOn (fun x : Pattern α => x.2.1)
  · rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,h0⟩ := mem_filter.mp hx
    obtain ⟨he,hf⟩ := empty_witness_edges hx h0
    obtain ⟨heH,hfH,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
    exact RegularizationCommonNeighbors.mem_both.mpr
      ⟨⟨hwu.symm,he ▸ heH⟩,⟨hwv.symm,hf ▸ hfH⟩⟩
  · rintro ⟨e,w,f⟩ hx ⟨e',w',f'⟩ hy heq
    obtain ⟨hx,hx0⟩ := mem_filter.mp hx
    obtain ⟨hy,hy0⟩ := mem_filter.mp hy
    obtain ⟨he,hf⟩ := empty_witness_edges hx hx0
    obtain ⟨he',hf'⟩ := empty_witness_edges hy hy0
    change w=w' at heq
    rw [he,hf,he',hf',heq]

variable {σ : Type*} [Fintype σ]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyMixedCommonTails
end EndpointModule038
-- End GreedyMixedCommonTails.lean

-- Begin GreedyMixedCommonProfiles.lean
section EndpointModule039

/- Counting the one-selected-vertex common-neighbor witnesses of a mixed
hypergraph. The shared rank-three link count is explicit, not silently
bounded by the initial graph common degree. -/
namespace Erdos773.GreedyMixedCommonProfiles
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyMixedCommonTails
open HypergraphDegreeTrim FourUniformRegularization UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Patterns whose first edge has rank two. -/
def firstTwo (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => x.1.card=2)

def secondTwo (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => x.2.2.card=2)

lemma firstTwo_card (H : Finset (Finset α)) (u v : α) (P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (firstTwo H u v).card≤degree (layer H 2) u*P := by
  let E := (layer H 2).filter (fun e => u∈e)
  have hs : firstTwo H u v ⊆ extensions H E v (fun e => e \ {u,v}) := by
    rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,hcard⟩ := mem_filter.mp hx
    obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨he,hcard⟩,hu⟩,
      mem_sdiff.mpr ⟨hw,by simp [hwu,hwv]⟩,hf,hv,hwf⟩
  have hsize (e : Finset α) (he : e∈E) : (e \ {u,v}).card≤1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    have hcard := (mem_filter.mp he).2
    have hsub : e \ {u,v}⊆e.erase u := by
      intro a ha
      exact mem_erase.mpr ⟨fun h => (mem_sdiff.mp ha).2 (by simp [h]),(mem_sdiff.mp ha).1⟩
    have hh := card_le_card hsub
    rw [card_erase_of_mem hu,hcard] at hh
    exact hh
  have hne (e : Finset α) (_he : e∈E) (w : α) (hw : w∈e \ {u,v}) : v≠w := by
    intro hvw
    exact (mem_sdiff.mp hw).2 (by simp [hvw])
  have hb := (card_le_card hs).trans (extensions_card_le H E v _ 1 P hsize hne hP)
  simpa only [Nat.mul_one] using hb

lemma secondTwo_card (H : Finset (Finset α)) (u v : α) (P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (secondTwo H u v).card≤degree (layer H 2) v*P := by
  apply (show (secondTwo H u v).card≤(firstTwo H v u).card from ?_).trans (firstTwo_card H v u P hP)
  apply card_le_card_of_injOn (fun x : Pattern α => (x.2.2,x.2.1,x.1))
  · rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,hcard⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨pattern_swap hx,hcard⟩
  · rintro ⟨e,w,f⟩ _ ⟨e',w',f'⟩ _ he
    simpa only [Prod.mk.injEq,and_comm,and_left_comm,and_assoc] using he

/-- Each shared two-link supplies exactly two possible middle-vertex roles. -/
def twinPatterns (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (RegularizationSharedLinks.links H u v).biUnion
    (fun A => A.image (fun w => (insert u A,w,insert v A)))

lemma twinPatterns_card (H : Finset (Finset α)) (u v : α) :
    (twinPatterns H u v).card≤2*RegularizationSharedLinks.count H u v := by
  calc
    _ ≤ ∑ A∈RegularizationSharedLinks.links H u v,
      (A.image (fun w => (insert u A,w,insert v A))).card := card_biUnion_le
    _ ≤ ∑ A∈RegularizationSharedLinks.links H u v, A.card :=
      sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by
      rw [sum_congr rfl (fun A hA => (RegularizationSharedLinks.mem_links.mp hA).1)]
      simp [RegularizationSharedLinks.count,mul_comm]

lemma one_support_twin {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (hx : (e,w,f)∈patterns H u v) (h1 : (witness u v (e,w,f)).card=1)
    (he2 : e.card≠2) (hf2 : f.card≠2) : (e,w,f)∈twinPatterns H u v := by
  obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,hve,huf⟩ := mem_patterns.mp hx
  obtain ⟨a,ha⟩ := card_eq_one.mp h1
  change (e \ {u,w})∪(f \ {v,w})={a} at ha
  have hepair : ({u,w} : Finset α)⊆e := by simp [insert_subset_iff,hu,hw]
  have hfpair : ({v,w} : Finset α)⊆f := by simp [insert_subset_iff,hv,hwf]
  have hene : (e \ {u,w}).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hsub
    have heq := Subset.antisymm hsub hepair
    apply he2
    rw [heq,card_pair hwu.symm]
  have hfne : (f \ {v,w}).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hsub
    have heq := Subset.antisymm hsub hfpair
    apply hf2
    rw [heq,card_pair hwv.symm]
  have heone : e \ {u,w}={a} := by
    have hs : e \ {u,w}⊆({a}:Finset α) := ha ▸ subset_union_left
    exact eq_singleton_iff_nonempty_unique_mem.mpr ⟨hene,fun b hb => mem_singleton.mp (hs hb)⟩
  have hfone : f \ {v,w}={a} := by
    have hs : f \ {v,w}⊆({a}:Finset α) := ha ▸ subset_union_right
    exact eq_singleton_iff_nonempty_unique_mem.mpr ⟨hfne,fun b hb => mem_singleton.mp (hs hb)⟩
  have hae : a∈e \ {u,w} := by rw [heone]; simp
  have haf : a∈f \ {v,w} := by rw [hfone]; simp
  have hau : a≠u := fun h => (mem_sdiff.mp hae).2 (by simp [h])
  have hav : a≠v := fun h => (mem_sdiff.mp haf).2 (by simp [h])
  have haw : a≠w := fun h => (mem_sdiff.mp hae).2 (by simp [h])
  have heq : e=insert u ({w,a}:Finset α) := by
    have hh := sdiff_union_of_subset hepair
    rw [heone] at hh
    simpa only [union_insert,union_singleton,insert_comm,insert_eq_of_mem (mem_singleton_self a)] using hh.symm
  have hfq : f=insert v ({w,a}:Finset α) := by
    have hh := sdiff_union_of_subset hfpair
    rw [hfone] at hh
    simpa only [union_insert,union_singleton,insert_comm,insert_eq_of_mem (mem_singleton_self a)] using hh.symm
  refine mem_biUnion.mpr ⟨{w,a},RegularizationSharedLinks.mem_links.mpr ⟨?_,?_,?_,?_,?_⟩,
    mem_image.mpr ⟨w,by simp,?_⟩⟩
  · exact card_pair haw.symm
  · simp [hwu.symm,hau.symm]
  · simp [hwv.symm,hav.symm]
  · rwa [← heq]
  · rwa [← hfq]
  · rw [← heq,← hfq]

/-- Every one-support pattern is a short-edge pattern or a shared
rank-three link. In particular, the latter cannot be charged at p^3. -/
lemma one_support_cover (H : Finset (Finset α)) (u v : α) :
    supportLayer H u v 1⊆(firstTwo H u v∪secondTwo H u v)∪twinPatterns H u v := by
  rintro ⟨e,w,f⟩ hx
  obtain ⟨hx,hcard⟩ := mem_filter.mp hx
  by_cases he : e.card=2
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,he⟩))
  by_cases hf : f.card=2
  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,hf⟩))
  exact mem_union_right _ (one_support_twin hx hcard he hf)

/-- Explicit one-support budget. This theorem needs neither regularity nor
an intersection cap, and retains the necessary shared-link term. -/
theorem one_support_bound (H : Finset (Finset α)) (u v : α) (P B D : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (hu : degree (layer H 2) u≤D) (hv : degree (layer H 2) v≤D)
    (hB : RegularizationSharedLinks.count H u v≤B) :
    (supportLayer H u v 1).card≤2*D*P+2*B := by
  have h0 := card_le_card (one_support_cover H u v)
  have h1 := card_union_le (firstTwo H u v∪secondTwo H u v) (twinPatterns H u v)
  have h2 := card_union_le (firstTwo H u v) (secondTwo H u v)
  have h3 := (firstTwo_card H u v P hP).trans (Nat.mul_le_mul_right P hu)
  have h4 := (secondTwo_card H u v P hP).trans (Nat.mul_le_mul_right P hv)
  have h5 := (twinPatterns_card H u v).trans (Nat.mul_le_mul_left 2 hB)
  simp only [Nat.mul_assoc]
  omega

end
end Erdos773.GreedyMixedCommonProfiles
end EndpointModule039
-- End GreedyMixedCommonProfiles.lean

-- Begin GreedyBatchCommonBudgets.lean
section EndpointModule040

/- Explicit mixed common-neighbor witness budgets for one Bernoulli batch.
Support sizes one, two, and at least three have different degree scales. -/
namespace Erdos773.GreedyBatchCommonBudgets
open Finset HypergraphDegreeTrim UniformLayerRegularization
open GreedyCommonNeighbors GreedyMixedCommonTails
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def firstRank (H : Finset (Finset α)) (u v : α) (r : ℕ) : Finset (Pattern α) :=
  (patterns H u v).filter (fun i => i.1.card=r)

def secondRank (H : Finset (Finset α)) (u v : α) (r : ℕ) : Finset (Pattern α) :=
  (patterns H u v).filter (fun i => i.2.2.card=r)

lemma firstRank_card (H : Finset (Finset α)) (u v : α) (r P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (firstRank H u v r).card≤degree (layer H r) u*(r-1)*P := by
  let E := (layer H r).filter (fun e => u∈e)
  have hs : firstRank H u v r⊆extensions H E v (fun e => e \ {u,v}) := by
    rintro ⟨e,w,f⟩ hi
    obtain ⟨hi,hr⟩ := mem_filter.mp hi
    obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hi
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨he,hr⟩,hu⟩,
      mem_sdiff.mpr ⟨hw,by simp [hwu,hwv]⟩,hf,hv,hwf⟩
  have hsize (e : Finset α) (he : e∈E) : (e \ {u,v}).card≤r-1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    have hs : e \ {u,v}⊆e.erase u := by
      intro a ha
      exact mem_erase.mpr ⟨fun h => (mem_sdiff.mp ha).2 (by simp [h]),(mem_sdiff.mp ha).1⟩
    have hh := card_le_card hs
    rwa [card_erase_of_mem hu,(mem_filter.mp he).2] at hh
  have hne (e : Finset α) (_he : e∈E) (w : α) (hw : w∈e \ {u,v}) : v≠w := by
    intro he
    exact (mem_sdiff.mp hw).2 (by simp [he])
  exact (card_le_card hs).trans (extensions_card_le H E v _ (r-1) P hsize hne hP)

lemma secondRank_card (H : Finset (Finset α)) (u v : α) (r P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (secondRank H u v r).card≤degree (layer H r) v*(r-1)*P := by
  apply (show (secondRank H u v r).card≤(firstRank H v u r).card from ?_).trans
    (firstRank_card H v u r P hP)
  apply card_le_card_of_injOn (fun i : Pattern α => (i.2.2,i.2.1,i.1))
  · rintro ⟨e,w,f⟩ hi
    obtain ⟨hi,hr⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨pattern_swap hi,hr⟩
  · rintro ⟨e,w,f⟩ _ ⟨e',w',f'⟩ _ he
    simpa only [Prod.mk.injEq,and_comm,and_left_comm,and_assoc] using he

lemma two_support_cover (H : Finset (Finset α)) (u v : α)
    (hH : ∀ e∈H, 2≤e.card ∧ e.card≤4)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2) :
    supportLayer H u v 2⊆(firstRank H u v 2∪firstRank H u v 3)∪
      (secondRank H u v 2∪secondRank H u v 3) := by
  rintro ⟨e,w,f⟩ hi
  obtain ⟨hi,hc⟩ := mem_filter.mp hi
  have hd := mem_patterns.mp hi
  by_cases he2 : e.card=2
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,he2⟩))
  by_cases he3 : e.card=3
  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,he3⟩))
  by_cases hf2 : f.card=2
  · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hi,hf2⟩))
  by_cases hf3 : f.card=3
  · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hi,hf3⟩))
  have he4 : e.card=4 := by have := hH e hd.1; omega
  have hf4 : f.card=4 := by have := hH f hd.2.1; omega
  have h4 : ∀ e∈layer H 4, e.card=4 := fun e he => (mem_filter.mp he).2
  have hI' : ∀ e∈layer H 4, ∀ f∈layer H 4, e≠f → (e∩f).card≤2 :=
    fun e he f hf hef => hI e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef
  have hi' : (e,w,f)∈patterns (layer H 4) u v := mem_patterns.mpr
    ⟨mem_filter.mpr ⟨hd.1,he4⟩,mem_filter.mpr ⟨hd.2.1,hf4⟩,hd.2.2⟩
  have hh := GreedyCommonNeighbors.witness_card_bounds h4 hI' hi'
  omega

lemma two_support_bound (H : Finset (Finset α)) (u v : α) (D2 D3 P : ℕ)
    (hH : ∀ e∈H, 2≤e.card ∧ e.card≤4)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (h2 : ∀ a, degree (layer H 2) a≤D2) (h3 : ∀ a, degree (layer H 3) a≤D3) :
    (supportLayer H u v 2).card≤4*(D2+D3)*P := by
  have h0 := card_le_card (two_support_cover H u v hH hI)
  have hu := card_union_le (firstRank H u v 2∪firstRank H u v 3) (secondRank H u v 2∪secondRank H u v 3)
  have h1 := card_union_le (firstRank H u v 2) (firstRank H u v 3)
  have h2' := card_union_le (secondRank H u v 2) (secondRank H u v 3)
  have hfu := (firstRank_card H u v 2 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ (h2 u)))
  have hfv := (secondRank_card H u v 2 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ (h2 v)))
  have htu := (firstRank_card H u v 3 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ (h3 u)))
  have htv := (secondRank_card H u v 3 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ (h3 v)))
  norm_num at hfu hfv htu htv
  nlinarith only [h0,hu,h1,h2',hfu,hfv,htu,htv,Nat.zero_le (D2*P)]

lemma total_patterns_bound (H : Finset (Finset α)) (u v : α) (D2 D3 D4 P : ℕ)
    (hH : ∀ e∈H, 2≤e.card ∧ e.card≤4)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (h2 : degree (layer H 2) u≤D2) (h3 : degree (layer H 3) u≤D3)
    (h4 : degree (layer H 4) u≤D4) :
    (patterns H u v).card≤3*(D2+D3+D4)*P := by
  have hs : patterns H u v⊆(firstRank H u v 2∪firstRank H u v 3)∪firstRank H u v 4 := by
    rintro ⟨e,w,f⟩ hi
    have hh := hH e (mem_patterns.mp hi).1
    have he : e.card=2 ∨ e.card=3 ∨ e.card=4 := by omega
    rcases he with he | he | he
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,he⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,he⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,he⟩)
  have h0 := card_le_card hs
  have h1 := card_union_le (firstRank H u v 2∪firstRank H u v 3) (firstRank H u v 4)
  have hu := card_union_le (firstRank H u v 2) (firstRank H u v 3)
  have hf2 := (firstRank_card H u v 2 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ h2))
  have hf3 := (firstRank_card H u v 3 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ h3))
  have hf4 := (firstRank_card H u v 4 P hP).trans (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ h4))
  norm_num at hf2 hf3 hf4
  nlinarith only [h0,h1,hu,hf2,hf3,hf4,Nat.zero_le (D2*P),Nat.zero_le (D3*P)]

def masses (D2 D3 D4 P B : ℕ) (r : ℕ) : ℕ :=
  if r=1 then 2*D2*P+2*B else if r=2 then 4*(D2+D3)*P else 3*(D2+D3+D4)*P

lemma support_mass (H : Finset (Finset α)) (u v : α) (D2 D3 D4 P B : ℕ)
    (hH : ∀ e∈H, 2≤e.card ∧ e.card≤4)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (h2 : ∀ a, degree (layer H 2) a≤D2) (h3 : ∀ a, degree (layer H 3) a≤D3)
    (h4 : ∀ a, degree (layer H 4) a≤D4)
    (hB : RegularizationSharedLinks.count H u v≤B) (r : ℕ) :
    (supportLayer H u v r).card≤ masses D2 D3 D4 P B r := by
  unfold masses
  split_ifs with h1 h2'
  · subst r
    exact GreedyMixedCommonProfiles.one_support_bound H u v P B D2 hP (h2 u) (h2 v) hB
  · subst r
    exact two_support_bound H u v D2 D3 P hH hI hP h2 h3
  · exact (card_filter_le _ _).trans (total_patterns_bound H u v D2 D3 D4 P hH hP (h2 u) (h3 u) (h4 u))

def overlapCaps (m P : ℕ) (k : ℕ) : ℕ := if k=0 then m else 4*P^2

/-- Ordinary Bernoulli tails for a fixed support layer. No survival-law
hypothesis is used, and the original pattern multiplicities are kept. -/
theorem layer_tail (H : Finset (Finset α)) (u v : α) (r M P q : ℕ)
    (hH : ∀ e∈H, e.card≤4) (hM : (supportLayer H u v r).card≤M)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(selectedCost H u v r (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget r q (overlapCaps M P) p/L)^q := by
  apply IndexedBernoulliMoments.tail_bound (supportLayer H u v r) (witness u v) r q
    (overlapCaps M P) p L hp hp1 hL
    (fun i hi => (mem_filter.mp hi).2)
  intro A hA
  by_cases hAc : A.card=0
  · have he := card_eq_zero.mp hAc
    subst A
    simpa [IndexedBernoulliMoments.incidence,overlapCaps] using hM
  · rw [overlapCaps,if_neg hAc]
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<A.card)
    apply (card_le_card (show (supportLayer H u v r).filter (fun i => A⊆witness u v i)⊆
      (supportLayer H u v r).filter (fun i => a∈witness u v i) from ?_)).trans
      (layer_incidence hH u v a r P hP)
    intro i hi
    obtain ⟨hi,hAi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,hAi ha⟩

end
end Erdos773.GreedyBatchCommonBudgets
end EndpointModule040
-- End GreedyBatchCommonBudgets.lean

-- Begin GreedyBatchCommonStep.lean
section EndpointModule041

/- Common-neighbor transport for the conservative batch. Tentative R need
not be independent, so ordinary greedy-residual identities are not assumed. -/
namespace Erdos773.GreedyBatchCommonStep
open Finset GreedyBatchState RegularizationCommonNeighbors GreedyCommonNeighbors
open GreedyMixedCommonTails
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma neighbor_witness (H : Finset (Finset α)) (R : Finset α) (x y : α) (hxy : x≠y)
    (z : α) (hz : z∈both (next H R) (next H R) x y) :
    ∃ i∈patterns H x y, i.2.1=z ∧ witness x y i⊆R := by
  obtain ⟨hx,hy⟩ := mem_both.mp hz
  have hxQ := next_subset hx.2 (by simp : x∈({x,z}:Finset α))
  have hyQ := next_subset hy.2 (by simp : y∈({y,z}:Finset α))
  obtain ⟨e,he,heq⟩ := mem_image.mp hx.2
  obtain ⟨f,hf,hfq⟩ := mem_image.mp hy.2
  have hxe : x∈e := (mem_sdiff.mp (heq.symm ▸ (by simp : x∈({x,z}:Finset α)))).1
  have hyf : y∈f := (mem_sdiff.mp (hfq.symm ▸ (by simp : y∈({y,z}:Finset α)))).1
  have hze : z∈e := (mem_sdiff.mp (heq.symm ▸ (by simp : z∈({x,z}:Finset α)))).1
  have hzf : z∈f := (mem_sdiff.mp (hfq.symm ▸ (by simp : z∈({y,z}:Finset α)))).1
  have hye : y∉e := by
    intro hy'
    have hm : y∈({x,z}:Finset α) := heq ▸ mem_sdiff.mpr ⟨hy',(mem_carrier.mp hyQ).1⟩
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim hxy.symm hy.1
  have hxf : x∉f := by
    intro hx'
    have hm : x∈({y,z}:Finset α) := hfq ▸ mem_sdiff.mpr ⟨hx',(mem_carrier.mp hxQ).1⟩
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim hxy hx.1
  refine ⟨(e,z,f),mem_patterns.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp hf).1,
    hxe,hyf,hze,hzf,hx.1.symm,hy.1.symm,hye,hxf⟩,rfl,?_⟩
  intro a ha
  by_contra haR
  rcases mem_union.mp ha with ha | ha
  · exact (mem_sdiff.mp ha).2 (heq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)
  · exact (mem_sdiff.mp ha).2 (hfq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)

lemma common_le_cost (H : Finset (Finset α)) (R : Finset α) (x y : α) (hxy : x≠y) :
    common (next H R) x y≤patternCost H x y R := by
  have hs : both (next H R) (next H R) x y⊆
      ((patterns H x y).filter (fun i => witness x y i⊆R)).image (fun i => i.2.1) := by
    intro z hz
    obtain ⟨i,hi,hiz,hR⟩ := neighbor_witness H R x y hxy z hz
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,hR⟩,hiz⟩
  exact (card_le_card hs).trans card_image_le

/-- All positive support sizes are retained; old graph common neighbors
are a deterministic starting term. -/
theorem common_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    common (next H R) x y≤common H x y+∑ r∈Icc 1 4, selectedCost H x y r R := by
  have hh := (common_le_cost H R x y hxy).trans_eq (cost_decomposition hH x y R)
  exact hh.trans (Nat.add_le_add_right (zero_le_initial_common H x y) _)

end
end Erdos773.GreedyBatchCommonStep
end EndpointModule041
-- End GreedyBatchCommonStep.lean

-- Begin GreedyBatchSelection.lean
section EndpointModule042

/- Selecting one good batch by a penalized continuation-density reward.
All bad-event estimates remain explicit finite hypotheses. No future density
or asymptotic profile is assumed without being passed as an input. -/
namespace Erdos773.GreedyBatchSelection
open Finset GreedyBatchState BernoulliEvents
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def reward (H : Finset (Finset α)) (δ : ℝ) (R : Finset α) : ℝ :=
  (chosen H R).card+δ*(carrier H R).card

def lowerReward (H : Finset (Finset α)) (p δ : ℝ) : ℝ :=
  p*Fintype.card α-(∑ e∈H, (e.card:ℝ)*p^e.card)+
    δ*((1-p)*Fintype.card α-∑ e∈H, (e.card:ℝ)*p^(e.card-1))

lemma reward_upper (H : Finset (Finset α)) (δ : ℝ) (hδ : δ≤1) (R : Finset α) :
    reward H δ R≤Fintype.card α := by
  have hd : Disjoint (chosen H R) (carrier H R) :=
    ((carrier_disjoint H R).mono_right (chosen_subset H R)).symm
  have hc := card_le_univ (chosen H R∪carrier H R)
  rw [card_union_of_disjoint hd] at hc
  have hc' : ((chosen H R).card:ℝ)+(carrier H R).card≤Fintype.card α := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (carrier H R).card : (0:ℝ)≤(carrier H R).card)
  unfold reward
  linarith only [hh,hc']

/-- An expected positive penalized reward supplies an actual batch avoiding
all bad events. This does not require separate carrier-size concentration. -/
theorem exists_avoiding (H : Finset (Finset α)) (p δ b : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hδ : 0≤δ) (hδ1 : δ≤1)
    (Bad : Finset α → Prop) (hb : prob p Bad≤b)
    (hpositive : 0<lowerReward H p δ-(Fintype.card α:ℝ)*b) :
    ∃ R : Finset α, ¬Bad R ∧
      lowerReward H p δ-(Fintype.card α:ℝ)*b≤reward H δ R := by
  let V : ℝ := Fintype.card α
  let score (f : α → Bool) : ℝ := reward H δ (selected f)-(if Bad (selected f) then V else 0)
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ score univ_nonempty
  have hupper : (∑ g : α → Bool, trialWeight p g*score g)≤score f := by
    calc
      _ ≤ ∑ g : α → Bool, trialWeight p g*score f := sum_le_sum (fun g hg =>
        mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g))
      _ = _ := by rw [← sum_mul,sum_trialWeight,one_mul]
  have hscore : (∑ g : α → Bool, trialWeight p g*score g)=
      (∑ g : α → Bool, trialWeight p g*reward H δ (selected g))-V*prob p Bad := by
    simp only [score,mul_sub,sum_sub_distrib,prob]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro g hg
    split_ifs <;> ring
  have hreward := reward_expectation H p δ hp hp1 hδ
  change lowerReward H p δ≤∑ g : α → Bool, trialWeight p g*reward H δ (selected g) at hreward
  have hV : 0≤V := Nat.cast_nonneg _
  have hbudget := mul_le_mul_of_nonneg_left hb hV
  rw [hscore] at hupper
  have hlo : lowerReward H p δ-V*b≤score f := by linarith only [hupper,hreward,hbudget]
  have hpos : 0<score f := hpositive.trans_le hlo
  have hgood : ¬Bad (selected f) := by
    intro hbad
    have hh := reward_upper H δ hδ1 (selected f)
    dsimp [score] at hpos
    rw [if_pos hbad] at hpos
    change reward H δ (selected f)≤V at hh
    linarith only [hh,hpos]
  refine ⟨selected f,hgood,?_⟩
  simpa only [score,if_neg hgood,sub_zero] using hlo

-- Unused development declaration omitted.

end
end Erdos773.GreedyBatchSelection
end EndpointModule042
-- End GreedyBatchSelection.lean

-- Begin FiniteHypergraphRestriction.lean
section EndpointModule043

/- Restricting a hypergraph to its actual finite carrier. These identities
avoid counting deleted ambient vertices in a residual density argument. -/
namespace Erdos773.FiniteHypergraphRestriction
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (Adj common both)
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

abbrev Carrier (Q : Finset α) := {a : α // a∈Q}

def down (Q : Finset α) (e : Finset α) : Finset (Carrier Q) := e.subtype (·∈Q)
def up (Q : Finset α) (e : Finset (Carrier Q)) : Finset α :=
  e.map (Function.Embedding.subtype _)
def restrict (Q : Finset α) (H : Finset (Finset α)) : Finset (Finset (Carrier Q)) :=
  H.image (down Q)

@[simp] lemma mem_down {Q e : Finset α} {x : Carrier Q} : x∈down Q e ↔ x.val∈e := by
  simp [down]
@[simp] lemma up_down {Q e : Finset α} (he : e⊆Q) : up Q (down Q e)=e :=
  subtype_map_of_mem he
@[simp] lemma down_up {Q : Finset α} (e : Finset (Carrier Q)) : down Q (up Q e)=e := by
  ext x
  simp [up,Function.Embedding.subtype]
lemma up_injective (Q : Finset α) : Function.Injective (up Q) :=
  fun _ _ h => by simpa using congrArg (down Q) h
@[simp] lemma up_card {Q : Finset α} (e : Finset (Carrier Q)) : (up Q e).card=e.card := card_map _
lemma up_subset {Q : Finset α} (e : Finset (Carrier Q)) : up Q e⊆Q :=
  fun _ ha => property_of_mem_map_subtype e ha
lemma down_card {Q e : Finset α} (he : e⊆Q) : (down Q e).card=e.card := by
  rw [← up_card,up_down he]

lemma mem_restrict {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) {f : Finset (Carrier Q)} :
    f∈restrict Q H ↔ up Q f∈H := by
  constructor
  · intro hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    rwa [up_down (hH e he)]
  · intro hf
    exact mem_image.mpr ⟨up Q f,hf,down_up f⟩

lemma down_injOn {Q : Finset α} {H : Finset (Finset α)} (hH : ∀ e∈H, e⊆Q) :
    Set.InjOn (down Q) H := by
  intro e he f hf hh
  rw [← up_down (hH e he),← up_down (hH f hf),hh]

lemma restrict_card {Q : Finset α} {H : Finset (Finset α)} (hH : ∀ e∈H, e⊆Q) :
    (restrict Q H).card=H.card := card_image_of_injOn (down_injOn hH)

lemma degree_all_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x : Carrier Q) : degree (restrict Q H) x=degree H x.val := by
  have he : (restrict Q H).filter (fun e => x∈e)=(H.filter (fun e => x.val∈e)).image (down Q) := by
    ext e
    simp only [restrict,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hx⟩
      exact ⟨f,⟨hf,mem_down.mp hx⟩,rfl⟩
    · rintro ⟨f,⟨hf,hx⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,mem_down.mpr hx⟩
  unfold degree
  rw [he]
  exact card_image_of_injOn (down_injOn (fun e he => hH e (mem_filter.mp he).1))

lemma restrict_induced {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (I : Finset (Carrier Q)) :
    (restrict Q H).filter (·⊆I)=restrict Q (H.filter (·⊆up Q I)) := by
  ext f
  simp only [restrict,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨e,he,rfl⟩,hsub⟩
    refine ⟨e,⟨he,?_⟩,rfl⟩
    have hh := (map_subset_map (f := Function.Embedding.subtype (·∈Q))).mpr hsub
    change up Q (down Q e)⊆up Q I at hh
    rwa [up_down (hH e he)] at hh
  · rintro ⟨e,⟨he,hsub⟩,rfl⟩
    refine ⟨⟨e,he,rfl⟩,?_⟩
    apply (map_subset_map (f := Function.Embedding.subtype (·∈Q))).mp
    change up Q (down Q e)⊆up Q I
    rwa [up_down (hH e he)]

lemma degree_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x : Carrier Q) (k : ℕ) :
    degree (layer (restrict Q H) k) x = degree (layer H k) x.val := by
  have he : ((layer (restrict Q H) k).filter (fun e => x∈e)).image (up Q)=
      (layer H k).filter (fun e => x.val∈e) := by
    ext e
    constructor
    · intro hm
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hm
      obtain ⟨hf,hx⟩ := mem_filter.mp hf
      obtain ⟨hf,hk⟩ := mem_filter.mp hf
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_restrict hH).mp hf,by simpa using hk⟩,?_⟩
      exact mem_map.mpr ⟨x,hx,rfl⟩
    · intro hm
      obtain ⟨he,hx⟩ := mem_filter.mp hm
      obtain ⟨he,hk⟩ := mem_filter.mp he
      refine mem_image.mpr ⟨down Q e,mem_filter.mpr ⟨mem_filter.mpr ⟨?_,?_⟩,mem_down.mpr hx⟩,up_down (hH e he)⟩
      · exact mem_image.mpr ⟨e,he,rfl⟩
      · rwa [down_card (hH e he)]
  unfold degree
  rw [← he,card_image_of_injective _ (up_injective Q)]

lemma pair_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    pairDegree (restrict Q H) x y = pairDegree H x.val y.val := by
  have he : ((restrict Q H).filter (fun e => x∈e ∧ y∈e)).image (up Q)=
      H.filter (fun e => x.val∈e ∧ y.val∈e) := by
    ext e
    constructor
    · intro hm
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hm
      obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
      exact mem_filter.mpr ⟨(mem_restrict hH).mp hf,mem_map.mpr ⟨x,hx,rfl⟩,mem_map.mpr ⟨y,hy,rfl⟩⟩
    · intro hm
      obtain ⟨he,hx,hy⟩ := mem_filter.mp hm
      exact mem_image.mpr ⟨down Q e,mem_filter.mpr ⟨mem_image.mpr ⟨e,he,rfl⟩,
        mem_down.mpr hx,mem_down.mpr hy⟩,up_down (hH e he)⟩
  unfold pairDegree
  rw [← he,card_image_of_injective _ (up_injective Q)]

lemma up_inter {Q : Finset α} (e f : Finset (Carrier Q)) : up Q (e∩f)=up Q e∩up Q f :=
  map_inter _ _

lemma adj_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    Adj (restrict Q H) x y ↔ x.val≠y.val ∧ ({x.val,y.val}:Finset α)∈H := by
  simp only [Adj,mem_restrict hH,up,map_insert,map_singleton,Function.Embedding.subtype_apply]
  exact and_congr (not_congr Subtype.ext_iff) Iff.rfl

lemma intersections {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (K : ℕ)
    (hK : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤K) :
    ∀ e∈restrict Q H, ∀ f∈restrict Q H, e≠f → (e∩f).card≤K := by
  intro e he f hf hef
  rw [← up_card,up_inter]
  exact hK _ ((mem_restrict hH).mp he) _ ((mem_restrict hH).mp hf)
    (fun h => hef (up_injective Q h))

lemma common_eq [Fintype α] {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    common (restrict Q H) x y = common H x.val y.val := by
  have he : up Q (both (restrict Q H) (restrict Q H) x y)=both H H x.val y.val := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
      obtain ⟨hx,hy⟩ := RegularizationCommonNeighbors.mem_both.mp hw
      exact RegularizationCommonNeighbors.mem_both.mpr
        ⟨(adj_eq hH x w).mp hx,(adj_eq hH y w).mp hy⟩
    · intro hz
      obtain ⟨hx,hy⟩ := RegularizationCommonNeighbors.mem_both.mp hz
      have hzQ : z∈Q := hH _ hx.2 (by simp)
      let w : Carrier Q := ⟨z,hzQ⟩
      exact mem_map.mpr ⟨w,RegularizationCommonNeighbors.mem_both.mpr
        ⟨(adj_eq hH x w).mpr hx,(adj_eq hH y w).mpr hy⟩,rfl⟩
  unfold common
  rw [← he,up_card]

lemma independent_iff {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (A : Finset (Carrier Q)) :
    (∀ e∈restrict Q H, ¬e⊆A) ↔ (∀ e∈H, ¬e⊆up Q A) := by
  constructor
  · intro hi e he hsub
    apply hi (down Q e) (mem_image.mpr ⟨e,he,rfl⟩)
    intro x hx
    have hm := hsub (mem_down.mp hx)
    obtain ⟨y,hy,hyx⟩ := mem_map.mp hm
    have hh : y=x := Subtype.ext hyx
    simpa only [hh] using hy
  · intro hi e he hsub
    apply hi (up Q e) ((mem_restrict hH).mp he)
    exact map_subset_map.mpr hsub

end
end Erdos773.FiniteHypergraphRestriction
end EndpointModule043
-- End FiniteHypergraphRestriction.lean

-- Begin GreedyBatchStructure.lean
section EndpointModule044

/- Deterministic structural caps for a conservative batch and its actual
carrier restriction. No independence of the tentative mark set is needed. -/
namespace Erdos773.GreedyBatchStructure
open Finset GreedyBatchState FourUniformRegularization
open FiniteHypergraphRestriction
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma pair_le (H : Finset (Finset α)) (R : Finset α) (x y : α) :
    pairDegree (next H R) x y≤pairDegree H x y := by
  have hs : (next H R).filter (fun f => x∈f ∧ y∈f)⊆
      (H.filter (fun e => x∈e ∧ y∈e)).image (fun e => e \ R) := by
    intro f hf
    obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨(mem_filter.mp he).1,
      (mem_sdiff.mp hx).1,(mem_sdiff.mp hy).1⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma intersections {H : Finset (Finset α)} (R : Finset α) (K : ℕ)
    (hK : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤K) :
    ∀ e∈next H R, ∀ f∈next H R, e≠f → (e∩f).card≤K := by
  intro e he f hf hef
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
  have hab : a≠b := fun h => hef (congrArg (fun s => s \ R) h)
  apply (card_le_card (show (a \ R)∩(b \ R)⊆a∩b from ?_)).trans
    (hK a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab)
  intro x hx
  exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp hx).1).1,(mem_sdiff.mp (mem_inter.mp hx).2).1⟩

/-- Shared links transport to the genuine carrier without increasing their
count. No deleted ambient vertex enters the density model. -/
lemma shared_restrict {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    RegularizationSharedLinks.count (restrict Q H) x y≤RegularizationSharedLinks.count H x.val y.val := by
  apply card_le_card_of_injOn (up Q)
  · intro A hA
    obtain ⟨hAc,hxA,hyA,hx,hy⟩ := RegularizationSharedLinks.mem_links.mp hA
    have hx' : x.val∉up Q A := by
      intro hx
      obtain ⟨z,hz,hzx⟩ := mem_map.mp hx
      have he : z=x := Subtype.ext hzx
      exact hxA (he ▸ hz)
    have hy' : y.val∉up Q A := by
      intro hy
      obtain ⟨z,hz,hzy⟩ := mem_map.mp hy
      have he : z=y := Subtype.ext hzy
      exact hyA (he ▸ hz)
    have he := (mem_restrict hH).mp hx
    have hf := (mem_restrict hH).mp hy
    simp only [up,map_insert,Function.Embedding.subtype_apply] at he hf
    exact RegularizationSharedLinks.mem_links.mpr ⟨by rwa [up_card],hx',hy',he,hf⟩
  · exact fun A hA B hB he => up_injective Q he

end
end Erdos773.GreedyBatchStructure
end EndpointModule044
-- End GreedyBatchStructure.lean

-- Begin GreedyBatchCertificate.lean
section EndpointModule045

/- A simultaneous finite batch certificate. All concentration hypotheses
are explicit scalar inequalities for the proved moment budgets. -/
namespace Erdos773.GreedyBatchCertificate
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open GreedyBatchScalarTails BernoulliEvents
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (common)
set_option maxHeartbeats 4000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure Caps where
  D2 : ℕ
  D3 : ℕ
  D4 : ℕ
  P : ℕ
  C : ℕ
  B : ℕ

def Caps.degree (c : Caps) (j : ℕ) : ℕ := if j=2 then c.D2 else if j=3 then c.D3 else c.D4

structure Margins where
  old : ℕ → ℝ
  promotion31 : ℝ
  promotion41 : ℝ
  promotion42 : ℝ
  sharedOld : ℝ
  shared34 : ℝ
  shared44 : ℝ
  common : ℕ → ℝ

structure Margins.Positive (L : Margins) : Prop where
  old : ∀ j, 0<L.old j
  promotion31 : 0<L.promotion31
  promotion41 : 0<L.promotion41
  promotion42 : 0<L.promotion42
  sharedOld : 0<L.sharedOld
  shared34 : 0<L.shared34
  shared44 : 0<L.shared44
  common : ∀ j, 0<L.common j

inductive VertexTest
  | old2 | old3 | old4 | promotion31 | promotion41 | promotion42
  deriving DecidableEq, Fintype

inductive PairTest
  | sharedOld | shared34 | shared43 | shared44 | common1 | common2 | common3 | common4
  deriving DecidableEq, Fintype

def vertexBad (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η : ℝ)
    (i : VertexTest) (x : α) (R : Finset α) : Prop :=
  match i with
  | .old2 => c.D2*retention 2 c.D2 c.C p η+L.old 2≤(GreedyBatchDegreeStep.oldCount H R 2 x:ℝ)
  | .old3 => c.D3*retention 3 c.D2 c.C p η+L.old 3≤(GreedyBatchDegreeStep.oldCount H R 3 x:ℝ)
  | .old4 => c.D4*retention 4 c.D2 c.C p η+L.old 4≤(GreedyBatchDegreeStep.oldCount H R 4 x:ℝ)
  | .promotion31 => L.promotion31≤(GreedyBatchPromotions.cost H x 3 1 R:ℝ)
  | .promotion41 => L.promotion41≤(GreedyBatchPromotions.cost H x 4 1 R:ℝ)
  | .promotion42 => L.promotion42≤(GreedyBatchPromotions.cost H x 4 2 R:ℝ)

def vertexError (c : Caps) (L : Margins) (p η : ℝ) (q : ℕ) (i : VertexTest) : ℝ :=
  match i with
  | .old2 => hitError c.D2 c.D2 c.C q p η (L.old 2)
  | .old3 => hitError c.D3 (2*c.D2) (c.D2*c.P) q p η (L.old 3)
  | .old4 => hitError c.D4 (3*c.D2) (c.D2*c.P) q p η (L.old 4)
  | .promotion31 => promotionError 3 1 c.D3 c.P q p L.promotion31
  | .promotion41 => promotionError 4 1 c.D4 c.P q p L.promotion41
  | .promotion42 => promotionError 4 2 c.D4 c.P q p L.promotion42

def pairEvent (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η : ℝ)
    (i : PairTest) (x y : α) (R : Finset α) : Prop :=
  match i with
  | .sharedOld => c.B*retention 3 c.D2 c.C p η+L.sharedOld≤(GreedyBatchSharedLoss.oldCount H x y R:ℝ)
  | .shared34 => L.shared34≤(GreedyBatchSharedWitnesses.cost H x y 3 4 R:ℝ)
  | .shared43 => L.shared34≤(GreedyBatchSharedWitnesses.cost H y x 3 4 R:ℝ)
  | .shared44 => L.shared44≤(GreedyBatchSharedWitnesses.cost H x y 4 4 R:ℝ)
  | .common1 => L.common 1≤(GreedyMixedCommonTails.selectedCost H x y 1 R:ℝ)
  | .common2 => L.common 2≤(GreedyMixedCommonTails.selectedCost H x y 2 R:ℝ)
  | .common3 => L.common 3≤(GreedyMixedCommonTails.selectedCost H x y 3 R:ℝ)
  | .common4 => L.common 4≤(GreedyMixedCommonTails.selectedCost H x y 4 R:ℝ)

def commonError (c : Caps) (L : Margins) (p : ℝ) (q r : ℕ) : ℝ :=
  (IndexedBernoulliMoments.budget r q
    (GreedyBatchCommonBudgets.overlapCaps
      (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r) c.P) p/L.common r)^q

def pairError (c : Caps) (L : Margins) (p η : ℝ) (q : ℕ) (i : PairTest) : ℝ :=
  match i with
  | .sharedOld => hitError c.B (2*c.D2) (c.D2*c.P) q p η L.sharedOld
  | .shared34 | .shared43 => sharedError 3 4 c.D3 c.P q p L.shared34
  | .shared44 => sharedError 4 4 c.D4 c.P q p L.shared44
  | .common1 => commonError c L p q 1
  | .common2 => commonError c L p q 2
  | .common3 => commonError c L p q 3
  | .common4 => commonError c L p q 4

structure Regular (H : Finset (Finset α)) (c : Caps) : Prop where
  ranks : ∀ e∈H, 2≤e.card ∧ e.card≤4
  intersections : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2
  degree2 : ∀ x, degree (layer H 2) x=c.D2
  degree3 : ∀ x, degree (layer H 3) x=c.D3
  degree4 : ∀ x, degree (layer H 4) x=c.D4
  pair : ∀ x y, x≠y → pairDegree H x y≤c.P
  common : ∀ x y, x≠y → common H x y≤c.C
  shared : ∀ x y, x≠y → RegularizationSharedLinks.count H x y≤c.B

structure ProbabilityRange (c : Caps) (p η : ℝ) : Prop where
  dp_pos : 0<c.D2*c.P
  common_pos : 0<c.C
  p_nonneg : 0≤p
  p_le_one : p≤1
  eta_nonneg : 0≤η
  eta_le_one : η≤1
  retention_nonneg : 0≤retention 3 c.D2 c.C p η

lemma vertex_tail (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η : ℝ) (q : ℕ)
    (h : Regular H c) (hL : L.Positive) (hp : ProbabilityRange c p η) (i : VertexTest) (x : α) :
    prob p (vertexBad H c L p η i x)≤vertexError c L p η q i := by
  cases i with
  | old2 =>
    simpa [vertexBad,vertexError,oldIncidence] using
      old_degree_tail H x 2 c.D2 c.D2 c.P c.C q h.degree2 (h.degree2 x) h.pair h.common
        hp.dp_pos hp.common_pos p η (L.old 2) hp.p_nonneg hp.p_le_one hp.eta_nonneg hp.eta_le_one (hL.old 2)
  | old3 =>
    simpa [vertexBad,vertexError,oldIncidence] using
      old_degree_tail H x 3 c.D2 c.D3 c.P c.C q h.degree2 (h.degree3 x) h.pair h.common
        hp.dp_pos hp.common_pos p η (L.old 3) hp.p_nonneg hp.p_le_one hp.eta_nonneg hp.eta_le_one (hL.old 3)
  | old4 =>
    simpa [vertexBad,vertexError,oldIncidence] using
      old_degree_tail H x 4 c.D2 c.D4 c.P c.C q h.degree2 (h.degree4 x) h.pair h.common
        hp.dp_pos hp.common_pos p η (L.old 4) hp.p_nonneg hp.p_le_one hp.eta_nonneg hp.eta_le_one (hL.old 4)
  | promotion31 =>
    exact promotion_tail H x 3 1 c.D3 c.P q (by decide) (h.degree3 x).le
      (h.pair x) p L.promotion31 hp.p_nonneg hp.p_le_one hL.promotion31
  | promotion41 =>
    exact promotion_tail H x 4 1 c.D4 c.P q (by decide) (h.degree4 x).le
      (h.pair x) p L.promotion41 hp.p_nonneg hp.p_le_one hL.promotion41
  | promotion42 =>
    exact promotion_tail H x 4 2 c.D4 c.P q (by decide) (h.degree4 x).le
      (h.pair x) p L.promotion42 hp.p_nonneg hp.p_le_one hL.promotion42

lemma pair_tail (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η : ℝ) (q : ℕ)
    (h : Regular H c) (hL : L.Positive) (hp : ProbabilityRange c p η)
    (i : PairTest) (x y : α) (hxy : x≠y) :
    prob p (pairEvent H c L p η i x y)≤pairError c L p η q i := by
  have hc (r : ℕ) : prob p (fun R => L.common r≤(GreedyMixedCommonTails.selectedCost H x y r R:ℝ))≤
      commonError c L p q r :=
    GreedyBatchCommonBudgets.layer_tail H x y r
      (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r) c.P q
      (fun e he => (h.ranks e he).2)
      (GreedyBatchCommonBudgets.support_mass H x y c.D2 c.D3 c.D4 c.P c.B h.ranks h.intersections
        h.pair (fun z => (h.degree2 z).le) (fun z => (h.degree3 z).le) (fun z => (h.degree4 z).le)
        (h.shared x y hxy) r)
      h.pair p (L.common r) hp.p_nonneg hp.p_le_one (hL.common r)
  cases i with
  | sharedOld =>
    exact old_shared_tail H x y c.D2 c.P c.C c.B q h.degree2 (h.pair x) h.common
      (h.shared x y hxy) hp.dp_pos p η L.sharedOld hp.p_nonneg hp.p_le_one hp.eta_nonneg hp.eta_le_one
      hL.sharedOld hp.retention_nonneg
  | shared34 =>
    exact shared_creation_tail H x y 3 4 c.D3 c.P q (by decide) (by decide)
      (h.degree3 x).le h.pair h.intersections p L.shared34 hp.p_nonneg hp.p_le_one hL.shared34
  | shared43 =>
    exact shared_creation_tail H y x 3 4 c.D3 c.P q (by decide) (by decide)
      (h.degree3 y).le h.pair h.intersections p L.shared34 hp.p_nonneg hp.p_le_one hL.shared34
  | shared44 =>
    exact shared_creation_tail H x y 4 4 c.D4 c.P q (by decide) (by decide)
      (h.degree4 x).le h.pair h.intersections p L.shared44 hp.p_nonneg hp.p_le_one hL.shared44
  | common1 =>
    exact hc 1
  | common2 =>
    exact hc 2
  | common3 =>
    exact hc 3
  | common4 =>
    exact hc 4

lemma exists_event_bound {β : Type*} [Fintype β] (p b : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (P : β → Finset α → Prop) (hP : ∀ i, prob p (P i)≤b) :
    prob p (fun R => ∃ i, P i R)≤Fintype.card β*b := by
  have hh := cover_bound p hp hp1 (univ : Finset β) P (fun R => ∃ i, P i R)
    (by rintro R ⟨i,hi⟩; exact ⟨i,mem_univ _,hi⟩)
  apply hh.trans
  have he := sum_le_sum (s := (univ : Finset β)) (fun i hi => hP i)
  simpa only [sum_const,card_univ,nsmul_eq_mul] using he

def Bad (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η : ℝ) (R : Finset α) : Prop :=
  (∃ i x, vertexBad H c L p η i x R) ∨ (∃ i x y, x≠y ∧ pairEvent H c L p η i x y R)

def tests (V : ℕ) : ℝ := 6*V+8*(V:ℝ)^2

/-- Explicit union of six vertex tests and eight ordered-pair tests. -/
theorem bad_tail (H : Finset (Finset α)) (c : Caps) (L : Margins) (p η b : ℝ) (q : ℕ)
    (h : Regular H c) (hL : L.Positive) (hp : ProbabilityRange c p η) (hb : 0≤b)
    (hv : ∀ i, vertexError c L p η q i≤b) (he : ∀ i, pairError c L p η q i≤b) :
    prob p (Bad H c L p η)≤tests (Fintype.card α)*b := by
  have h1 := exists_event_bound p b hp.p_nonneg hp.p_le_one
    (fun i : VertexTest×α => vertexBad H c L p η i.1 i.2)
    (fun i => (vertex_tail H c L p η q h hL hp i.1 i.2).trans (hv i.1))
  have h2 := exists_event_bound p b hp.p_nonneg hp.p_le_one
    (fun i : PairTest×α×α => fun R => i.2.1≠i.2.2 ∧ pairEvent H c L p η i.1 i.2.1 i.2.2 R) (by
      intro i
      by_cases hxy : i.2.1=i.2.2
      · simpa [prob,hxy] using hb
      · exact (mono p hp.p_nonneg hp.p_le_one _ _ (fun R hh => hh.2)).trans
          ((pair_tail H c L p η q h hL hp i.1 i.2.1 i.2.2 hxy).trans (he i.1)))
  have hh := union_bound p hp.p_nonneg hp.p_le_one
    (fun R => ∃ i : VertexTest×α, vertexBad H c L p η i.1 i.2 R)
    (fun R => ∃ i : PairTest×α×α, i.2.1≠i.2.2 ∧ pairEvent H c L p η i.1 i.2.1 i.2.2 R)
  have hh' := hh.trans (add_le_add h1 h2)
  have hV : Fintype.card VertexTest=6 := by decide
  have hP : Fintype.card PairTest=8 := by decide
  simpa only [Bad,Prod.exists,Fintype.card_prod,hV,hP,Nat.cast_mul,Nat.cast_ofNat,
    tests,pow_two,add_mul,mul_assoc] using hh'

/-- Deterministic target inequalities for the explicit local thresholds. -/
structure Fits (c : Caps) (L : Margins) (p η : ℝ) (c' : Caps) : Prop where
  degree2 : c.D2*retention 2 c.D2 c.C p η+L.old 2+L.promotion31+L.promotion42≤c'.D2
  degree3 : c.D3*retention 3 c.D2 c.C p η+L.old 3+L.promotion41≤c'.D3
  degree4 : c.D4*retention 4 c.D2 c.C p η+L.old 4≤c'.D4
  shared : c.B*retention 3 c.D2 c.C p η+L.sharedOld+2*L.shared34+L.shared44≤c'.B
  common : c.C+(∑ r∈Icc 1 4, L.common r)≤c'.C

structure NextBounds (H : Finset (Finset α)) (c : Caps) : Prop where
  degree2 : ∀ x, degree (layer H 2) x≤c.D2
  degree3 : ∀ x, degree (layer H 3) x≤c.D3
  degree4 : ∀ x, degree (layer H 4) x≤c.D4
  shared : ∀ x y, x≠y → RegularizationSharedLinks.count H x y≤c.B
  common : ∀ x y, x≠y → common H x y≤c.C

lemma bounds_of_good (H : Finset (Finset α)) (c c' : Caps) (L : Margins) (p η : ℝ)
    (h : Regular H c) (hf : Fits c L p η c') (R : Finset α) (hR : ¬Bad H c L p η R) :
    NextBounds (next H R) c' := by
  have hv (i : VertexTest) (x : α) : ¬vertexBad H c L p η i x R := fun hh => hR (Or.inl ⟨i,x,hh⟩)
  have hp (i : PairTest) (x y : α) (hxy : x≠y) : ¬pairEvent H c L p η i x y R :=
    fun hh => hR (Or.inr ⟨i,x,y,hxy,hh⟩)
  have hrank := fun e he => (h.ranks e he).2
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x
    have hh : (degree (layer (next H R) 2) x:ℝ)≤(GreedyBatchDegreeStep.oldCount H R 2 x:ℝ)+
        (GreedyBatchPromotions.cost H x 3 1 R:ℝ)+(GreedyBatchPromotions.cost H x 4 2 R:ℝ) := by
      exact_mod_cast GreedyBatchDegreeStep.degree_two H R hrank x
    have h0 := lt_of_not_ge (hv .old2 x)
    have h1 := lt_of_not_ge (hv .promotion31 x)
    have h2 := lt_of_not_ge (hv .promotion42 x)
    have ht := hf.degree2
    have he : (degree (layer (next H R) 2) x:ℝ)≤c'.D2 := by linarith only [hh,h0,h1,h2,ht]
    exact_mod_cast he
  · intro x
    have hh : (degree (layer (next H R) 3) x:ℝ)≤(GreedyBatchDegreeStep.oldCount H R 3 x:ℝ)+
        (GreedyBatchPromotions.cost H x 4 1 R:ℝ) := by
      exact_mod_cast GreedyBatchDegreeStep.degree_three H R hrank x
    have h0 := lt_of_not_ge (hv .old3 x)
    have h1 := lt_of_not_ge (hv .promotion41 x)
    have ht := hf.degree3
    have he : (degree (layer (next H R) 3) x:ℝ)≤c'.D3 := by linarith only [hh,h0,h1,ht]
    exact_mod_cast he
  · intro x
    have hh : (degree (layer (next H R) 4) x:ℝ)≤(GreedyBatchDegreeStep.oldCount H R 4 x:ℝ) := by
      exact_mod_cast GreedyBatchDegreeStep.degree_four H R hrank x
    have h0 := lt_of_not_ge (hv .old4 x)
    have ht := hf.degree4
    have he : (degree (layer (next H R) 4) x:ℝ)≤c'.D4 := by linarith only [hh,h0,ht]
    exact_mod_cast he
  · intro x y hxy
    have hh : (RegularizationSharedLinks.count (next H R) x y:ℝ)≤(GreedyBatchSharedLoss.oldCount H x y R:ℝ)+
        (GreedyBatchSharedWitnesses.cost H x y 3 4 R:ℝ)+(GreedyBatchSharedWitnesses.cost H y x 3 4 R:ℝ)+
        (GreedyBatchSharedWitnesses.cost H x y 4 4 R:ℝ) := by
      exact_mod_cast GreedyBatchSharedStep.shared_step H R hrank x y hxy
    have h0 := lt_of_not_ge (hp .sharedOld x y hxy)
    have h1 := lt_of_not_ge (hp .shared34 x y hxy)
    have h2 := lt_of_not_ge (hp .shared43 x y hxy)
    have h3 := lt_of_not_ge (hp .shared44 x y hxy)
    have ht := hf.shared
    have he : (RegularizationSharedLinks.count (next H R) x y:ℝ)≤c'.B := by linarith only [hh,h0,h1,h2,h3,ht]
    exact_mod_cast he
  · intro x y hxy
    have hcost (r : ℕ) (hr : r∈Icc 1 4) : (GreedyMixedCommonTails.selectedCost H x y r R:ℝ)≤L.common r := by
      obtain ⟨hr1,hr4⟩ := mem_Icc.mp hr
      interval_cases r
      · exact (lt_of_not_ge (hp .common1 x y hxy)).le
      · exact (lt_of_not_ge (hp .common2 x y hxy)).le
      · exact (lt_of_not_ge (hp .common3 x y hxy)).le
      · exact (lt_of_not_ge (hp .common4 x y hxy)).le
    have hh : (common (next H R) x y:ℝ)≤(common H x y:ℝ)+
        ∑ r∈Icc 1 4, (GreedyMixedCommonTails.selectedCost H x y r R:ℝ) := by
      exact_mod_cast GreedyBatchCommonStep.common_step H R hrank x y hxy
    have hc : (common H x y:ℝ)≤c.C := by exact_mod_cast h.common x y hxy
    have hs := sum_le_sum hcost
    have ht := hf.common
    have he : (common (next H R) x y:ℝ)≤c'.C := by linarith only [hh,hc,hs,ht]
    exact_mod_cast he

/-- The complete finite simultaneous stage. No local probability estimate
is left as an assumption: only explicit numerical budgets remain. -/
theorem exists_batch (H : Finset (Finset α)) (c c' : Caps) (L : Margins) (p η δ b : ℝ) (q : ℕ)
    (h : Regular H c) (hL : L.Positive) (hp : ProbabilityRange c p η) (hf : Fits c L p η c')
    (hδ : 0≤δ) (hδ1 : δ≤1) (hb : 0≤b)
    (hv : ∀ i, vertexError c L p η q i≤b) (he : ∀ i, pairError c L p η q i≤b)
    (hpositive : 0<GreedyBatchSelection.lowerReward H p δ-
      (Fintype.card α:ℝ)*tests (Fintype.card α)*b) :
    ∃ R : Finset α, NextBounds (next H R) c' ∧
      GreedyBatchSelection.lowerReward H p δ-(Fintype.card α:ℝ)*tests (Fintype.card α)*b≤
        GreedyBatchSelection.reward H δ R := by
  obtain ⟨R,hR,hr⟩ := GreedyBatchSelection.exists_avoiding H p δ (tests (Fintype.card α)*b)
    hp.p_nonneg hp.p_le_one hδ hδ1 (Bad H c L p η)
    (bad_tail H c L p η b q h hL hp hb hv he) (by simpa only [mul_assoc] using hpositive)
  exact ⟨R,bounds_of_good H c c' L p η h hf R hR,by simpa only [mul_assoc] using hr⟩

end
end Erdos773.GreedyBatchCertificate
end EndpointModule045
-- End GreedyBatchCertificate.lean

-- Begin GreedyBatchScaledErrors.lean
section EndpointModule046

/- All fourteen local scalar errors at shrinking-batch scales. The coarse
cap inequalities are explicit and do not assume an asymptotic trajectory. -/
namespace Erdos773.GreedyBatchScaledErrors
open GreedyBatchCertificate GreedyBatchScalarTails GreedyBatchScaleTails
open IndexedBernoulliMoments
set_option maxHeartbeats 3500000
noncomputable section

structure Conditions (c : Caps) (m : ℕ) (p d : ℝ) : Prop where
  large : 100≤ m
  p_nonneg : 0≤p
  p_le_one : p≤1
  common_pos : 0<c.C
  dp_pos : 0<c.D2*c.P
  pair : c.P≤ m
  degree2 : m^52≤c.D2
  degree3 : m^52≤c.D3
  old2 : m^30*c.C≤c.D2
  old3 : m^30*(c.D2*c.P)≤c.D3
  old4 : m^30*(c.D2*c.P)≤c.D4
  oldShared : m^30*(c.D2*c.P)≤c.B
  graph_load : (c.D2:ℝ)*p≤4/(m:ℝ)^2
  promotion31 : 2*c.D3*p≤10*c.D2/(m:ℝ)^2
  promotion41 : 3*c.D4*p≤10*c.D3/(m:ℝ)^2
  promotion42 : 3*c.D4*p^2≤10*c.D2/(m:ℝ)^2
  shared34 : (c.D3:ℝ)*c.P*p≤(m:ℝ)*d/4
  shared44 : 3*(c.D4:ℝ)*c.P*p^2≤(m:ℝ)*d/4
  shared_overlap : (m:ℝ)^46≤(m:ℝ)*d/4
  common : ∀ r∈Finset.Icc 1 4,
    (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r:ℝ)*p^r≤(m:ℝ)^52/4

def margins (c : Caps) (m : ℕ) (p d : ℝ) : Margins where
  old j := 100*c.degree j/(m:ℝ)^4
  promotion31 := 2*c.D3*p+c.D2/(m:ℝ)^4
  promotion41 := 3*c.D4*p+c.D3/(m:ℝ)^4
  promotion42 := 3*c.D4*p^2+c.D2/(m:ℝ)^4
  sharedOld := 100*c.B/(m:ℝ)^4
  shared34 := (m:ℝ)*d
  shared44 := (m:ℝ)*d
  common _ := (m:ℝ)^52

lemma exp_le_failure (m : ℕ) : Real.exp (-(m:ℝ)^7)≤failure m := by
  have hh := (Real.exp_pos (-(m:ℝ)^7)).le
  dsimp [GreedyBatchScaleTails.failure]
  linarith only [hh]

lemma pair_caps (m P : ℕ) (hm : 1≤ m) (hP : P≤ m) :
    8*P≤8*m^2 ∧ 2*P^2≤8*m^2 ∧ 4*P^2≤8*m^2 := by
  have hm2 : m≤ m^2 := by nlinarith only [hm]
  have hp2 := Nat.pow_le_pow_left hP 2
  omega

lemma near_promotion (m r k Dr P S : ℕ) (p : ℝ)
    (hm : 100≤ m) (hk : k≤4) (hP : P≤ m) (hS : m^52≤S)
    (hp : 0≤p) (hp1 : p≤1)
    (hmean : (Dr*(r-1).choose k:ℕ)*p^k≤10*S/(m:ℝ)^2) :
    promotionError r k Dr P (m^10) p
      ((Dr*(r-1).choose k:ℕ)*p^k+S/(m:ℝ)^4)≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hS0 : (0:ℝ)<S := by
    have hs : (m:ℝ)^52≤S := by exact_mod_cast hS
    exact (pow_pos hm0 52).trans_le hs
  apply scaled_moment m k (Dr*(r-1).choose k) _ p _ hm hk hp hp1 (by positivity)
  · simp [GreedyBatchPromotions.overlapCaps]
  · intro j hj hjk
    rw [GreedyBatchPromotions.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m P (by omega) hP).1
  · exact near_mean_margin m S _ hm (by exact_mod_cast hS) hmean

lemma loose_shared (m r s Dr P : ℕ) (p L : ℝ)
    (hm : 100≤ m) (hrs : (r-3)+(s-3)≤4) (hP : P≤ m) (hp : 0≤p) (hp1 : p≤1)
    (hmean : ((Dr*(r-1).choose 2*P:ℕ):ℝ)*p^((r-3)+(s-3))≤L/4)
    (hE : (m:ℝ)^46≤L/4) :
    sharedError r s Dr P (m^10) p L≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hL : 0<L := by have hh := (pow_pos hm0 46).trans_le hE; linarith only [hh]
  apply scaled_moment m ((r-3)+(s-3)) (Dr*(r-1).choose 2*P) _ p L hm hrs hp hp1 hL
  · simp [GreedyBatchSharedWitnesses.overlapCaps]
  · intro j hj hjk
    rw [GreedyBatchSharedWitnesses.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m P (by omega) hP).2.1
  · exact loose_margin m _ L (by omega) hL.le hmean hE

lemma common_overlap (m : ℕ) (hm : 100≤ m) : (m:ℝ)^46≤(m:ℝ)^52/4 := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤100) hmR 6
  have h6 : (4:ℝ)≤(m:ℝ)^6 := by norm_num at hh; linarith only [hh]
  have hh := mul_le_mul_of_nonneg_right h6 (pow_nonneg hm0 46)
  nlinarith only [hh]

lemma common_moment (c : Caps) (m r : ℕ) (p d : ℝ) (h : Conditions c m p d)
    (hr : r∈Finset.Icc 1 4) :
    commonError c (margins c m p d) p (m^10) r≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by have := h.large; omega)
  apply scaled_moment m r (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r)
    _ p ((m:ℝ)^52) h.large (Finset.mem_Icc.mp hr).2 h.p_nonneg h.p_le_one (by positivity)
  · simp [GreedyBatchCommonBudgets.overlapCaps]
  · intro j hj hjr
    rw [GreedyBatchCommonBudgets.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m c.P (by have := h.large; omega) h.pair).2.2
  · exact loose_margin m _ _ (by have := h.large; omega) (by positivity) (h.common r hr) (common_overlap m h.large)

/-- The six vertex-local scalar errors are uniformly small. -/
theorem vertex_errors (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ∀ i, vertexError c (margins c m p d) p (1/(m:ℝ)^2) (m^10) i≤failure m := by
  intro i
  cases i with
  | old2 =>
    simpa only [vertexError,margins,Caps.degree,if_pos rfl] using
      old_scaled m c.D2 c.D2 c.D2 c.C p h.large h.common_pos h.old2 (by omega) h.p_nonneg h.graph_load
  | old3 =>
    simpa [vertexError,margins,Caps.degree] using
      old_scaled m c.D3 (2*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos h.old3 (by omega) h.p_nonneg h.graph_load
  | old4 =>
    simpa [vertexError,margins,Caps.degree] using
      old_scaled m c.D4 (3*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos h.old4 le_rfl h.p_nonneg h.graph_load
  | promotion31 =>
    have hh := near_promotion m 3 1 c.D3 c.P c.D2 p h.large (by decide) h.pair h.degree2 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion31)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh
  | promotion41 =>
    have hh := near_promotion m 4 1 c.D4 c.P c.D3 p h.large (by decide) h.pair h.degree3 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion41)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh
  | promotion42 =>
    have hh := near_promotion m 4 2 c.D4 c.P c.D2 p h.large (by decide) h.pair h.degree2 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion42)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh

/-- The eight ordered-pair scalar errors, including all common layers. -/
theorem pair_errors (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ∀ i, pairError c (margins c m p d) p (1/(m:ℝ)^2) (m^10) i≤failure m := by
  have h34 := loose_shared m 3 4 c.D3 c.P p ((m:ℝ)*d) h.large (by decide) h.pair h.p_nonneg h.p_le_one
    (by simpa using h.shared34) h.shared_overlap
  have h44 := loose_shared m 4 4 c.D4 c.P p ((m:ℝ)*d) h.large (by decide) h.pair h.p_nonneg h.p_le_one
    (by simpa [mul_comm,mul_left_comm,mul_assoc] using h.shared44) h.shared_overlap
  intro i
  cases i with
  | sharedOld =>
    exact old_scaled m c.B (2*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos
      h.oldShared (by omega) h.p_nonneg h.graph_load
  | shared34 =>
    exact h34.trans (exp_le_failure m)
  | shared43 =>
    exact h34.trans (exp_le_failure m)
  | shared44 =>
    exact h44.trans (exp_le_failure m)
  | common1 =>
    exact (common_moment c m 1 p d h (by decide)).trans (exp_le_failure m)
  | common2 =>
    exact (common_moment c m 2 p d h (by decide)).trans (exp_le_failure m)
  | common3 =>
    exact (common_moment c m 3 p d h (by decide)).trans (exp_le_failure m)
  | common4 =>
    exact (common_moment c m 4 p d h (by decide)).trans (exp_le_failure m)

/-- Positivity of every chosen threshold follows from the same coarse caps. -/
lemma margins_positive (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    (margins c m p d).Positive := by
  have hm : 0< m := by have := h.large; omega
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have h52 : 0< m^52 := pow_pos hm 52
  have h2 : 0<c.D2 := h52.trans_le h.degree2
  have h3 : 0<c.D3 := h52.trans_le h.degree3
  have hprod : 0< m^30*(c.D2*c.P) := Nat.mul_pos (pow_pos hm 30) h.dp_pos
  have h4 : 0<c.D4 := hprod.trans_le h.old4
  have hB : 0<c.B := hprod.trans_le h.oldShared
  have hdj (j : ℕ) : 0<c.degree j := by dsimp [Caps.degree]; split_ifs <;> assumption
  have hmd : 0<(m:ℝ)*d := by
    have hh := (pow_pos hmR 46).trans_le h.shared_overlap
    linarith only [hh]
  have hp := h.p_nonneg
  constructor
  · intro j
    dsimp [margins]
    have hh := hdj j
    positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · exact hmd
  · exact hmd
  · intro j; exact pow_pos hmR 52

/-- The probability and nonnegative-retention guards are also consequences
of the coarse scale conditions, not additional stochastic assumptions. -/
lemma probability_range (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ProbabilityRange c p (1/(m:ℝ)^2) := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (8:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have he0 : (0:ℝ)≤1/(m:ℝ)^2 := by positivity
  have he1 : (1:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  refine ⟨h.dp_pos,h.common_pos,h.p_nonneg,h.p_le_one,he0,he1,?_⟩
  have hp := h.p_nonneg
  have hloss : (1-1/(m:ℝ)^2)*p*(2*c.D2-(2+c.C))≤2*c.D2*p := by
    have h1 : p*(2*c.D2-(2+c.C))≤2*c.D2*p := by
      have hh := mul_nonneg hp (show (0:ℝ)≤2+c.C by positivity)
      nlinarith only [hh]
    have h2 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr he1)
    have h3 := mul_le_mul_of_nonneg_right (show (1:ℝ)-1/(m:ℝ)^2≤1 by linarith only [he0])
      (show (0:ℝ)≤2*c.D2*p by positivity)
    nlinarith only [h2,h3]
  have hload : 2*(c.D2:ℝ)*p≤1 := by
    have hh := h.graph_load
    have h8 : (8:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hm2
    ring_nf at hh h8 ⊢
    nlinarith only [hh,h8]
  have hh := sub_nonneg.mpr (hloss.trans hload)
  simpa [retention] using hh

end
end Erdos773.GreedyBatchScaledErrors
end EndpointModule046
-- End GreedyBatchScaledErrors.lean

-- Begin GreedyBatchReward.lean
section EndpointModule047

/- Exact continuation reward for regular mixed ranks. -/
namespace Erdos773.GreedyBatchReward
open Finset HypergraphDegreeTrim UniformLayerRegularization
open GreedyBatchCertificate GreedyBatchSelection
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma layer_degree_sum (H : Finset (Finset α)) (j D : ℕ)
    (hD : ∀ x, degree (layer H j) x=D) : j*(layer H j).card=Fintype.card α*D := by
  have hh : (∑ x : α, degree (layer H j) x)=∑ e∈layer H j, e.card := by
    have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset α)) (t := layer H j) (fun a e => a∈e)
    simpa only [degree,bipartiteAbove,bipartiteBelow,filter_univ_mem] using he
  have hj := sum_congr rfl (fun e (he : e∈layer H j) => (mem_filter.mp he).2)
  rw [hj] at hh
  simp_rw [hD] at hh
  simpa [mul_comm] using hh.symm

lemma weighted_card_sum (H : Finset (Finset α)) (c : Caps) (h : Regular H c) (w : ℕ → ℝ) :
    (∑ e∈H, (e.card:ℝ)*w e.card)=
      (Fintype.card α:ℝ)*(c.D2*w 2+c.D3*w 3+c.D4*w 4) := by
  have hD (j : ℕ) (hj : j∈Icc 2 4) : j*(layer H j).card=Fintype.card α*c.degree j := by
    obtain ⟨hj2,hj4⟩ := mem_Icc.mp hj
    interval_cases j
    · exact layer_degree_sum H 2 c.D2 h.degree2
    · exact layer_degree_sum H 3 c.D3 h.degree3
    · exact layer_degree_sum H 4 c.D4 h.degree4
  have he := sum_fiberwise_of_maps_to (s := H) (t := Icc 2 4) (g := Finset.card)
    (fun e he => mem_Icc.mpr (h.ranks e he)) (fun e => (e.card:ℝ)*w e.card)
  have hl (j : ℕ) (hj : j∈Icc 2 4) :
      (∑ e∈H.filter (fun e => e.card=j), (e.card:ℝ)*w e.card)=
        (Fintype.card α:ℝ)*c.degree j*w j := by
    calc
      _ = ∑ _e∈layer H j, (j:ℝ)*w j := sum_congr rfl (fun e he => by rw [(mem_filter.mp he).2])
      _ = (j*(layer H j).card:ℕ)*w j := by simp; ring
      _ = _ := by rw [hD j hj]; push_cast; ring
  rw [← he,sum_congr rfl hl]
  have hI : Icc 2 4=({2,3,4}:Finset ℕ) := by decide
  rw [hI]
  simp [Caps.degree]
  ring

def load (c : Caps) (p : ℝ) : ℝ := c.D2*p+c.D3*p^2+c.D4*p^3

def rate (c : Caps) (p δ : ℝ) : ℝ := p*(1-load c p)+δ*(1-p-load c p)

theorem lowerReward_eq (H : Finset (Finset α)) (c : Caps) (h : Regular H c) (p δ : ℝ) :
    lowerReward H p δ=(Fintype.card α:ℝ)*rate c p δ := by
  have h1 := weighted_card_sum H c h (fun j => p^j)
  have h2 := weighted_card_sum H c h (fun j => p^(j-1))
  simp only [lowerReward]
  rw [h1,h2]
  norm_num [rate,load]
  ring

lemma tests_mono {U V : ℕ} (h : U≤V) : tests U≤tests V := by
  have hh : (U:ℝ)≤V := by exact_mod_cast h
  have h0 : (0:ℝ)≤U := Nat.cast_nonneg U
  dsimp [tests]
  nlinarith only [hh,h0]

end
end Erdos773.GreedyBatchReward
end EndpointModule047
-- End GreedyBatchReward.lean

-- Begin MixedLayerRegularization.lean
section EndpointModule048

/- Simultaneous rank-2/3/4 regularization with polynomially many copies.
It preserves independent-set density and the original codegree/intersection
caps, and increases the graph common-neighbor cap by at most three.
No stochastic restart or asymptotic square-Sidon bound is asserted here. -/
namespace Erdos773.MixedLayerRegularization
open Finset UniformLayerRegularization HypergraphDegreeTrim
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (common)
set_option maxHeartbeats 2500000
noncomputable section

section OneLayer
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

/-- Exact data for one regularized degree layer, retaining every other rank. -/
structure Result (H : Finset (Finset α)) (D K C : ℕ)
    (G : Finset (Finset (Vertex α ρ F))) : Prop where
  ranks : ∀ e ∈ G, 2≤e.card ∧ e.card≤4
  target : ∀ x, degree (layer G (Fintype.card ρ)) x=D
  other : ∀ k, k≠Fintype.card ρ → ∀ x, degree (layer G k) x=degree (layer H k) x.1
  pair : ∀ x y, x≠y → pairDegree G x y≤K
  intersections : ∀ e ∈ G, ∀ f ∈ G, e≠f → (e∩f).card≤2
  common : ∀ x y, x≠y → RegularizationCommonNeighbors.common G x y≤C
  transfer : ∀ B : Finset (Vertex α ρ F), (∀ e ∈ G, ¬e⊆B) →
    ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤(Fintype.card ρ*Fintype.card F)*A.card
  shared : ∀ B : ℕ, (∀ a b, a≠b → RegularizationSharedLinks.count H a b≤B) →
    ∀ x y, x≠y → RegularizationSharedLinks.count G x y≤B

/-- Higher-rank additions do not change the graph common-neighbor bound. -/
theorem higher (H : Finset (Finset α)) (D K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hdeg : ∀ a, degree (layer H (Fintype.card ρ)) a≤D)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C)
    (hρ : 2≤Fintype.card ρ ∧ Fintype.card ρ≤4) (hne : Fintype.card ρ≠2)
    (hD : D≤Fintype.card F) (h : ρ → F) (hh : Function.Injective h) :
    ∃ G : Finset (Finset (Vertex α ρ F)), Result H D K C G := by
  obtain ⟨S,hS⟩ := exists_slopes (F := F) (layer H (Fintype.card ρ)) D hD
  refine ⟨regularized H h S,⟨rank_range H h S hH hρ,?_,
    fun k hk x => degree_layer_other H h S hk x,
    regularized_pair_degree H h hh S K hK hpair,
    regularized_intersections H h hh S 2 (by omega) hinter,
    RegularizationCommonNeighbors.higher_common_bound H h S hne C hcommon,
    independent_slice H h S,RegularizationSharedLinks.count_bound H h hh S⟩⟩
  intro x
  rw [degree_layer_same H h hh S x,hS x.1]
  exact Nat.add_sub_of_le (hdeg x.1)

/-- A Sidon reservoir makes the rank-two padding graph sparse in common
neighbors, including when the old graph layer is nonempty. -/
theorem two (H : Finset (Finset α)) (D K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hdeg : ∀ a, degree (layer H 2) a≤D)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C)
    (T : Finset F) (hTcard : D≤T.card) (hT : IsSidon (T:Set F))
    (h : Fin 2 → F) (hh : Function.Injective h) :
    ∃ G : Finset (Finset (Vertex α (Fin 2) F)), Result H D K (C+3) G := by
  obtain ⟨S,hST,hS⟩ := exists_slopes_subset (layer H 2) D T hTcard
  refine ⟨regularized H h S,⟨rank_range H h S hH (by norm_num),?_,
    fun k hk x => degree_layer_other H h S hk x,
    regularized_pair_degree H h hh S K hK hpair,
    regularized_intersections H h hh S 2 (by omega) hinter,
    RegularizationCommonNeighbors.two_common_bound H h hh S T hST hT C hcommon,
    independent_slice H h S,RegularizationSharedLinks.count_bound H h hh S⟩⟩
  intro x
  rw [degree_layer_same H h hh S x]
  simp only [Fintype.card_fin,hS]
  exact Nat.add_sub_of_le (hdeg x.1)
end OneLayer

/-- One prime field suffices for all three regularization layers. -/
def cap (D2 D3 D4 : ℕ) : ℕ := max (max D3 D4) (2*PolynomialSidonSlopes.height D2+5)

abbrev Model (α : Type*) (p : ℕ) :=
  Vertex (Vertex (Vertex α (Fin 4) (ZMod p)) (Fin 3) (ZMod p)) (Fin 2) (ZMod p)

def labels (r p : ℕ) : Fin r → ZMod p := fun i => i.val

lemma labels_injective {r p : ℕ} (hp : r≤p) : Function.Injective (labels r p) := by
  intro i j he
  apply Fin.ext
  have hh := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp he
  simpa only [Nat.mod_eq_of_lt (i.isLt.trans_le hp),Nat.mod_eq_of_lt (j.isLt.trans_le hp)] using hh

lemma model_card {α : Type*} [Fintype α] {p : ℕ} [NeZero p] :
    Fintype.card (Model α p)=24*p^3*Fintype.card α := by
  simp only [Model,Vertex,Copy,Fintype.card_prod,Fintype.card_fin,ZMod.card]
  ring

section Assemble
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A genuine finite mixed-rank regularization. All three target degrees
are achieved simultaneously. The number of copies is exactly 24*p^3,
with p bounded polynomially in the three prescribed degree caps. -/
theorem exists_regularization (H : Finset (Finset α)) (D2 D3 D4 K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (h2 : ∀ a, degree (layer H 2) a≤D2)
    (h3 : ∀ a, degree (layer H 3) a≤D3)
    (h4 : ∀ a, degree (layer H 4) a≤D4)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C) :
    ∃ p : ℕ, ∃ hprime : p.Prime,
      letI : Fact p.Prime := ⟨hprime⟩
      cap D2 D3 D4≤p ∧ p≤2*cap D2 D3 D4 ∧
      ∃ G : Finset (Finset (Model α p)),
        (∀ e ∈ G, 2≤e.card ∧ e.card≤4) ∧
        (∀ x, degree (layer G 2) x=D2) ∧
        (∀ x, degree (layer G 3) x=D3) ∧
        (∀ x, degree (layer G 4) x=D4) ∧
        (∀ x y, x≠y → pairDegree G x y≤K) ∧
        (∀ e ∈ G, ∀ f ∈ G, e≠f → (e∩f).card≤2) ∧
        (∀ x y, x≠y → common G x y≤C+3) ∧
        (∀ B : Finset (Model α p), (∀ e ∈ G, ¬e⊆B) →
          ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤24*p^3*A.card) ∧
        (∀ B : ℕ, (∀ a b, a≠b → RegularizationSharedLinks.count H a b≤B) →
          ∀ x y, x≠y → RegularizationSharedLinks.count G x y≤B) := by
  have hcap : 5≤cap D2 D3 D4 := by unfold cap; omega
  obtain ⟨p,hprime,hp,hpupper⟩ := Nat.exists_prime_lt_and_le_two_mul (cap D2 D3 D4) (by omega)
  letI : Fact p.Prime := ⟨hprime⟩
  have hp5 : 5≤p := hcap.trans hp.le
  have hp3 : D3≤Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact (le_max_left D3 D4).trans ((le_max_left _ _).trans hp.le)
  have hp4 : D4≤Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact (le_max_right D3 D4).trans ((le_max_left _ _).trans hp.le)
  have hpT : 2*PolynomialSidonSlopes.height D2<p := by
    have hh := (le_max_right (max D3 D4) (2*PolynomialSidonSlopes.height D2+5)).trans hp.le
    omega
  obtain ⟨G4,g4⟩ := higher (ρ := Fin 4) H D4 K C hH
    (by simpa only [Fintype.card_fin] using h4) hK hpair hinter hcommon
    (by norm_num) (by norm_num) hp4 (labels 4 p) (labels_injective (by omega))
  have g43 : ∀ x, degree (layer G4 3) x≤D3 := by
    intro x
    rw [g4.other 3 (by norm_num)]
    exact h3 x.1
  obtain ⟨G3,g3⟩ := higher (ρ := Fin 3) G4 D3 K C g4.ranks
    (by simpa only [Fintype.card_fin] using g43) hK g4.pair g4.intersections g4.common
    (by norm_num) (by norm_num) hp3 (labels 3 p) (labels_injective (by omega))
  have g32 : ∀ x, degree (layer G3 2) x≤D2 := by
    intro x
    rw [g3.other 2 (by norm_num),g4.other 2 (by norm_num)]
    exact h2 x.1.1
  obtain ⟨G2,g2⟩ := two G3 D2 K C g3.ranks g32 hK g3.pair g3.intersections g3.common
    (PolynomialSidonSlopes.seed D2 p) (by rw [PolynomialSidonSlopes.seed_card D2 p hpT])
    (PolynomialSidonSlopes.seed_sidon D2 p hpT) (labels 2 p) (labels_injective (by omega))
  refine ⟨p,hprime,hp.le,hpupper,G2,g2.ranks,?_,?_,?_,g2.pair,g2.intersections,g2.common,?_,?_⟩
  · simpa only [Fintype.card_fin] using g2.target
  · intro x
    rw [g2.other 3 (by norm_num)]
    exact g3.target x.1
  · intro x
    rw [g2.other 4 (by norm_num),g3.other 4 (by norm_num)]
    exact g4.target x.1.1
  · intro B hB
    obtain ⟨A3,hA3,hc3⟩ := g2.transfer B hB
    obtain ⟨A4,hA4,hc4⟩ := g3.transfer A3 hA3
    obtain ⟨A,hA,hc⟩ := g4.transfer A4 hA4
    refine ⟨A,hA,?_⟩
    simp only [Fintype.card_fin,ZMod.card] at hc3 hc4 hc
    calc
      B.card ≤ (2*p)*A3.card := hc3
      _ ≤ (2*p)*((3*p)*A4.card) := Nat.mul_le_mul_left _ hc4
      _ ≤ (2*p)*((3*p)*((4*p)*A.card)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
      _ = 24*p^3*A.card := by ring
  · intro B hB
    exact g2.shared B (g3.shared B (g4.shared B hB))

omit [DecidableEq α] in
/-- The resulting cardinality transfer is precisely a density transfer,
not a further constant-factor loss. -/
lemma density_transfer {p : ℕ} (hp : p.Prime) (H : Finset (Finset α))
    (G : Finset (Finset (Model α p)))
    (htransfer : ∀ B : Finset (Model α p), (∀ e ∈ G, ¬e⊆B) →
      ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤24*p^3*A.card)
    (B : Finset (Model α p)) (hB : ∀ e ∈ G, ¬e⊆B) (δ : ℝ)
    (hδ : δ*(24*p^3*Fintype.card α)≤(B.card:ℝ)) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ δ*Fintype.card α≤(A.card:ℝ) := by
  obtain ⟨A,hA,hcard⟩ := htransfer B hB
  refine ⟨A,hA,?_⟩
  have hc : (B.card:ℝ)≤24*(p:ℝ)^3*A.card := by exact_mod_cast hcard
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  apply le_of_mul_le_mul_left (a := 24*(p:ℝ)^3) _ (by positivity)
  nlinarith only [hδ,hc]
end Assemble

end
end Erdos773.MixedLayerRegularization
end EndpointModule048
-- End MixedLayerRegularization.lean

-- Begin GreedyBatchDensityStep.lean
section EndpointModule049

/- One backward density step for conservative batches, with an explicit
forward volume bound. Residuals are restricted to their true carriers before
regularization. There is no assertion of a successful asymptotic iteration. -/
namespace Erdos773.GreedyBatchDensityStep
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open GreedyBatchCertificate GreedyBatchReward GreedyHypergraphState
open FiniteHypergraphRestriction (Carrier restrict up)
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3500000
noncomputable section
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def post (c : Caps) : Caps := { c with C := c.C+3 }

def copies (c : Caps) : ℕ := 24*(2*MixedLayerRegularization.cap c.D2 c.D3 c.D4)^3

/-- The bounded-volume induction predicate. -/
def UniformDensity (c : Caps) (V : ℕ) (δ : ℝ) : Prop :=
  ∀ (β : Type u) [Fintype β] [DecidableEq β] (H : Finset (Finset β)),
    Regular H c → Fintype.card β≤V →
      ∃ A : Finset β, Independent H A ∧ δ*Fintype.card β≤(A.card:ℝ)

lemma zero_density (c : Caps) (V : ℕ) : UniformDensity.{u} c V 0 := by
  intro β _ _ H h hV
  refine ⟨∅,?_,by simp⟩
  intro e he hesub
  have hh := card_le_card hesub
  have hr := (h.ranks e he).1
  simp only [card_empty] at hh
  omega

/-- A regular model of the actual conservative residual. Its independent
sets transfer to the restricted residual before any extension is attempted. -/
theorem regularize_next (H : Finset (Finset α)) (R : Finset α) (c c' : Caps)
    (h : Regular H c) (hn : NextBounds (next H R) c') (hP : c.P≤c'.P) (hPpos : 1≤c'.P) :
    ∃ r : ℕ, ∃ hprime : r.Prime,
      letI : Fact r.Prime := ⟨hprime⟩
      MixedLayerRegularization.cap c'.D2 c'.D3 c'.D4≤r ∧
      r≤2*MixedLayerRegularization.cap c'.D2 c'.D3 c'.D4 ∧
      ∃ G : Finset (Finset (MixedLayerRegularization.Model (Carrier (carrier H R)) r)),
        Regular G (post c') ∧
        (∀ B : Finset (MixedLayerRegularization.Model (Carrier (carrier H R)) r), Independent G B →
          ∃ A : Finset (Carrier (carrier H R)), Independent (restrict (carrier H R) (next H R)) A ∧
            B.card≤24*r^3*A.card) := by
  let Q := carrier H R
  let K := restrict Q (next H R)
  have hQ : ∀ e∈next H R, e⊆Q := fun e he => next_subset he
  have hrank : ∀ e∈K, 2≤e.card ∧ e.card≤4 := by
    intro e he
    have hh := next_rank (fun e he => (h.ranks e he).2) ((FiniteHypergraphRestriction.mem_restrict hQ).mp he)
    simpa only [FiniteHypergraphRestriction.up_card] using hh
  have h2 (x : Carrier Q) : degree (layer K 2) x≤c'.D2 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree2 x.val
  have h3 (x : Carrier Q) : degree (layer K 3) x≤c'.D3 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree3 x.val
  have h4 (x : Carrier Q) : degree (layer K 4) x≤c'.D4 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree4 x.val
  have hp (x y : Carrier Q) (hxy : x≠y) : pairDegree K x y≤c'.P := by
    rw [FiniteHypergraphRestriction.pair_eq hQ]
    exact (GreedyBatchStructure.pair_le H R x.val y.val).trans
      ((h.pair _ _ (fun he => hxy (Subtype.ext he))).trans hP)
  have hc (x y : Carrier Q) (hxy : x≠y) : RegularizationCommonNeighbors.common K x y≤c'.C := by
    rw [FiniteHypergraphRestriction.common_eq hQ]
    exact hn.common _ _ (fun he => hxy (Subtype.ext he))
  have hb (x y : Carrier Q) (hxy : x≠y) : RegularizationSharedLinks.count K x y≤c'.B :=
    (GreedyBatchStructure.shared_restrict hQ x y).trans
      (hn.shared _ _ (fun he => hxy (Subtype.ext he)))
  obtain ⟨r,hprime,hrL,hrU,G,hr,hg2,hg3,hg4,hgp,hgi,hgc,ht,hbG⟩ :=
    MixedLayerRegularization.exists_regularization K c'.D2 c'.D3 c'.D4 c'.P c'.C
      hrank h2 h3 h4 hPpos hp
      (FiniteHypergraphRestriction.intersections hQ 2 (GreedyBatchStructure.intersections R 2 h.intersections)) hc
  letI : Fact r.Prime := ⟨hprime⟩
  refine ⟨r,hprime,hrL,hrU,G,?_,ht⟩
  exact ⟨hr,hgi,hg2,hg3,hg4,hgp,hgc,hbG c'.B hb⟩

/-- Continue on a good residual using the bounded-volume future density
hypothesis. The selected batch is added only after density transfer. -/
theorem continue_batch (H : Finset (Finset α)) (R : Finset α) (c c' : Caps) (V W : ℕ) (δ : ℝ)
    (h : Regular H c) (hn : NextBounds (next H R) c') (hP : c.P≤c'.P) (hPpos : 1≤c'.P)
    (hV : Fintype.card α≤V) (hW : copies c'*V≤W)
    (hfuture : UniformDensity.{u} (post c') W δ) :
    ∃ A : Finset α, Independent H A ∧ GreedyBatchSelection.reward H δ R≤(A.card:ℝ) := by
  obtain ⟨r,hprime,hrL,hrU,G,hG,ht⟩ := regularize_next H R c c' h hn hP hPpos
  letI : Fact r.Prime := ⟨hprime⟩
  let Q := carrier H R
  have hvol : Fintype.card (MixedLayerRegularization.Model (Carrier Q) r)≤W := by
    rw [MixedLayerRegularization.model_card,Fintype.card_coe]
    apply le_trans _ hW
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hrU 3))
      ((card_le_univ Q).trans hV)
  obtain ⟨B,hB,hδB⟩ := hfuture (MixedLayerRegularization.Model (Carrier Q) r) G hG hvol
  have hδB' : δ*(24*(r:ℝ)^3*Fintype.card (Carrier Q))≤(B.card:ℝ) := by
    simpa only [MixedLayerRegularization.model_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hδB
  obtain ⟨J,hJ,hδJ⟩ := MixedLayerRegularization.density_transfer hprime (restrict Q (next H R)) G ht B hB δ hδB'
  let A := up Q J
  have hA : A⊆carrier H R := FiniteHypergraphRestriction.up_subset J
  have hi : Independent (next H R) A :=
    (FiniteHypergraphRestriction.independent_iff (fun e he => next_subset he) J).mp hJ
  refine ⟨chosen H R∪A,extension R (fun e he => card_pos.mp (by have := (h.ranks e he).1; omega)) hA hi,?_⟩
  have hcard : δ*(carrier H R).card≤(A.card:ℝ) := by
    simpa only [Fintype.card_coe,A,FiniteHypergraphRestriction.up_card] using hδJ
  rw [extension_card H R hA,Nat.cast_add]
  exact add_le_add le_rfl hcard

/-- One rigorous backward induction step. The numerical hypotheses involve
only current caps, proposed margins, future caps, and forward volume bounds. -/
theorem density_step (c c' : Caps) (L : Margins) (p η δ ρ b : ℝ) (q V W : ℕ)
    (hL : L.Positive) (hp : ProbabilityRange c p η) (hf : Fits c L p η c')
    (hP : c.P≤c'.P) (hδ : 0≤δ) (hδ1 : δ≤1) (hρ : 0<ρ) (hb : 0≤b)
    (hv : ∀ i, vertexError c L p η q i≤b) (he : ∀ i, pairError c L p η q i≤b)
    (hrate : ρ≤rate c p δ-tests V*b) (hW : copies c'*V≤W)
    (hfuture : UniformDensity.{u} (post c') W δ) : UniformDensity.{u} c V ρ := by
  intro β _ _ H h hV
  by_cases hempty : Fintype.card β=0
  · refine ⟨∅,?_,by simp [hempty]⟩
    intro e he hesub
    have hh := card_le_card hesub
    have hr := (h.ranks e he).1
    simp only [card_empty] at hh
    omega
  have hvolpos : (0:ℝ)<Fintype.card β := by exact_mod_cast Nat.pos_of_ne_zero hempty
  have hm := mul_le_mul_of_nonneg_right (tests_mono hV) hb
  have hrate' : ρ≤rate c p δ-tests (Fintype.card β)*b := by linarith only [hrate,hm]
  have hpositive : 0<GreedyBatchSelection.lowerReward H p δ-
      (Fintype.card β:ℝ)*tests (Fintype.card β)*b := by
    rw [lowerReward_eq H c h]
    have hh := mul_pos hvolpos (hρ.trans_le hrate')
    nlinarith only [hh]
  obtain ⟨R,hn,hr⟩ := exists_batch H c c' L p η δ b q h hL hp hf hδ hδ1 hb hv he hpositive
  have hPpos : 1≤c'.P := by
    have hh := hp.dp_pos
    have hn := Nat.pos_of_mul_pos_left hh
    omega
  obtain ⟨A,hA,hrA⟩ := continue_batch H R c c' V W δ h hn hP hPpos hV hW hfuture
  refine ⟨A,hA,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hrate' hvolpos.le
  rw [lowerReward_eq H c h] at hr
  nlinarith only [hmul,hr,hrA]

end
end Erdos773.GreedyBatchDensityStep
end EndpointModule049
-- End GreedyBatchDensityStep.lean

-- Begin GreedyBatchScaledStep.lean
section EndpointModule050

/- The finite density step with every local tail fully instantiated at
shrinking-batch scales. Only deterministic cap, fit, rate and volume
inequalities remain to validate an actual schedule. -/
namespace Erdos773.GreedyBatchScaledStep
open GreedyBatchCertificate GreedyBatchDensityStep GreedyBatchReward
open GreedyBatchScaledErrors GreedyBatchScaleTails
set_option maxHeartbeats 2500000
noncomputable section
universe u

-- Unused development declaration omitted.

end
end Erdos773.GreedyBatchScaledStep
end EndpointModule050
-- End GreedyBatchScaledStep.lean

-- Begin GreedyBatchProfileLower.lean
section EndpointModule051

/- Elementary lower bounds for the proposed exponential mixed-degree
profiles. Only exp(x)>=1+x and polynomial estimates are used. -/
namespace Erdos773.GreedyBatchProfileLower
set_option maxHeartbeats 2500000
noncomputable section

def delta (t h : ℝ) : ℝ := (t+h)^3-t^3

lemma delta_nonneg (t h : ℝ) (ht : 0≤t) (hh : 0≤h) : 0≤delta t h := by
  dsimp [delta]
  exact sub_nonneg.mpr (pow_le_pow_left₀ ht (by linarith only [hh]) 3)

lemma delta_error (t h κ : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ) :
    delta t h≤3*t^2*h+4*κ ∧
    delta t h*(t+h)≤3*t^3*h+11*t*κ ∧
    delta t h*(t+h)^2≤3*t^4*h+25*t^2*κ := by
  have h2 := mul_le_mul_of_nonneg_right hht hh
  have h3 := mul_le_mul_of_nonneg_right hht (sq_nonneg h)
  have hd : delta t h≤3*t^2*h+4*t*h^2 := by dsimp [delta]; nlinarith only [h3]
  have hs : (t+h)^2≤t^2+3*t*h := by nlinarith only [h2]
  refine ⟨by nlinarith only [hd,hκ],?_,?_⟩
  · have he := mul_le_mul_of_nonneg_right hd (add_nonneg ht hh)
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0:ℝ)≤4*t by positivity)
    have hκ' := mul_le_mul_of_nonneg_left hκ (show (0:ℝ)≤11*t by positivity)
    nlinarith only [he,h3',hκ']
  · have he := mul_le_mul hd hs (sq_nonneg (t+h)) (by positivity)
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0:ℝ)≤12*t^2 by positivity)
    have hκ' := mul_le_mul_of_nonneg_left hκ (show (0:ℝ)≤25*t^2 by positivity)
    nlinarith only [he,h3',hκ']

lemma rank_two (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    t^2+2*t*h-3*a*t^4*h-25*t^2*κ≤Real.exp (-a*delta t h)*(t+h)^2 := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-a*delta t h)) (sq_nonneg (t+h))
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).2.2 ha
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤25*t^2*κ by positivity)
  nlinarith only [he,hd,hc,sq_nonneg h]

lemma rank_three (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    t+h-6*a*t^3*h-22*t*κ≤Real.exp (-2*a*delta t h)*(t+h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2*a*delta t h)) (add_nonneg ht hh)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).2.1 (show (0:ℝ)≤2*a by positivity)
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤22*t*κ by positivity)
  nlinarith only [he,hd,hc]

lemma rank_four (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    1-9*a*t^2*h-12*κ≤Real.exp (-3*a*delta t h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := Real.add_one_le_exp (-3*a*delta t h)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).1 (show (0:ℝ)≤3*a by positivity)
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤12*κ by positivity)
  nlinarith only [he,hd,hc]

lemma shared (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    1-3*a*t^2*h-4*κ≤Real.exp (-a*delta t h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := Real.add_one_le_exp (-a*delta t h)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).1 ha
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤4*κ by positivity)
  nlinarith only [he,hd,hc]

/-- Normalized ideal updates are absorbed with considerable coefficient slack.
The three-mark and shared profiles retain every positive creation term. -/
lemma ideal_two (A B a η x y z κ : ℝ) (hA : 3≤A) (hBA : B≤A) (hy : 0≤y) (hκ : 0≤κ)
    (hz : z≤κ) (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    A*(1-(1-η)*A*x)+2*B*y+3*z+250*A*κ≤A*(1+2*y-3*a*x-25*κ) := by
  have hA0 : 0≤A := by linarith only [hA]
  have hh := mul_le_mul_of_nonneg_left hgap hA0
  have hab := mul_le_mul_of_nonneg_right hBA hy
  have hk := mul_le_mul_of_nonneg_right hA hκ
  have hAk := mul_nonneg hA0 hκ
  nlinarith only [hh,hab,hk,hz,hAk]

lemma ideal_three (A B a η x y κ : ℝ) (hB : 3≤B) (hy : 0≤y) (hκ : 0≤κ)
    (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    B*(1-2*(1-η)*A*x)+3*y+250*B*κ≤B*(1+y-6*a*x-22*κ) := by
  have hB0 : 0≤B := by linarith only [hB]
  have hh := mul_le_mul_of_nonneg_left hgap hB0
  have hby := mul_le_mul_of_nonneg_right hB hy
  have hBk := mul_nonneg hB0 hκ
  nlinarith only [hh,hby,hBk]

lemma ideal_four (A a η x κ : ℝ) (hκ : 0≤κ) (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    1-3*(1-η)*A*x+250*κ≤1-9*a*x-12*κ := by
  nlinarith only [hκ,hgap]

lemma ideal_shared (A a η x κ : ℝ) (ha : 0≤a) (hx : 0≤x) (hκ : 0≤κ)
    (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    1-2*(1-η)*A*x+250*κ≤1-3*a*x-4*κ := by
  have hh := mul_nonneg ha hx
  nlinarith only [hh,hκ,hgap]

end
end Erdos773.GreedyBatchProfileLower
end EndpointModule051
-- End GreedyBatchProfileLower.lean

-- Begin GreedyBatchCeilingErrors.lean
section EndpointModule052

/- Coarse deterministic rounding estimates for one mixed-rank batch. -/
namespace Erdos773.GreedyBatchCeilingErrors
set_option maxHeartbeats 2500000
noncomputable section

/-- Old survival plus the 100n*kappa margin costs at most 202F*kappa
beyond the ideal loss. The deficit retains its sign and its p factor. -/
theorem old_upper (n F D F2 k e p η κ : ℝ)
    (hn0 : 0≤n) (hF : 0≤F) (hD : 0≤D) (hk : 0≤k) (he : 0≤e) (hp : 0≤p)
    (hη : 0≤η) (hη1 : η≤1) (hκ : 0≤κ)
    (hn : n≤F+1) (hn2 : n≤2*F) (hround : 1≤F*κ) (hF2 : F2≤D)
    (hload : k*D*p≤1) (hdef : p*e≤κ/2) :
    n*(1-(1-η)*p*(k*D-e))+100*n*κ≤F*(1-(1-η)*p*k*F2)+202*F*κ := by
  have heta0 : 0≤1-η := sub_nonneg.mpr hη1
  have hc0 : 0≤(1-η)*p*k*D := by positivity
  have hc1 : (1-η)*p*k*D≤1 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-η≤1 by linarith only [hη])
      (show 0≤k*D*p by positivity)
    nlinarith only [hh,hload]
  have hr0 : 0≤1-(1-η)*p*k*D := by linarith only [hc1]
  have hnr := mul_le_mul_of_nonneg_right hn hr0
  have hc := mul_le_mul_of_nonneg_left hF2 (show 0≤F*((1-η)*p*k) by positivity)
  have he0 : 0≤p*e := mul_nonneg hp he
  have he1 : (1-η)*(p*e)≤κ/2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-η≤1 by linarith only [hη]) he0
    linarith only [hh,hdef]
  have hne := mul_le_mul_of_nonneg_left he1 hn0
  have hnκ := mul_le_mul_of_nonneg_right hn2 hκ
  nlinarith only [hnr,hc0,hc,hne,hnκ,hround]

/-- A ceiling in the source degree and a residual margin cost at most
three target-profile margins when the scalar witness weight is tiny. -/
lemma promotion_upper (D F E S w κ : ℝ) (hw : 0≤w) (hκ : 0≤κ)
    (hD : D≤F+1) (hE : E≤2*S) (hsmall : w≤S*κ) :
    w*D+E*κ≤w*F+3*S*κ := by
  have h1 := mul_le_mul_of_nonneg_left hD hw
  have h2 := mul_le_mul_of_nonneg_right hE hκ
  nlinarith only [h1,h2,hsmall]

end
end Erdos773.GreedyBatchCeilingErrors
end EndpointModule052
-- End GreedyBatchCeilingErrors.lean

-- Begin GreedyBatchProfileStep.lean
section EndpointModule053

/- The shrinking time step and coefficient slack for exponential profiles. -/
namespace Erdos773.GreedyBatchProfileStep
set_option maxHeartbeats 2500000
noncomputable section

def a (m : ℕ) : ℝ := 1-1000/(m:ℝ)^2
def A (m : ℕ) : ℝ := 3+6000/(m:ℝ)^2
def B (m : ℕ) : ℝ := 3+3000/(m:ℝ)^2
def step (m : ℕ) (t : ℝ) : ℝ := 1/((m:ℝ)^2*(1+t^2))

lemma coefficients (m : ℕ) (hm : 100≤ m) :
    3≤B m ∧ B m≤A m ∧ A m≤4 ∧ 0≤a m ∧ a m≤1 ∧
    1000/(m:ℝ)^2≤(1-1/(m:ℝ)^2)*A m-3*a m := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have h6 : (6000:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  have h1 : (1000:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  have hn1 : (0:ℝ)≤1000/(m:ℝ)^2 := by positivity
  have hn3 : (0:ℝ)≤3000/(m:ℝ)^2 := by positivity
  have h36 : (3000:ℝ)/(m:ℝ)^2≤6000/(m:ℝ)^2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  refine ⟨by dsimp [B]; linarith only [hn3],by dsimp [B,A]; linarith only [h36],
    by dsimp [A]; linarith only [h6],by dsimp [a]; linarith only [h1],
    by dsimp [a]; linarith only [hn1],?_⟩
  have he : ((1-1/(m:ℝ)^2)*A m-3*a m)-1000/(m:ℝ)^2=
      (7997*(m:ℝ)^2-6000)/(m:ℝ)^4 := by
    dsimp [A,a]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (by nlinarith only [hm2]) (by positivity)

lemma step_pos (m : ℕ) (t : ℝ) (hm : 0< m) : 0<step m t := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  unfold step
  positivity

lemma step_bound (m : ℕ) (t : ℝ) (hm : 1≤ m) : step m t≤1/(m:ℝ)^2 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  unfold step
  apply one_div_le_one_div_of_le (by positivity)
  have hh := mul_nonneg (sq_nonneg (m:ℝ)) (sq_nonneg t)
  nlinarith only [hh]

lemma step_le_time (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) : step m t≤t := by
  apply (step_bound m t hm).trans
  have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
  have hh : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hmR
  have he : (1:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hh
  exact he.trans ht

lemma step_squared (m : ℕ) (t : ℝ) (hm : 1≤ m) : (step m t)^2≤1/(m:ℝ)^4 := by
  have hh := pow_le_pow_left₀ (step_pos m t (by omega)).le (step_bound m t hm) 2
  convert hh using 1 <;> ring

lemma step_squared_time (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    (step m t)^2*t≤1/(m:ℝ)^4 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have ht2 : t≤(1+t^2)^2 := by nlinarith only [ht,sq_nonneg (t^2)]
  have hr : t/(1+t^2)^2≤1 := (div_le_one (by positivity)).mpr ht2
  calc
    _ = (1/(m:ℝ)^4)*(t/(1+t^2)^2) := by unfold step; field_simp
    _ ≤ (1/(m:ℝ)^4)*1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

lemma step_time_squared (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    1/(2*(m:ℝ)^2)≤step m t*t^2 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have he : step m t*t^2=t^2/((m:ℝ)^2*(1+t^2)) := by unfold step; ring
  rw [he]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)^2*(1+t^2))).mpr
  have he : 1/(2*(m:ℝ)^2)*((m:ℝ)^2*(1+t^2))=(1+t^2)/2 := by field_simp
  rw [he]
  nlinarith only [ht]

lemma step_gap (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    500/(m:ℝ)^4≤((1-1/(m:ℝ)^2)*A m-3*a m)*(step m t*t^2) := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hgap := (coefficients m hm).2.2.2.2.2
  have hx := step_time_squared m t (by omega) ht
  have hh := mul_le_mul hgap hx (by positivity : (0:ℝ)≤1/(2*(m:ℝ)^2))
    ((by positivity : (0:ℝ)≤1000/(m:ℝ)^2).trans hgap)
  convert hh using 1 <;> ring

end
end Erdos773.GreedyBatchProfileStep
end EndpointModule053
-- End GreedyBatchProfileStep.lean

-- Begin GreedyBatchProfiles.lean
section EndpointModule054

/- The actual ceiling profiles used by the proposed shrinking-batch
schedule, and their elementary size bounds. -/
namespace Erdos773.GreedyBatchProfiles
open GreedyBatchCertificate GreedyBatchProfileStep
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def f2 (m : ℕ) (d t : ℝ) : ℝ := A m*d*t^2
def f3 (m : ℕ) (d t : ℝ) : ℝ := B m*d^2*t
def f4 (d : ℝ) : ℝ := d^3
def fb (m : ℕ) (d : ℝ) : ℝ := (m:ℝ)^50*d

def probability (m : ℕ) (d t : ℝ) : ℝ := step m t/d

def nextD (m : ℕ) (d t : ℝ) : ℝ := d*Real.exp (-a m*GreedyBatchProfileLower.delta t (step m t))

def caps (m : ℕ) (d t : ℝ) (C P : ℕ) : Caps where
  D2 := ⌈f2 m d t⌉₊
  D3 := ⌈f3 m d t⌉₊
  D4 := ⌈f4 d⌉₊
  P := P
  C := C
  B := ⌈fb m d⌉₊

structure Range (m : ℕ) (d t : ℝ) (C P : ℕ) : Prop where
  large : 100≤ m
  d : (m:ℝ)^1000≤d
  t_one : 1≤t
  t_upper : t≤ m
  common : C≤ m^60
  common_one : 1≤C
  pair_one : 1≤P
  pair_upper : P≤ m

lemma Range.m_pos {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (0:ℝ)< m := by
  exact_mod_cast (show 0< m by have := h.large; omega)

lemma Range.m_one {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (1:ℝ)≤ m := by
  exact_mod_cast (show 1≤ m by have := h.large; omega)

lemma Range.power_le_d {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) (k : ℕ) (hk : k≤1000) :
    (m:ℝ)^k≤d := (pow_le_pow_right₀ h.m_one hk).trans h.d

lemma Range.m_le_d {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (m:ℝ)≤d := by
  simpa only [pow_one] using h.power_le_d 1 (by decide)

lemma Range.d_large {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (100:ℝ)≤d := by
  have hm : (100:ℝ)≤ m := by exact_mod_cast h.large
  exact hm.trans h.m_le_d

lemma Range.d_pos {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : 0<d := by
  have hh := h.d_large
  linarith only [hh]

lemma upper_coefficient (m : ℕ) (hm : 100≤ m) : A m≤15/4 ∧ B m≤15/4 := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hh : (6000:ℝ)/(m:ℝ)^2≤3/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm2])
  have hA : A m≤15/4 := by dsimp [A]; linarith only [hh]
  exact ⟨hA,(coefficients m hm).2.1.trans hA⟩

lemma ceil_bounds (x : ℝ) (hx : 0≤x) : x≤(⌈x⌉₊:ℝ) ∧ (⌈x⌉₊:ℝ)≤x+1 :=
  ⟨Nat.le_ceil x,(Nat.ceil_lt_add_one hx).le⟩

lemma profile_positive (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    0<f2 m d t ∧ 0<f3 m d t ∧ 0<f4 d ∧ 0<fb m d := by
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hm := h.m_pos
  have hB : (0:ℝ)<B m := lt_of_lt_of_le (by norm_num) (coefficients m h.large).1
  have hA : (0:ℝ)<A m := hB.trans_le (coefficients m h.large).2.1
  dsimp [f2,f3,f4,fb]
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma base_large (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    4≤d*t^2 ∧ 4≤d^2*t ∧ 1≤d^3 ∧ 1≤(m:ℝ)^50*d := by
  have hd := h.d_large
  have hd0 := h.d_pos.le
  have ht := h.t_one
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have h1 := mul_le_mul_of_nonneg_left ht2 hd0
  have h2 := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have h3 : (1:ℝ)≤d^3 := one_le_pow₀ (by linarith only [hd])
  have h4 := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 50) h.m_one) hd0
  refine ⟨by nlinarith only [hd,h1],by nlinarith only [hd,h2],h3,by nlinarith only [hd,h4]⟩

/-- Useful coarse bounds for all four natural ceilings. -/
theorem cap_bounds (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    3*d*t^2≤((caps m d t C P).D2:ℝ) ∧ ((caps m d t C P).D2:ℝ)≤4*d*t^2 ∧
    3*d^2*t≤((caps m d t C P).D3:ℝ) ∧ ((caps m d t C P).D3:ℝ)≤4*d^2*t ∧
    d^3≤((caps m d t C P).D4:ℝ) ∧ ((caps m d t C P).D4:ℝ)≤2*d^3 ∧
    (m:ℝ)^50*d≤((caps m d t C P).B:ℝ) ∧ ((caps m d t C P).B:ℝ)≤2*(m:ℝ)^50*d := by
  obtain ⟨hpos2,hpos3,hpos4,hposB⟩ := profile_positive m d t C P h
  obtain ⟨hl2,hu2⟩ := ceil_bounds (f2 m d t) hpos2.le
  obtain ⟨hl3,hu3⟩ := ceil_bounds (f3 m d t) hpos3.le
  obtain ⟨hl4,hu4⟩ := ceil_bounds (f4 d) hpos4.le
  obtain ⟨hlB,huB⟩ := ceil_bounds (fb m d) hposB.le
  obtain ⟨hb2,hb3,hb4,hbB⟩ := base_large m d t C P h
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hc := coefficients m h.large
  have hlA : 3≤A m := hc.1.trans hc.2.1
  obtain ⟨huA,huB'⟩ := upper_coefficient m h.large
  have hAlo := mul_le_mul_of_nonneg_right hlA (show 0≤d*t^2 by positivity)
  have hAhi := mul_le_mul_of_nonneg_right huA (show 0≤d*t^2 by positivity)
  have hBlo := mul_le_mul_of_nonneg_right hc.1 (show 0≤d^2*t by positivity)
  have hBhi := mul_le_mul_of_nonneg_right huB' (show 0≤d^2*t by positivity)
  dsimp [caps]
  dsimp [f2,f3,f4,fb] at hl2 hu2 hl3 hu3 hl4 hu4 hlB huB ⊢
  exact ⟨by nlinarith only [hl2,hAlo],by nlinarith only [hu2,hAhi,hb2],
    by nlinarith only [hl3,hBlo],by nlinarith only [hu3,hBhi,hb3],hl4,
    by linarith only [hu4,hb4],hlB,by nlinarith only [huB,hbB]⟩

lemma probability_pos (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) : 0<probability m d t :=
  div_pos (step_pos m t (by have := h.large; omega)) h.d_pos

lemma probability_mul (m : ℕ) (d t : ℝ) (hd : d≠0) : probability m d t*d=step m t := by
  exact div_mul_cancel₀ _ hd

lemma probability_le_step (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    probability m d t≤step m t := by
  have hd1 : 1≤d := by have := h.d_large; linarith
  exact div_le_self (step_pos m t (by have := h.large; omega)).le hd1

lemma probability_le_one (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) : probability m d t≤1 := by
  apply (probability_le_step m d t C P h).trans
  apply (step_bound m t (by have := h.large; omega)).trans
  exact (div_le_one (by have := h.m_pos; positivity)).mpr (one_le_pow₀ h.m_one)

end
end Erdos773.GreedyBatchProfiles
end EndpointModule054
-- End GreedyBatchProfiles.lean

-- Begin GreedyBatchProfileConditions.lean
section EndpointModule055

/- The coarse conditions for all scaled error estimates hold for the
actual ceiling profiles throughout the prescribed large-d regime. -/
namespace Erdos773.GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchScaledErrors
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma power_slack (m i j : ℕ) (c : ℝ) (hm : 100≤ m) (hc : c≤100) (hij : i<j) :
    c*(m:ℝ)^i≤(m:ℝ)^j := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  calc
    _ ≤ (m:ℝ)*(m:ℝ)^i := mul_le_mul_of_nonneg_right (hc.trans hmR) (by positivity)
    _ = (m:ℝ)^(i+1) := by ring
    _ ≤ _ := pow_le_pow_right₀ hm1 (by omega)

lemma step_weighted (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    step m t*t^2≤1/(m:ℝ)^2 ∧ step m t*t≤1/(m:ℝ)^2 ∧ step m t≤1 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hpos := (step_pos m t (by omega)).le
  have hsq : step m t*t^2≤1/(m:ℝ)^2 := by
    have hh : t^2/(1+t^2)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = (1/(m:ℝ)^2)*(t^2/(1+t^2)) := by unfold step; field_simp
      _ ≤ (1/(m:ℝ)^2)*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := mul_one _
  refine ⟨hsq,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (by nlinarith only [ht] : t≤t^2) hpos).trans hsq
  · apply (step_bound m t hm).trans
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)

structure WeightedBounds (c : Caps) (m : ℕ) (d t p h : ℝ) : Prop where
  graph : (c.D2:ℝ)*p≤4*h*t^2
  three_one : (c.D3:ℝ)*p≤4*d*t*h
  three_two : (c.D3:ℝ)*p^2≤4*t*h^2
  four_one : (c.D4:ℝ)*p≤2*d^2*h
  four_two : (c.D4:ℝ)*p^2≤2*d*h^2
  four_three : (c.D4:ℝ)*p^3≤2*h^3
  shared : (c.B:ℝ)*p≤2*(m:ℝ)^50*h

lemma weighted_bounds (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    WeightedBounds (caps m d t C P) m d t (probability m d t) (step m t) := by
  have hp := (probability_pos m d t C P h).le
  have he := probability_mul m d t (ne_of_gt h.d_pos)
  obtain ⟨h2l,h2,h3l,h3,h4l,h4,hBl,hB⟩ := cap_bounds m d t C P h
  constructor
  · calc
      _ ≤ (4*d*t^2)*probability m d t := mul_le_mul_of_nonneg_right h2 hp
      _ = 4*(probability m d t*d)*t^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (4*d^2*t)*probability m d t := mul_le_mul_of_nonneg_right h3 hp
      _ = 4*d*t*(probability m d t*d) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (4*d^2*t)*(probability m d t)^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = 4*t*(probability m d t*d)^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*probability m d t := mul_le_mul_of_nonneg_right h4 hp
      _ = 2*d^2*(probability m d t*d) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*(probability m d t)^2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = 2*d*(probability m d t*d)^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*(probability m d t)^3 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hp _)
      _ = 2*(probability m d t*d)^3 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*(m:ℝ)^50*d)*probability m d t := mul_le_mul_of_nonneg_right hB hp
      _ = 2*(m:ℝ)^50*(probability m d t*d) := by ring
      _ = _ := by rw [he]

/-- All old-family incidence ratios follow from the ceiling profile sizes. -/
lemma incidence_ratios (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    m^52≤(caps m d t C P).D2 ∧ m^52≤(caps m d t C P).D3 ∧
    m^30*C≤(caps m d t C P).D2 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).D3 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).D4 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).B := by
  obtain ⟨h2,h2u,h3,h3u,h4,h4u,hB,hBu⟩ := cap_bounds m d t C P h
  have hd := h.d_pos.le
  have hd1 : 1≤d := by have := h.d_large; linarith
  have ht := h.t_one
  have hm := h.m_pos.le
  have ht0 : 0≤t := by linarith only [ht]
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have hdt := mul_le_mul_of_nonneg_left ht2 hd
  have hd2t := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hd2 : d≤d^2 := by nlinarith only [hd1]
  have hD2 : d≤((caps m d t C P).D2:ℝ) := by nlinarith only [h2,hdt,hd]
  have hD3 : d^2≤((caps m d t C P).D3:ℝ) := by nlinarith only [h3,hd2t,sq_nonneg d]
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have htupper : t^2≤(m:ℝ)^2 := pow_le_pow_left₀ ht0 h.t_upper 2
  have hDP : ((caps m d t C P).D2:ℝ)*P≤4*d*(m:ℝ)^3 := by
    have hh := mul_le_mul h2u hP (Nat.cast_nonneg P) (show 0≤4*d*t^2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left htupper (show 0≤4*d*m by positivity)
    nlinarith only [hh,hh']
  have hsmall : 4*(m:ℝ)^33≤d :=
    (power_slack m 33 34 4 h.large (by norm_num) (by decide)).trans (h.power_le_d 34 (by decide))
  have hmass : (m:ℝ)^30*((caps m d t C P).D2:ℝ)*P≤d^2 := by
    have hh := mul_le_mul_of_nonneg_left hDP (pow_nonneg hm 30)
    have hh' := mul_le_mul_of_nonneg_left hsmall hd
    nlinarith only [hh,hh']
  have hmassB : (m:ℝ)^30*((caps m d t C P).D2:ℝ)*P≤(m:ℝ)^50*d := by
    have hh := mul_le_mul_of_nonneg_left hDP (pow_nonneg hm 30)
    have hh' := mul_le_mul_of_nonneg_right (power_slack m 33 50 4 h.large (by norm_num) (by decide)) hd
    nlinarith only [hh,hh']
  have hmassC : (m:ℝ)^30*C≤d := by
    have hC : (C:ℝ)≤(m:ℝ)^60 := by exact_mod_cast h.common
    have hh := mul_le_mul_of_nonneg_left hC (pow_nonneg hm 30)
    have hd90 := h.power_le_d 90 (by decide)
    nlinarith only [hh,hd90]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast (h.power_le_d 52 (by decide)).trans hD2
  · exact_mod_cast (h.power_le_d 52 (by decide)).trans (hd2.trans hD3)
  · exact_mod_cast hmassC.trans hD2
  · rw [← Nat.mul_assoc]
    exact_mod_cast hmass.trans hD3
  · rw [← Nat.mul_assoc]
    have hh : d^2≤d^3 := pow_le_pow_right₀ hd1 (by decide)
    exact_mod_cast hmass.trans (hh.trans h4)
  · rw [← Nat.mul_assoc]
    exact_mod_cast hmassB.trans hB

lemma graph_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ((caps m d t C P).D2:ℝ)*probability m d t≤4/(m:ℝ)^2 := by
  have hw := (weighted_bounds m d t C P h).graph
  have hs := (step_weighted m t (by have := h.large; omega) h.t_one).1
  ring_nf at hw hs ⊢
  linarith only [hw,hs]

lemma base_lower (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    d≤((caps m d t C P).D2:ℝ) ∧ d^2≤((caps m d t C P).D3:ℝ) := by
  obtain ⟨h2,_,h3,_⟩ := cap_bounds m d t C P h
  have hd := h.d_pos.le
  have ht := h.t_one
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have hdt := mul_le_mul_of_nonneg_left ht2 hd
  have hd2t := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  exact ⟨by nlinarith only [h2,hdt,hd],by nlinarith only [h3,hd2t,sq_nonneg d]⟩

lemma promotion_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    2*((caps m d t C P).D3:ℝ)*probability m d t≤10*(caps m d t C P).D2/(m:ℝ)^2 ∧
    3*((caps m d t C P).D4:ℝ)*probability m d t≤10*(caps m d t C P).D3/(m:ℝ)^2 ∧
    3*((caps m d t C P).D4:ℝ)*(probability m d t)^2≤10*(caps m d t C P).D2/(m:ℝ)^2 := by
  have hw := weighted_bounds m d t C P h
  have hs := step_bound m t (by have := h.large; omega)
  have hs1 := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs0 := (step_pos m t (by have := h.large; omega)).le
  have hs2 : (step m t)^2≤1/(m:ℝ)^2 := by
    have hh : (step m t)^2≤step m t := by nlinarith only [hs0,hs1]
    exact hh.trans hs
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hdt : d*t≤d*t^2 := mul_le_mul_of_nonneg_left (by have := h.t_one; nlinarith : t≤t^2) hd
  have h2 := (cap_bounds m d t C P h).1
  obtain ⟨hb2,hb3⟩ := base_lower m d t C P h
  have hcoef2 : 8*d*t≤10*((caps m d t C P).D2:ℝ) := by
    have hh : 0≤d*t := mul_nonneg hd ht
    nlinarith only [h2,hdt,hh]
  have hcoef3 : 6*d^2≤10*((caps m d t C P).D3:ℝ) := by nlinarith only [hb3,sq_nonneg d]
  have hcoef4 : 6*d≤10*((caps m d t C P).D2:ℝ) := by nlinarith only [hb2,hd]
  have hdiv2 := div_le_div_of_nonneg_right hcoef2 (sq_nonneg (m:ℝ))
  have hdiv3 := div_le_div_of_nonneg_right hcoef3 (sq_nonneg (m:ℝ))
  have hdiv4 := div_le_div_of_nonneg_right hcoef4 (sq_nonneg (m:ℝ))
  have hstep2 := mul_le_mul_of_nonneg_left hs (show 0≤8*d*t by positivity)
  have hstep3 := mul_le_mul_of_nonneg_left hs (show 0≤6*d^2 by positivity)
  have hstep4 := mul_le_mul_of_nonneg_left hs2 (show 0≤6*d by positivity)
  have hw2 := hw.three_one
  have hw3 := hw.four_one
  have hw4 := hw.four_two
  ring_nf at hstep2 hstep3 hstep4 hdiv2 hdiv3 hdiv4 hw2 hw3 hw4 ⊢
  exact ⟨by linarith only [hw2,hstep2,hdiv2],by linarith only [hw3,hstep3,hdiv3],
    by linarith only [hw4,hstep4,hdiv4]⟩

lemma shared_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ((caps m d t C P).D3:ℝ)*P*probability m d t≤(m:ℝ)*d/4 ∧
    3*((caps m d t C P).D4:ℝ)*P*(probability m d t)^2≤(m:ℝ)*d/4 ∧
    (m:ℝ)^46≤(m:ℝ)*d/4 := by
  have hw := weighted_bounds m d t C P h
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have hm0 := h.m_pos
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have h1 := mul_le_mul hw.three_one hP (Nat.cast_nonneg P) (show 0≤4*d*t*step m t by positivity)
  have h2 := mul_le_mul hw.four_two hP (Nat.cast_nonneg P) (show 0≤2*d*(step m t)^2 by positivity)
  have hst := (step_weighted m t (by have := h.large; omega) h.t_one).2.1
  have hs2 := step_squared m t (by have := h.large; omega)
  have ht1 := mul_le_mul_of_nonneg_left hst (show 0≤4*(m:ℝ)*d by positivity)
  have ht2 := mul_le_mul_of_nonneg_left hs2 (show 0≤6*(m:ℝ)*d by positivity)
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hm4 : (10000:ℝ)≤(m:ℝ)^4 := hm2.trans (pow_le_pow_right₀ h.m_one (by decide))
  have hc1 : (4:ℝ)/(m:ℝ)^2≤1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm2])
  have hc2 : (6:ℝ)/(m:ℝ)^4≤1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm4])
  have hfinal1 := mul_le_mul_of_nonneg_left hc1 (show 0≤(m:ℝ)*d by positivity)
  have hfinal2 := mul_le_mul_of_nonneg_left hc2 (show 0≤(m:ℝ)*d by positivity)
  have hsmall : 4*(m:ℝ)^45≤d :=
    (power_slack m 45 46 4 h.large (by norm_num) (by decide)).trans (h.power_le_d 46 (by decide))
  have hfinal3 := mul_le_mul_of_nonneg_left hsmall hm0.le
  ring_nf at h1 h2 ht1 ht2 hfinal1 hfinal2 hfinal3 ⊢
  exact ⟨by linarith only [h1,ht1,hfinal1],by linarith only [h2,ht2,hfinal2],by linarith only [hfinal3]⟩

lemma common_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ∀ r∈Finset.Icc 1 4,
      (GreedyBatchCommonBudgets.masses (caps m d t C P).D2 (caps m d t C P).D3
        (caps m d t C P).D4 P (caps m d t C P).B r:ℝ)*(probability m d t)^r≤(m:ℝ)^52/4 := by
  let c := caps m d t C P
  let p := probability m d t
  have hp : 0≤p := (probability_pos m d t C P h).le
  have hp1 : p≤1 := probability_le_one m d t C P h
  have hm := h.m_pos
  have hm1 := h.m_one
  have hs := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs0 := (step_pos m t (by have := h.large; omega)).le
  have ht : 0≤t := by have := h.t_one; linarith
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have hw := weighted_bounds m d t C P h
  have hload := graph_load m d t C P h
  have h4div : (4:ℝ)/(m:ℝ)^2≤4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hm1
    linarith only [hh]
  have h4div4 : (4:ℝ)/(m:ℝ)^4≤4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (1:ℝ)≤(m:ℝ)^4 := one_le_pow₀ hm1
    linarith only [hh]
  have h2p : (c.D2:ℝ)*p≤4 := hload.trans h4div
  have h2p2 : (c.D2:ℝ)*p^2≤4 := by
    have hh := mul_le_mul h2p hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h2p3 : (c.D2:ℝ)*p^3≤4 := by
    have hh := mul_le_mul h2p2 hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h3p2 : (c.D3:ℝ)*p^2≤4 := by
    have hh := hw.three_two
    have ht := step_squared_time m t (by have := h.large; omega) h.t_one
    change (c.D3:ℝ)*p^2≤_ at hh
    ring_nf at hh ht h4div4 ⊢
    linarith only [hh,ht,h4div4]
  have h3p3 : (c.D3:ℝ)*p^3≤4 := by
    have hh := mul_le_mul h3p2 hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h4p3 : (c.D4:ℝ)*p^3≤2 := by
    have hh := hw.four_three
    have ht := pow_le_one₀ hs0 hs (n := 3)
    change (c.D4:ℝ)*p^3≤_ at hh
    nlinarith only [hh,ht]
  have hBp : (c.B:ℝ)*p≤2*(m:ℝ)^48 := by
    have hh := hw.shared
    have hs := mul_le_mul_of_nonneg_left (step_bound m t (by have := h.large; omega))
      (show (0:ℝ)≤2*(m:ℝ)^50 by positivity)
    have he : 2*(m:ℝ)^50*(1/(m:ℝ)^2)=2*(m:ℝ)^48 := by field_simp
    rw [he] at hs
    exact hh.trans hs
  have hmass1 : ((2*c.D2*P+2*c.B:ℕ):ℝ)*p≤(m:ℝ)^50 := by
    have hh := mul_le_mul h2p hP (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4)
    have hmpow : (m:ℝ)≤(m:ℝ)^48 := by simpa only [pow_one] using pow_le_pow_right₀ hm1 (by decide : 1≤48)
    have hslack := power_slack m 48 50 12 h.large (by norm_num) (by decide)
    push_cast
    nlinarith only [hh,hBp,hmpow,hslack]
  have hmass2 : ((4*(c.D2+c.D3)*P:ℕ):ℝ)*p^2≤(m:ℝ)^50 := by
    have hh := mul_le_mul (add_le_add h2p2 h3p2) hP (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4+4)
    have hslack := power_slack m 1 50 32 h.large (by norm_num) (by decide)
    push_cast
    norm_num only [pow_one] at hslack
    nlinarith only [hh,hslack]
  have hmass3 : ((3*(c.D2+c.D3+c.D4)*P:ℕ):ℝ)*p^3≤(m:ℝ)^50 := by
    have hh := mul_le_mul (add_le_add (add_le_add h2p3 h3p3) h4p3) hP
      (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4+4+2)
    have hslack := power_slack m 1 50 30 h.large (by norm_num) (by decide)
    push_cast
    norm_num only [pow_one] at hslack
    nlinarith only [hh,hslack]
  have hmass4 : ((3*(c.D2+c.D3+c.D4)*P:ℕ):ℝ)*p^4≤(m:ℝ)^50 := by
    have hh := mul_le_mul hmass3 hp1 hp (by positivity : (0:ℝ)≤(m:ℝ)^50)
    nlinarith only [hh]
  have hquarter : (m:ℝ)^50≤(m:ℝ)^52/4 := by
    have hh := power_slack m 50 52 4 h.large (by norm_num) (by decide)
    linarith only [hh]
  intro r hr
  have hsmall : (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 P c.B r:ℝ)*p^r≤(m:ℝ)^50 := by
    obtain ⟨hr1,hr4⟩ := Finset.mem_Icc.mp hr
    interval_cases r
    · simpa [GreedyBatchCommonBudgets.masses] using hmass1
    · simpa [GreedyBatchCommonBudgets.masses] using hmass2
    · simpa [GreedyBatchCommonBudgets.masses] using hmass3
    · simpa [GreedyBatchCommonBudgets.masses] using hmass4
  exact hsmall.trans hquarter

/-- The actual ceiling profiles supply every coarse condition needed for
all fourteen exp(-m^7) local estimates. -/
theorem conditions (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    Conditions (caps m d t C P) m (probability m d t) d := by
  obtain ⟨hd2,hd3,ho2,ho3,ho4,hoB⟩ := incidence_ratios m d t C P h
  obtain ⟨hp31,hp41,hp42⟩ := promotion_means m d t C P h
  obtain ⟨hs34,hs44,hsE⟩ := shared_means m d t C P h
  have hD2 : 0<(caps m d t C P).D2 := by
    exact_mod_cast h.d_pos.trans_le (base_lower m d t C P h).1
  have hP : 0<P := by have := h.pair_one; omega
  exact {
    large := h.large
    p_nonneg := (probability_pos m d t C P h).le
    p_le_one := probability_le_one m d t C P h
    common_pos := by have := h.common_one; change 0<C; omega
    dp_pos := Nat.mul_pos hD2 hP
    pair := h.pair_upper
    degree2 := hd2
    degree3 := hd3
    old2 := ho2
    old3 := ho3
    old4 := ho4
    oldShared := hoB
    graph_load := graph_load m d t C P h
    promotion31 := hp31
    promotion41 := hp41
    promotion42 := hp42
    shared34 := hs34
    shared44 := hs44
    shared_overlap := hsE
    common := common_means m d t C P h }

end
end Erdos773.GreedyBatchProfileConditions
end EndpointModule055
-- End GreedyBatchProfileConditions.lean

-- Begin GreedyBatchFutureProfiles.lean
section EndpointModule056

/- The real future profiles dominate all ideal mixed-rank updates with
250 relative rounding/error margins. -/
namespace Erdos773.GreedyBatchFutureProfiles
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileLower
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma normalized_gap (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    500*(1/(m:ℝ)^4)≤((1-1/(m:ℝ)^2)*A m-3*a m)*(step m t*t^2) := by
  convert step_gap m t hm ht using 1 <;> ring

lemma normalized_square (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    (step m t/t)^2≤1/(m:ℝ)^4 := by
  have hs := (step_pos m t (by omega)).le
  have ht0 : 0≤t := by linarith only [ht]
  have hh := div_le_self hs ht
  exact (pow_le_pow_left₀ (div_nonneg hs ht0) hh 2).trans (step_squared m t hm)

/-- The direct rank-four-to-two promotion is retained. -/
theorem two (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f2 m d t*(1-(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+
      2*probability m d t*f3 m d t+3*(probability m d t)^2*f4 d+
      250*f2 m d t/(m:ℝ)^4≤f2 m (nextD m d t) (t+step m t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hA : 3≤A m := hB.trans hBA
  have hA0 : 0≤A m := by linarith only [hA]
  have hi := ideal_two (A m) (B m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (step m t/t)
    ((step m t/t)^2) (1/(m:ℝ)^4) hA hBA (div_nonneg hs ht.le) (by positivity)
    (normalized_square m t (by have := h.large; omega) h.t_one) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d*t^2 by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_two t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤A m*d by positivity)
  calc
    _ ≤ A m*d*(t^2+2*t*step m t-3*a m*t^4*step m t-25*t^2*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f3,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      convert hl using 1 <;> dsimp [f2,nextD] <;> ring

/-- The leading rank-four-to-three promotion is retained. -/
theorem three (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f3 m d t*(1-2*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+
      3*probability m d t*f4 d+250*f3 m d t/(m:ℝ)^4≤f3 m (nextD m d t) (t+step m t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hB0 : 0≤B m := by linarith only [hB]
  have hi := ideal_three (A m) (B m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (step m t/t)
    (1/(m:ℝ)^4) hB (div_nonneg hs ht.le) (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d^2*t by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_three t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤B m*d^2 by positivity)
  have he : (Real.exp (-a m*delta t (step m t)))^2=Real.exp (-2*a m*delta t (step m t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ B m*d^2*(t+step m t-6*a m*t^3*step m t-22*t*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f3,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      dsimp [f3,nextD]
      rw [mul_pow,he]
      convert hl using 1 <;> ring

theorem four (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f4 d*(1-3*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+250*f4 d/(m:ℝ)^4≤f4 (nextD m d t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hi := ideal_four (A m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (1/(m:ℝ)^4)
    (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d^3 by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_four t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤d^3 by positivity)
  have he : (Real.exp (-a m*delta t (step m t)))^3=Real.exp (-3*a m*delta t (step m t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ d^3*(1-9*a m*t^2*step m t-12*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      dsimp [f4,nextD]
      rw [mul_pow,he]
      convert hl using 1 <;> ring

theorem shared (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    fb m d*(1-2*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+250*fb m d/(m:ℝ)^4≤fb m (nextD m d t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hi := ideal_shared (A m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (1/(m:ℝ)^4)
    ha (by positivity) (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤fb m d by dsimp [fb]; positivity)
  have hl := mul_le_mul_of_nonneg_left
    (GreedyBatchProfileLower.shared t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤fb m d by dsimp [fb]; positivity)
  calc
    _ ≤ fb m d*(1-3*a m*t^2*step m t-4*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,fb,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      convert hl using 1 <;> dsimp [fb,nextD] <;> ring

end
end Erdos773.GreedyBatchFutureProfiles
end EndpointModule056
-- End GreedyBatchFutureProfiles.lean

-- Begin GreedyBatchProfileFits.lean
section EndpointModule057

/- Complete deterministic Fits verification for the actual ceiling profiles. -/
namespace Erdos773.GreedyBatchProfileFits
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchScaledErrors GreedyBatchScalarTails
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma profile_large (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    3*(m:ℝ)^4≤f2 m d t ∧ 3*(m:ℝ)^4≤f3 m d t ∧
    3*(m:ℝ)^4≤f4 d ∧ 3*(m:ℝ)^4≤fb m d := by
  have hm := h.m_pos.le
  have hd := h.d_pos.le
  have hd1 : 1≤d := by have := h.d_large; linarith
  have ht := h.t_one
  have hdt := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) ht) hd
  have hdt3 := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hd2 : d≤d^2 := by nlinarith only [hd1]
  have hd3 : d≤d^3 := by simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1≤3)
  have hmd := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 50) h.m_one) hd
  have hc := coefficients m h.large
  have hA := mul_le_mul_of_nonneg_right (hc.1.trans hc.2.1) (show 0≤d*t^2 by positivity)
  have ht0 : 0≤t := by linarith only [ht]
  have hB := mul_le_mul_of_nonneg_right hc.1 (show 0≤d^2*t by positivity)
  have hsmall : 3*(m:ℝ)^4≤d :=
    (power_slack m 4 5 3 h.large (by norm_num) (by decide)).trans (h.power_le_d 5 (by decide))
  dsimp [f2,f3,f4,fb]
  exact ⟨by nlinarith only [hsmall,hA,hdt,hd],by nlinarith only [hsmall,hB,hdt3,hd2,sq_nonneg d],
    hsmall.trans hd3,by nlinarith only [hsmall,hmd]⟩

/-- Every old killing-set deficit is negligible at the large-d scale. -/
lemma deficit_bound (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    probability m d t*(3*(C+1):ℕ)≤1/(2*(m:ℝ)^4) := by
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hC : (C:ℝ)≤(m:ℝ)^60 := by exact_mod_cast h.common
  have hpow : (1:ℝ)≤(m:ℝ)^60 := one_le_pow₀ h.m_one
  have hC1 : (C:ℝ)+1≤2*(m:ℝ)^60 := by linarith only [hC,hpow]
  have hh := mul_le_mul_of_nonneg_right hC1 (show 0≤6*(m:ℝ)^2 by positivity)
  have hslack : 12*(m:ℝ)^62≤d :=
    (power_slack m 62 63 12 h.large (by norm_num) (by decide)).trans (h.power_le_d 63 (by decide))
  have hsmall : 6*((C:ℝ)+1)*(m:ℝ)^2≤d := by nlinarith only [hh,hslack]
  have hp' := mul_le_mul_of_nonneg_right hsmall hp
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have hstep : step m t*(m:ℝ)^2≤1 :=
    (le_div_iff₀ (by positivity)).mp (step_bound m t (by have := h.large; omega))
  have hp'' := mul_le_mul_of_nonneg_right hp' (sq_nonneg (m:ℝ))
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(m:ℝ)^4)).mpr
  push_cast
  have he : d*probability m d t*(m:ℝ)^2=step m t*(m:ℝ)^2 := by rw [mul_comm d,hpd]
  rw [he] at hp''
  nlinarith only [hp'',hstep]

lemma ceil_small (m : ℕ) (F : ℝ) (hm : 1≤ m) (hF : 3*(m:ℝ)^4≤F) :
    0≤F ∧ (⌈F⌉₊:ℝ)≤F+1 ∧ (⌈F⌉₊:ℝ)≤2*F ∧ 3≤F/(m:ℝ)^4 := by
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hm1]
  have hpow : (1:ℝ)≤(m:ℝ)^4 := one_le_pow₀ hm1
  have hF0 : 0≤F := by nlinarith only [hF,hpow]
  have hc := (ceil_bounds F hF0).2
  exact ⟨hF0,hc,by linarith only [hc,hF,hpow],(le_div_iff₀ (by positivity)).mpr (by linarith only [hF])⟩

lemma old_bound (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (F : ℝ) (hF : 3*(m:ℝ)^4≤F) (k e : ℕ) (hk : k≤3) (he : e≤3*(C+1)) :
    (⌈F⌉₊:ℝ)*(1-(1-1/(m:ℝ)^2)*probability m d t*((k*(caps m d t C P).D2:ℕ)-(e:ℕ):ℝ))+
      100*(⌈F⌉₊:ℝ)/(m:ℝ)^4≤
      F*(1-(1-1/(m:ℝ)^2)*probability m d t*k*f2 m d t)+202*F/(m:ℝ)^4 := by
  obtain ⟨hF0,hceil,hceil2,hround⟩ := ceil_small m F (by have := h.large; omega) hF
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hprob := probability_range _ m _ d (conditions m d t C P h)
  have hgl := graph_load m d t C P h
  have hkR : (k:ℝ)≤3 := by exact_mod_cast hk
  have hload : (k:ℝ)*(caps m d t C P).D2*probability m d t≤1 := by
    have hh := mul_le_mul_of_nonneg_right hkR
      (show 0≤((caps m d t C P).D2:ℝ)*probability m d t by positivity)
    have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
    have h12 : (12:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith only [hmR])
    ring_nf at hh hgl h12 ⊢
    nlinarith only [hh,hgl,h12]
  have hdef : probability m d t*(e:ℝ)≤(1/(m:ℝ)^4)/2 := by
    have hh := mul_le_mul_of_nonneg_left (show (e:ℝ)≤(3*(C+1):ℕ) by exact_mod_cast he) hp
    have hd := deficit_bound m d t C P h
    convert hh.trans hd using 1 <;> ring
  have ht := GreedyBatchCeilingErrors.old_upper (⌈F⌉₊:ℝ) F (caps m d t C P).D2 (f2 m d t)
    k e (probability m d t) (1/(m:ℝ)^2) (1/(m:ℝ)^4)
    (Nat.cast_nonneg _) hF0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp
    hprob.eta_nonneg hprob.eta_le_one (by positivity) hceil hceil2
    (by ring_nf at hround ⊢; linarith only [hround]) (Nat.le_ceil _) hload hdef
  convert ht using 1 <;> push_cast <;> ring

lemma promotion_bound (m : ℕ) (F S w : ℝ) (hm : 1≤ m) (hF : 0≤F) (hS : 3*(m:ℝ)^4≤S)
    (hw : 0≤w) (hw3 : w≤3) :
    w*(⌈F⌉₊:ℝ)+(⌈S⌉₊:ℝ)/(m:ℝ)^4≤w*F+3*S/(m:ℝ)^4 := by
  obtain ⟨hS0,hceil,hceil2,hround⟩ := ceil_small m S hm hS
  have hsource := (ceil_bounds F hF).2
  have hh := GreedyBatchCeilingErrors.promotion_upper (⌈F⌉₊:ℝ) F (⌈S⌉₊:ℝ) S w (1/(m:ℝ)^4)
    hw (by positivity) hsource hceil2 (by ring_nf at hround ⊢; linarith only [hw3,hround])
  convert hh using 1 <;> ring

lemma shared_margin (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    (m:ℝ)*d≤fb m d/(m:ℝ)^4 := by
  have hm := h.m_pos
  have hd := h.d_pos.le
  have hp : (m:ℝ)≤(m:ℝ)^46 := by simpa only [pow_one] using pow_le_pow_right₀ h.m_one (by decide : 1≤46)
  have hh := mul_le_mul_of_nonneg_right hp hd
  have he : fb m d/(m:ℝ)^4=(m:ℝ)^46*d := by unfold fb; field_simp
  rwa [he]

/-- Every deterministic target inequality holds for the next ceiling
profiles. This does not assert that the next d is still above m^1000. -/
theorem fits (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    Fits (caps m d t C P) (margins (caps m d t C P) m (probability m d t) d)
      (probability m d t) (1/(m:ℝ)^2)
      (caps m (nextD m d t) (t+step m t) (C+4*m^52) P) := by
  have hm := h.m_pos
  have hp := (probability_pos m d t C P h).le
  have hp1 := probability_le_one m d t C P h
  have hp2 := pow_le_one₀ hp hp1 (n := 2)
  obtain ⟨hF2,hF3,hF4,hFB⟩ := profile_large m d t C P h
  obtain ⟨hpos2,hpos3,hpos4,hposB⟩ := profile_positive m d t C P h
  have ho2 := old_bound m d t C P h (f2 m d t) hF2 1 1 (by decide) (by omega)
  have ho3 := old_bound m d t C P h (f3 m d t) hF3 2 (2+C) (by decide) (by omega)
  have ho4 := old_bound m d t C P h (f4 d) hF4 3 (3+3*C) (by decide) (by omega)
  have hoB := old_bound m d t C P h (fb m d) hFB 2 (2+C) (by decide) (by omega)
  have hp31 := promotion_bound m (f3 m d t) (f2 m d t) (2*probability m d t)
    (by have := h.large; omega) hpos3.le hF2 (by positivity) (by linarith only [hp1])
  have hp41 := promotion_bound m (f4 d) (f3 m d t) (3*probability m d t)
    (by have := h.large; omega) hpos4.le hF3 (by positivity) (by linarith only [hp1])
  have hp42 := promotion_bound m (f4 d) (f2 m d t) (3*(probability m d t)^2)
    (by have := h.large; omega) hpos4.le hF2 (by positivity) (by linarith only [hp2])
  have hnext2 := (GreedyBatchFutureProfiles.two m d t C P h).trans (Nat.le_ceil _)
  have hnext3 := (GreedyBatchFutureProfiles.three m d t C P h).trans (Nat.le_ceil _)
  have hnext4 := (GreedyBatchFutureProfiles.four m d t C P h).trans (Nat.le_ceil _)
  have hnextB := (GreedyBatchFutureProfiles.shared m d t C P h).trans (Nat.le_ceil _)
  have hmargin := shared_margin m d t C P h
  have hn2 : 0≤f2 m d t/(m:ℝ)^4 := by positivity
  have hn3 : 0≤f3 m d t/(m:ℝ)^4 := by positivity
  have hn4 : 0≤f4 d/(m:ℝ)^4 := by positivity
  have hnB : 0≤fb m d/(m:ℝ)^4 := by positivity
  dsimp only [caps] at ho2 ho3 ho4 hoB
  constructor
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho2 ⊢
    ring_nf at ho2 hp31 hp42 hnext2 hn2 ⊢
    nlinarith only [ho2,hp31,hp42,hnext2,hn2]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho3 ⊢
    ring_nf at ho3 hp41 hnext3 hn3 ⊢
    nlinarith only [ho3,hp41,hnext3,hn3]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at ho4 ⊢
    ring_nf at ho4 hnext4 hn4 ⊢
    nlinarith only [ho4,hnext4,hn4]
  · dsimp [margins,caps,Caps.degree,retention]
    norm_num at hoB ⊢
    ring_nf at hoB hnextB hmargin hnB ⊢
    nlinarith only [hoB,hnextB,hmargin,hnB]
  · dsimp [margins,caps]
    have hI : Finset.Icc 1 4=({1,2,3,4}:Finset ℕ) := by decide
    rw [hI]
    simp

end
end Erdos773.GreedyBatchProfileFits
end EndpointModule057
-- End GreedyBatchProfileFits.lean

-- Begin GreedyBatchRateGeometry.lean
section EndpointModule058

/- Load and exponential-growth estimates for the continuation reward.
The leading load coefficient is retained to within O(m^-2). -/
namespace Erdos773.GreedyBatchRateGeometry
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchReward
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def growth (m : ℕ) (t : ℝ) : ℝ := a m*GreedyBatchProfileLower.delta t (step m t)

lemma precise_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    load (caps m d t C P) (probability m d t)≤
      A m*step m t*t^2+B m*t*(step m t)^2+(step m t)^3+
      probability m d t+(probability m d t)^2+(probability m d t)^3 := by
  have hp := (probability_pos m d t C P h).le
  obtain ⟨hf2,hf3,hf4,hfB⟩ := profile_positive m d t C P h
  have h2 := mul_le_mul_of_nonneg_right (ceil_bounds (f2 m d t) hf2.le).2 hp
  have h3 := mul_le_mul_of_nonneg_right (ceil_bounds (f3 m d t) hf3.le).2 (sq_nonneg (probability m d t))
  have h4 := mul_le_mul_of_nonneg_right (ceil_bounds (f4 d) hf4.le).2 (pow_nonneg hp 3)
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have he2 : f2 m d t*probability m d t=A m*step m t*t^2 := by
    calc
      _ = A m*(probability m d t*d)*t^2 := by unfold f2; ring
      _ = _ := by rw [hpd]
  have he3 : f3 m d t*(probability m d t)^2=B m*t*(step m t)^2 := by
    calc
      _ = B m*t*(probability m d t*d)^2 := by unfold f3; ring
      _ = _ := by rw [hpd]
  have he4 : f4 d*(probability m d t)^3=(step m t)^3 := by
    calc
      _ = (probability m d t*d)^3 := by unfold f4; ring
      _ = _ := by rw [hpd]
  dsimp [load,caps]
  nlinarith only [h2,h3,h4,he2,he3,he4]

lemma coarse_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    load (caps m d t C P) (probability m d t)≤10*step m t*t^2 ∧
    probability m d t+load (caps m d t C P) (probability m d t)≤20*step m t*t^2 ∧
    load (caps m d t C P) (probability m d t)≤10/(m:ℝ)^2 ∧
    probability m d t+load (caps m d t C P) (probability m d t)≤1 := by
  have hm := h.m_pos
  have ht : 0≤t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hh := step_le_time m t (by have := h.large; omega) h.t_one
  have hw := weighted_bounds m d t C P h
  have h21 := mul_le_mul_of_nonneg_left hh (show 0≤step m t*t by positivity)
  have h31 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have hw2 := hw.graph
  have hw3 := hw.three_two
  have hw4 := hw.four_three
  have hz : load (caps m d t C P) (probability m d t)≤10*step m t*t^2 := by
    dsimp [load]
    nlinarith only [hw2,hw3,hw4,h21,h31]
  have hx0 : 0≤step m t*t^2 := by positivity
  have hpt := probability_le_step m d t C P h
  have htx := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h.t_one) hs
  have hx : probability m d t+load (caps m d t C P) (probability m d t)≤20*step m t*t^2 := by
    nlinarith only [hz,hpt,htx,hx0]
  have hsx := (step_weighted m t (by have := h.large; omega) h.t_one).1
  have hz' : load (caps m d t C P) (probability m d t)≤10/(m:ℝ)^2 := by
    ring_nf at hz hsx ⊢
    linarith only [hz,hsx]
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have h20 : (20:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith only [hmR])
  refine ⟨hz,hx,hz',?_⟩
  ring_nf at hx hsx h20 ⊢
  linarith only [hx,hsx,h20]

lemma growth_bounds (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    0≤growth m t ∧ 3*a m*step m t*t^2≤growth m t ∧ growth m t≤7*step m t*t^2 := by
  have ht0 : 0≤t := by linarith only [ht]
  have hs := (step_pos m t (by omega)).le
  have hst := step_le_time m t (by omega) ht
  obtain ⟨hB,hBA,hA4,ha,ha1,hgap⟩ := coefficients m hm
  have hD0 := GreedyBatchProfileLower.delta_nonneg t (step m t) ht0 hs
  have hDlo : 3*t^2*step m t≤GreedyBatchProfileLower.delta t (step m t) := by
    have h1 := mul_nonneg ht0 (sq_nonneg (step m t))
    have h2 := pow_nonneg hs 3
    dsimp [GreedyBatchProfileLower.delta]
    nlinarith only [h1,h2]
  have hDup := (GreedyBatchProfileLower.delta_error t (step m t) ((step m t)^2*t) ht0 hs hst le_rfl).1
  have ht2 := mul_le_mul_of_nonneg_left hst (show 0≤step m t*t by positivity)
  have h1 := mul_le_mul_of_nonneg_left hDlo ha
  have h2 := mul_le_mul_of_nonneg_right ha1 hD0
  dsimp [growth]
  exact ⟨mul_nonneg ha hD0,by nlinarith only [h1],by nlinarith only [h2,hDup,ht2]⟩

lemma growth_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    growth m t*(probability m d t+load (caps m d t C P) (probability m d t))≤
      140*step m t*t^2/(m:ℝ)^2 := by
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have hz0 : 0≤load (caps m d t C P) (probability m d t) := by unfold load; positivity
  have hu := (growth_bounds m t h.large h.t_one).2.2
  have hz := (coarse_load m d t C P h).2.1
  have hh := mul_le_mul hu hz (add_nonneg hp hz0) (show 0≤7*step m t*t^2 by positivity)
  have hsx := (step_weighted m t (by have := h.large; omega) h.t_one).1
  have hx := mul_le_mul_of_nonneg_right hsx (show 0≤step m t*t^2 by positivity)
  ring_nf at hh hx ⊢
  nlinarith only [hh,hx]

lemma small_terms (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    B m*t*(step m t)^2≤4*step m t*t^2/(m:ℝ)^2 ∧
    (step m t)^3≤step m t*t^2/(m:ℝ)^2 ∧
    probability m d t≤step m t*t^2/(m:ℝ)^2 := by
  have hm := h.m_pos
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have ht : 0≤t := by have := h.t_one; linarith
  have ht2 := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h.t_one) hs
  have hratio := div_le_div_of_nonneg_right ht2 (sq_nonneg (m:ℝ))
  have hst := (step_weighted m t (by have := h.large; omega) h.t_one).2.1
  have hst' := mul_le_mul_of_nonneg_left hst hs
  have hcoef := (coefficients m h.large).2.1.trans (coefficients m h.large).2.2.1
  have hB := mul_le_mul_of_nonneg_right hcoef (show 0≤t*(step m t)^2 by positivity)
  have hs1 := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs2 : (step m t)^2≤step m t := by nlinarith only [hs,hs1]
  have hss := mul_le_mul_of_nonneg_left (hs2.trans (step_bound m t (by have := h.large; omega))) hs
  have hd2 := h.power_le_d 2 (by decide)
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have hdp := mul_le_mul_of_nonneg_left hd2 hp
  have hpstep : probability m d t≤step m t/(m:ℝ)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hpd] at hdp
    exact hdp
  ring_nf at hratio hst' hB hss hpstep ⊢
  exact ⟨by nlinarith only [hratio,hst',hB],by nlinarith only [hss,hratio],by linarith only [hpstep,hratio]⟩

/-- The continuation multiplier differs from the inverse degree scale by
at most 10000*h*t^2/m^2 in a single batch. -/
theorem bracket_lower (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    -10000*step m t*t^2/(m:ℝ)^2≤growth m t-
      (probability m d t+load (caps m d t C P) (probability m d t))*(1+growth m t) := by
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have hp1 := probability_le_one m d t C P h
  have hp2 : (probability m d t)^2≤probability m d t := by nlinarith only [hp,hp1]
  have hp3 : (probability m d t)^3≤probability m d t := by
    have hh := mul_le_mul_of_nonneg_right hp2 hp
    nlinarith only [hh,hp2]
  have hz := precise_load m d t C P h
  have hu := (growth_bounds m t h.large h.t_one).2.1
  have hprod := growth_load m d t C P h
  obtain ⟨hB,hcube,hround⟩ := small_terms m d t C P h
  have hgap : (A m-3*a m)*(step m t*t^2)=9000*step m t*t^2/(m:ℝ)^2 := by
    unfold A a
    ring
  have hnonneg : 0≤step m t*t^2/(m:ℝ)^2 := by positivity
  ring_nf at hz hu hprod hB hcube hround hgap hnonneg ⊢
  nlinarith only [hz,hu,hprod,hB,hcube,hround,hgap,hp2,hp3,hnonneg]

end
end Erdos773.GreedyBatchRateGeometry
end EndpointModule058
-- End GreedyBatchRateGeometry.lean

-- Begin GreedyBatchDensityProfile.lean
section EndpointModule059

/- A continuation-density profile with enough slack to pay for all
shrinking-batch discrepancies. The future failure penalty is kept separate. -/
namespace Erdos773.GreedyBatchDensityProfile
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchRateGeometry GreedyBatchReward
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def efficiency (m : ℕ) : ℝ := 1-1000000/(m:ℝ)
def density (m : ℕ) (S d t : ℝ) : ℝ := efficiency m*(S-t)/d

lemma efficiency_bounds (m : ℕ) (hm : 2000000≤ m) : 1/2≤efficiency m ∧ efficiency m≤1 := by
  have hmR : (2000000:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hh : (1000000:ℝ)/(m:ℝ)≤1/2 := (div_le_iff₀ hm0).mpr (by linarith only [hmR])
  have hz : (0:ℝ)≤1000000/(m:ℝ) := by positivity
  dsimp [efficiency]
  exact ⟨by linarith only [hh],by linarith only [hz]⟩

lemma next_density (m : ℕ) (S d t : ℝ) (hd : d≠0) :
    density m S (nextD m d t) (t+step m t)=
      (efficiency m*(S-(t+step m t))/d)*Real.exp (growth m t) := by
  have he : nextD m d t=d*Real.exp (-growth m t) := by
    dsimp [nextD,growth]
    congr 1
    congr 1
    ring
  unfold density
  rw [he,Real.exp_neg]
  field_simp

lemma future_lower (m : ℕ) (S d t : ℝ) (hm : 2000000≤ m) (hd : 0<d) (hS : t+step m t≤S) :
    (efficiency m*(S-(t+step m t))/d)*(1+growth m t)≤
      density m S (nextD m d t) (t+step m t) := by
  have hell : 0≤efficiency m := le_trans (by norm_num) (efficiency_bounds m hm).1
  have hs : 0≤S-(t+step m t) := sub_nonneg.mpr hS
  rw [next_density m S d t (ne_of_gt hd)]
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (growth m t))
    (show 0≤efficiency m*(S-(t+step m t))/d by positivity)
  simpa only [add_comm] using hh

/-- The density profile has a spare p/m per stage, before charging the
explicit union-bound failure penalty. -/
theorem rate_margin (m : ℕ) (S d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hmLarge : 2000000≤ m) (hS : t+step m t≤S) (hS3 : S^3≤ m) :
    density m S d t+probability m d t/(m:ℝ)≤
      rate (caps m d t C P) (probability m d t) (density m S (nextD m d t) (t+step m t)) := by
  let ell := efficiency m
  let s := S-(t+step m t)
  let z := load (caps m d t C P) (probability m d t)
  let p := probability m d t
  let u := growth m t
  let hstep := step m t
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0≤t := by have := h.t_one; linarith
  have hs : 0≤s := sub_nonneg.mpr hS
  have hs0 : 0≤hstep := (step_pos m t (by have := h.large; omega)).le
  have hell0 : 0≤ell := le_trans (by norm_num) (efficiency_bounds m hmLarge).1
  have hell1 : ell≤1 := (efficiency_bounds m hmLarge).2
  have hcoarse := coarse_load m d t C P h
  have hQ : 0≤1-p-z := by have hh := hcoarse.2.2.2; change p+z≤1 at hh; linarith only [hh]
  have hf := future_lower m S d t hmLarge hd hS
  have hrate : p*(1-z)+(ell*s/d)*(1+u)*(1-p-z)≤
      rate (caps m d t C P) p (density m S (nextD m d t) (t+hstep)) := by
    have hh := mul_le_mul_of_nonneg_right hf hQ
    exact add_le_add le_rfl hh
  have hrateD := mul_le_mul_of_nonneg_right hrate hd.le
  have he : (p*(1-z)+(ell*s/d)*(1+u)*(1-p-z))*d=
      hstep*(1-z)+ell*s*(1+u)*(1-p-z) := by
    dsimp only [p,probability,hstep]
    field_simp
  rw [he] at hrateD
  have htS : t≤S := (le_add_of_nonneg_right hs0).trans hS
  have hS0 : 0≤S := ht.trans htS
  have hsS : s≤S := by dsimp [s]; linarith only [ht,hs0]
  have ht2 : t^2≤S^2 := pow_le_pow_left₀ ht htS 2
  have hsx : s*t^2≤(m:ℝ) := by
    have hh := mul_le_mul hsS ht2 (sq_nonneg t) hS0
    nlinarith only [hh,hS3]
  have hbr := bracket_lower m d t C P h
  change -10000*hstep*t^2/(m:ℝ)^2≤u-(p+z)*(1+u) at hbr
  have hb := mul_le_mul_of_nonneg_left hbr (mul_nonneg hell0 hs)
  have herror : ell*s*(10000*hstep*t^2/(m:ℝ)^2)≤10000*hstep/(m:ℝ) := by
    calc
      _ ≤ s*(10000*hstep*t^2/(m:ℝ)^2) := by
        have hh := mul_le_mul_of_nonneg_right hell1
          (show 0≤s*(10000*hstep*t^2/(m:ℝ)^2) by positivity)
        nlinarith only [hh]
      _ = (10000*hstep/(m:ℝ)^2)*(s*t^2) := by ring
      _ ≤ (10000*hstep/(m:ℝ)^2)*m := mul_le_mul_of_nonneg_left hsx (by positivity)
      _ = _ := by field_simp
  have hbfinal : -10000*hstep/(m:ℝ)≤ell*s*(u-(p+z)*(1+u)) := by
    ring_nf at hb herror ⊢
    nlinarith only [hb,herror]
  have hz : z≤10/(m:ℝ) := by
    have hh : (m:ℝ)≤(m:ℝ)^2 := by have hm1 := h.m_one; nlinarith only [hm1]
    exact hcoarse.2.2.1.trans (div_le_div_of_nonneg_left (by norm_num) hm hh)
  have hzh := mul_le_mul_of_nonneg_left hz hs0
  have hell : hstep*(1-ell)=1000000*hstep/(m:ℝ) := by dsimp [ell,efficiency]; ring
  have hnonneg : 0≤hstep/(m:ℝ) := by positivity
  have henergy : hstep/(m:ℝ)≤hstep*(1-ell)-hstep*z+ell*s*(u-(p+z)*(1+u)) := by
    ring_nf at hzh hell hbfinal hnonneg ⊢
    nlinarith only [hzh,hell,hbfinal,hnonneg]
  have hmain : ell*(s+hstep)+hstep/(m:ℝ)≤
      rate (caps m d t C P) p (density m S (nextD m d t) (t+hstep))*d := by
    nlinarith only [hrateD,henergy]
  apply le_of_mul_le_mul_right ?_ hd
  calc
    (density m S d t+probability m d t/(m:ℝ))*d=ell*(s+hstep)+hstep/(m:ℝ) := by
      dsimp [density,probability,ell,s,hstep]
      field_simp
      ring
    _ ≤ _ := hmain

lemma density_bounds (m : ℕ) (S d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : 2000000≤ m) (htS : t≤S) (hS3 : S^3≤ m) :
    0≤density m S d t ∧ density m S d t≤1 := by
  obtain ⟨hell,hell1⟩ := efficiency_bounds m hm
  have hell0 : 0≤efficiency m := le_trans (by norm_num) hell
  have hs : 0≤S-t := sub_nonneg.mpr htS
  have hd := h.d_pos
  have hS1 : 1≤S := h.t_one.trans htS
  have hS : S≤d := by
    have hh : S≤S^3 := by simpa only [pow_one] using pow_le_pow_right₀ hS1 (by decide : 1≤3)
    exact hh.trans (hS3.trans h.m_le_d)
  have ht : 0≤t := by have := h.t_one; linarith
  constructor
  · unfold density; positivity
  · unfold density
    apply (div_le_one hd).mpr
    have hh := mul_le_mul_of_nonneg_right hell1 hs
    nlinarith only [hh,hS,ht]

lemma density_pos (m : ℕ) (S d t : ℝ) (hm : 2000000≤ m) (hd : 0<d) (htS : t<S) :
    0<density m S d t := by
  have hell : 0<efficiency m := lt_of_lt_of_le (by norm_num) (efficiency_bounds m hm).1
  exact div_pos (mul_pos hell (sub_pos.mpr htS)) hd

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end
end Erdos773.GreedyBatchDensityProfile
end EndpointModule059
-- End GreedyBatchDensityProfile.lean

-- Begin GreedyBatchVolume.lean
section EndpointModule060

/- Polynomial forward volumes for repeated mixed regularization. Coarse
exponents are used because only exp(m^5) total volume is required. -/
namespace Erdos773.GreedyBatchVolume
open GreedyBatchProfiles GreedyBatchProfileConditions GreedyBatchDensityStep
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def increment (A : ℕ) : ℕ := 30*A+100
def volume (m A i : ℕ) : ℕ := m^(A+increment A*i)

lemma nat_power_slack (m i j c : ℕ) (hm : 100≤  m) (hc : c≤ 100) (hij : i<j) : c*m^i≤  m^j := by
  have hh := power_slack m i j c hm (by exact_mod_cast hc) hij
  exact_mod_cast hh

lemma degree_power (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    (caps m d t C P).D2≤  m^(3*A+7) ∧ (caps m d t C P).D3≤  m^(3*A+7) ∧
    (caps m d t C P).D4≤  m^(3*A+7) := by
  let R : ℝ := (m:ℝ)^(A+2)
  have hdR : d≤ R := hd.trans (pow_le_pow_right₀ h.m_one (by omega))
  have htR : t≤ R := h.t_upper.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ h.m_one (by omega : 1≤ A+2))
  have hd0 := h.d_pos.le
  have ht0 : 0≤ t := by have := h.t_one; linarith
  have hR0 : 0≤ R := by dsimp [R]; positivity
  have h2 := mul_le_mul hdR (pow_le_pow_left₀ ht0 htR 2) (sq_nonneg t) hR0
  have h3 := mul_le_mul (pow_le_pow_left₀ hd0 hdR 2) htR ht0 (sq_nonneg R)
  have h4 := pow_le_pow_left₀ hd0 hdR 3
  have he : R^3=(m:ℝ)^(3*A+6) := by dsimp [R]; rw [← pow_mul]; congr 1; omega
  have hs := power_slack m (3*A+6) (3*A+7) 4 h.large (by norm_num) (by omega)
  rw [← he] at hs
  obtain ⟨h2l,h2u,h3l,h3u,h4l,h4u,_⟩ := cap_bounds m d t C P h
  have hc2 : ((caps m d t C P).D2:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h2u,h2,hs]
  have hc3 : ((caps m d t C P).D3:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h3u,h3,hs]
  have hc4 : ((caps m d t C P).D4:ℝ)≤ (m:ℝ)^(3*A+7) := by nlinarith only [h4u,h4,hs,pow_nonneg hR0 3]
  exact ⟨by exact_mod_cast hc2,by exact_mod_cast hc3,by exact_mod_cast hc4⟩

/-- The exact mixed regularization factor is bounded by one fixed polynomial
in m, uniformly along a profile with d<=m^A. -/
theorem copies_bound (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    copies (caps m d t C P)≤  m^(increment A) := by
  obtain ⟨h2,h3,h4⟩ := degree_power m A d t C P h hd
  have hm : 1≤  m := by have := h.large; omega
  have hpow : 1≤  m^(3*A+7) := one_le_pow₀ hm
  have h2plus : (caps m d t C P).D2+1≤  m^(3*A+8) := by
    have hh := nat_power_slack m (3*A+7) (3*A+8) 2 h.large (by decide) (by omega)
    omega
  have hheight : PolynomialSidonSlopes.height (caps m d t C P).D2≤  m^(9*A+25) := by
    have hh := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h2plus 3)
    have he : (m^(3*A+8))^3=m^(9*A+24) := by rw [← pow_mul]; congr 1; omega
    rw [he] at hh
    exact hh.trans (nat_power_slack m (9*A+24) (9*A+25) 3 h.large (by decide) (by omega))
  have hcap2 : 2*PolynomialSidonSlopes.height (caps m d t C P).D2+5≤  m^(9*A+26) := by
    have hpow : 1≤  m^(9*A+25) := one_le_pow₀ hm
    have hh := nat_power_slack m (9*A+25) (9*A+26) 7 h.large (by decide) (by omega)
    omega
  have hcap : MixedLayerRegularization.cap (caps m d t C P).D2 (caps m d t C P).D3
      (caps m d t C P).D4≤  m^(9*A+26) := by
    apply max_le (max_le _ _) hcap2
    · exact h3.trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact h4.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hc2 : 2*MixedLayerRegularization.cap (caps m d t C P).D2 (caps m d t C P).D3
      (caps m d t C P).D4≤  m^(9*A+27) :=
    (Nat.mul_le_mul_left 2 hcap).trans (nat_power_slack m (9*A+26) (9*A+27) 2 h.large (by decide) (by omega))
  have hh := Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hc2 3)
  have he : (m^(9*A+27))^3=m^(27*A+81) := by rw [← pow_mul]; congr 1; omega
  rw [he] at hh
  apply hh.trans
  apply (nat_power_slack m (27*A+81) (27*A+82) 24 h.large (by decide) (by omega)).trans
  exact Nat.pow_le_pow_right (by omega) (by dsimp [increment]; omega)

lemma volume_step (m A i K : ℕ) (hK : K≤  m^(increment A)) : K*volume m A i≤ volume m A (i+1) := by
  apply (Nat.mul_le_mul_right _ hK).trans_eq
  dsimp [volume]
  rw [← pow_add]
  congr 1
  ring

lemma volume_exponent (m A i : ℕ) (hm : 3*increment A≤  m) (hi : i≤ 2*m^3) :
    A+increment A*i≤  m^4 := by
  have hA : A≤ increment A := by dsimp [increment]; omega
  have hinc : 100≤ increment A := by dsimp [increment]; omega
  have hm1 : 1≤ m := by omega
  have hp : 1≤  m^3 := one_le_pow₀ hm1
  have h1 := Nat.mul_le_mul_left (increment A) hi
  have h2 := Nat.mul_le_mul_right (m^3) hm
  have h3 := Nat.mul_le_mul_left (increment A) hp
  nlinarith only [hA,h1,h2,h3]

/-- All forward volumes stay below exp(m^5) for at most 2m^3 batches. -/
theorem volume_exp (m A i : ℕ) (hm : 3*increment A≤  m) (hi : i≤ 2*m^3) :
    (volume m A i:ℝ)≤ Real.exp ((m:ℝ)^5) := by
  have hinc : 100≤ increment A := by dsimp [increment]; omega
  have hmN : 1≤ m := by omega
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hm1 : (1:ℝ)≤  m := by exact_mod_cast hmN
  have he : (A+increment A*i:ℕ)≤  m^4 := volume_exponent m A i hm hi
  have heR : ((A+increment A*i:ℕ):ℝ)≤ (m:ℝ)^4 := by exact_mod_cast he
  have hlog : Real.log (m:ℝ)≤  m := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
  have hh := mul_le_mul heR hlog (Real.log_nonneg hm1) (pow_nonneg hm0.le 4)
  calc
    _ = Real.exp (((A+increment A*i:ℕ):ℝ)*Real.log (m:ℝ)) := by
      rw [Real.exp_nat_mul,Real.exp_log hm0]
      norm_cast
    _ ≤  _ := Real.exp_le_exp.mpr (by nlinarith only [hh])

end
end Erdos773.GreedyBatchVolume
end EndpointModule060
-- End GreedyBatchVolume.lean

-- Begin GreedyBatchFailurePenalty.lean
section EndpointModule061

/- The total failure penalty is smaller than the spare p/m in the
continuation profile, uniformly over all forward stage volumes. -/
namespace Erdos773.GreedyBatchFailurePenalty
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchScaleTails GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma probability_lower (m A : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) (hd : d≤ (m:ℝ)^A) :
    1/(2*(m:ℝ)^(A+5))≤ probability m d t/(m:ℝ) := by
  have hm := h.m_pos
  have hd0 := h.d_pos
  have ht0 : 0≤ t := by have := h.t_one; linarith
  have ht2 := pow_le_pow_left₀ ht0 h.t_upper 2
  have hm2 : (1:ℝ)≤ (m:ℝ)^2 := one_le_pow₀ h.m_one
  have hden : (m:ℝ)^2*(1+t^2)≤ 2*(m:ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_left (show 1+t^2≤ 2*(m:ℝ)^2 by linarith only [ht2,hm2]) (sq_nonneg (m:ℝ))
    nlinarith only [hh]
  have hs : 1/(2*(m:ℝ)^4)≤ step m t :=
    one_div_le_one_div_of_le (by positivity) hden
  have hp1 := div_le_div_of_nonneg_right hs hd0.le
  have hp2 := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤ 1/(2*(m:ℝ)^4)) hd0 hd
  have hp := div_le_div_of_nonneg_right (hp2.trans hp1) hm.le
  have he : (1/(2*(m:ℝ)^4))/(m:ℝ)^A/(m:ℝ)=1/(2*(m:ℝ)^(A+5)) := by
    rw [pow_add]
    field_simp
  simpa only [he,probability] using hp

lemma tests_exp (m V : ℕ) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V≤ 14*Real.exp (2*(m:ℝ)^5) := by
  have hE : 1≤ Real.exp ((m:ℝ)^5) := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 := (Real.exp_pos ((m:ℝ)^5)).le
  have hV0 : (0:ℝ)≤ V := Nat.cast_nonneg V
  have hV2 := pow_le_pow_left₀ hV0 hV 2
  have hE2 : Real.exp ((m:ℝ)^5)≤ (Real.exp ((m:ℝ)^5))^2 := by nlinarith only [hE]
  have hh : tests V≤ 14*(Real.exp ((m:ℝ)^5))^2 := by
    unfold tests
    nlinarith only [hV,hV2,hE2]
  have he : (Real.exp ((m:ℝ)^5))^2=Real.exp (2*(m:ℝ)^5) := by rw [← Real.exp_nat_mul]; norm_num
  rwa [he] at hh

lemma penalty_exp (m V : ℕ) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V*GreedyBatchScaleTails.failure m≤ 28*Real.exp (2*(m:ℝ)^5-(m:ℝ)^7) := by
  have hf : 0≤ GreedyBatchScaleTails.failure m := by unfold GreedyBatchScaleTails.failure; positivity
  have hh := mul_le_mul_of_nonneg_right (tests_exp m V hV) hf
  apply hh.trans_eq
  unfold GreedyBatchScaleTails.failure
  calc
    _ = 28*(Real.exp (2*(m:ℝ)^5)*Real.exp (-(m:ℝ)^7)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

lemma logarithmic_budget (m A : ℕ) (hm : A+100≤ m) :
    Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5≤ (m:ℝ)^7 := by
  have hm100 : 100≤ m := by omega
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm100
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  have hA : ((A+5:ℕ):ℝ)≤ m := by exact_mod_cast (show A+5≤ m by omega)
  have hlog : Real.log (m:ℝ)≤ m := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
  have hlog56 : Real.log 56≤ 56 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<56)).trans (by norm_num)
  have hh := mul_le_mul hA hlog (Real.log_nonneg hm1) hm0.le
  have hm2 : (56:ℝ)≤ (m:ℝ)^2 := by nlinarith only [hmR]
  have h25 := power_slack m 2 5 2 hm100 (by norm_num) (by decide)
  have h57 := power_slack m 5 7 3 hm100 (by norm_num) (by decide)
  nlinarith only [hlog56,hh,hm2,h25,h57]

lemma exponential_small (m A : ℕ) (hm : A+100≤ m) :
    28*Real.exp (2*(m:ℝ)^5-(m:ℝ)^7)≤ 1/(2*(m:ℝ)^(A+5)) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hh := logarithmic_budget m A hm
  have he : Real.exp (Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5-(m:ℝ)^7)≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hh])
  have hsum : Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ)+2*(m:ℝ)^5-(m:ℝ)^7=
      (Real.log 56+((A+5:ℕ):ℝ)*Real.log (m:ℝ))+(2*(m:ℝ)^5-(m:ℝ)^7) := by ring
  rw [hsum,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<56),
    Real.exp_nat_mul,Real.exp_log hm0] at he
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(m:ℝ)^(A+5))).mpr
  nlinarith only [he]

/-- Explicit total failure control for an arbitrary volume up to exp(m^5). -/
theorem penalty (m A V : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : A+100≤ m) (hd : d≤ (m:ℝ)^A) (hV : (V:ℝ)≤ Real.exp ((m:ℝ)^5)) :
    tests V*GreedyBatchScaleTails.failure m≤ probability m d t/(m:ℝ) :=
  (penalty_exp m V hV).trans ((exponential_small m A hm).trans (probability_lower m A d t C P h hd))

/-- The prescribed forward-volume schedule supplies the failure control. -/
theorem volume_penalty (m A i : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P)
    (hm : 3*increment A≤ m) (hi : i≤ 2*m^3) (hd : d≤ (m:ℝ)^A) :
    tests (volume m A i)*GreedyBatchScaleTails.failure m≤ probability m d t/(m:ℝ) := by
  apply penalty m A (volume m A i) d t C P h _ hd (volume_exp m A i hm hi)
  dsimp [increment] at hm
  omega

end
end Erdos773.GreedyBatchFailurePenalty
end EndpointModule061
-- End GreedyBatchFailurePenalty.lean

-- Begin GreedyBatchTrajectory.lean
section EndpointModule062

/- A finite deterministic time trajectory for the verified batch profiles,
with an explicit stopping index and terminal-scale comparison. -/
namespace Erdos773.GreedyBatchTrajectory
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def time (m : ℕ) : ℕ → ℝ
  | 0 => 1
  | i+1 => time m i+step m (time m i)

@[simp] lemma time_zero (m : ℕ) : time m 0=1 := rfl
lemma time_succ (m i : ℕ) : time m (i+1)=time m i+step m (time m i) := rfl

def scale (m : ℕ) (d : ℝ) (i : ℕ) : ℝ := d*Real.exp (-a m*((time m i)^3-1))
def commonCap (m i : ℕ) : ℕ := 3+i*(4*m^52+3)

lemma time_strict (m : ℕ) (hm : 0< m) : StrictMono (time m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [time_succ]
  exact lt_add_of_pos_right _ (step_pos m (time m i) hm)

lemma time_one (m i : ℕ) (hm : 0< m) : 1≤ time m i := by
  simpa only [time_zero] using (time_strict m hm).monotone (Nat.zero_le i)

@[simp] lemma scale_zero (m : ℕ) (d : ℝ) : scale m d 0=d := by simp [scale]

lemma scale_succ (m i : ℕ) (d : ℝ) : scale m d (i+1)=nextD m (scale m d i) (time m i) := by
  dsimp [scale,nextD]
  rw [time_succ,mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  dsimp [GreedyBatchProfileLower.delta]
  ring

lemma scale_antitone (m : ℕ) (d : ℝ) (hm : 100≤ m) (hd : 0≤ d) : Antitone (scale m d) := by
  intro i j hij
  have ha := (coefficients m hm).2.2.2.1
  have hi := time_one m i (by omega)
  have htime := (time_strict m (by omega)).monotone hij
  have hp := pow_le_pow_left₀ (by linarith only [hi] : 0≤ time m i) htime 3
  have hh := mul_le_mul_of_nonneg_left hp ha
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hd
  nlinarith only [hh]

lemma scale_le_initial (m i : ℕ) (d : ℝ) (hm : 100≤ m) (hd : 0≤ d) : scale m d i≤ d := by
  simpa only [scale_zero] using scale_antitone m d hm hd (Nat.zero_le i)

lemma common_succ (m i : ℕ) : commonCap m (i+1)=commonCap m i+4*m^52+3 := by
  unfold commonCap
  ring

lemma common_one (m i : ℕ) : 1≤ commonCap m i := by unfold commonCap; omega

lemma common_bound (m i : ℕ) (hm : 100≤ m) (hi : i≤ 2*m^3) : commonCap m i≤ m^60 := by
  have hm1 : 1≤ m := by omega
  have h1 := Nat.mul_le_mul_right (4*m^52+3) hi
  have hp3 : m^3≤ m^55 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1≤ m^55 := one_le_pow₀ hm1
  have hs := nat_power_slack m 55 60 17 hm (by decide) (by decide)
  unfold commonCap
  nlinarith only [h1,hp3,hp1,hs]

/-- A terminal lower scale and upper time suffice for the whole trajectory. -/
theorem ranges (m L : ℕ) (d : ℝ) (P : ℕ) (hm : 100≤ m) (hd : 0<d)
    (hP1 : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) :
    ∀ i≤ L, Range m (scale m d i) (time m i) (commonCap m i) P := by
  intro i hi
  have ht1 := time_one m i (by omega)
  have hT1 := time_one m L (by omega)
  have hT : time m L≤ (m:ℝ) := by
    have hh : time m L≤ (time m L)^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hT1 (by decide : 1≤ 3)
    exact hh.trans hS
  exact {
    large := hm
    d := hdL.trans (scale_antitone m d hm hd.le hi)
    t_one := ht1
    t_upper := ((time_strict m (by omega)).monotone hi).trans hT
    common := common_bound m i hm (hi.trans hL)
    common_one := common_one m i
    pair_one := hP1
    pair_upper := hPm }

lemma time_progress (m n : ℕ) (T : ℝ) (hm : 0< m) (hT : ∀ i≤ n, time m i≤ T) :
    1+(n:ℝ)/((m:ℝ)^2*(1+T^2))≤ time m n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := hT n (by omega)
    have ht0 : 0≤ time m n := by have hh := time_one m n hm; linarith only [hh]
    have hm0 : (0:ℝ)< m := by exact_mod_cast hm
    have hpow := pow_le_pow_left₀ ht0 ht 2
    have hden : (m:ℝ)^2*(1+(time m n)^2)≤ (m:ℝ)^2*(1+T^2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hpow]) (sq_nonneg (m:ℝ))
    have hs : 1/((m:ℝ)^2*(1+T^2))≤ step m (time m n) :=
      one_div_le_one_div_of_le (by positivity) hden
    have hh := ih (fun i hi => hT i (by omega))
    rw [time_succ,Nat.cast_add,Nat.cast_one]
    ring_nf at hh hs ⊢
    linarith only [hh,hs]

lemma time_reaches (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ m) :
    T≤ time m (2*m^3) := by
  by_contra! hbad
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hbound (i : ℕ) (hi : i≤ 2*m^3) : time m i≤ T :=
    ((time_strict m (by omega)).monotone hi).trans hbad.le
  have hh := time_progress m (2*m^3) T (by omega) hbound
  have he : ((2*m^3:ℕ):ℝ)/((m:ℝ)^2*(1+T^2))=2*(m:ℝ)/(1+T^2) := by
    push_cast
    field_simp
  rw [he] at hh
  have ht3 : T≤ T^3 := by simpa only [pow_one] using pow_le_pow_right₀ hT (by decide : 1≤ 3)
  have ht : T≤ 2*(m:ℝ)/(1+T^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [ht3,hT3])
  linarith only [hbad,hh,ht]

/-- A least crossing has overshoot no larger than one shrinking step. -/
theorem stopping_index (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ m) :
    ∃ L : ℕ, L≤ 2*m^3 ∧ T≤ time m L ∧ time m L≤ T+1/(m:ℝ)^2 := by
  have hex : ∃ L, T≤ time m L := ⟨2*m^3,time_reaches m T hm hT hT3⟩
  let L := Nat.find hex
  have hL : L≤ 2*m^3 := Nat.find_min' hex (time_reaches m T hm hT hT3)
  refine ⟨L,hL,Nat.find_spec hex,?_⟩
  by_cases hL0 : L=0
  · rw [hL0,time_zero]
    have hz : (0:ℝ)≤ 1/(m:ℝ)^2 := by positivity
    linarith only [hT,hz]
  · obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hL0
    have hiL : i<L := by omega
    have ht : time m i<T := lt_of_not_ge (Nat.find_min hex hiL)
    have hs := step_bound m (time m i) hm
    rw [hi,time_succ]
    linarith only [ht,hs]

/-- The stopped horizon remains within the range required by the rate
profile, while reaching at least the desired physical time. -/
theorem stopping_small (m : ℕ) (T : ℝ) (hm : 1≤ m) (hT : 1≤ T) (hT3 : T^3≤ (m:ℝ)/16) :
    ∃ L : ℕ, L≤ 2*m^3 ∧ T≤ time m L ∧ time m L≤ T+1 ∧ (time m L)^3≤ m := by
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  obtain ⟨L,hL,htL,hLT⟩ := stopping_index m T hm hT (by linarith only [hT3,hm0])
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
  have hs : (1:ℝ)/(m:ℝ)^2≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)
  have hLT' : time m L≤ T+1 := by linarith only [hLT,hs]
  have htwice : time m L≤ 2*T := by linarith only [hLT',hT]
  have ht0 : 0≤ time m L := by have := time_one m L (by omega); linarith
  have hc := pow_le_pow_left₀ ht0 htwice 3
  exact ⟨L,hL,htL,hLT',by nlinarith only [hc,hT3,hm0]⟩

lemma terminal_scale (m L : ℕ) (d T : ℝ) (hm : 100≤ m) (hd : 0≤ d) (hT : 1≤ T)
    (hLT : time m L≤ T+1) : d*Real.exp (-a m*((T+1)^3-1))≤ scale m d L := by
  have ht0 : 0≤ time m L := by have := time_one m L (by omega); linarith
  have hp := pow_le_pow_left₀ ht0 hLT 3
  have hh := mul_le_mul_of_nonneg_left hp (coefficients m hm).2.2.2.1
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hd
  nlinarith only [hh]

end
end Erdos773.GreedyBatchTrajectory
end EndpointModule062
-- End GreedyBatchTrajectory.lean

-- Begin GreedyBatchSchedule.lean
section EndpointModule063

/- Finite backward iteration of the proved batch density step. Every
hypothesis is a deterministic scalar condition on a prescribed schedule. -/
namespace Erdos773.GreedyBatchSchedule
open GreedyBatchCertificate GreedyBatchReward GreedyBatchDensityStep
set_option maxHeartbeats 2500000
noncomputable section
universe u

structure Schedule where
  current : ℕ → Caps
  target : ℕ → Caps
  margins : ℕ → Margins
  p : ℕ → ℝ
  eta : ℕ → ℝ
  density : ℕ → ℝ
  failure : ℕ → ℝ
  moment : ℕ → ℕ
  volume : ℕ → ℕ

structure Valid (s : Schedule) (T : ℕ) : Prop where
  margins : ∀ i<T, (s.margins i).Positive
  probability : ∀ i<T, ProbabilityRange (s.current i) (s.p i) (s.eta i)
  fits : ∀ i<T, Fits (s.current i) (s.margins i) (s.p i) (s.eta i) (s.target i)
  pair : ∀ i<T, (s.current i).P≤(s.target i).P
  density_nonneg : ∀ i≤T, 0≤s.density i
  density_le_one : ∀ i≤T, s.density i≤1
  density_pos : ∀ i<T, 0<s.density i
  failure_nonneg : ∀ i<T, 0≤s.failure i
  vertex : ∀ i<T, ∀ k, vertexError (s.current i) (s.margins i) (s.p i) (s.eta i) (s.moment i) k≤s.failure i
  pairError : ∀ i<T, ∀ k, pairError (s.current i) (s.margins i) (s.p i) (s.eta i) (s.moment i) k≤s.failure i
  rate : ∀ i<T, s.density i≤rate (s.current i) (s.p i) (s.density (i+1))-tests (s.volume i)*s.failure i
  volume : ∀ i<T, copies (s.target i)*s.volume i≤s.volume (i+1)
  next : ∀ i<T, post (s.target i)=s.current (i+1)
  terminal : s.density T=0

/-- Exact backward iteration, including forward regularization volumes. -/
theorem iterate (s : Schedule) (T : ℕ) (h : Valid s T) :
    ∀ i≤T, UniformDensity.{u} (s.current i) (s.volume i) (s.density i) := by
  have hind (k : ℕ) : ∀ i, i+k=T → UniformDensity.{u} (s.current i) (s.volume i) (s.density i) := by
    induction k with
    | zero =>
      intro i hi
      have he : i=T := by omega
      subst i
      rw [h.terminal]
      exact zero_density _ _
    | succ k ih =>
      intro i hi
      have hiT : i<T := by omega
      have hnT : i+1≤T := by omega
      have hn : UniformDensity.{u} (post (s.target i)) (s.volume (i+1)) (s.density (i+1)) := by
        rw [h.next i hiT]
        exact ih (i+1) (by omega)
      exact density_step (s.current i) (s.target i) (s.margins i) (s.p i) (s.eta i)
        (s.density (i+1)) (s.density i) (s.failure i) (s.moment i) (s.volume i) (s.volume (i+1))
        (h.margins i hiT) (h.probability i hiT) (h.fits i hiT) (h.pair i hiT)
        (h.density_nonneg (i+1) hnT) (h.density_le_one (i+1) hnT) (h.density_pos i hiT)
        (h.failure_nonneg i hiT) (h.vertex i hiT) (h.pairError i hiT)
        (h.rate i hiT) (h.volume i hiT) hn
  intro i hi
  exact hind (T-i) i (by omega)

end
end Erdos773.GreedyBatchSchedule
end EndpointModule063
-- End GreedyBatchSchedule.lean

-- Begin GreedyBatchProfileIteration.lean
section EndpointModule064

/- Fully instantiated finite iteration of the exponential mixed-rank
profiles, with explicit time, terminal scale and volume hypotheses. -/
namespace Erdos773.GreedyBatchProfileIteration
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchDensityStep GreedyBatchDensityProfile GreedyBatchVolume GreedyBatchTrajectory
open GreedyBatchSchedule
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section
universe u

def schedule (m A L : ℕ) (d : ℝ) (P : ℕ) : Schedule where
  current i := caps m (scale m d i) (time m i) (commonCap m i) P
  target i := caps m (scale m d (i+1)) (time m (i+1)) (commonCap m i+4*m^52) P
  margins i := GreedyBatchScaledErrors.margins
    (caps m (scale m d i) (time m i) (commonCap m i) P) m
    (probability m (scale m d i) (time m i)) (scale m d i)
  p i := probability m (scale m d i) (time m i)
  eta _ := 1/(m:ℝ)^2
  density i := density m (time m L) (scale m d i) (time m i)
  failure _ := GreedyBatchScaleTails.failure m
  moment _ := m^10
  volume i := volume m A i

/-- Every finite numeric hypothesis of the abstract batch schedule is now
proved for these concrete profiles. -/
theorem valid (m A L : ℕ) (d : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) : Valid (schedule m A L d P) L := by
  have hm100 : 100≤ m := by omega
  have hr := ranges m L d P hm100 hd hP hPm hL hS hdL
  have hc (i : ℕ) (hi : i≤ L) := conditions m (scale m d i) (time m i) (commonCap m i) P (hr i hi)
  have hdI (i : ℕ) : scale m d i≤ (m:ℝ)^A := (scale_le_initial m i d hm100 hd.le).trans hdU
  have htime (i : ℕ) (hi : i≤ L) : time m i≤ time m L := (time_strict m (by omega)).monotone hi
  constructor
  · intro i hi
    exact GreedyBatchScaledErrors.margins_positive _ m _ _ (hc i hi.le)
  · intro i hi
    exact GreedyBatchScaledErrors.probability_range _ m _ _ (hc i hi.le)
  · intro i hi
    have hh := GreedyBatchProfileFits.fits m (scale m d i) (time m i) (commonCap m i) P (hr i hi.le)
    simpa only [schedule,scale_succ,time_succ] using hh
  · intro i hi
    exact le_rfl
  · intro i hi
    exact (density_bounds m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi) hm (htime i hi) hS).1
  · intro i hi
    exact (density_bounds m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi) hm (htime i hi) hS).2
  · intro i hi
    exact density_pos m (time m L) (scale m d i) (time m i) hm (hr i hi.le).d_pos (time_strict m (by omega) hi)
  · intro i hi
    unfold schedule GreedyBatchScaleTails.failure
    positivity
  · intro i hi
    exact GreedyBatchScaledErrors.vertex_errors _ m _ _ (hc i hi.le)
  · intro i hi
    exact GreedyBatchScaledErrors.pair_errors _ m _ _ (hc i hi.le)
  · intro i hi
    have hnext : time m i+step m (time m i)≤ time m L := by
      rw [← time_succ]
      exact htime (i+1) (by omega)
    have hrate := rate_margin m (time m L) (scale m d i) (time m i) (commonCap m i) P (hr i hi.le) hm hnext hS
    have hpen := GreedyBatchFailurePenalty.volume_penalty m A i (scale m d i) (time m i)
      (commonCap m i) P (hr i hi.le) hmV (hi.le.trans hL) (hdI i)
    rw [← scale_succ,← time_succ] at hrate
    dsimp only [schedule]
    linarith only [hrate,hpen]
  · intro i hi
    have hcopy := copies_bound m A (scale m d (i+1)) (time m (i+1)) (commonCap m (i+1)) P
      (hr (i+1) (by omega)) (hdI (i+1))
    change copies ((schedule m A L d P).target i)≤ m^(increment A) at hcopy
    exact volume_step m A i _ hcopy
  · intro i hi
    dsimp [schedule,post,caps]
    rw [common_succ]
  · simp [schedule,density]

/-- The finite regular mixed-hypergraph density bound at a prescribed final
index. No implicit asymptotic or tracking hypotheses remain. -/
theorem uniform_fixed (m A L : ℕ) (d : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hL : L≤ 2*m^3) (hS : (time m L)^3≤ m)
    (hdL : (m:ℝ)^1000≤ scale m d L) :
    UniformDensity.{u} (caps m d 1 3 P) (m^A) (efficiency m*(time m L-1)/d) := by
  have hh := iterate (schedule m A L d P) L (valid m A L d P hm hmV hd hdU hP hPm hL hS hdL) 0 (Nat.zero_le L)
  simpa [schedule,commonCap,volume,density] using hh

lemma uniform_mono (c : Caps) (V : ℕ) (δ ε : ℝ) (hδε : δ≤ ε)
    (h : UniformDensity.{u} c V ε) : UniformDensity.{u} c V δ := by
  intro β _ _ H hH hV
  obtain ⟨A,hA,hcard⟩ := h β H hH hV
  exact ⟨A,hA,(mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg _)).trans hcard⟩

/-- A desired physical time can be reached with an explicit terminal-scale
condition and at most 2m^3 bounded-volume restarts. -/
theorem uniform_horizon (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment A≤ m) (hd : 0<d) (hdU : d≤ (m:ℝ)^A)
    (hP : 1≤ P) (hPm : P≤ m) (hT : 1≤ T) (hT3 : T^3≤ (m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤ d*Real.exp (-a m*((T+1)^3-1))) :
    UniformDensity.{u} (caps m d 1 3 P) (m^A) (efficiency m*(T-1)/d) := by
  obtain ⟨L,hL,hTL,hLT,hS⟩ := stopping_small m T (by omega) hT hT3
  have hdL := hterminal.trans (terminal_scale m L d T (by omega) hd.le hT hLT)
  have hh := uniform_fixed m A L d P hm hmV hd hdU hP hPm hL hS hdL
  apply uniform_mono _ _ _ _ _ hh
  have he : 0≤ efficiency m := le_trans (by norm_num) (efficiency_bounds m hm).1
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hTL]) he) hd.le

end
end Erdos773.GreedyBatchProfileIteration
end EndpointModule064
-- End GreedyBatchProfileIteration.lean

-- Begin GreedyBatchInitialExtraction.lean
section EndpointModule065

/- Initial regularization and exact density transfer for the shrinking
mixed-batch theorem. The initial hypergraph is genuinely four-uniform. -/
namespace Erdos773.GreedyBatchInitialExtraction
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyHypergraphState
open FourUniformRegularization (pairDegree)
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep
open GreedyBatchDensityStep GreedyBatchDensityProfile GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma layer_four (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) : layer H 4=H := by
  ext e
  simp only [layer,mem_filter]
  exact ⟨And.left,fun he => ⟨he,hfour e he⟩⟩

omit [Fintype α] in
lemma layer_empty (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (k : ℕ) (hk : k≠4) :
    layer H k=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hc⟩ := mem_filter.mp he
  exact hk (hc.symm.trans (hfour e he))

lemma common_zero (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (x y : α) :
    RegularizationCommonNeighbors.common H x y=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨⟨hne,he⟩,_⟩ := RegularizationCommonNeighbors.mem_both.mp hz
  have hh := hfour _ he
  simp [hne] at hh

lemma shared_zero (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (x y : α) :
    RegularizationSharedLinks.count H x y=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hc,hx,_,hm,_⟩ := RegularizationSharedLinks.mem_links.mp he
  have hh := hfour _ hm
  rw [card_insert_of_notMem hx,hc] at hh
  omega

lemma initial_range (m : ℕ) (d T : ℝ) (P : ℕ) (hm : 2000000≤ m)
    (hd : 0<d) (hP : 1≤P) (hPm : P≤ m) (hT : 1≤T)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1))) : Range m d 1 3 P := by
  have hm100 : 100≤ m := by omega
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm100
  have hpow : (1:ℝ)≤(T+1)^3 := one_le_pow₀ (by linarith only [hT])
  have ha := (coefficients m hm100).2.2.2.1
  have hexp : Real.exp (-a m*((T+1)^3-1))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg ha (sub_nonneg.mpr hpow)
    nlinarith only [this]
  refine ⟨hm100,hterminal.trans ?_,le_rfl,by linarith only [hmR],?_,by omega,hP,hPm⟩
  · exact (mul_le_mul_of_nonneg_left hexp hd.le).trans_eq (mul_one d)
  · exact (show 3≤ m by omega).trans (Nat.le_pow (by omega : 0<60))

/-- No density is lost in regularizing the original four-uniform carrier.
The enlarged exponent accounts for every copy used by this initial step. -/
theorem independent (H : Finset (Finset α)) (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (A+increment A)≤ m)
    (hd : 0<d) (hdU : d≤ (m:ℝ)^A) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hvol : Fintype.card α≤ m^A) (hfour : ∀ e ∈ H, e.card=4)
    (hdegree : ∀ x, (degree H x:ℝ)≤d^3)
    (hpair : ∀ x y, x≠y → pairDegree H x y≤P)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2) :
    ∃ I : Finset α, Independent H I ∧ efficiency m*(T-1)/d*Fintype.card α≤(I.card:ℝ) := by
  let c := caps m d 1 3 P
  have hr := initial_range m d T P hm hd hP hPm hT hterminal
  have hdegree' (x : α) : degree (layer H 4) x≤c.D4 := by
    rw [layer_four H hfour]
    exact_mod_cast (hdegree x).trans (Nat.le_ceil (f4 d))
  obtain ⟨r,hprime,hrL,hrU,G,hGr,hG2,hG3,hG4,hGp,hGi,hGc,ht,hGb⟩ :=
    MixedLayerRegularization.exists_regularization H c.D2 c.D3 c.D4 P 0
      (fun e he => by rw [hfour e he]; omega)
      (fun x => by rw [layer_empty H hfour 2 (by omega)]; simp [degree])
      (fun x => by rw [layer_empty H hfour 3 (by omega)]; simp [degree])
      hdegree' hP hpair hinter (fun x y _ => by rw [common_zero H hfour])
  letI : Fact r.Prime := ⟨hprime⟩
  have hG : Regular G c := ⟨hGr,hGi,hG2,hG3,hG4,hGp,hGc,
    hGb c.B (fun x y _ => by rw [shared_zero H hfour]; omega)⟩
  have hcopy : 24*r^3≤ m^(increment A) :=
    (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hrU 3)).trans
      (copies_bound m A d 1 3 P hr hdU)
  have hGV : Fintype.card (MixedLayerRegularization.Model α r)≤ m^(A+increment A) := by
    rw [MixedLayerRegularization.model_card,pow_add]
    exact (Nat.mul_le_mul hcopy hvol).trans_eq (Nat.mul_comm _ _)
  have hdV : d≤(m:ℝ)^(A+increment A) :=
    hdU.trans (pow_le_pow_right₀ hr.m_one (Nat.le_add_right _ _))
  obtain ⟨B,hB,hcard⟩ := GreedyBatchProfileIteration.uniform_horizon m (A+increment A) d T P
    hm hmV hd hdV hP hPm hT hT3 hterminal (MixedLayerRegularization.Model α r) G hG hGV
  have hcard' : efficiency m*(T-1)/d*(24*(r:ℝ)^3*Fintype.card α)≤(B.card:ℝ) := by
    simpa only [MixedLayerRegularization.model_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hcard
  exact MixedLayerRegularization.density_transfer hprime H G ht B hB _ hcard'

/-- Ambient finite-set form of the four-uniform selection theorem. -/
theorem selection {β : Type u} [DecidableEq β] (V : Finset β) (H : Finset (Finset β))
    (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (A+increment A)≤ m)
    (hd : 0<d) (hdU : d≤(m:ℝ)^A) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hvol : V.card≤ m^A) (hH : ∀ e ∈ H, e⊆V) (hfour : ∀ e ∈ H, e.card=4)
    (hdegree : ∀ x ∈ V, (degree H x:ℝ)≤d^3)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, x≠y → pairDegree H x y≤P)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2) :
    ∃ I⊆V, (∀ e ∈ H, ¬e⊆I) ∧ efficiency m*(T-1)/d*V.card≤(I.card:ℝ) := by
  let K := FiniteHypergraphRestriction.restrict V H
  have hfour' : ∀ e ∈ K, e.card=4 := by
    intro e he
    have hh := hfour _ ((FiniteHypergraphRestriction.mem_restrict hH).mp he)
    simpa only [FiniteHypergraphRestriction.up_card] using hh
  have hdeg' (x : FiniteHypergraphRestriction.Carrier V) : (degree K x:ℝ)≤d^3 := by
    rw [← layer_four K hfour',FiniteHypergraphRestriction.degree_eq hH,layer_four H hfour]
    exact hdegree x.val x.property
  obtain ⟨I,hI,hcard⟩ := independent K m A d T P
    hm hmV hd hdU hP hPm hT hT3 hterminal (by simpa only [Fintype.card_coe] using hvol)
    hfour' hdeg'
    (fun x y hxy => by
      rw [FiniteHypergraphRestriction.pair_eq hH]
      exact hpair x.val x.property y.val y.property (fun he => hxy (Subtype.ext he)))
    (FiniteHypergraphRestriction.intersections hH 2 hinter)
  refine ⟨FiniteHypergraphRestriction.up V I,FiniteHypergraphRestriction.up_subset I,
    (FiniteHypergraphRestriction.independent_iff hH I).mp hI,?_⟩
  simpa only [FiniteHypergraphRestriction.up_card,Fintype.card_coe] using hcard

end
end Erdos773.GreedyBatchInitialExtraction
end EndpointModule065
-- End GreedyBatchInitialExtraction.lean

-- Begin ProductCorrelation.lean
section EndpointModule066

/-
Finite product distributions on chains and positive correlation of increasing
functions. These are probability/averaging lemmas, not a Sidon construction.
-/
namespace Erdos773.ProductCorrelation
open Finset
set_option maxHeartbeats 1000000

section Lattice
variable {Ω ι : Type*} [Fintype Ω] [DistribLattice Ω] [DecidableEq ι]

-- Unused development declaration omitted.

-- Unused development declaration omitted.
end Lattice

section Product
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

variable [DecidableEq β]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Product
end Erdos773.ProductCorrelation
end EndpointModule066
-- End ProductCorrelation.lean

-- Begin PriorityHypergraphSelection.lean
section EndpointModule067

/-
Independent sets obtained from finite random priorities. The FKG bound accounts
for overlapping links, but is not a logarithmic-gain extraction theorem.
-/
namespace Erdos773.PriorityHypergraphSelection
open Finset ProductCorrelation
set_option maxHeartbeats 1000000
variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.PriorityHypergraphSelection
end EndpointModule067
-- End PriorityHypergraphSelection.lean

-- Begin PriorityIntegralSelection.lean
section EndpointModule068

/-
The integral version of the finite priority bound. The discretization error
is bounded directly by a monotone sum/integral comparison.
-/
namespace Erdos773.PriorityIntegralSelection
open Finset PriorityHypergraphSelection
set_option maxHeartbeats 1000000

-- Unused development declaration omitted.

variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.PriorityIntegralSelection
end EndpointModule068
-- End PriorityIntegralSelection.lean

-- Begin CaroTuzaFourUniform.lean
section EndpointModule069

/-
An explicit four-uniform Caro--Tuza bound. This improves the constant in an
alteration estimate, not its exponent, and does not settle Erdős 773.
-/
namespace Erdos773.CaroTuzaFourUniform
open Finset PriorityIntegralSelection
set_option maxHeartbeats 1500000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

variable {α : Type*} [Fintype α] [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.CaroTuzaFourUniform
end EndpointModule069
-- End CaroTuzaFourUniform.lean

-- Begin FixedCardinalitySampling.lean
section EndpointModule070

/-
Weighted sampling with a prescribed cardinality. This is a finite averaging
lemma, proved by deleting one vertex at a time and using Bernoulli's inequality.
It does not assert that any selected hypergraph is independent.
-/
namespace Erdos773.FixedCardinalitySampling
open Finset
set_option maxHeartbeats 1000000
variable {α : Type*} [DecidableEq α]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.FixedCardinalitySampling
end EndpointModule070
-- End FixedCardinalitySampling.lean

-- Begin DivisorBound.lean
section EndpointModule071

/- A uniform subpower bound for the divisor function. -/

namespace Erdos773

open Finset Filter

lemma divisor_card_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  let b : ℝ := 2 ^ δ
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + 1 / (b - 1)
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ 1 / (b - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcb : c * (b - 1) = b := by
    dsimp [c]
    field_simp [show b - 1 ≠ 0 by linarith]
    <;> ring
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ c * b ^ e := by
    have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ b) e
    calc
      (e : ℝ) + 1 ≤ c + (e : ℝ) * b := by
        nlinarith [mul_nonneg (Nat.cast_nonneg e) (le_of_lt (sub_pos.mpr hb))]
      _ = c * (1 + (e : ℝ) * (b - 1)) := by
        rw [mul_add, mul_one, ← mul_left_comm, hcb]
      _ ≤ c * b ^ e := mul_le_mul_of_nonneg_left hber hcpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ≥ K, (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    exact eventually_atTop.mp
      (tendsto_atTop.mp ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop) 2)
  refine ⟨c ^ K, pow_pos hcpos _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hδ.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p + 1 : ℕ) ≤
        (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpk : p < K
    · rw [if_pos hpk]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) = (n.factorization p : ℝ) + 1 := by push_cast; rfl
        _ ≤ c * b ^ n.factorization p := hsmall _
        _ ≤ c * ((p : ℝ) ^ δ) ^ n.factorization p := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpk, one_mul]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n.factorization p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p)))
        _ ≤ ((p : ℝ) ^ δ) ^ n.factorization p :=
          pow_le_pow_left₀ (by norm_num) (hK p (by omega)) _
  have hcoeff : (∏ p ∈ n.primeFactors, if p < K then c else 1) ≤ c ^ K := by
    have hcard : (n.primeFactors.filter (· < K)).card ≤ K := by
      calc
        _ ≤ (Finset.range K).card := Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = K := Finset.card_range K
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hc hcard
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    have hnprod' : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_pow_eq_self hn]
    exact_mod_cast hnprod'
  have hrpow : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p) = (n : ℝ) ^ δ := by
    calc
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ δ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
          ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm δ]
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ δ :=
        Real.finset_prod_rpow _ _ (by intros; positivity) _
      _ = (n : ℝ) ^ δ := by rw [hnprod]
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p :=
      Finset.prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < K then c else 1) * (n : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, hrpow]
    _ ≤ c ^ K * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg n) δ)


end Erdos773
end EndpointModule071
-- End DivisorBound.lean

-- Begin APBounds.lean
section EndpointModule072

/- Counting three-term progressions among the squares by their gaps. -/

namespace Erdos773

open Finset Filter

lemma squareAP_parameters {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) :
    let y := c - b
    let d := 2 * b - (a + c)
    0 < y ∧ 0 < d ∧ a + y + d = b ∧ a + 2 * y + d = c ∧
      2 * y ^ 2 = d * (2 * a + d) := by
  dsimp only
  have hy : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hyb : c - b + b = c := Nat.sub_add_cancel hbc.le
  have hac : a + c < 2 * b := by
    have he' : (a : ℤ) ^ 2 + (c : ℤ) ^ 2 = 2 * (b : ℤ) ^ 2 := by exact_mod_cast he
    have hpos : 0 < ((a : ℤ) - c) ^ 2 := sq_pos_of_ne_zero (by omega)
    by_contra! h
    have h' : 2 * (b : ℤ) ≤ (a : ℤ) + c := by exact_mod_cast h
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 2 * b) h' 2
    nlinarith only [hs, he', hpos]
  have hd : 0 < 2 * b - (a + c) := Nat.sub_pos_of_lt hac
  have hdac := Nat.sub_add_cancel hac.le
  have hb : a + (c - b) + (2 * b - (a + c)) = b := by omega
  have hc : a + 2 * (c - b) + (2 * b - (a + c)) = c := by omega
  refine ⟨hy, hd, hb, hc, ?_⟩
  nth_rw 1 [← hb] at he
  nth_rw 1 [← hc] at he
  nlinarith only [he]

def squareAPs (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ (Icc 1 N)).filter
    (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧ t.1.1 ^ 2 + t.2 ^ 2 = 2 * t.1.2 ^ 2)

-- Unused development declaration omitted.

-- Unused development declaration omitted.


end Erdos773
end EndpointModule072
-- End APBounds.lean

-- Begin SquareProgressionSupports.lean
section EndpointModule073

/-
Three-root progression supports for the square-Sidon problem. Each support
is counted once. Avoiding these supports gives progression-free square values,
not Sidon square values.
-/
noncomputable section
namespace Erdos773.SquareProgressionSupports
open Finset
set_option maxHeartbeats 1000000

/-- Three distinct roots whose squares form a three-term progression. -/
def progressions (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact A.powerset.filter (fun e => e.card=3 ∧ ∃ a b c : ℕ,
    e={a,b,c} ∧ a^2+c^2=2*b^2)

lemma mem_progressions {A e : Finset ℕ} :
    e ∈ progressions A ↔ e ⊆ A ∧ e.card=3 ∧ ∃ a b c : ℕ,
      e={a,b,c} ∧ a^2+c^2=2*b^2 := by
  classical
  simp only [progressions,mem_filter,mem_powerset]

lemma distinct_of_card_three {a b c : ℕ} (h : ({a,b,c}:Finset ℕ).card=3) :
    a≠b ∧ a≠c ∧ b≠c := by
  simp only [card_insert_eq_ite,card_singleton,mem_insert,mem_singleton] at h
  split_ifs at h <;> simp_all

-- Unused development declaration omitted.

-- Unused development declaration omitted.

/-- The existing ordered progression count bounds these supports. -/
lemma progression_card_bound (N : ℕ) :
    (progressions (Icc 1 N)).card ≤ (squareAPs N).card := by
  classical
  let f : (ℕ × ℕ) × ℕ → Finset ℕ := fun t => {t.1.1,t.1.2,t.2}
  have hsub : progressions (Icc 1 N) ⊆ (squareAPs N).image f := by
    intro e he
    obtain ⟨heA,hcard,a,b,c,rfl,hs⟩ := mem_progressions.mp he
    obtain ⟨hab,hac,hbc⟩ := distinct_of_card_three hcard
    have ha := heA (by simp : a ∈ ({a,b,c}:Finset ℕ))
    have hb := heA (by simp : b ∈ ({a,b,c}:Finset ℕ))
    have hc := heA (by simp : c ∈ ({a,b,c}:Finset ℕ))
    rcases lt_or_gt_of_ne hac with hh | hh
    · have hab' : a<b := by nlinarith
      have hbc' : b<c := by nlinarith
      refine mem_image.mpr ⟨((a,b),c),?_,rfl⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hc⟩,hab',hbc',hs⟩
    · have hcb' : c<b := by nlinarith
      have hba' : b<a := by nlinarith
      refine mem_image.mpr ⟨((c,b),a),?_,?_⟩
      · exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hc,hb⟩,ha⟩,
          hcb',hba',by nlinarith only [hs]⟩
      · ext n
        simp only [f,mem_insert,mem_singleton]
        tauto
  exact (card_le_card hsub).trans card_image_le

lemma ap_free_of_avoids {A B : Finset ℕ} (hBA : B ⊆ A)
    (havoid : ∀ e ∈ progressions A, ¬e ⊆ B) :
    ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) := by
  intro x hx y hy z hz he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
  by_contra hne
  have hab : a≠b := fun h => hne (congrArg (fun n : ℕ => n^2) h)
  have hac : a≠c := by intro h; subst c; apply hne; nlinarith only [he]
  have hbc : b≠c := by intro h; subst c; apply hne; nlinarith only [he]
  have heB : ({a,b,c}:Finset ℕ) ⊆ B := by
    intro n hn
    simp only [mem_insert,mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> assumption
  apply havoid {a,b,c} _ heB
  exact mem_progressions.mpr ⟨heB.trans hBA,by simp [hab,hac,hbc],a,b,c,rfl,by omega⟩

end Erdos773.SquareProgressionSupports
end
end EndpointModule073
-- End SquareProgressionSupports.lean

-- Begin PrimitiveSquareCollisions.lean
section EndpointModule074

/-
Primitive gap parameters for four distinct positive roots with equal square
sums. This is a counting tool, not a settlement of Erdős 773.
-/
namespace Erdos773.PrimitiveSquareCollisions
open Finset
set_option maxHeartbeats 1000000

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

/-- Increasing positive roots; every support has just one such ordering. -/
def ordered (N : ℕ) : Finset Quad :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter
    (fun q => q.1.1 < q.1.2 ∧ q.1.2 < q.2.1 ∧ q.2.1 < q.2.2 ∧
      q.1.1 ^ 2 + q.2.2 ^ 2 = q.1.2 ^ 2 + q.2.1 ^ 2)

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.PrimitiveSquareCollisions
end EndpointModule074
-- End PrimitiveSquareCollisions.lean

-- Begin ParityTriangleCount.lean
section EndpointModule075

/-
Elementary parity-sensitive lattice counts for triangular parameter regions.
These estimates are auxiliary to square-collision counting.
-/
noncomputable section
namespace Erdos773.ParityTriangleCount
open Finset
set_option maxHeartbeats 1000000

lemma interval_card_bound (S : Finset ℕ) (L U : ℝ) (hLU : L ≤ U)
    (h : ∀ n ∈ S, L ≤ n ∧ (n : ℝ) ≤ U) : (S.card : ℝ) ≤ U-L+1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [card_empty,Nat.cast_zero]
    linarith
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := min'_mem _ hS
    have hb : b ∈ S := max'_mem _ hS
    have hab : a ≤ b := min'_le _ _ hb
    have hsub : S ⊆ Icc a b := fun n hn => mem_Icc.mpr
      ⟨min'_le _ _ hn,le_max' _ _ hn⟩
    have hc := card_le_card hsub
    have hcard : (Icc a b).card = b-a+1 := by simp; omega
    rw [hcard] at hc
    have hcast : (S.card : ℝ) ≤ (b : ℝ)-a+1 := by
      exact_mod_cast (show S.card ≤ b-a+1 from hc)
    have hal := (h a ha).1
    have hbu := (h b hb).2
    linarith

lemma residue_interval_card_bound (S : Finset ℕ) (L U : ℝ) (q s : ℕ)
    (hq : 0 < q) (hLU : L ≤ U)
    (h : ∀ n ∈ S, n%q=s ∧ L ≤ n ∧ (n : ℝ) ≤ U) :
    (S.card : ℝ) ≤ (U-L)/q+1 := by
  let T := S.image (fun n => n/q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hinj : Set.InjOn (fun n : ℕ => n/q) S := by
    intro n hn m hm he
    have hn' := (h n hn).1
    have hm' := (h m hm).1
    dsimp only at he
    have hnq := Nat.mod_add_div n q
    have hmq := Nat.mod_add_div m q
    rw [hn',he] at hnq
    rw [hm'] at hmq
    omega
  have hcard : T.card = S.card := card_image_iff.mpr hinj
  have hT : ∀ n ∈ T, (L-s)/q ≤ n ∧ (n : ℝ) ≤ (U-s)/q := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨hmod,hl,hu⟩ := h m hm
    have he : m = q*(m/q)+s := by have hh := Nat.mod_add_div m q; omega
    have heR : (m : ℝ) = q*(m/q : ℕ)+s := by exact_mod_cast he
    constructor
    · apply (div_le_iff₀ hqR).mpr
      nlinarith only [heR,hl]
    · apply (le_div_iff₀ hqR).mpr
      nlinarith only [heR,hu]
  have hh := interval_card_bound T ((L-s)/q) ((U-s)/q)
    (div_le_div_of_nonneg_right (by linarith) hqR.le) hT
  rw [hcard] at hh
  have heq : (U-s)/q-(L-s)/q+1 = (U-L)/q+1 := by ring
  rwa [heq] at hh

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.ParityTriangleCount
end
end EndpointModule075
-- End ParityTriangleCount.lean

-- Begin PeriodicCollisionWeights.lean
section EndpointModule076

/-
Periodic averaging of the parity and small-prime sieve weights. The estimates
are uniform and have explicit additive errors.
-/
noncomputable section
namespace Erdos773.PeriodicCollisionWeights
open Finset PrimitiveSquareCollisions ParityTriangleCount
set_option maxHeartbeats 1000000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

lemma inverse_square_sum (M : ℕ) : (∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) ≤ 2 := by
  have hstrong (M : ℕ) : (∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) ≤ 2-2/((M:ℝ)+1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      have hstep : 1/((M:ℝ)+1)^2 ≤ 2/((M:ℝ)+1)-2/((M:ℝ)+2) := by
        have h1 : (0:ℝ) < M+1 := by positivity
        have h2 : (0:ℝ) < M+2 := by positivity
        apply (div_le_iff₀ (sq_pos_of_pos h1)).mpr
        field_simp
        nlinarith
      have he : (M:ℝ)+1+1 = M+2 := by ring
      rw [he]
      linarith
  have hh := hstrong M
  have hn : (0:ℝ) ≤ 2/((M:ℝ)+1) := by positivity
  linarith

end Erdos773.PeriodicCollisionWeights
end
end EndpointModule076
-- End PeriodicCollisionWeights.lean

-- Begin SharpSquareCollisionCount.lean
section EndpointModule077

/-
Sharper counts for ordered four-root square-sum collisions, retaining the
primitive gap and parity information. This file does not settle Erdős 773.
-/
noncomputable section
namespace Erdos773.SharpSquareCollisionCount
open Finset PrimitiveSquareCollisions ParityTriangleCount PeriodicCollisionWeights
set_option maxHeartbeats 1000000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.
-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.SharpSquareCollisionCount
end
end EndpointModule077
-- End SharpSquareCollisionCount.lean

-- Begin GaussianDivisorBound.lean
section EndpointModule078

/-
Uniform subpower bounds for the number of Gaussian prime-factor submultisets.
This is an arithmetic ingredient for collision codegree estimates, not a
settlement of the square-Sidon conjecture.
-/
namespace Erdos773.GaussianDivisorBound
open Finset Filter UniqueFactorizationMonoid
set_option maxHeartbeats 1000000

noncomputable local instance : NormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- The nonnegative integral Gaussian norm. -/
def gNorm : GaussianInt →* ℕ :=
  Int.natAbsHom.toMonoidHom.comp (Zsqrtd.normMonoidHom : GaussianInt →* ℤ)

lemma gNorm_eq (z : GaussianInt) : gNorm z = z.norm.natAbs := rfl

lemma gNorm_associated {z w : GaussianInt} (h : Associated z w) : gNorm z = gNorm w := by
  exact congrArg Int.natAbs (Zsqrtd.norm_eq_of_associated (by norm_num) h)

lemma gNorm_prime {z : GaussianInt} (hz : Prime z) : 2 ≤ gNorm z := by
  have h0 : gNorm z ≠ 0 := by
    simpa [gNorm_eq, GaussianInt.norm_eq_zero] using hz.ne_zero
  have h1 : gNorm z ≠ 1 := fun h => hz.not_unit (Zsqrtd.norm_eq_one_iff.mp h)
  omega

/-- A finite box containing all Gaussian integers of norm less than K. -/
def normBox (K : ℕ) : Finset GaussianInt :=
  ((Icc (-(K : ℤ)) K) ×ˢ (Icc (-(K : ℤ)) K)).image (fun p => ⟨p.1, p.2⟩)

lemma mem_normBox {K : ℕ} {z : GaussianInt} (h : gNorm z < K) : z ∈ normBox K := by
  have hnorm : z.re ^ 2 + z.im ^ 2 < (K : ℤ) := by
    have hh : (gNorm z : ℤ) < K := by exact_mod_cast h
    rw [gNorm_eq, GaussianInt.abs_natCast_norm] at hh
    simpa [Zsqrtd.norm, pow_two] using hh
  have hK : (0 : ℤ) ≤ K := by positivity
  have hre : -(K : ℤ) ≤ z.re ∧ z.re ≤ K := by
    constructor <;> nlinarith [sq_nonneg z.im, sq_nonneg (z.re + K), sq_nonneg (z.re - K)]
  have him : -(K : ℤ) ≤ z.im ∧ z.im ≤ K := by
    constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.im + K), sq_nonneg (z.im - K)]
  exact mem_image.mpr ⟨(z.re,z.im), mem_product.mpr ⟨mem_Icc.mpr hre,mem_Icc.mpr him⟩, rfl⟩

/-- The ordinary divisor-function proof applies to Gaussian prime factors:
there are finitely many factors with small norm, and all others absorb the
linear exponent-count cost into an arbitrarily small power of their norm. -/
theorem factor_submultisets_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ z : GaussianInt, z ≠ 0 →
      ((Iic (normalizedFactors z)).card : ℝ) ≤ C * (gNorm z : ℝ) ^ δ := by
  classical
  let b : ℝ := 2 ^ δ
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + 1 / (b - 1)
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ 1 / (b - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcb : c * (b - 1) = b := by
    dsimp [c]
    field_simp [show b - 1 ≠ 0 by linarith]
    ring
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ c * b ^ e := by
    have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ b) e
    calc
      (e : ℝ) + 1 ≤ c + (e : ℝ) * b := by
        nlinarith [mul_nonneg (Nat.cast_nonneg e) (le_of_lt (sub_pos.mpr hb))]
      _ = c * (1 + (e : ℝ) * (b - 1)) := by
        rw [mul_add, mul_one, ← mul_left_comm, hcb]
      _ ≤ c * b ^ e := mul_le_mul_of_nonneg_left hber hcpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ≥ K, (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    exact eventually_atTop.mp
      (tendsto_atTop.mp ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop) 2)
  refine ⟨c ^ (normBox K).card, pow_pos hcpos _, fun z hz => ?_⟩
  let s := normalizedFactors z
  have hfactor (p : GaussianInt) (hp : p ∈ s.toFinset) :
      ((s.count p + 1 : ℕ) : ℝ) ≤
        (if gNorm p < K then c else 1) * ((gNorm p : ℝ) ^ δ) ^ s.count p := by
    have hp2 : (2 : ℝ) ≤ gNorm p := by
      exact_mod_cast gNorm_prime (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp))
    by_cases hpk : gNorm p < K
    · rw [if_pos hpk]
      calc
        ((s.count p + 1 : ℕ) : ℝ) = (s.count p : ℝ) + 1 := by push_cast; rfl
        _ ≤ c * b ^ s.count p := hsmall _
        _ ≤ c * ((gNorm p : ℝ) ^ δ) ^ s.count p := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpk, one_mul]
      calc
        ((s.count p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s.count p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := s.count p)))
        _ ≤ ((gNorm p : ℝ) ^ δ) ^ s.count p :=
          pow_le_pow_left₀ (by norm_num) (hK _ (by omega)) _
  have hcoeff : (∏ p ∈ s.toFinset, if gNorm p < K then c else 1) ≤ c ^ (normBox K).card := by
    have hcard : (s.toFinset.filter (fun p => gNorm p < K)).card ≤ (normBox K).card :=
      card_le_card (fun p hp => mem_normBox (mem_filter.mp hp).2)
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hc hcard
  have hprod : (∏ p ∈ s.toFinset, (gNorm p : ℝ) ^ s.count p) = gNorm z := by
    have hh : (∏ p ∈ s.toFinset, gNorm p ^ s.count p) = gNorm z := by
      rw [← Finset.prod_multiset_map_count, ← map_multiset_prod]
      exact gNorm_associated (prod_normalizedFactors hz)
    exact_mod_cast hh
  have hrpow : (∏ p ∈ s.toFinset, ((gNorm p : ℝ) ^ δ) ^ s.count p) = (gNorm z : ℝ) ^ δ := by
    calc
      _ = ∏ p ∈ s.toFinset, ((gNorm p : ℝ) ^ s.count p) ^ δ := by
        apply prod_congr rfl
        intro p hp
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),
          ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm δ]
      _ = (∏ p ∈ s.toFinset, (gNorm p : ℝ) ^ s.count p) ^ δ :=
        Real.finset_prod_rpow _ _ (by intros; positivity) _
      _ = _ := by rw [hprod]
  change ((Iic s).card : ℝ) ≤ _
  calc
    _ = ∏ p ∈ s.toFinset, ((s.count p + 1 : ℕ) : ℝ) := by rw [Multiset.card_Iic, Nat.cast_prod]
    _ ≤ ∏ p ∈ s.toFinset, (if gNorm p < K then c else 1) * ((gNorm p : ℝ) ^ δ) ^ s.count p :=
      prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ s.toFinset, if gNorm p < K then c else 1) * (gNorm z : ℝ) ^ δ := by
      rw [prod_mul_distrib, hrpow]
    _ ≤ c ^ (normBox K).card * (gNorm z : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg _) δ)

end Erdos773.GaussianDivisorBound
end EndpointModule078
-- End GaussianDivisorBound.lean

-- Begin SquareSumRepresentations.lean
section EndpointModule079

/-
Uniform subpower estimates for representations as a sum of two positive
squares. These supply the same-side case of square-collision codegrees.
-/
namespace Erdos773.SquareSumRepresentations
open Finset Filter UniqueFactorizationMonoid GaussianDivisorBound
set_option maxHeartbeats 1000000

noncomputable local instance : NormalizationMonoid GaussianInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Positive first-quadrant Gaussian integers have no distinct associates. -/
lemma eq_of_associated_positive {z w : GaussianInt}
    (hzr : 0 < z.re) (hzi : 0 < z.im) (hwr : 0 < w.re) (hwi : 0 < w.im)
    (h : Associated z w) : z = w := by
  obtain ⟨u, hu⟩ := h
  have hn : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  have hs : (u : GaussianInt).re ^ 2 + (u : GaussianInt).im ^ 2 = 1 := by
    simpa [Zsqrtd.norm, pow_two] using hn
  have hr : -1 ≤ (u : GaussianInt).re ∧ (u : GaussianInt).re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).im]
  have hi : -1 ≤ (u : GaussianInt).im ∧ (u : GaussianInt).im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re]
  have hre := congrArg Zsqrtd.re hu
  have him := congrArg Zsqrtd.im hu
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  have he : (u : GaussianInt).re = 1 ∧ (u : GaussianInt).im = 0 := by
    rcases (by omega : (u : GaussianInt).re = -1 ∨ (u : GaussianInt).re = 0 ∨
      (u : GaussianInt).re = 1) with h | h | h <;> rw [h] at hs hre him
    · have : (u : GaussianInt).im = 0 := by nlinarith
      simp [this] at hre
      omega
    · rcases (by nlinarith [sq_nonneg ((u : GaussianInt).im - 1),
          sq_nonneg ((u : GaussianInt).im + 1)] :
          (u : GaussianInt).im = -1 ∨ (u : GaussianInt).im = 1) with hi' | hi'
      · simp [hi'] at him
        omega
      · simp [hi'] at hre
        omega
    · exact ⟨h, by nlinarith⟩
  apply Zsqrtd.ext <;> simp_all

/-- Ordered positive representations, with a root-height cutoff. -/
def reps (N T : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = T)

def gaussianPair (p : ℕ × ℕ) : GaussianInt := ⟨p.1, p.2⟩

lemma gaussianPair_norm (p : ℕ × ℕ) :
    (gaussianPair p).norm = (p.1 ^ 2 + p.2 ^ 2 : ℕ) := by
  simp [gaussianPair, Zsqrtd.norm, pow_two]

lemma gaussianPair_ne_zero {N T : ℕ} {p : ℕ × ℕ} (hp : p ∈ reps N T) :
    gaussianPair p ≠ 0 := by
  have hpos := (mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1).1
  intro h
  have hh := congrArg Zsqrtd.re h
  simp [gaussianPair] at hh
  omega

/-- Inject each representation into the prime-factor submultisets of T
in the Gaussian integers. Positivity makes the injection unit-free. -/
theorem reps_card_le_factor_submultisets (N T : ℕ) (hT : 0 < T) :
    (reps N T).card ≤ (Iic (normalizedFactors (T : GaussianInt))).card := by
  classical
  apply card_le_card_of_injOn (fun p => normalizedFactors (gaussianPair p))
  · intro p hp
    have hn : (gaussianPair p).norm = T := by rw [gaussianPair_norm, (mem_filter.mp hp).2]
    have hd : gaussianPair p ∣ (T : GaussianInt) := by
      refine ⟨star (gaussianPair p), ?_⟩
      have hh := Zsqrtd.norm_eq_mul_conj (gaussianPair p)
      simpa [hn] using hh
    exact mem_Iic.mpr ((dvd_iff_normalizedFactors_le_normalizedFactors
      (gaussianPair_ne_zero hp) (by exact_mod_cast hT.ne')).mp hd)
  · intro p hp q hq he
    have ha := (associated_iff_normalizedFactors_eq_normalizedFactors
      (gaussianPair_ne_zero hp) (gaussianPair_ne_zero hq)).mpr he
    have hpp := mem_product.mp (mem_filter.mp hp).1
    have hqp := mem_product.mp (mem_filter.mp hq).1
    have hh : gaussianPair p = gaussianPair q := eq_of_associated_positive
      (by change (0 : ℤ) < p.1; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hpp.1).1)) (by change (0 : ℤ) < p.2; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hpp.2).1))
      (by change (0 : ℤ) < q.1; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hqp.1).1)) (by change (0 : ℤ) < q.2; exact_mod_cast (Nat.lt_of_succ_le (mem_Icc.mp hqp.2).1)) ha
    apply Prod.ext
    · have he := congrArg Zsqrtd.re hh
      simpa [gaussianPair] using he
    · have he := congrArg Zsqrtd.im hh
      simpa [gaussianPair] using he

/-- The representation count is subpower in the represented integer,
uniformly in the cutoff N. -/
theorem reps_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N T : ℕ, 0 < T →
      ((reps N T).card : ℝ) ≤ C * (T : ℝ) ^ δ := by
  obtain ⟨C,hC,hb⟩ := factor_submultisets_subpower (δ/2) (by linarith)
  refine ⟨C,hC,fun N T hT => ?_⟩
  have hnorm : gNorm (T : GaussianInt) = T ^ 2 := by
    simp [gNorm_eq, Zsqrtd.norm_natCast, pow_two, Int.natAbs_mul]
  calc
    _ ≤ ((Iic (normalizedFactors (T : GaussianInt))).card : ℝ) := by
      exact_mod_cast reps_card_le_factor_submultisets N T hT
    _ ≤ C * (gNorm (T : GaussianInt) : ℝ) ^ (δ/2) :=
      hb _ (by exact_mod_cast hT.ne')
    _ = C * (T : ℝ) ^ δ := by
      rw [hnorm, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg T)]
      congr 2
      push_cast
      ring

/-- Root-height version, covering every positive sum at most 2*N^2. -/
theorem reps_height_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N T : ℕ, 0 < T → T ≤ 2*N^2 →
      ((reps N T).card : ℝ) ≤ C * (N : ℝ) ^ δ := by
  obtain ⟨C,hC,hb⟩ := reps_subpower (δ/2) (by linarith)
  refine ⟨C * 2^(δ/2), by positivity,fun N T hT hTN => ?_⟩
  have hh : (T : ℝ) ≤ 2 * (N : ℝ)^2 := by exact_mod_cast hTN
  calc
    _ ≤ C * (T : ℝ)^(δ/2) := hb N T hT
    _ ≤ C * (2 * (N : ℝ)^2)^(δ/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hh (by linarith)) hC.le
    _ = C * 2^(δ/2) * (N : ℝ)^δ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ)*(δ/2)=δ by ring]
      ring

end Erdos773.SquareSumRepresentations
end EndpointModule079
-- End SquareSumRepresentations.lean

-- Begin CollisionBounds.lean
section EndpointModule080

/- Bounds for square-difference representations. -/

namespace Erdos773

open Finset Filter

lemma difference_factor {x y D : ℕ} (hxy : y < x) (he : x ^ 2 = y ^ 2 + D) :
    D = (x - y) * (x + y) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hxy.le
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [he]

def squareDifferenceReps (N D : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 < p.2 ∧ p.2 ^ 2 = p.1 ^ 2 + D)

lemma squareDifferenceReps_card_le (N D : ℕ) (hD : 0 < D) :
    (squareDifferenceReps N D).card ≤ D.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2 + p.1, difference_factor hp.1 hp.2⟩, hD.ne'⟩
  · intro p hp q hq heq
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq⟩ := Finset.mem_filter.mp hq
    have hpF := difference_factor hp.1 hp.2
    have hqF := difference_factor hq.1 hq.2
    dsimp at heq
    rw [← heq] at hqF
    have hsum : p.2 + p.1 = q.2 + q.1 := by
      exact mul_left_cancel₀ (Nat.sub_pos_of_lt hp.1).ne' (hpF.symm.trans hqF)
    apply Prod.ext <;> omega

lemma squareDifferenceReps_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N D : ℕ, 0 < D → D ≤ N ^ 2 →
      ((squareDifferenceReps N D).card : ℝ) ≤ C * (N : ℝ) ^ (2 * δ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_subpower δ hδ
  refine ⟨C, hC, ?_⟩
  intro N D hD hDN
  have hDN' : (D : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hDN
  calc
    ((squareDifferenceReps N D).card : ℝ) ≤ (D.divisors.card : ℝ) := by
      exact_mod_cast squareDifferenceReps_card_le N D hD
    _ ≤ C * (D : ℝ) ^ δ := hbound D
    _ ≤ C * ((N : ℝ) ^ 2) ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg D) hDN' hδ.le) hC.le
    _ = C * (N : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      norm_num

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.


end Erdos773
end EndpointModule080
-- End CollisionBounds.lean

-- Begin SquareCollisionCodegrees.lean
section EndpointModule081

/-
Subpower pair codegrees for four-distinct-root square-sum collisions.
The result concerns local hypergraph counts. It is not a near-linear
Sidon extraction theorem.
-/
namespace Erdos773.SquareCollisionCodegrees
open Finset Filter
set_option maxHeartbeats 1000000

/-- Unordered four-root supports, counted once each. -/
noncomputable def edges (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact A.powerset.filter (fun e => e.card = 4 ∧ ∃ a b c d : ℕ,
    e = {a,b,c,d} ∧ a^2+b^2=c^2+d^2)

/-- Edges containing both prescribed roots. -/
noncomputable def pairEdges (A : Finset ℕ) (a b : ℕ) : Finset (Finset ℕ) :=
  (edges A).filter (fun e => a ∈ e ∧ b ∈ e)

lemma relabel {e : Finset ℕ} {a b : ℕ} (hab : a ≠ b)
    (ha : a ∈ e) (hb : b ∈ e)
    (he : ∃ u v w x : ℕ, e = {u,v,w,x} ∧ u^2+v^2=w^2+x^2) :
    ∃ c ∈ e, ∃ d ∈ e, e = {a,b,c,d} ∧
      (a^2+b^2=c^2+d^2 ∨ a^2+c^2=b^2+d^2 ∨ a^2+d^2=b^2+c^2) := by
  obtain ⟨u,v,w,x,rfl,he⟩ := he
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl
  all_goals try exact (hab rfl).elim
  all_goals
    first
    | exact ⟨u, by simp, v, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨u, by simp, w, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨u, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨v, by simp, w, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨v, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨w, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩

lemma pairEdges_cover {N a b : ℕ} (hab : a < b) :
    pairEdges (Icc 1 N) a b ⊆
      (SquareSumRepresentations.reps N (a^2+b^2)).image (fun p => ({a,b,p.1,p.2} : Finset ℕ)) ∪
      (squareDifferenceReps N (b^2-a^2)).image (fun p => ({a,b,p.1,p.2} : Finset ℕ)) := by
  classical
  intro e he
  obtain ⟨he,ha,hb⟩ := mem_filter.mp he
  obtain ⟨heA,hcard,heq⟩ := mem_filter.mp he
  have heA' := mem_powerset.mp heA
  obtain ⟨c,hc,d,hd,he,hcase⟩ := relabel hab.ne ha hb heq
  have hcN := heA' hc
  have hdN := heA' hd
  rcases hcase with hs | hs | hs
  · apply mem_union_left
    exact mem_image.mpr ⟨(c,d), mem_filter.mpr ⟨mem_product.mpr ⟨hcN,hdN⟩,hs.symm⟩,he.symm⟩
  · apply mem_union_right
    have hcd : d < c := by nlinarith
    refine mem_image.mpr ⟨(d,c), mem_filter.mpr ⟨mem_product.mpr ⟨hdN,hcN⟩,hcd,?_⟩,?_⟩
    · change c^2 = d^2 + (b^2-a^2)
      have hh : a^2 ≤ b^2 := Nat.pow_le_pow_left hab.le 2
      have ht := Nat.sub_add_cancel hh
      omega
    · rw [he]
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
  · apply mem_union_right
    have hcd : c < d := by nlinarith
    refine mem_image.mpr ⟨(c,d), mem_filter.mpr ⟨mem_product.mpr ⟨hcN,hdN⟩,hcd,?_⟩,he.symm⟩
    change d^2 = c^2 + (b^2-a^2)
    have hh : a^2 ≤ b^2 := Nat.pow_le_pow_left hab.le 2
    have ht := Nat.sub_add_cancel hh
    omega

/-- Each pair has only two kinds of completions: a fixed sum or a fixed
positive difference. The complement's order incurs no additional factor. -/
theorem pairEdges_card_bound {N a b : ℕ} (hab : a < b) :
    (pairEdges (Icc 1 N) a b).card ≤
      (SquareSumRepresentations.reps N (a^2+b^2)).card +
      (squareDifferenceReps N (b^2-a^2)).card := by
  classical
  exact (card_le_card (pairEdges_cover hab)).trans
    ((card_union_le _ _).trans (Nat.add_le_add (card_image_le) (card_image_le)))

/-- Uniform subpower pair codegrees at root height N. -/
theorem pair_codegree_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N a b : ℕ, 1 ≤ a → a < b → b ≤ N →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ C * (N : ℝ)^δ := by
  obtain ⟨C,hC,hc⟩ := SquareSumRepresentations.reps_height_subpower δ hδ
  obtain ⟨D,hD,hd⟩ := squareDifferenceReps_subpower (δ/2) (by linarith)
  refine ⟨C+D,by positivity,fun N a b ha hab hb => ?_⟩
  have haN : a ≤ N := hab.le.trans hb
  have hb2 := Nat.pow_le_pow_left hb 2
  have ha2 := Nat.pow_le_pow_left haN 2
  have hsum : 0 < a^2+b^2 := by positivity
  have hsumN : a^2+b^2 ≤ 2*N^2 := by omega
  have hdiff : 0 < b^2-a^2 := Nat.sub_pos_of_lt (by nlinarith)
  have hdiffN : b^2-a^2 ≤ N^2 := (Nat.sub_le _ _).trans hb2
  have h1 := hc N _ hsum hsumN
  have h2 := hd N _ hdiff hdiffN
  rw [show 2*(δ/2)=δ by ring] at h2
  have h3 : ((pairEdges (Icc 1 N) a b).card : ℝ) ≤
      (SquareSumRepresentations.reps N (a^2+b^2)).card +
      (squareDifferenceReps N (b^2-a^2)).card := by
    exact_mod_cast pairEdges_card_bound hab
  nlinarith only [h1,h2,h3]

lemma edges_mono {A B : Finset ℕ} (hAB : A ⊆ B) : edges A ⊆ edges B := by
  classical
  intro e he
  obtain ⟨heA,h4,hs⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp heA).trans hAB),h4,hs⟩

lemma pairEdges_mono {A B : Finset ℕ} (hAB : A ⊆ B) (a b : ℕ) :
    pairEdges A a b ⊆ pairEdges B a b := by
  classical
  intro e he
  obtain ⟨he,ha,hb⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨edges_mono hAB he,ha,hb⟩

lemma pairEdges_comm (A : Finset ℕ) (a b : ℕ) : pairEdges A a b = pairEdges A b a := by
  classical
  ext e
  simp [pairEdges,and_comm]

/-- Coefficient-free, unordered, eventually uniform codegree bound. -/
theorem eventually_pair_codegree_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ (N : ℝ)^δ := by
  obtain ⟨C,hC,hb⟩ := pair_codegree_subpower (δ/2) (by linarith)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C,eventually_ge_atTop 1] with N hlarge hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hord (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbN : b ≤ N) :
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ (N : ℝ)^δ := by
    calc
      _ ≤ C*(N : ℝ)^(δ/2) := hb N a b ha hab hbN
      _ ≤ (N : ℝ)^(δ/2)*(N : ℝ)^(δ/2) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with hh | hh
  · exact hord a b (mem_Icc.mp ha).1 hh (mem_Icc.mp hb).2
  · rw [pairEdges_comm]
    exact hord b a (mem_Icc.mp hb).1 hh (mem_Icc.mp ha).2

end Erdos773.SquareCollisionCodegrees
end EndpointModule081
-- End SquareCollisionCodegrees.lean

-- Begin SquareCollisionIntersections.lean
section EndpointModule082

/-
In a progression-free set of square values, distinct four-root collision
supports intersect in at most two roots. This is a structural input to
selection, not a bound for the maximum Sidon subset.
-/
namespace Erdos773.SquareCollisionIntersections
open Finset SquareCollisionCodegrees
set_option maxHeartbeats 1000000

lemma distinct_of_card_four {a b c d : ℕ} (h : ({a,b,c,d} : Finset ℕ).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [card_insert_eq_ite, card_singleton, mem_insert, mem_singleton] at h
  split_ifs at h <;> simp_all

lemma sum_four_squares {a b c d : ℕ} (h : ({a,b,c,d} : Finset ℕ).card = 4) :
    (∑ n ∈ ({a,b,c,d} : Finset ℕ), n^2) = a^2+b^2+c^2+d^2 := by
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := distinct_of_card_four h
  simp [hab,hac,had,hbc,hbd,hcd,add_assoc]

lemma partner {e : Finset ℕ} (he4 : e.card = 4) {a : ℕ} (ha : a ∈ e)
    (he : ∃ u v w x : ℕ, e = {u,v,w,x} ∧ u^2+v^2=w^2+x^2) :
    ∃ t ∈ e, t ≠ a ∧ (∑ n ∈ e, n^2) = 2*(a^2+t^2) := by
  obtain ⟨u,v,w,x,rfl,hs⟩ := he
  obtain ⟨huv,huw,hux,hvw,hvx,hwx⟩ := distinct_of_card_four he4
  rw [sum_four_squares he4]
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨v,by simp,huv.symm,by omega⟩
  · exact ⟨u,by simp,huv,by omega⟩
  · exact ⟨x,by simp,hwx.symm,by omega⟩
  · exact ⟨w,by simp,hwx,by omega⟩

/-- The three possible pair partitions of a four-root support. -/
lemma partitions {A : Finset ℕ} {a b c d : ℕ}
    (he : ({a,b,c,d} : Finset ℕ) ∈ edges A) :
    a^2+b^2=c^2+d^2 ∨ a^2+c^2=b^2+d^2 ∨ a^2+d^2=b^2+c^2 := by
  classical
  obtain ⟨_,h4,hbal⟩ := mem_filter.mp he
  obtain ⟨t,ht,hne,hs⟩ := partner h4 (by simp : a ∈ ({a,b,c,d} : Finset ℕ)) hbal
  rw [sum_four_squares h4] at hs
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact (hne rfl).elim
  · omega
  · omega
  · omega

lemma fourth_eq {A : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    {a b c d t : ℕ}
    (he : ({a,b,c,d} : Finset ℕ) ∈ edges A)
    (hf : ({a,b,c,t} : Finset ℕ) ∈ edges A) : d = t := by
  classical
  have heA := mem_powerset.mp (mem_filter.mp he).1
  have hfA := mem_powerset.mp (mem_filter.mp hf).1
  have ha : a^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨a,heA (by simp),rfl⟩
  have hb : b^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨b,heA (by simp),rfl⟩
  have hc : c^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨c,heA (by simp),rfl⟩
  have hd : d^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨d,heA (by simp),rfl⟩
  have ht : t^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨t,hfA (by simp),rfl⟩
  have hs : d^2 = t^2 := by
    rcases partitions he with he | he | he <;>
      rcases partitions hf with hf | hf | hf
    all_goals first
    | omega
    | have hh := hAP hd ha ht (by omega); omega
    | have hh := hAP hd hb ht (by omega); omega
    | have hh := hAP hd hc ht (by omega); omega
  exact Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) hs

lemma complete_triple {e : Finset ℕ} (he : e.card = 4)
    {a b c : ℕ} (hT : ({a,b,c} : Finset ℕ) ⊆ e)
    (hTc : ({a,b,c} : Finset ℕ).card = 3) :
    ∃ d : ℕ, e = {a,b,c,d} := by
  have hdiff : (e \ {a,b,c}).card = 1 := by rw [card_sdiff_of_subset hT,he,hTc]
  obtain ⟨d,hd⟩ := card_eq_one.mp hdiff
  refine ⟨d,?_⟩
  calc
    e = {a,b,c} ∪ (e \ {a,b,c}) := (union_sdiff_of_subset hT).symm
    _ = {a,b,c,d} := by rw [hd]; ext z; simp only [mem_union,mem_insert,mem_singleton]; tauto

/-- In an AP-free square-value family, three common roots force equality
of the two four-root collision supports. -/
theorem eq_of_three_common {A e f : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (he : e ∈ edges A) (hf : f ∈ edges A) (hcommon : 3 ≤ (e ∩ f).card) : e = f := by
  classical
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq hcommon
  obtain ⟨a,b,c,hab,hac,hbc,hTrep⟩ := card_eq_three.mp hTc
  subst T
  have hTe : ({a,b,c} : Finset ℕ) ⊆ e := hT.trans inter_subset_left
  have hTf : ({a,b,c} : Finset ℕ) ⊆ f := hT.trans inter_subset_right
  obtain ⟨d,rfl⟩ := complete_triple (mem_filter.mp he).2.1 hTe hTc
  obtain ⟨t,rfl⟩ := complete_triple (mem_filter.mp hf).2.1 hTf hTc
  rw [fourth_eq hAP he hf]

/-- The exact intersection bound needed before linearizing the hypergraph. -/
theorem intersection_card_le_two {A e f : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (he : e ∈ edges A) (hf : f ∈ edges A) (hne : e ≠ f) : (e ∩ f).card ≤ 2 := by
  by_contra! hh
  exact hne (eq_of_three_common hAP he hf hh)

end Erdos773.SquareCollisionIntersections
end EndpointModule082
-- End SquareCollisionIntersections.lean

-- Begin SquareSupportCounting.lean
section EndpointModule083

/-
Identification of the ordered collision count with the unordered hyperedge
count, and the resulting explicit logarithmic upper bound. These are not
independent-set or Sidon-extraction theorems.
-/
noncomputable section
namespace Erdos773.SquareSupportCounting
open Finset Filter PrimitiveSquareCollisions SharpSquareCollisionCount
open SquareCollisionCodegrees SquareCollisionIntersections
set_option maxHeartbeats 1000000

def support (q : Quad) : Finset ℕ := {q.1.1,q.1.2,q.2.1,q.2.2}

-- Unused development declaration omitted.

-- Unused development declaration omitted.

lemma ordered_representation {N : ℕ} {e : Finset ℕ} (he : e ∈ edges (Icc 1 N)) :
    ∃ q ∈ ordered N, support q = e := by
  classical
  have heA := mem_powerset.mp (mem_filter.mp he).1
  have he4 := (mem_filter.mp he).2.1
  let f := e.orderIsoOfFin he4
  let a : ℕ := (f 0).val
  let b : ℕ := (f 1).val
  let c : ℕ := (f 2).val
  let d : ℕ := (f 3).val
  have hab : a < b := f.strictMono (by decide : (0:Fin 4)<1)
  have hbc : b < c := f.strictMono (by decide : (1:Fin 4)<2)
  have hcd : c < d := f.strictMono (by decide : (2:Fin 4)<3)
  have hrep : e = {a,b,c,d} := by
    ext n
    simp only [mem_insert,mem_singleton]
    constructor
    · intro hn
      obtain ⟨i,hi⟩ := f.surjective ⟨n,hn⟩
      have hiv := congrArg Subtype.val hi
      fin_cases i
      · exact Or.inl hiv.symm
      · exact Or.inr (Or.inl hiv.symm)
      · exact Or.inr (Or.inr (Or.inl hiv.symm))
      · exact Or.inr (Or.inr (Or.inr hiv.symm))
    · intro hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact (f 0).property
      · exact (f 1).property
      · exact (f 2).property
      · exact (f 3).property
  have hpart := partitions (hrep ▸ he)
  have heq : a^2+d^2=b^2+c^2 := by
    rcases hpart with hh | hh | hh
    · have hac := Nat.pow_lt_pow_left (hab.trans hbc) (by decide : (2:ℕ) ≠ 0)
      have hbd := Nat.pow_lt_pow_left (hbc.trans hcd) (by decide : (2:ℕ) ≠ 0)
      omega
    · have hab2 := Nat.pow_lt_pow_left hab (by decide : (2:ℕ) ≠ 0)
      have hcd2 := Nat.pow_lt_pow_left hcd (by decide : (2:ℕ) ≠ 0)
      omega
    · exact hh
  refine ⟨((a,b),(c,d)),mem_filter.mpr ⟨?_,hab,hbc,hcd,heq⟩,hrep.symm⟩
  simp only [mem_product]
  exact ⟨⟨heA (f 0).property,heA (f 1).property⟩,
    ⟨heA (f 2).property,heA (f 3).property⟩⟩

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.SquareSupportCounting
end
end EndpointModule083
-- End SquareSupportCounting.lean

-- Begin AverageAPBound.lean
section EndpointModule084

/- An average bound for three-term arithmetic progressions of squares.
This file does not settle Erdős 773. -/
namespace Erdos773.AverageAP
open Finset
set_option maxHeartbeats 1000000

lemma ap_parametrization {a b c N : ℕ} (hab : a < b) (hbc : b < c)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) (hcN : c ≤ N) :
    ∃ r ∈ Icc 1 (4 * N), ∃ s ∈ Icc 1 (4 * N),
      ∃ k ∈ Icc 1 (4 * N / (max r s) ^ 2),
        4 * a + k * r ^ 2 = 2 * k * s ^ 2 ∧
        4 * b = k * (2 * s ^ 2 + 2 * r * s + r ^ 2) ∧
        4 * c = k * (2 * s ^ 2 + 4 * r * s + r ^ 2) := by
  obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
  let y := c - b
  let d := 2 * b - (a + c)
  change 0 < y at hy
  change 0 < d at hd
  change a + y + d = b at hb
  change a + 2 * y + d = c at hc
  change 2 * y ^ 2 = d * (2 * a + d) at hfac
  obtain ⟨g,r,s,hg,hrs,hdr,hys⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left y hd)
  have hr : 0 < r := by
    by_contra! hh
    have hz : r = 0 := by omega
    rw [hz, zero_mul] at hdr
    omega
  have hs : 0 < s := by
    by_contra! hh
    have hz : s = 0 := by omega
    rw [hz, zero_mul] at hys
    omega
  have hfac' : (2 * g) * s ^ 2 = r * (2 * a + r * g) := by
    apply Nat.eq_of_mul_eq_mul_right hg
    simpa only [hdr, hys, pow_two, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
      using hfac
  have hr2g : r ∣ 2 * g := (hrs.pow_right 2).dvd_of_dvd_mul_right
    ⟨2 * a + r * g, hfac'⟩
  obtain ⟨k,hkg⟩ := hr2g
  have hk : 0 < k := by
    by_contra! hh
    have hz : k = 0 := by omega
    rw [hz, mul_zero] at hkg
    omega
  have he' : k * s ^ 2 = 2 * a + r * g := by
    apply Nat.eq_of_mul_eq_mul_left hr
    calc
      r * (k * s ^ 2) = (r * k) * s ^ 2 := by ring
      _ = _ := by rw [← hkg]; exact hfac'
  have hkr : k * r ^ 2 = 2 * d := by
    calc
      _ = r * (r * k) := by ring
      _ = r * (2 * g) := by rw [← hkg]
      _ = _ := by rw [hdr]; ring
  have hkrs : k * r * s = 2 * y := by
    calc
      _ = s * (r * k) := by ring
      _ = s * (2 * g) := by rw [← hkg]
      _ = _ := by rw [hys]; ring
  have hA : 4 * a + k * r ^ 2 = 2 * k * s ^ 2 := by
    rw [hkr]
    have hh : k * s ^ 2 = 2 * a + d := by simpa only [← hdr] using he'
    nlinarith only [hh]
  have hB : 4 * b = k * (2 * s ^ 2 + 2 * r * s + r ^ 2) := by
    nlinarith only [hb,hA,hkr,hkrs]
  have hC : 4 * c = k * (2 * s ^ 2 + 4 * r * s + r ^ 2) := by
    nlinarith only [hc,hA,hkr,hkrs]
  have hkmax : k * (max r s) ^ 2 ≤ 4 * N := by
    rcases le_total r s with h | h
    · rw [max_eq_right h]
      nlinarith only [hC, hcN, Nat.zero_le (k * r * s), Nat.zero_le (k * r ^ 2)]
    · rw [max_eq_left h]
      nlinarith only [hC, hcN, Nat.zero_le (k * r * s), Nat.zero_le (k * s ^ 2)]
  have hmax : 0 < max r s := lt_of_lt_of_le hr (le_max_left _ _)
  have hmaxN : max r s ≤ 4 * N := by
    have hh := Nat.mul_le_mul_right ((max r s) ^ 2) hk
    exact (Nat.le_self_pow (by decide : 2 ≠ 0) (max r s)).trans
      ((by simpa using hh : (max r s) ^ 2 ≤ k * (max r s) ^ 2).trans hkmax)
  have hkN := (Nat.le_div_iff_mul_le (pow_pos hmax 2)).mpr hkmax
  exact ⟨r, mem_Icc.mpr ⟨hr,(le_max_left r s).trans hmaxN⟩,
    s, mem_Icc.mpr ⟨hs,(le_max_right r s).trans hmaxN⟩,
    k, mem_Icc.mpr ⟨hk,hkN⟩, hA,hB,hC⟩

def parameterImage (M : ℕ) (rs : ℕ × ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (Icc 1 (M / (max rs.1 rs.2) ^ 2)).image (fun k =>
    (((2 * k * rs.2 ^ 2 - k * rs.1 ^ 2) / 4,
      k * (2 * rs.2 ^ 2 + 2 * rs.1 * rs.2 + rs.1 ^ 2) / 4),
      k * (2 * rs.2 ^ 2 + 4 * rs.1 * rs.2 + rs.1 ^ 2) / 4))

lemma squareAPs_card_le_parameters (N : ℕ) :
    (squareAPs N).card ≤
      ∑ r ∈ Icc 1 (4 * N), ∑ s ∈ Icc 1 (4 * N), 4 * N / (max r s) ^ 2 := by
  have hsub : squareAPs N ⊆
      ((Icc 1 (4 * N)) ×ˢ (Icc 1 (4 * N))).biUnion (parameterImage (4 * N)) := by
    rintro ⟨⟨a,b⟩,c⟩ ht
    obtain ⟨ht, hab, hbc, he⟩ := mem_filter.mp ht
    dsimp only at hab hbc he
    have hcN : c ≤ N := by
      simp only [mem_product, mem_Icc] at ht
      exact ht.2.2
    obtain ⟨r,hr,s,hs,k,hk,hA,hB,hC⟩ := ap_parametrization hab hbc he hcN
    apply mem_biUnion.mpr
    refine ⟨(r,s), mem_product.mpr ⟨hr,hs⟩, ?_⟩
    apply mem_image.mpr
    refine ⟨k, hk, ?_⟩
    have ha : 2 * k * s ^ 2 - k * r ^ 2 = 4 * a := by omega
    simp [ha, ← hB, ← hC]
  calc
    _ ≤ (((Icc 1 (4*N)) ×ˢ (Icc 1 (4*N))).biUnion (parameterImage (4*N))).card :=
      card_le_card hsub
    _ ≤ ∑ rs ∈ (Icc 1 (4*N)) ×ˢ (Icc 1 (4*N)), (parameterImage (4*N) rs).card :=
      card_biUnion_le
    _ ≤ ∑ rs ∈ (Icc 1 (4*N)) ×ˢ (Icc 1 (4*N)), 4*N / (max rs.1 rs.2) ^ 2 := by
      apply sum_le_sum
      intro rs hrs
      exact card_image_le.trans_eq (by simp)
    _ = _ := by rw [sum_product]

lemma max_sum_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, M / (max r s) ^ 2) ≤
      2 * ∑ r ∈ Icc 1 M, r * (M / r ^ 2) := by
  have hpoint (r s : ℕ) : M / (max r s) ^ 2 ≤
      (if s ≤ r then M / r ^ 2 else 0) + (if r ≤ s then M / s ^ 2 else 0) := by
    rcases le_total r s with h | h
    · simp [h]
    · simp [h]
  have hsum (r : ℕ) (hr : r ∈ Icc 1 M) :
      ∑ s ∈ Icc 1 M, (if s ≤ r then M / r ^ 2 else 0) = r * (M / r ^ 2) := by
    have hf : (Icc 1 M).filter (fun s => s ≤ r) = Icc 1 r := by
      ext s
      simp only [mem_filter, mem_Icc]
      have := (mem_Icc.mp hr).2
      omega
    rw [← sum_filter, hf]
    simp
  calc
    _ ≤ ∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M,
        ((if s ≤ r then M / r ^ 2 else 0) + (if r ≤ s then M / s ^ 2 else 0)) := by
      exact sum_le_sum (fun r hr => sum_le_sum (fun s hs => hpoint r s))
    _ = (∑ r ∈ Icc 1 M, ∑ s ∈ Icc 1 M, if s ≤ r then M / r ^ 2 else 0) +
        (∑ s ∈ Icc 1 M, ∑ r ∈ Icc 1 M, if r ≤ s then M / s ^ 2 else 0) := by
      simp only [sum_add_distrib]
      congr 1
      exact sum_comm
    _ = _ := by
      rw [sum_congr rfl hsum]
      omega

lemma sum_floor_bound (M : ℕ) :
    (∑ r ∈ Icc 1 M, (r : ℝ) * (M / r ^ 2 : ℕ)) ≤ (M : ℝ) * harmonic M := by
  have hp (r : ℕ) (hr : r ∈ Icc 1 M) :
      (r : ℝ) * (M / r ^ 2 : ℕ) ≤ (M : ℝ) / r := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hprod : (r : ℝ) ^ 2 * (M / r ^ 2 : ℕ) ≤ M := by
      exact_mod_cast Nat.mul_div_le M (r ^ 2)
    apply (le_div_iff₀ hrpos).mpr
    nlinarith only [hprod]
  calc
    _ ≤ ∑ r ∈ Icc 1 M, (M : ℝ) / r := sum_le_sum hp
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [div_eq_mul_inv, mul_sum]

lemma squareAPs_log_bound (N : ℕ) :
    ((squareAPs N).card : ℝ) ≤ 8 * (N : ℝ) * (1 + Real.log (4 * N)) := by
  have hnat := (squareAPs_card_le_parameters N).trans (max_sum_bound (4 * N))
  have hreal : ((squareAPs N).card : ℝ) ≤
      2 * ∑ r ∈ Icc 1 (4 * N), (r : ℝ) * (4 * N / r ^ 2 : ℕ) := by
    exact_mod_cast hnat
  have h := sum_floor_bound (4 * N)
  have hh := harmonic_le_one_add_log (4 * N)
  have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (4 * N) : (0:ℝ) ≤ (4*N:ℕ))
  push_cast at h hmul
  nlinarith only [hreal,h,hmul]

end Erdos773.AverageAP
end EndpointModule084
-- End AverageAPBound.lean

-- Begin ControlledSquareSampling.lean
section EndpointModule085

/-
Prescribed-size sampling followed by progression deletion, while retaining
an asymptotically sharp bound for four-root collisions. The selected square
values are progression-free, not necessarily Sidon.
-/
noncomputable section
namespace Erdos773.ControlledSquareSampling
open Finset Filter SquareProgressionSupports SquareCollisionCodegrees
set_option maxHeartbeats 1000000

lemma edges_restrict {A B : Finset ℕ} (hBA : B ⊆ A) :
    edges B = (edges A).filter (fun e => e ⊆ B) := by
  classical
  ext e
  simp only [edges,mem_filter,mem_powerset]
  constructor
  · rintro ⟨heB,h4,hs⟩
    exact ⟨⟨heB.trans hBA,h4,hs⟩,heB⟩
  · rintro ⟨⟨heA,h4,hs⟩,heB⟩
    exact ⟨heB,h4,hs⟩

-- Unused development declaration omitted.

lemma progression_log_bound (N : ℕ) (hN : 0 < N) (hL : 2 ≤ Real.log (N:ℝ)) :
    ((progressions (Icc 1 N)).card : ℝ) ≤ 24*(N:ℝ)*Real.log N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hc : ((progressions (Icc 1 N)).card : ℝ) ≤ (squareAPs N).card := by
    exact_mod_cast progression_card_bound N
  have hb := AverageAP.squareAPs_log_bound N
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  norm_num at hl4
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hN0.ne'] at hb
  have hh : 1+Real.log 4+Real.log N ≤ 3*Real.log N := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 8*N by positivity)
  nlinarith only [hc,hb,hmul]

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.ControlledSquareSampling
end
end EndpointModule085
-- End ControlledSquareSampling.lean

-- Begin APFreeExtraction.lean
section EndpointModule086

/-
Near-linear subsets of the squares with no three-term arithmetic progression.
This removes three-value Sidon obstructions, not four-value obstructions.
-/
namespace Erdos773.APFreeExtraction

open Finset Filter
set_option maxHeartbeats 1000000

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

/-- In a three-AP-free set, a nontrivial repeated pair sum has four distinct
entries. -/
lemma four_distinct_of_collision {B : Set ℕ} (hB : ThreeAPFree B)
    {a b c d : ℕ} (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B)
    (he : a + b = c + d)
    (hnt : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hab : a ≠ b := by
    intro hh
    have hca := hB hc ha hd (by omega)
    exact hnt (Or.inl ⟨hca.symm, by omega⟩)
  have hcd : c ≠ d := by
    intro hh
    have hac := hB ha hc hb (by omega)
    exact hnt (Or.inl ⟨hac, by omega⟩)
  refine ⟨hab, ?_, ?_, ?_, ?_, hcd⟩ <;>
    intro hh <;> apply hnt <;> omega


-- Unused development declaration omitted.



end Erdos773.APFreeExtraction
end EndpointModule086
-- End APFreeExtraction.lean

-- Begin PrioritySquareSidonLower.lean
section EndpointModule087

/-
Applying the four-uniform priority bound to progression-free square carriers.
The resulting Sidon lower bound still has a logarithmic loss.
-/
namespace Erdos773.PrioritySquareSidonLower
open Finset Filter SquareCollisionCodegrees
set_option maxHeartbeats 1500000

lemma sidon_of_edge_avoidance {A B : Finset ℕ} (hBA : B ⊆ A)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (havoid : ∀ e ∈ edges A, ¬e ⊆ B) :
    IsSidon ((B.image (fun n : ℕ => n^2)) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd he
  obtain ⟨a,ha',rfl⟩ := mem_image.mp ha
  obtain ⟨b,hb',rfl⟩ := mem_image.mp hb
  obtain ⟨c,hc',rfl⟩ := mem_image.mp hc
  obtain ⟨d,hd',rfl⟩ := mem_image.mp hd
  by_contra hn
  have hmem (x : ℕ) (hx : x ∈ B) : x^2 ∈ A.image (fun n : ℕ => n^2) :=
    mem_image.mpr ⟨x,hBA hx,rfl⟩
  have hdist := APFreeExtraction.four_distinct_of_collision hAP
    (hmem a ha') (hmem c hc') (hmem b hb') (hmem d hd') he hn
  have hac : a ≠ c := fun h => hdist.1 (congrArg (fun n : ℕ => n^2) h)
  have hab : a ≠ b := fun h => hdist.2.1 (congrArg (fun n : ℕ => n^2) h)
  have had : a ≠ d := fun h => hdist.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hcb : c ≠ b := fun h => hdist.2.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hcd : c ≠ d := fun h => hdist.2.2.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hbd : b ≠ d := fun h => hdist.2.2.2.2.2 (congrArg (fun n : ℕ => n^2) h)
  have hsub : ({a,c,b,d} : Finset ℕ) ⊆ B := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  apply havoid {a,c,b,d} _ hsub
  exact mem_filter.mpr ⟨mem_powerset.mpr (hsub.trans hBA),
    by simp [hac,hab,had,hcb,hcd,hbd],a,c,b,d,rfl,he⟩

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

-- Unused development declaration omitted.

end Erdos773.PrioritySquareSidonLower
end EndpointModule087
-- End PrioritySquareSidonLower.lean

-- Begin GreedyBatchSquareCertificate.lean
section EndpointModule088

/- A finite square-Sidon certificate using the shrinking mixed profiles. -/
namespace Erdos773.GreedyBatchSquareCertificate
open Finset SquareCollisionCodegrees SquareCollisionIntersections HypergraphDegreeTrim
open GreedyBatchDensityProfile GreedyBatchProfileStep GreedyBatchVolume
set_option maxHeartbeats 3000000
noncomputable section

theorem certificate (N m K : ℕ) (d T : ℝ) (P : ℕ) (A : Finset ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (K+increment K)≤ m)
    (hd : 0<d) (hdU : d≤(m:ℝ)^K) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hA : A⊆Icc 1 N) (hvol : N≤ m^K)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)):Set ℕ))
    (hdegree : ∀ x ∈ A, (degree (edges A) x:ℝ)≤d^3)
    (hpair : ∀ x ∈ A, ∀ y ∈ A, x≠y → (pairEdges A x y).card≤P) :
    efficiency m*(T-1)/d*A.card≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  have hAc : A.card≤N := by simpa using card_le_card hA
  obtain ⟨I,hIA,hI,hcard⟩ := GreedyBatchInitialExtraction.selection A (edges A) m K d T P
    hm hmV hd hdU hP hPm hT hT3 hterminal (hAc.trans hvol)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) hdegree hpair
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne)
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIA hAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIA.trans hA)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ)≠0))] at hmax
  exact hcard.trans (by exact_mod_cast hmax)

end
end Erdos773.GreedyBatchSquareCertificate
end EndpointModule088
-- End GreedyBatchSquareCertificate.lean

-- Begin GreedyBatchSquareScales.lean
section EndpointModule089

/- Explicit scalar parameters for applying the shrinking-batch theorem to
squares. These lemmas address the two-thirds coefficient only. -/
namespace Erdos773.GreedyBatchSquareScales
open Filter GreedyBatchDensityProfile GreedyBatchProfileStep GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def exponent : ℕ := 1000000000
def eta : ℝ := 1/1000000000
def kappa : ℝ := 1999/6000
def c : ℝ := 19999/60000
def loss : ℝ := 99999/100000
def smallDelta : ℝ := 1/240000

def root (X : ℝ) : ℕ := ⌈X^eta⌉₊
def scale (X : ℝ) : ℝ := (kappa*X/(Real.log X)^2)^(1/3:ℝ)
def horizon (X : ℝ) : ℝ := (c*Real.log X)^(1/3:ℝ)

lemma scale_pos {X : ℝ} (hX : 0<X) (hL : 0<Real.log X) : 0<scale X := by
  apply Real.rpow_pos_of_pos
  dsimp [kappa]
  positivity

lemma scale_cube {X : ℝ} (hX : 0≤X) : (scale X)^3=kappa*X/(Real.log X)^2 := by
  unfold scale
  rw [← Real.rpow_mul_natCast (by dsimp [kappa]; positivity : 0≤kappa*X/(Real.log X)^2)]
  norm_num

lemma horizon_pos {X : ℝ} (hL : 0<Real.log X) : 0<horizon X := by
  apply Real.rpow_pos_of_pos
  dsimp [c]
  positivity

lemma horizon_cube {X : ℝ} (hL : 0≤Real.log X) : (horizon X)^3=c*Real.log X := by
  unfold horizon
  rw [← Real.rpow_mul_natCast (by dsimp [c]; positivity : 0≤c*Real.log X)]
  norm_num

lemma root_lower (X : ℝ) : X^eta≤(root X:ℝ) := Nat.le_ceil _

lemma volume {X : ℝ} (hX : 0≤X) : X≤(root X:ℝ)^exponent := by
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hX eta) (root_lower X) exponent
  rw [← Real.rpow_mul_natCast hX] at hh
  norm_num [eta,exponent] at hh
  exact hh

lemma root_upper {X : ℝ} (hX : 0≤X) (htwo : 2≤X^eta) : (root X:ℝ)≤X^(2*eta) := by
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg hX eta)).le
  have hs : X^eta+1≤(X^eta)^2 := by nlinarith only [htwo]
  have hh := hc.trans hs
  rw [← Real.rpow_mul_natCast hX] at hh
  simpa only [root,Nat.cast_ofNat,mul_comm eta (2:ℝ)] using hh

lemma horizon_large {X : ℝ} (hL : (4000000000000000000:ℝ)≤Real.log X) : 1000000≤horizon X := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hc := horizon_cube hL0.le
  apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (horizon_pos hL0).le
  rw [hc]
  dsimp [c]
  nlinarith only [hL]

lemma horizon_shift {X : ℝ} (hL : (4000000000000000000:ℝ)≤Real.log X) :
    (horizon X+1)^3-1≤(c+smallDelta)*Real.log X := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have ht := horizon_large hL
  have ht0 := horizon_pos hL0
  have hsq : horizon X≤(horizon X)^2 := by nlinarith only [ht]
  have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg (horizon X))
  have hc := horizon_cube hL0.le
  have hdelta : 6*(horizon X)^2≤smallDelta*Real.log X := by
    dsimp [c,smallDelta] at hc ⊢
    nlinarith only [hmul,hc,hL0.le]
  nlinarith only [hsq,hc,hdelta]

lemma scale_upper {X : ℝ} (hX : 1≤X) (hL : 1≤Real.log X) : scale X≤X := by
  have hsq : 1≤(Real.log X)^2 := one_le_pow₀ hL
  have hscale : (scale X)^3≤X := by
    rw [scale_cube (by linarith only [hX])]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq (by linarith only [hX] : 0≤X)
    dsimp [kappa]
    linarith only [hh,hX]
  have hpow : X≤X^3 := by simpa using pow_le_pow_right₀ hX (by decide : 1≤3)
  exact le_of_pow_le_pow_left₀ (by decide : 3≠0) (by linarith only [hX]) (hscale.trans hpow)

lemma scale_lower {X : ℝ} (hX : 0<X) (hL : 0<Real.log X)
    (hs : Real.log X≤(1/2:ℝ)*X^(1/160000:ℝ)) : X^(1/3-smallDelta)≤scale X := by
  have hs2 := pow_le_pow_left₀ hL.le hs 2
  rw [mul_pow,← Real.rpow_mul_natCast hX.le] at hs2
  have hsq : (Real.log X)^2≤kappa*X^(3*smallDelta) := by
    norm_num [kappa,smallDelta] at hs2 ⊢
    have hh := Real.rpow_nonneg hX.le (1/80000:ℝ)
    linarith only [hs2,hh]
  have hp : X^(1-3*smallDelta)*X^(3*smallDelta)=X := by
    rw [← Real.rpow_add hX]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hX.le (1-3*smallDelta))
  have hc : X^(1-3*smallDelta)≤kappa*X/(Real.log X)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ X^(1-3*smallDelta)*(kappa*X^(3*smallDelta)) := hm
      _ = kappa*X := by rw [← mul_assoc,mul_comm _ kappa,mul_assoc,hp]
  apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (scale_pos hX hL).le
  rw [scale_cube hX.le,← Real.rpow_mul_natCast hX.le]
  convert hc using 1 <;> congr 1 <;> ring

lemma terminal {X : ℝ} (hX : 1≤X) (hm : 2000000≤root X)
    (hL : (4000000000000000000:ℝ)≤Real.log X) (htwo : 2≤X^eta)
    (hs : Real.log X≤(1/2:ℝ)*X^(1/160000:ℝ)) :
    (root X:ℝ)^1000≤scale X*Real.exp (-a (root X)*((horizon X+1)^3-1)) := by
  have hX0 : 0<X := by linarith only [hX]
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hscale := scale_lower hX0 hL0 hs
  have hshift := horizon_shift hL
  have hT := horizon_large hL
  have hE : 0≤(horizon X+1)^3-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith only [hT]))
  have ha : a (root X)≤1 := (coefficients (root X) (by omega)).2.2.2.2.1
  have hpen : a (root X)*((horizon X+1)^3-1)≤(c+smallDelta)*Real.log X :=
    (mul_le_mul_of_nonneg_right ha hE).trans (by simpa using hshift)
  have he : X^(-(c+smallDelta))≤Real.exp (-a (root X)*((horizon X+1)^3-1)) := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    nlinarith only [hpen]
  have hprod := mul_le_mul hscale he (Real.rpow_nonneg hX0.le _) (scale_pos hX0 hL0).le
  rw [← Real.rpow_add hX0] at hprod
  have hid : (1/3-smallDelta)+-(c+smallDelta)=(1/120000:ℝ) := by norm_num [smallDelta,c]
  rw [hid] at hprod
  have hroot := pow_le_pow_left₀ (Nat.cast_nonneg (root X)) (root_upper hX0.le htwo) 1000
  rw [← Real.rpow_mul_natCast hX0.le] at hroot
  exact hroot.trans ((Real.rpow_le_rpow_of_exponent_le hX (by norm_num [eta])).trans hprod)

lemma efficiency_lower (m : ℕ) (hm : 100000000000≤ m) : loss≤efficiency m := by
  have hmR : (100000000000:ℝ)≤ m := by exact_mod_cast hm
  have hh : (1000000:ℝ)/(m:ℝ)≤1/100000 := (div_le_iff₀ (by linarith only [hmR])).mpr (by linarith only [hmR])
  dsimp [loss,efficiency]
  linarith only [hh]

/-- The tiny coefficient gain is kept explicitly, instead of discarded as
an unspecified constant. -/
lemma coefficient {X V : ℝ} {m : ℕ} (hX : 0<X)
    (hL : (4000000000000000000:ℝ)≤Real.log X) (hm : 100000000000≤ m)
    (hV : loss*X/Real.log X≤V) :
    X^(2/3:ℝ)≤efficiency m*(horizon X-1)/scale X*V := by
  have hL0 : 0<Real.log X := by linarith only [hL]
  have hd := scale_pos hX hL0
  have hT := horizon_large hL
  have ht : 0<horizon X := horizon_pos hL0
  have htime : loss*horizon X≤horizon X-1 := by dsimp [loss]; linarith only [hT]
  have hl : (0:ℝ)≤loss := by norm_num [loss]
  have he := efficiency_lower m hm
  have hV0 : 0≤V := le_trans (by positivity) hV
  have hh := mul_le_mul he htime (by positivity : 0≤loss*horizon X) (hl.trans he)
  have htm : 0≤horizon X-1 := by linarith only [hT]
  have hh' := mul_le_mul (div_le_div_of_nonneg_right hh hd.le) hV (by positivity : 0≤loss*X/Real.log X)
    (by have := hl.trans he; positivity : 0≤efficiency m*(horizon X-1)/scale X)
  let w : ℝ := loss^3*horizon X*X/(scale X*Real.log X)
  have hw : w≤efficiency m*(horizon X-1)/scale X*V := by
    convert hh' using 1 <;> dsimp [w] <;> ring
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hw3 : w^3=(loss^9*c/kappa)*X^2 := by
    dsimp [w]
    simp only [div_pow,mul_pow]
    rw [horizon_cube hL0.le,scale_cube hX.le]
    have hk : kappa≠0 := by norm_num [kappa]
    field_simp [hX.ne',hL0.ne',hk]
    <;> ring
  have hconst : (1:ℝ)≤loss^9*c/kappa := by norm_num [loss,c,kappa]
  have hr : (X^(2/3:ℝ))^3=X^2 := by
    rw [← Real.rpow_mul_natCast hX.le]
    norm_num
  have hc := mul_le_mul_of_nonneg_right hconst (sq_nonneg X)
  have hlow : X^(2/3:ℝ)≤w := by
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) hw0
    rw [hr,hw3]
    simpa only [one_mul] using hc
  exact hlow.trans hw

end
end Erdos773.GreedyBatchSquareScales
end EndpointModule089
-- End GreedyBatchSquareScales.lean

-- Begin UniformDegreeSampling.lean
section EndpointModule090

/- Finite simultaneous sampling with prescribed upper bounds for every
member of a family of induced edge counts, followed by obstruction deletion. -/
namespace Erdos773.UniformDegreeSampling
open Finset HypergraphSamplingMoments
set_option maxHeartbeats 2000000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

def potential (H : β → Finset (Finset α)) (q : ℕ) (T : ℝ) (B : Finset α) : ℝ :=
  ∑ b : β, (((H b).filter (· ⊆ B)).card/T:ℝ)^q

omit [Fintype α] in
lemma potential_nonneg (H : β → Finset (Finset α)) (q : ℕ) (T : ℝ) (hT : 0<T) (B : Finset α) :
    0 ≤ potential H q T B := by
  apply sum_nonneg
  intro b hb
  exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) hT.le) _

lemma potential_bound (H : β → Finset (Finset α)) (r K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hr : ∀ b, ∀ e ∈ H b, e.card=r)
    (hK : ∀ b a, ((H b).filter (fun e => a ∈ e)).card ≤ K)
    (hcard : ∀ b, ((H b).card:ℝ) ≤ D) :
    (∑ f : α → Bool, trialWeight p f*potential H q T (selected f)) ≤
      (Fintype.card β:ℝ)*((p^r*D+(r*q:ℕ)*K)/T)^q := by
  have hmoment (b : β) :
      (∑ f : α → Bool, trialWeight p f*((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q) ≤
        ((p^r*D+(r*q:ℕ)*K)/T)^q := by
    simp only [div_pow,← mul_div_assoc,← sum_div]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hT.le _)
    apply (moment_bound (H b) r K q p hp hp1 (hr b) (hK b)).trans
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (hcard b) (pow_nonneg hp _)) le_rfl
  calc
    _ = ∑ b : β, ∑ f : α → Bool,
        trialWeight p f*((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q := by
      simp only [potential,mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _b : β, ((p^r*D+(r*q:ℕ)*K)/T)^q := sum_le_sum (fun b _ => hmoment b)
    _ = _ := by simp

/-- An actual subset satisfies ALL link-count caps. The penalty for failure
is the entire carrier size; its high-moment expectation pays for the union
bound without needing an additional cardinality concentration theorem. -/
theorem finite_selection (H : β → Finset (Finset α)) (P : Finset (Finset α))
    (r s K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hr : ∀ b, ∀ e ∈ H b, e.card=r)
    (hK : ∀ b a, ((H b).filter (fun e => a ∈ e)).card ≤ K)
    (hcard : ∀ b, ((H b).card:ℝ) ≤ D)
    (hP : ∀ e ∈ P, e.card=s) (hs : 0<s)
    (hpositive : 0 < p*Fintype.card α-p^s*P.card-
      (Fintype.card α:ℝ)*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q) :
    ∃ B : Finset α, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ b, (((H b).filter (· ⊆ B)).card:ℝ)<T) ∧
      p*Fintype.card α-p^s*P.card-
        (Fintype.card α:ℝ)*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  classical
  let V : ℝ := Fintype.card α
  let cost (f : α → Bool) : ℝ := (selected f).card-(P.filter (· ⊆ selected f)).card-
    V*potential H q T (selected f)
  have hV : 0 ≤ V := Nat.cast_nonneg _
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ cost univ_nonempty
  have hupper : (∑ g : α → Bool, trialWeight p g*cost g) ≤ cost f := by
    calc
      _ ≤ ∑ g : α → Bool, trialWeight p g*cost f :=
        sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g))
      _ = _ := by rw [← sum_mul,sum_trialWeight,one_mul]
  have hPsum : (∑ e ∈ P, p^e.card) = p^s*P.card := by
    simp only [sum_congr rfl (fun e he => congrArg (fun j => p^j) (hP e he)),sum_const,nsmul_eq_mul]
    ring
  have hexpect : (∑ g : α → Bool, trialWeight p g*cost g) =
      p*Fintype.card α-p^s*P.card-V*(∑ g : α → Bool, trialWeight p g*potential H q T (selected g)) := by
    simp only [cost,mul_sub,sum_sub_distrib,sum_trialWeight_card,sum_trialWeight_edgeCount,hPsum]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro g hg
    ring
  have hpot := potential_bound H r K q p T D hp hp1 hT hr hK hcard
  have hmul := mul_le_mul_of_nonneg_left hpot hV
  have hlower : p*Fintype.card α-p^s*P.card-
      V*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q ≤ cost f := by
    rw [hexpect] at hupper
    nlinarith only [hupper,hmul]
  have hpos : 0<cost f := lt_of_lt_of_le hpositive hlower
  have hcaps (b : β) : (((H b).filter (· ⊆ selected f)).card:ℝ)<T := by
    by_contra! hn
    have hratio : 1 ≤ ((((H b).filter (· ⊆ selected f)).card:ℝ)/T) :=
      (one_le_div hT).mpr hn
    have hterm : 1 ≤ ((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q := one_le_pow₀ hratio
    have hsum : 1 ≤ potential H q T (selected f) := by
      apply hterm.trans
      unfold potential
      apply single_le_sum (f := fun c : β => ((((H c).filter (· ⊆ selected f)).card:ℝ)/T)^q)
      · intro c hc; positivity
      · exact mem_univ b
    have hc : ((selected f).card:ℝ) ≤ V := by
      dsimp [V]
      exact_mod_cast card_le_univ (selected f)
    have hmul := mul_le_mul_of_nonneg_left hsum hV
    have hPnon : (0:ℝ) ≤ (P.filter (· ⊆ selected f)).card := Nat.cast_nonneg _
    dsimp [cost] at hpos
    nlinarith only [hc,hmul,hPnon,hpos]
  obtain ⟨B,hB,hBc,havoid⟩ := delete_forbidden_edges (selected f) (P.filter (· ⊆ selected f))
    (fun e he => card_pos.mp (by rw [hP e (mem_filter.mp he).1]; exact hs))
  refine ⟨B,?_,?_,?_⟩
  · intro e he heB
    exact havoid e (mem_filter.mpr ⟨he,heB.trans hB⟩) heB
  · intro b
    have hc : (((H b).filter (· ⊆ B)).card:ℝ) ≤ ((H b).filter (· ⊆ selected f)).card := by
      exact_mod_cast card_le_card (show (H b).filter (· ⊆ B) ⊆ (H b).filter (· ⊆ selected f) by
        intro e he
        obtain ⟨he,heB⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨he,heB.trans hB⟩)
    exact hc.trans_lt (hcaps b)
  · have hc : ((selected f).card:ℝ) ≤ B.card+(P.filter (· ⊆ selected f)).card := by exact_mod_cast hBc
    have hnon := mul_nonneg hV (potential_nonneg H q T hT (selected f))
    dsimp [cost] at hlower
    nlinarith only [hc,hnon,hlower]

end
end Erdos773.UniformDegreeSampling
end EndpointModule090
-- End UniformDegreeSampling.lean

-- Begin UniformHypergraphSampling.lean
section EndpointModule091

/- Uniform maximum-degree control under sampling of a four-uniform
hypergraph, simultaneously with deletion of three-vertex obstructions. -/
namespace Erdos773.UniformHypergraphSampling
open Finset HypergraphDegreeTrim
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

def link (H : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  (H.filter (fun e => a ∈ e)).image (fun e => e.erase a)

lemma erase_injective (a : α) {H : Finset (Finset α)} :
    Set.InjOn (fun e : Finset α => e.erase a) (H.filter (fun e => a ∈ e)) := by
  intro e he f hf hh
  change e.erase a=f.erase a at hh
  rw [← insert_erase (mem_filter.mp he).2,← insert_erase (mem_filter.mp hf).2,hh]

lemma link_card (H : Finset (Finset α)) (a : α) : (link H a).card=degree H a := by
  unfold link degree
  exact card_image_of_injOn (erase_injective a)

lemma link_uniform {H : Finset (Finset α)} (hr : ∀ e ∈ H, e.card=4)
    (a : α) : ∀ e ∈ link H a, e.card=3 := by
  intro e he
  unfold link at he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  rw [card_erase_of_mem (mem_filter.mp hf).2,hr f (mem_filter.mp hf).1]

lemma link_degree (H : Finset (Finset α)) (a b : α) (K : ℕ)
    (hK : ∀ b, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K) :
    ((link H a).filter (fun e => b ∈ e)).card ≤ K := by
  by_cases hab : a=b
  · subst b
    have he : (link H a).filter (fun e => a ∈ e)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,ha⟩ := mem_filter.mp he
      unfold link at he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact notMem_erase a f ha
    rw [he,card_empty]
    omega
  · have hs : (link H a).filter (fun e => b ∈ e) ⊆
        (H.filter (fun e => a ∈ e ∧ b ∈ e)).image (fun e => e.erase a) := by
      intro e he
      obtain ⟨he,hb⟩ := mem_filter.mp he
      unfold link at he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact mem_image.mpr ⟨f,mem_filter.mpr ⟨(mem_filter.mp hf).1,
        (mem_filter.mp hf).2,mem_of_mem_erase hb⟩,rfl⟩
    exact ((card_le_card hs).trans card_image_le).trans (hK b hab)

lemma induced_degree_le_link (H : Finset (Finset α)) (B : Finset α) (a : α) :
    degree (H.filter (· ⊆ B)) a ≤ ((link H a).filter (· ⊆ B)).card := by
  have hs : ((H.filter (· ⊆ B)).filter (fun e => a ∈ e)).image (fun e => e.erase a) ⊆
      (link H a).filter (· ⊆ B) := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,ha⟩ := mem_filter.mp hf
    obtain ⟨hf,hsub⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,ha⟩,rfl⟩,
      (erase_subset _ _).trans hsub⟩
  have hh := card_le_card hs
  rw [card_image_of_injOn (erase_injective a)] at hh
  exact hh

variable [Fintype α]

/-- No average-degree trimming is performed. All surviving degrees meet
    the same cap T. -/
theorem finite_selection (H P : Finset (Finset α)) (K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hfour : ∀ e ∈ H, e.card=4) (hthree : ∀ e ∈ P, e.card=3)
    (hdegree : ∀ a, (degree H a:ℝ) ≤ D)
    (hpair : ∀ a b, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K)
    (hpositive : 0 < p*Fintype.card α-p^3*P.card-
      (Fintype.card α:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B : Finset α, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ a, (degree (H.filter (· ⊆ B)) a:ℝ)<T) ∧
      p*Fintype.card α-p^3*P.card-
        (Fintype.card α:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  obtain ⟨B,hP,hcap,hcard⟩ := UniformDegreeSampling.finite_selection (link H) P
    3 3 K q p T D hp hp1 hT (link_uniform hfour) (fun a b => link_degree H a b K (hpair a))
    (fun a => by rw [link_card]; exact hdegree a) hthree (by omega) (by simpa only [pow_two] using hpositive)
  refine ⟨B,hP,?_,?_⟩
  · intro a
    have hh : (degree (H.filter (· ⊆ B)) a:ℝ) ≤ ((link H a).filter (· ⊆ B)).card := by
      exact_mod_cast induced_degree_le_link H B a
    exact hh.trans_lt (hcap a)
  · simpa only [pow_two] using hcard

end
end Erdos773.UniformHypergraphSampling
end EndpointModule091
-- End UniformHypergraphSampling.lean

-- Begin UniformAmbientSampling.lean
section EndpointModule092

/- Transport of uniform sampling to arbitrary finite ambient carriers. -/
namespace Erdos773.UniformAmbientSampling
open Finset HypergraphDegreeTrim FiniteHypergraphRestriction
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- The finite carrier is arbitrary; no global Fintype structure is needed. -/
theorem finite_selection (A : Finset α) (H P : Finset (Finset α)) (K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hH : ∀ e ∈ H, e ⊆ A) (hP : ∀ e ∈ P, e ⊆ A)
    (hfour : ∀ e ∈ H, e.card=4) (hthree : ∀ e ∈ P, e.card=3)
    (hdegree : ∀ a ∈ A, (degree H a:ℝ) ≤ D)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K)
    (hpositive : 0 < p*A.card-p^3*P.card-(A.card:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B ⊆ A, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ a ∈ A, (degree (H.filter (· ⊆ B)) a:ℝ)<T) ∧
      p*A.card-p^3*P.card-(A.card:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  have hPcard : (restrict A P).card=P.card := restrict_card hP
  obtain ⟨I,hI,hcap,hcard⟩ := UniformHypergraphSampling.finite_selection
    (restrict A H) (restrict A P) K q p T D hp hp1 hT
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      rw [down_card (hH f hf),hfour f hf])
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      rw [down_card (hP f hf),hthree f hf])
    (by intro a; rw [degree_all_eq hH]; exact hdegree a.val a.property)
    (by
      intro a b hab
      change FourUniformRegularization.pairDegree (restrict A H) a b ≤ K
      rw [pair_eq hH]
      exact hpair a.val a.property b.val b.property (fun h => hab (Subtype.ext h)))
    (by simpa only [Fintype.card_coe,hPcard] using hpositive)
  refine ⟨up A I,?_,(independent_iff hP I).mp hI,?_,?_⟩
  · exact up_subset I
  · intro a ha
    have hh := hcap ⟨a,ha⟩
    rw [restrict_induced hH,degree_all_eq (fun e he => hH e (mem_filter.mp he).1)] at hh
    exact hh
  · simpa only [up_card,Fintype.card_coe,hPcard] using hcard

end
end Erdos773.UniformAmbientSampling
end EndpointModule092
-- End UniformAmbientSampling.lean

-- Begin GaussianDirectionWeights.lean
section EndpointModule093

/- A period-210 sieve for primitive opposite-parity Gaussian directions. -/
noncomputable section
namespace Erdos773.GaussianDirectionWeights
open Finset ParityTriangleCount
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def weight (u v : ℕ) : ℕ :=
  if u%2=v%2 ∨ (u%3=0 ∧ v%3=0) ∨ (u%5=0 ∧ v%5=0) ∨ (u%7=0 ∧ v%7=0) then 0 else 1

lemma weight_le_one (u v : ℕ) : weight u v ≤ 1 := by unfold weight; split_ifs <;> omega

lemma weight_of_coprime {u v : ℕ} (hc : u.Coprime v) (hp : u%2 ≠ v%2) : weight u v=1 := by
  have hnot (p : ℕ) (hp : 1<p) : ¬(u%p=0 ∧ v%p=0) := by
    rintro ⟨hu,hv⟩
    have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
    rw [hc.gcd_eq_one] at hd
    have hh := Nat.le_of_dvd (by omega : 0<1) hd
    omega
  simp [weight,hp,hnot 3 (by omega),hnot 5 (by omega),hnot 7 (by omega)]

lemma weight_mod (u v : ℕ) : weight u v=weight (u%210) (v%210) := by
  simp only [weight,Nat.mod_mod_of_dvd _ (by decide : 2∣210),
    Nat.mod_mod_of_dvd _ (by decide : 3∣210),Nat.mod_mod_of_dvd _ (by decide : 5∣210),
    Nat.mod_mod_of_dvd _ (by decide : 7∣210)]

lemma weight_mod_right (u v : ℕ) : weight u v=weight u (v%210) := by
  simp only [weight,Nat.mod_mod_of_dvd _ (by decide : 2∣210),
    Nat.mod_mod_of_dvd _ (by decide : 3∣210),Nat.mod_mod_of_dvd _ (by decide : 5∣210),
    Nat.mod_mod_of_dvd _ (by decide : 7∣210)]

def row (u : ℕ) : ℕ := ∑ v ∈ range 210, weight u v

private lemma row_cert_210 : row 210 = 48 := by decide +kernel
private lemma row_cert_30 : row 30 = 56 := by decide +kernel
private lemma row_cert_42 : row 42 = 60 := by decide +kernel
private lemma row_cert_6 : row 6 = 70 := by decide +kernel
private lemma row_cert_70 : row 70 = 72 := by decide +kernel
private lemma row_cert_10 : row 10 = 84 := by decide +kernel
private lemma row_cert_14 : row 14 = 90 := by decide +kernel
private lemma row_cert_2 : row 2 = 105 := by decide +kernel
private lemma row_cert_105 : row 105 = 48 := by decide +kernel
private lemma row_cert_15 : row 15 = 56 := by decide +kernel
private lemma row_cert_21 : row 21 = 60 := by decide +kernel
private lemma row_cert_3 : row 3 = 70 := by decide +kernel
private lemma row_cert_35 : row 35 = 72 := by decide +kernel
private lemma row_cert_5 : row 5 = 84 := by decide +kernel
private lemma row_cert_7 : row 7 = 90 := by decide +kernel
private lemma row_cert_1 : row 1 = 105 := by decide +kernel
lemma row_formula (u : ℕ) :
    row u = (if u%3=0 then 2 else 3) * (if u%5=0 then 4 else 5) *
      (if u%7=0 then 6 else 7) := by
  rcases Nat.mod_two_eq_zero_or_one u with h2 | h2 <;>
    by_cases h3 : u%3=0 <;> by_cases h5 : u%5=0 <;> by_cases h7 : u%7=0
  all_goals simp only [row,weight,h2,h3,h5,h7]
  · simpa [row,weight] using row_cert_210
  · simpa [row,weight] using row_cert_30
  · simpa [row,weight] using row_cert_42
  · simpa [row,weight] using row_cert_6
  · simpa [row,weight] using row_cert_70
  · simpa [row,weight] using row_cert_10
  · simpa [row,weight] using row_cert_14
  · simpa [row,weight] using row_cert_2
  · simpa [row,weight] using row_cert_105
  · simpa [row,weight] using row_cert_15
  · simpa [row,weight] using row_cert_21
  · simpa [row,weight] using row_cert_3
  · simpa [row,weight] using row_cert_35
  · simpa [row,weight] using row_cert_5
  · simpa [row,weight] using row_cert_7
  · simpa [row,weight] using row_cert_1
lemma weight_sum : ∑ u ∈ range 210, ∑ v ∈ range 210, weight u v=18432 := by
  change (∑ u ∈ range 210, row u) = 18432
  simp_rw [row_formula]
  decide +kernel

lemma row_le (u : ℕ) : row u  ≤  210 := by
  calc
    _  ≤  ∑ _v ∈ range 210, 1 := sum_le_sum (fun v _ => weight_le_one u v)
    _ = 210 := by norm_num

lemma row_mod (u : ℕ) : row u = row (u%210) := by
  apply sum_congr rfl
  intro v hv
  rw [weight_mod u v,Nat.mod_eq_of_lt (mem_range.mp hv)]

lemma row_sum : ∑ u ∈ range 210, row u = 18432 := weight_sum

lemma weighted_interval (S : Finset ℕ) (u : ℕ) (L U : ℝ) (hLU : L  ≤  U)
    (hS : ∀ v ∈ S, L  ≤  v ∧ (v : ℝ)  ≤  U) :
    (∑ v ∈ S, (weight u v : ℝ))  ≤  (row u : ℝ)*((U-L)/210+1) := by
  have hf := sum_fiberwise_of_maps_to
    (fun (v : ℕ) (_hv : v ∈ S) => mem_range.mpr (Nat.mod_lt v (by omega : 0 < 210)))
    (fun v => (weight u v : ℝ))
  rw [← hf]
  calc
    _ = ∑ j ∈ range 210, (weight u j : ℝ)*(S.filter (fun v => v%210=j)).card := by
      apply sum_congr rfl
      intro j hj
      calc
        _ = ∑ _v ∈ S.filter (fun v => v%210=j), (weight u j : ℝ) := by
          apply sum_congr rfl
          intro v hv
          rw [weight_mod_right u v,(mem_filter.mp hv).2]
        _ = _ := by simp [mul_comm]
    _  ≤  ∑ j ∈ range 210, (weight u j : ℝ)*((U-L)/210+1) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply residue_interval_card_bound _ L U 210 j (by omega) hLU
      intro v hv
      obtain ⟨hv,hpar⟩ := mem_filter.mp hv
      exact ⟨hpar,(hS v hv).1,(hS v hv).2⟩
    _ = _ := by rw [← sum_mul]; norm_cast

lemma weighted_bin (S : Finset ℕ) (u i : ℕ)
    (hS : ∀ v ∈ S, u*i  ≤  40*v ∧ 40*v  ≤  u*(i+1)) :
    (∑ v ∈ S, (weight u v : ℝ))  ≤  (row u : ℝ)*((u:ℝ)/8400+1) := by
  have hl : (0 : ℝ)  ≤  u := by positivity
  have hb := weighted_interval S u ((u:ℝ)*i/40) ((u:ℝ)*(i+1)/40)
    (by nlinarith) (by
      intro v hv
      obtain ⟨hvlo,hvhi⟩ := hS v hv
      have hlo : (u:ℝ)*i  ≤  40*v := by exact_mod_cast hvlo
      have hhi : 40*(v:ℝ)  ≤  (u:ℝ)*(i+1) := by exact_mod_cast hvhi
      constructor <;> nlinarith only [hlo,hhi])
  have heq : (((u:ℝ)*(i+1)/40)-(u:ℝ)*i/40)/210+1 = (u:ℝ)/8400+1 := by ring
  rwa [heq] at hb

lemma row_harmonic (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*harmonic M+44100 := by
  let T := (Icc 1 M).filter (fun u => 210  ≤  u)
  let P := (Icc 1 M).filter (fun u => ¬210  ≤  u)
  let F : ℕ × ℕ → ℝ := fun t => (row t.2 : ℝ)/(210*t.1)
  have hPcard : P.card  ≤  210 := by
    apply (card_le_card (show P ⊆ range 210 by
      intro u hu
      obtain ⟨_,hu⟩ := mem_filter.mp hu
      exact mem_range.mpr (by omega))).trans_eq
    exact card_range 210
  have hP : (∑ u ∈ P, (row u : ℝ)/u)  ≤  44100 := by
    calc
      _  ≤  ∑ _u ∈ P, (210:ℝ) := by
        apply sum_le_sum
        intro u hu
        have hu1 := (mem_Icc.mp (mem_filter.mp hu).1).1
        have huR : (1:ℝ)  ≤  u := by exact_mod_cast hu1
        have hur : (row u : ℝ)  ≤  210 := by exact_mod_cast row_le u
        apply (div_le_iff₀ (by linarith : (0:ℝ)<u)).mpr
        nlinarith only [huR,hur]
      _ = 210*(P.card : ℝ) := by simp [mul_comm]
      _  ≤  44100 := by exact_mod_cast (show 210*P.card  ≤  44100 by omega)
  have hmap : (T.image (fun u => (u/210,u%210))) ⊆ (Icc 1 M) ×ˢ range 210 := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hu,hu30⟩ := mem_filter.mp hu
    have huM := (mem_Icc.mp hu).2
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨by omega,(Nat.div_le_self _ _).trans huM⟩,
      mem_range.mpr (Nat.mod_lt _ (by omega))⟩
  have hinj : Set.InjOn (fun u : ℕ => (u/210,u%210)) T := by
    intro u hu v hv he
    simp only [Prod.mk.injEq] at he
    omega
  have hT : (∑ u ∈ T, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*harmonic M := by
    calc
      _  ≤  ∑ u ∈ T, F (u/210,u%210) := by
        apply sum_le_sum
        intro u hu
        have hu30 := (mem_filter.mp hu).2
        have hk : (0:ℝ) < 210*(u/210 : ℕ) := by exact_mod_cast (show 0<210*(u/210) by omega)
        have hup : (210:ℝ)*(u/210 : ℕ)  ≤  u := by exact_mod_cast Nat.mul_div_le u 210
        dsimp [F]
        rw [row_mod u]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk hup
      _ = ∑ t ∈ T.image (fun u => (u/210,u%210)), F t := (sum_image hinj).symm
      _  ≤  ∑ t ∈ (Icc 1 M) ×ˢ range 210, F t :=
        sum_le_sum_of_subset_of_nonneg hmap (fun t ht _ => by
          exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      _ = (18432/210:ℝ)*harmonic M := by
        rw [sum_product]
        dsimp [F]
        simp only [← sum_div]
        have hrow : (∑ v ∈ range 210, (row v : ℝ)) = 18432 := by exact_mod_cast row_sum
        simp only [hrow,div_mul_eq_div_div]
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [div_eq_mul_inv,← mul_sum]
  have heq : (∑ u ∈ T, (row u : ℝ)/u)+(∑ u ∈ P, (row u : ℝ)/u) =
      ∑ u ∈ Icc 1 M, (row u : ℝ)/u := sum_filter_add_sum_filter_not _ _ _
  linarith

lemma row_log (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*(1+Real.log M)+44100 := by
  have hh := harmonic_le_one_add_log M
  have hb := row_harmonic M
  nlinarith only [hh,hb]

end Erdos773.GaussianDirectionWeights
end
end EndpointModule093
-- End GaussianDirectionWeights.lean

-- Begin GaussianRadialBins.lean
section EndpointModule094

/- A rational upper-step bound for the radial integral in the Gaussian direction count. -/
namespace Erdos773.GaussianRadialBins
open Finset
set_option maxHeartbeats 2000000

def height (i : ℕ) : ℚ := 1600/(1600+(i:ℚ)^2)

lemma height_nonneg (i : ℕ) : 0 ≤ height i := by unfold height; positivity
-- Unused development declaration omitted.
lemma height_sum : ∑ i ∈ range 40, height i ≤ 793/25 := by
  norm_num [sum_range_succ,height]
lemma height_sum_real : (∑ i ∈ range 40, (height i:ℝ)) ≤ 793/25 := by
  have hh := (Rat.cast_le (K := ℝ)).mpr height_sum
  simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_ofNat] using hh

lemma reciprocal_bound {u v i : ℕ} (hu : 0<u) (hlo : u*i ≤ 40*v) :
    1/((u:ℝ)^2+(v:ℝ)^2) ≤ (height i:ℝ)/(u:ℝ)^2 := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hloR : (u:ℝ)*i ≤ 40*v := by exact_mod_cast hlo
  have hs := pow_le_pow_left₀ (show (0:ℝ) ≤ u*i by positivity) hloR 2
  have hi : (height i:ℝ)=1600/(1600+(i:ℝ)^2) := by norm_num [height]
  rw [hi]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<u^2+v^2) (sq_pos_of_pos huR)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1600+(i:ℝ)^2)).mpr
  nlinarith only [hs]

end Erdos773.GaussianRadialBins
end EndpointModule094
-- End GaussianRadialBins.lean

-- Begin GaussianRadialCounting.lean
section EndpointModule095

/- Weighted reciprocal sums for the primitive Gaussian-direction count. -/
namespace Erdos773.GaussianRadialCounting
open Finset GaussianDirectionWeights GaussianRadialBins
set_option maxHeartbeats 2000000
noncomputable section

lemma bin_index {u v : ℕ} (hu : 0 < u) (hv : v < u) :
    40*v/u < 40 ∧ u*(40*v/u)  ≤  40*v ∧ 40*v < u*(40*v/u+1) := by
  exact ⟨(Nat.div_lt_iff_lt_mul hu).mpr (by omega),Nat.mul_div_le _ _,
    Nat.lt_mul_div_succ _ hu⟩

lemma weighted_height_sum (u : ℕ) (hu : 0 < u) :
    (∑ v ∈ Icc 1 (u-1), (weight u v : ℝ)*(height (40*v/u) : ℝ))  ≤ 
      (row u : ℝ)*((u:ℝ)/8400+1)*(793/25) := by
  have hb (v : ℕ) (hv : v ∈ Icc 1 (u-1)) := bin_index hu (show v<u by
    have hh := (mem_Icc.mp hv).2
    omega)
  have hf := sum_fiberwise_of_maps_to
    (fun v hv => mem_range.mpr (hb v hv).1)
    (fun v => (weight u v : ℝ)*(height (40*v/u) : ℝ))
  rw [← hf]
  calc
    _ = ∑ i ∈ range 40, (height i : ℝ)*
        (∑ v ∈ (Icc 1 (u-1)).filter (fun v => 40*v/u=i), (weight u v : ℝ)) := by
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]
      ring
    _  ≤  ∑ i ∈ range 40, (height i : ℝ)*((row u : ℝ)*((u:ℝ)/8400+1)) := by
      apply sum_le_sum
      intro i hi
      have hi40 := mem_range.mp hi
      have hpos : (0:ℝ)  ≤  height i := (Rat.cast_nonneg (K:=ℝ)).mpr (height_nonneg i)
      apply mul_le_mul_of_nonneg_left _ hpos
      apply weighted_bin
      intro v hv
      obtain ⟨hv,hvi⟩ := mem_filter.mp hv
      have ht := hb v hv
      rw [hvi] at ht
      exact ⟨ht.2.1,ht.2.2.le⟩
    _ = (row u : ℝ)*((u:ℝ)/8400+1)*(∑ i ∈ range 40, (height i : ℝ)) := by
      rw [← sum_mul]
      ring
    _  ≤  _ := mul_le_mul_of_nonneg_left height_sum_real
      (mul_nonneg (Nat.cast_nonneg _) (by positivity))

lemma row_reciprocal_bound (u : ℕ) (hu : 0<u) :
    (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2))  ≤ 
      (793/210000:ℝ)*(row u:ℝ)/u+(33306/5:ℝ)/(u:ℝ)^2 := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hb : (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2))  ≤ 
      (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)*(height (40*v/u):ℝ))/(u:ℝ)^2 := by
    rw [sum_div]
    apply sum_le_sum
    intro v hv
    have hh := mul_le_mul_of_nonneg_left
      (reciprocal_bound hu (Nat.mul_div_le (40*v) u)) (Nat.cast_nonneg (weight u v): (0:ℝ) ≤ weight u v)
    simpa only [mul_one_div,mul_div_assoc] using hh
  have hs := div_le_div_of_nonneg_right (weighted_height_sum u hu) (sq_nonneg (u:ℝ))
  have hr : (row u:ℝ) ≤ 210 := by exact_mod_cast row_le u
  have heq : ((row u:ℝ)*((u:ℝ)/8400+1)*(793/25))/(u:ℝ)^2 =
      (793/210000:ℝ)*(row u:ℝ)/u+(793/25:ℝ)*(row u:ℝ)/(u:ℝ)^2 := by
    generalize (row u : ℝ) = R
    field_simp
    ring
  rw [heq] at hs
  have herr : (793/25:ℝ)*(row u:ℝ)/(u:ℝ)^2  ≤  (33306/5:ℝ)/(u:ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith only [hr]
  exact (hb.trans hs).trans (add_le_add le_rfl herr)

def triangleSum (M : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2)

/-- A rational leading coefficient strictly below one third. -/
theorem triangle_sum_bound {M : ℕ} (hM : 1 ≤ M) :
    triangleSum M  ≤  (83/250:ℝ)*(1+Real.log M)+14000 := by
  have hs := sum_le_sum (s := Icc 1 M) (fun u hu => row_reciprocal_bound u (by have := mem_Icc.mp hu; omega))
  change triangleSum M  ≤  _ at hs
  have he : (∑ u ∈ Icc 1 M, ((793/210000:ℝ)*(row u:ℝ)/u+(33306/5:ℝ)/(u:ℝ)^2)) =
      (793/210000:ℝ)*(∑ u ∈ Icc 1 M, (row u:ℝ)/u)+
      (33306/5:ℝ)*(∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) := by
    rw [sum_add_distrib,mul_sum,mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intros <;> ring
  rw [he] at hs
  have hr := row_log M
  have hi := PeriodicCollisionWeights.inverse_square_sum M
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  nlinarith only [hs,hr,hi,hlog]

end
end Erdos773.GaussianRadialCounting
end EndpointModule095
-- End GaussianRadialCounting.lean

-- Begin GaussianCollisionFactorization.lean
section EndpointModule096

/- A small-factor encoding step for equal Gaussian norms. No counting or Sidon bound is asserted. -/
namespace Erdos773.GaussianCollisionFactorization
abbrev G := GaussianInt
open Zsqrtd
set_option maxHeartbeats 1000000
noncomputable section
local instance : GCDMonoid G := EuclideanDomain.gcdMonoid G

lemma norm_eq_of_associated {z w : G} (h : Associated z w) : z.norm=w.norm := by
  obtain ⟨u,hu⟩ := h
  have hn : (u.val : G).norm=1 := (norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mpr u.isUnit
  have he := congrArg Zsqrtd.norm hu
  rw [Zsqrtd.norm_mul,hn,mul_one] at he
  exact he

/-- Equal norms split into a common Gaussian factor and conjugate factors,
    up to a unit. -/
theorem factorization {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ Associated w (g*star h) := by
  obtain ⟨h,k,hz',hw',hcop⟩ := extract_gcd z w
  let g := gcd z w
  change z=g*h at hz'
  change w=g*k at hw'
  have hg : g ≠ 0 := by intro h; apply hz; simpa [g,h] using hz'
  have hh : h ≠ 0 := by intro h0; apply hz; simp [h0] at hz'; exact hz'
  have hgN : g.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hg
  have hhN : h.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hh
  have hnorm : h.norm=k.norm := by
    rw [hz',hw',Zsqrtd.norm_mul,Zsqrtd.norm_mul] at he
    exact mul_left_cancel₀ hgN he
  have hprod : h*star h=k*star k := by
    rw [← norm_eq_mul_conj,← norm_eq_mul_conj,hnorm]
  have hdiv : h ∣ star k :=
    ((gcd_isUnit_iff h k).mp hcop).dvd_of_dvd_mul_left ⟨star h,hprod.symm⟩
  obtain ⟨u,hu⟩ := hdiv
  have hunit : IsUnit u := by
    apply (norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mp
    have hh' := congrArg Zsqrtd.norm hu
    rw [norm_conj,Zsqrtd.norm_mul,← hnorm] at hh'
    apply mul_left_cancel₀ hhN
    simpa only [mul_one] using hh'.symm
  have ha : Associated h (star k) := by
    obtain ⟨v,hv⟩ := hunit
    refine ⟨v,?_⟩
    rw [hv]
    exact hu.symm
  have hk : Associated k (star h) := by
    have ha' := ha.map (starRingEnd G)
    simpa only [starRingEnd_apply,star_star] using ha'.symm
  refine ⟨g,h,hz',?_⟩
  rw [hw']
  exact hk.mul_left g

/-- One of the two factors can always be chosen with squared norm no
    larger than the original norm. Conjugating the output does not alter
    its unordered absolute coordinate pair. -/
theorem small_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hw⟩ := factorization hz he
  have hg0 : g ≠ 0 := by intro hg; apply hz; simpa [hg] using hz'
  have hh0 : h ≠ 0 := by intro hh; apply hz; simpa [hh] using hz'
  have hgN := GaussianInt.norm_nonneg g
  have hhN := GaussianInt.norm_nonneg h
  have hn : z.norm=g.norm*h.norm := by rw [hz',Zsqrtd.norm_mul]
  by_cases hle : h.norm ≤ g.norm
  · refine ⟨g,h,hz',hh0,?_,Or.inl hw⟩
    nlinarith [mul_le_mul_of_nonneg_right hle hhN]
  · refine ⟨h,g,by simpa only [mul_comm] using hz',hg0,?_,Or.inr ?_⟩
    · have hle' : g.norm ≤ h.norm := le_of_lt (lt_of_not_ge hle)
      nlinarith [mul_le_mul_of_nonneg_right hle' hgN]
    · have hw' := hw.map (starRingEnd G)
      simpa only [starRingEnd_apply,star_mul,star_star,mul_comm] using hw'

/-- Removing the rational-integer content cannot increase the norm. -/
lemma primitive_part {h : G} (hh : h ≠ 0) :
    ∃ k : ℤ, ∃ h₀ : G, h=(k:G)*h₀ ∧ IsCoprime h₀.re h₀.im ∧
      h₀ ≠ 0 ∧ h₀.norm ≤ h.norm := by
  obtain ⟨r,s,hr,hs,hcop⟩ := extract_gcd h.re h.im
  let k := gcd h.re h.im
  change h.re=k*r at hr
  change h.im=k*s at hs
  let h₀ : G := ⟨r,s⟩
  have he : h=(k:G)*h₀ := by
    ext <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_intCast,
      Zsqrtd.im_intCast,zero_mul,mul_zero,add_zero,h₀] <;> assumption
  have hk : k ≠ 0 := by
    intro hk
    apply hh
    rw [he,hk]
    simp
  have hh₀ : h₀ ≠ 0 := by
    intro hz
    apply hh
    rw [he,hz,mul_zero]
  have hn : h.norm=k^2*h₀.norm := by
    rw [he,Zsqrtd.norm_mul]
    simp [Zsqrtd.norm_intCast,pow_two]
  have hk1 : 1 ≤ k^2 := by have := sq_pos_of_ne_zero hk; omega
  have hhN := GaussianInt.norm_nonneg h₀
  refine ⟨k,h₀,he,(gcd_isUnit_iff r s).mp hcop,hh₀,?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hk1 hhN]

/-- The small Gaussian factor may also be taken to have coprime coordinates.
    The odd-norm and quadrant normalizations needed for a counting bound are
    not included in this theorem. -/
theorem small_primitive_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ IsCoprime h.re h.im ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hh,hsmall,hw⟩ := small_factor hz he
  obtain ⟨k,h₀,hh₀,hcop,hne,hN⟩ := primitive_part hh
  have heq : g*star h=(g*(k:G))*star h₀ := by
    rw [hh₀,star_mul]
    simp only [star_intCast]
    ring
  refine ⟨g*(k:G),h₀,?_,hne,hcop,?_,?_⟩
  · rw [hz',hh₀]
    ring
  · have hp := pow_le_pow_left₀ (GaussianInt.norm_nonneg h₀) hN 2
    exact hp.trans hsmall
  · rwa [← heq]

end
end Erdos773.GaussianCollisionFactorization
end EndpointModule096
-- End GaussianCollisionFactorization.lean

-- Begin GaussianOddFactor.lean
section EndpointModule097

/- Removing the ramified factor 1+i while preserving the collision encoding. -/
namespace Erdos773.GaussianOddFactor
open GaussianCollisionFactorization
set_option maxHeartbeats 1000000
noncomputable section

def ramified : G := ⟨1,1⟩
def imagUnit : Gˣ := ⟨⟨0,1⟩,⟨0,-1⟩,by ext <;> norm_num,by ext <;> norm_num⟩

lemma ramified_associated : Associated (star ramified) ramified := by
  refine ⟨imagUnit,?_⟩
  ext <;> norm_num [ramified,imagUnit]

/-- Coprime same-parity coordinates must both be odd. -/
lemma same_parity {h : G} (hcop : IsCoprime h.re h.im)
    (he : h.re%2=h.im%2) : h.re%2=1 ∧ h.im%2=1 := by
  have hr0 := Int.emod_nonneg h.re (by norm_num : (2:ℤ) ≠ 0)
  have hr2 := Int.emod_lt_of_pos h.re (by norm_num : (0:ℤ)<2)
  have hn : h.re%2 ≠ 0 := by
    intro hz
    have hd₁ : (2:ℤ) ∣ h.re := Int.dvd_of_emod_eq_zero hz
    have hd₂ : (2:ℤ) ∣ h.im := Int.dvd_of_emod_eq_zero (he.symm.trans hz)
    have hh := hcop.isRelPrime hd₁ hd₂
    norm_num [Int.isUnit_iff_natAbs_eq] at hh
  omega

/-- The normalized factor has opposite-parity coprime coordinates. No
    orientation or uniqueness statement is included here. -/
theorem remove_ramified (g h : G) (hcop : IsCoprime h.re h.im) :
    ∃ g' h' : G, g*h=g'*h' ∧ Associated (g*star h) (g'*star h') ∧
      IsCoprime h'.re h'.im ∧ h'.re%2 ≠ h'.im%2 ∧ h'.norm ≤ h.norm := by
  by_cases ho : h.re%2 ≠ h.im%2
  · exact ⟨g,h,rfl,Associated.refl _,hcop,ho,le_refl _⟩
  have hodd := same_parity hcop (not_ne_iff.mp ho)
  let x := (h.re+h.im)/2
  let y := (h.im-h.re)/2
  let h' : G := ⟨x,y⟩
  have hx : h.re=x-y := by dsimp [x,y]; omega
  have hy : h.im=x+y := by dsimp [x,y]; omega
  have he : h=ramified*h' := by
    ext <;> simp [ramified,h',hx,hy] <;> ring
  have hcop' : IsCoprime x y := by
    apply IsRelPrime.isCoprime
    intro d hdx hdy
    apply hcop.isRelPrime
    · rw [hx]; exact dvd_sub hdx hdy
    · rw [hy]; exact dvd_add hdx hdy
  have ho' : x%2 ≠ y%2 := by omega
  have hnorm : h.norm=2*h'.norm := by
    rw [he,Zsqrtd.norm_mul]
    norm_num [ramified,Zsqrtd.norm_def]
  refine ⟨g*ramified,h',?_,?_,hcop',ho',?_⟩
  · rw [he,mul_assoc]
  · rw [he,star_mul]
    have hh := ramified_associated.mul_left (g*star h')
    convert hh using 1 <;> ring
  · have hh := GaussianInt.norm_nonneg h'
    linarith

-- Unused development declaration omitted.

/-- Equal nonzero Gaussian norms admit a small primitive odd-norm factor. -/
theorem small_odd_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ IsCoprime h.re h.im ∧
      h.re%2 ≠ h.im%2 ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hh,hcop,hsmall,hw⟩ := small_primitive_factor hz he
  obtain ⟨g',h',he',hw',hcop',ho',hN⟩ := remove_ramified g h hcop
  have hz'' : z=g'*h' := hz'.trans he'
  have hh' : h' ≠ 0 := by intro h0; apply hz; simpa [h0] using hz''
  refine ⟨g',h',hz'',hh',hcop',ho',?_,?_⟩
  · exact (pow_le_pow_left₀ (GaussianInt.norm_nonneg h') hN 2).trans hsmall
  · exact hw.imp (fun h => h.trans hw') (fun h => h.trans hw')

end
end Erdos773.GaussianOddFactor
end EndpointModule097
-- End GaussianOddFactor.lean

-- Begin GaussianQuadrantFactor.lean
section EndpointModule098

/- Unit and quadrant normalizations for the small-factor collision encoding. -/
namespace Erdos773.GaussianQuadrantFactor
open GaussianCollisionFactorization GaussianOddFactor
set_option maxHeartbeats 1000000
noncomputable section

def squareCoords (z : G) : Finset ℤ := {z.re^2,z.im^2}

lemma unit_coords (u : Gˣ) :
    ((u:G).re=1 ∧ (u:G).im=0) ∨ ((u:G).re= -1 ∧ (u:G).im=0) ∨
    ((u:G).re=0 ∧ (u:G).im=1) ∨ ((u:G).re=0 ∧ (u:G).im= -1) := by
  have hn : (u:G).norm=1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mpr u.isUnit
  have hn' : (u:G).re^2+(u:G).im^2=1 := by rw [Zsqrtd.norm_def] at hn; nlinarith
  have hr : -1 ≤ (u:G).re ∧ (u:G).re ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u:G).im]
  have hi : -1 ≤ (u:G).im ∧ (u:G).im ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u:G).re]
  obtain ⟨hr₁,hr₂⟩ := hr
  obtain ⟨hi₁,hi₂⟩ := hi
  interval_cases hr' : (u:G).re <;> interval_cases hi' : (u:G).im <;> norm_num [hr',hi'] at *

lemma squareCoords_star (z : G) : squareCoords (star z)=squareCoords z := by
  simp [squareCoords]

lemma squareCoords_associated {z w : G} (h : Associated z w) : squareCoords z=squareCoords w := by
  obtain ⟨u,rfl⟩ := h
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp [squareCoords,Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,Finset.pair_comm]

lemma coprime_mul_unit {h : G} (hc : IsCoprime h.re h.im) (u : Gˣ) :
    IsCoprime (h*(u:G)).re (h*(u:G)).im := by
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,mul_one,mul_zero,mul_neg_one,
      add_zero,zero_add,neg_mul,neg_neg,one_mul,IsCoprime.neg_left_iff,IsCoprime.neg_right_iff]
  · exact hc
  · exact hc
  · exact hc.symm
  · exact hc.symm

lemma parity_mul_unit {h : G} (hp : h.re%2 ≠ h.im%2) (u : Gˣ) :
    (h*(u:G)).re%2 ≠ (h*(u:G)).im%2 := by
  rcases unit_coords u with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ <;>
    simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,mul_one,mul_zero,mul_neg_one,
      add_zero,zero_add,neg_mul,neg_neg] <;> omega

lemma exists_quadrant_unit {h : G} (hh : h ≠ 0) :
    ∃ u : Gˣ, 0<(h*(u:G)).re ∧ 0 ≤ (h*(u:G)).im := by
  by_cases hr : 0<h.re
  · by_cases hi : 0 ≤ h.im
    · exact ⟨1,by simpa using And.intro hr hi⟩
    · refine ⟨imagUnit,?_⟩
      simp [imagUnit]
      omega
  · by_cases hi : 0<h.im
    · refine ⟨-imagUnit,?_⟩
      simp [imagUnit]
      omega
    · by_cases hr' : h.re<0
      · have hi' : 0 ≤ -h.im := by omega
        exact ⟨-1,by simpa using And.intro (neg_pos.mpr hr') hi'⟩
      · have hr0 : h.re=0 := by omega
        have hi' : h.im<0 := by
          by_contra hi'
          apply hh
          have hi0 : h.im=0 := by omega
          ext <;> simp [hr0,hi0]
        refine ⟨imagUnit,?_⟩
        simp [imagUnit,hr0]
        omega

/-- Both the input factorization and the unordered output coordinates survive
    first-quadrant normalization of the small primitive odd factor. -/
theorem quadrant_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ 0<h.re ∧ 0 ≤ h.im ∧ IsCoprime h.re h.im ∧
      h.re%2 ≠ h.im%2 ∧ h.norm^2 ≤ z.norm ∧ squareCoords w=squareCoords (g*star h) := by
  obtain ⟨g,h,hz',hh,hcop,hpar,hsmall,hw⟩ := small_odd_factor hz he
  obtain ⟨u,hur,hui⟩ := exists_quadrant_unit hh
  let g' := g*(↑(u⁻¹):G)
  let h' := h*(u:G)
  have hz'' : z=g'*h' := by
    rw [hz']
    dsimp [g',h']
    calc
      g*h = (g*h)*((↑(u⁻¹):G)*(u:G)) := by simp
      _ = _ := by ring
  have ha : Associated (g*star h) (g'*star h') := by
    refine ⟨u⁻¹*star u,?_⟩
    dsimp [g',h']
    simp only [star_mul]
    ring
  have hnorm : h.norm=h'.norm := norm_eq_of_associated (show Associated h h' from ⟨u,rfl⟩)
  refine ⟨g',h',hz'',hur,hui,coprime_mul_unit hcop u,parity_mul_unit hpar u,?_,?_⟩
  · rwa [← hnorm]
  · rcases hw with hw | hw
    · exact squareCoords_associated (hw.trans ha)
    · simpa only [squareCoords_star] using squareCoords_associated (hw.trans ha)

end
end Erdos773.GaussianQuadrantFactor
end EndpointModule098
-- End GaussianQuadrantFactor.lean

-- Begin GaussianFactorResidues.lean
section EndpointModule099

/- Congruence and uniqueness consequences of the normalized Gaussian factor. -/
namespace Erdos773.GaussianFactorResidues
open GaussianCollisionFactorization GaussianQuadrantFactor
set_option maxHeartbeats 1000000
noncomputable section

lemma real_coprime_norm {h : G} (hc : IsCoprime h.re h.im) : IsCoprime h.re h.norm := by
  apply IsRelPrime.isCoprime
  intro d hdU hdQ
  apply (show IsCoprime h.re (h.im^2) from hc.pow_right).isRelPrime hdU
  have hh := dvd_sub hdQ (dvd_mul_of_dvd_left hdU h.re)
  convert hh using 1
  rw [Zsqrtd.norm_def]
  ring

lemma norm_dvd_cross {z g h : G} (he : z=g*h) : h.norm ∣ z.im*h.re-z.re*h.im := by
  have hh : z*star h=g*(h*star h) := by rw [he]; ring
  rw [← Zsqrtd.norm_eq_mul_conj] at hh
  have hi := congrArg Zsqrtd.im hh
  simp only [Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star,Zsqrtd.re_intCast,
    Zsqrtd.im_intCast,mul_zero] at hi
  refine ⟨g.im,?_⟩
  nlinarith only [hi]

/-- For a fixed primitive factor and fixed real input coordinate, all
    imaginary input coordinates occupy one residue class modulo its norm. -/
theorem partner_congruence {a b c : ℤ} {h g g' : G}
    (hc : IsCoprime h.re h.im) (he : (⟨a,b⟩:G)=g*h) (he' : (⟨a,c⟩:G)=g'*h) :
    h.norm ∣ b-c := by
  have hb := norm_dvd_cross he
  have hc' := norm_dvd_cross he'
  have hd := dvd_sub hb hc'
  have heq : (b*h.re-a*h.im)-(c*h.re-a*h.im)=(b-c)*h.re := by ring
  change h.norm ∣ (b*h.re-a*h.im)-(c*h.re-a*h.im) at hd
  rw [heq] at hd
  exact (real_coprime_norm hc).symm.dvd_of_dvd_mul_right hd

lemma fixed_factor_unique {z g g' h : G} (hh : h ≠ 0)
    (he : z=g*h) (he' : z=g'*h) : g=g' :=
  mul_right_cancel₀ hh (he.symm.trans he')

lemma output_unique {z w w' g g' h : G} (hh : h ≠ 0)
    (he : z=g*h) (he' : z=g'*h)
    (hw : squareCoords w=squareCoords (g*star h))
    (hw' : squareCoords w'=squareCoords (g'*star h)) : squareCoords w=squareCoords w' := by
  have hg := fixed_factor_unique hh he he'
  rw [hw,hw',hg]

/-- Height only: the small factor's norm is at most 2N. -/
lemma norm_height {a b N : ℕ} {h : G} (ha : a ≤ N) (hb : b ≤ N)
    (hh : h.norm^2 ≤ (⟨(a:ℤ),(b:ℤ)⟩:G).norm) : h.norm ≤ 2*N := by
  have ha' : (a:ℤ) ≤ N := by exact_mod_cast ha
  have hb' : (b:ℤ) ≤ N := by exact_mod_cast hb
  have hN : (0:ℤ) ≤ N := by positivity
  have ha0 : (0:ℤ) ≤ a := by positivity
  have hb0 : (0:ℤ) ≤ b := by positivity
  have hasq := pow_le_pow_left₀ ha0 ha' 2
  have hbsq := pow_le_pow_left₀ hb0 hb' 2
  have hn := GaussianInt.norm_nonneg h
  have he : (⟨(a:ℤ),(b:ℤ)⟩:G).norm=(a:ℤ)^2+(b:ℤ)^2 := by
    rw [Zsqrtd.norm_def]
    dsimp only
    ring
  rw [he] at hh
  nlinarith

end
end Erdos773.GaussianFactorResidues
end EndpointModule099
-- End GaussianFactorResidues.lean

-- Begin GaussianIncidentEncoding.lean
section EndpointModule100

/- Finite Gaussian-direction witnesses and a sharp partner-fiber cardinality bound. -/
namespace Erdos773.GaussianIncidentEncoding
open Finset GaussianCollisionFactorization GaussianQuadrantFactor GaussianFactorResidues
set_option maxHeartbeats 2000000
noncomputable section

def gauss (a b : ℕ) : G := ⟨a,b⟩
def normSq (p : ℕ × ℕ) := p.1^2+p.2^2

lemma norm_gauss (a b : ℕ) : (gauss a b).norm=((a^2+b^2:ℕ):ℤ) := by
  classical
  dsimp [gauss]
  rw [Zsqrtd.norm_def]
  push_cast
  ring

lemma gauss_ne_zero {a b : ℕ} (ha : 0<a) : gauss a b ≠ 0 := by
  classical
  intro he
  have hh := congrArg Zsqrtd.re he
  simp [gauss] at hh
  omega

def directions (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (2*N)) ×ˢ (Icc 0 (2*N))).filter (fun p =>
    p.1.Coprime p.2 ∧ p.1%2 ≠ p.2%2 ∧ normSq p ≤ 2*N)

def partners (a N : ℕ) (p : ℕ × ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter (fun b => gauss p.1 p.2 ∣ gauss a b)

lemma mem_directions {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    0<p.1 ∧ p.1.Coprime p.2 ∧ p.1%2 ≠ p.2%2 ∧ normSq p ≤ 2*N := by
  classical
  obtain ⟨hm,hcop,hpar,hN⟩ := mem_filter.mp hp
  simp only [mem_product,mem_Icc] at hm
  exact ⟨by omega,hcop,hpar,hN⟩

lemma direction_coprime {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    IsCoprime (gauss p.1 p.2).re (gauss p.1 p.2).im := by
  classical
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa [gauss] using (mem_directions hp).2.1

lemma partner_mem_modEq {a N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N)
    {b c : ℕ} (hb : b ∈ partners a N p) (hc : c ∈ partners a N p) :
    b ≡ c [MOD normSq p] := by
  classical
  obtain ⟨g,hg⟩ := (mem_filter.mp hb).2
  obtain ⟨g',hg'⟩ := (mem_filter.mp hc).2
  have hb' : gauss a b=g*gauss p.1 p.2 := by simpa only [mul_comm] using hg
  have hc' : gauss a c=g'*gauss p.1 p.2 := by simpa only [mul_comm] using hg'
  have hh := partner_congruence (direction_coprime hp) hc' hb'
  rw [norm_gauss] at hh
  apply Int.natCast_modEq_iff.mp
  exact Int.modEq_iff_dvd.mpr hh

/-- Each fixed Gaussian direction allows at most N/q+1 partners, where q
    is its norm. This is an actual finite cardinality bound. -/
theorem partners_card {a N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    ((partners a N p).card:ℝ)  ≤  (N:ℝ)/normSq p+1 := by
  classical
  have hq : 0<normSq p := by
    classical
    have hu := (mem_directions hp).1
    dsimp [normSq]
    positivity
  rcases (partners a N p).eq_empty_or_nonempty with he | hne
  · rw [he,card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨b,hb⟩ := hne
    have hh := ParityTriangleCount.residue_interval_card_bound (partners a N p)
      0 (N:ℝ) (normSq p) (b%normSq p) hq (by positivity) (fun c hc => ?_)
    · simpa only [sub_zero] using hh
    · refine ⟨partner_mem_modEq hp hc hb,by positivity,?_⟩
      exact_mod_cast (mem_Icc.mp (mem_filter.mp hc).1).2

lemma squareCoords_ordered_injective {c d e f : ℕ} (hcd : c ≤ d) (hef : e ≤ f)
    (he : squareCoords (gauss c d)=squareCoords (gauss e f)) : c=e ∧ d=f := by
  classical
  change ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ)={(e:ℤ)^2,(f:ℤ)^2} at he
  have hcd' : (c:ℤ)^2 ≤ (d:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left hcd 2
  have hef' : (e:ℤ)^2 ≤ (f:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left hef 2
  have hc : (c:ℤ)^2=(e:ℤ)^2 := by
    classical
    have hc : (c:ℤ)^2 ∈ ({(e:ℤ)^2,(f:ℤ)^2}:Finset ℤ) := he ▸ (by simp)
    have he' : (e:ℤ)^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hc he'
    omega
  have hd : (d:ℤ)^2=(f:ℤ)^2 := by
    classical
    have hd : (d:ℤ)^2 ∈ ({(e:ℤ)^2,(f:ℤ)^2}:Finset ℤ) := he ▸ (by simp)
    have hf : (f:ℤ)^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2}:Finset ℤ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hd hf
    omega
  constructor
  · exact_mod_cast (sq_eq_sq₀ (by positivity : (0:ℤ) ≤ c) (by positivity : (0:ℤ) ≤ e)).mp hc
  · exact_mod_cast (sq_eq_sq₀ (by positivity : (0:ℤ) ≤ d) (by positivity : (0:ℤ) ≤ f)).mp hd

/-- Every bounded equal-square-sum relation has a finite direction witness.
    The norm bound is at most 2N, including all rounding and unit effects. -/
theorem exists_direction {a b c d N : ℕ} (ha : 0<a) (haN : a ≤ N) (hbN : b ≤ N)
    (he : a^2+b^2=c^2+d^2) :
    ∃ p ∈ directions N, ∃ g : G, gauss a b=g*gauss p.1 p.2 ∧
      squareCoords (gauss c d)=squareCoords (g*star (gauss p.1 p.2)) := by
  classical
  have hnorm : (gauss a b).norm=(gauss c d).norm := by rw [norm_gauss,norm_gauss,he]
  obtain ⟨g,h,hz,hr,hi,hcop,hpar,hsmall,hw⟩ := quadrant_factor (gauss_ne_zero ha) hnorm
  let u := h.re.toNat
  let v := h.im.toNat
  have hu : (u:ℤ)=h.re := Int.toNat_of_nonneg hr.le
  have hv : (v:ℤ)=h.im := Int.toNat_of_nonneg hi
  have hh : gauss u v=h := by ext <;> assumption
  have hu0 : 0<u := by exact_mod_cast (hu ▸ hr)
  have hc : u.Coprime v := by
    classical
    have ht := Int.isCoprime_iff_nat_coprime.mp hcop
    rw [← hu,← hv] at ht
    simpa using ht
  have hp : u%2 ≠ v%2 := by
    classical
    rw [← hu,← hv] at hpar
    exact_mod_cast hpar
  have hnormN := norm_height haN hbN hsmall
  have hq : normSq (u,v) ≤ 2*N := by
    classical
    rw [← hh,norm_gauss] at hnormN
    exact_mod_cast hnormN
  have huN : u ≤ 2*N := by dsimp [normSq] at hq; nlinarith
  have hvN : v ≤ 2*N := by dsimp [normSq] at hq; nlinarith
  refine ⟨(u,v),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,huN⟩,
    mem_Icc.mpr ⟨Nat.zero_le _,hvN⟩⟩,hc,hp,hq⟩,g,?_,?_⟩
  · simpa only [hh] using hz
  · simpa only [hh] using hw

end
end Erdos773.GaussianIncidentEncoding
end EndpointModule100
-- End GaussianIncidentEncoding.lean

-- Begin GaussianIncidentCounting.lean
section EndpointModule101

/- A finite, multiplicity-safe upper bound for square-collision incident degrees. -/
namespace Erdos773.GaussianIncidentCounting
open Finset GaussianCollisionFactorization GaussianQuadrantFactor GaussianFactorResidues
open GaussianIncidentEncoding SquareCollisionCodegrees
set_option maxHeartbeats 2000000
noncomputable section

abbrev Triple := ℕ × (ℕ × ℕ)

def representations (a N : ℕ) : Finset Triple :=
  ((Icc 1 N) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter
    (fun t => t.2.1 ≤ t.2.2 ∧ a^2+t.1^2=t.2.1^2+t.2.2^2)

def Witness (a : ℕ) (p : ℕ × ℕ) (t : Triple) : Prop :=
  ∃ g : G, gauss a t.1=g*gauss p.1 p.2 ∧
    squareCoords (gauss t.2.1 t.2.2)=squareCoords (g*star (gauss p.1 p.2))

def fiber (a N : ℕ) (p : ℕ × ℕ) : Finset Triple := by
  classical
  exact (representations a N).filter (Witness a p)

lemma fiber_card {a N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    (fiber a N p).card ≤ (partners a N p).card := by
  classical
  apply card_le_card_of_injOn Prod.fst
  · intro t ht
    obtain ⟨ht, g,hg,hw⟩ := mem_filter.mp ht
    have hb := (mem_product.mp (mem_filter.mp ht).1).1
    exact mem_filter.mpr ⟨hb,g,by simpa only [mul_comm] using hg⟩
  · rintro ⟨b,c,d⟩ ht ⟨b',c',d'⟩ ht' he
    change b=b' at he
    subst b'
    obtain ⟨ht,g,hg,hw⟩ := mem_filter.mp ht
    obtain ⟨ht',g',hg',hw'⟩ := mem_filter.mp ht'
    have ho := output_unique (gauss_ne_zero (mem_directions hp).1) hg hg' hw hw'
    have hh := squareCoords_ordered_injective (mem_filter.mp ht).2.1 (mem_filter.mp ht').2.1 ho
    rcases hh with ⟨rfl,rfl⟩
    rfl

lemma representations_cover {a N : ℕ} (ha : 0<a) (haN : a ≤ N) :
    representations a N ⊆ (directions N).biUnion (fiber a N) := by
  classical
  intro t ht
  obtain ⟨hm,hord,he⟩ := mem_filter.mp ht
  have hbN := (mem_Icc.mp (mem_product.mp hm).1).2
  obtain ⟨p,hp,g,hg,hw⟩ := exists_direction ha haN hbN he
  exact mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨ht,g,hg,hw⟩⟩

/-- Ordered representations are covered without multiplying the bound by
    the number of possible Gaussian witnesses for a single representation. -/
theorem representations_card_bound {a N : ℕ} (ha : 0<a) (haN : a ≤ N) :
    ((representations a N).card:ℝ)  ≤ 
      ∑ p ∈ directions N, ((N:ℝ)/normSq p+1) := by
  classical
  have h₁ := card_le_card (representations_cover ha haN)
  have h₂ := card_biUnion_le (s := directions N) (t := fiber a N)
  have h₃ := sum_le_sum (s := directions N) (fun p hp => fiber_card (a := a) hp)
  have hh : (representations a N).card ≤ ∑ p ∈ directions N, (partners a N p).card :=
    h₁.trans (h₂.trans h₃)
  have hR : ((representations a N).card:ℝ)  ≤ 
      ∑ p ∈ directions N, ((partners a N p).card:ℝ) := by exact_mod_cast hh
  exact hR.trans (sum_le_sum (fun p hp => partners_card hp))

def support (a : ℕ) (t : Triple) : Finset ℕ := {a,t.1,t.2.1,t.2.2}

lemma incident_cover (a N : ℕ) :
    (edges (Icc 1 N)).filter (fun e => a ∈ e) ⊆
      (representations a N).image (support a) := by
  classical
  intro e he
  obtain ⟨he,ha⟩ := mem_filter.mp he
  obtain ⟨q,hq,hqe⟩ := SquareSupportCounting.ordered_representation he
  rcases q with ⟨⟨u,v⟩,⟨w,x⟩⟩
  obtain ⟨hm,huv,hvw,hwx,hEq⟩ := mem_filter.mp hq
  simp only [mem_product] at hm
  dsimp only at huv hvw hwx hEq
  change ({u,v,w,x}:Finset ℕ)=e at hqe
  rw [← hqe] at ha ⊢
  simp only [mem_insert,mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · refine mem_image.mpr ⟨(x,v,w),mem_filter.mpr ⟨mem_product.mpr ⟨hm.2.2,
      mem_product.mpr ⟨hm.1.2,hm.2.1⟩⟩,hvw.le,hEq⟩,?_⟩
    ext n; simp only [support,mem_insert,mem_singleton]; tauto
  · refine mem_image.mpr ⟨(w,u,x),mem_filter.mpr ⟨mem_product.mpr ⟨hm.2.1,
      mem_product.mpr ⟨hm.1.1,hm.2.2⟩⟩,(huv.trans (hvw.trans hwx)).le,hEq.symm⟩,?_⟩
    ext n; simp only [support,mem_insert,mem_singleton]; tauto
  · refine mem_image.mpr ⟨(v,u,x),mem_filter.mpr ⟨mem_product.mpr ⟨hm.1.2,
      mem_product.mpr ⟨hm.1.1,hm.2.2⟩⟩,(huv.trans (hvw.trans hwx)).le,by dsimp only; omega⟩,?_⟩
    ext n; simp only [support,mem_insert,mem_singleton]; tauto
  · refine mem_image.mpr ⟨(u,v,w),mem_filter.mpr ⟨mem_product.mpr ⟨hm.1.1,
      mem_product.mpr ⟨hm.1.2,hm.2.1⟩⟩,hvw.le,by dsimp only; omega⟩,?_⟩
    ext n; simp only [support,mem_insert,mem_singleton]; tauto

/-- Actual incident four-support degree, with no ordering or unit factor
    in front of the Gaussian-direction sum. -/
theorem degree_bound {a N : ℕ} (ha : 0<a) (haN : a ≤ N) :
    (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ)  ≤ 
      ∑ p ∈ directions N, ((N:ℝ)/normSq p+1) := by
  have hc := (card_le_card (incident_cover a N)).trans card_image_le
  have hh : (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ)  ≤ 
      ((representations a N).card:ℝ) := by exact_mod_cast hc
  exact hh.trans (representations_card_bound ha haN)

end
end Erdos773.GaussianIncidentCounting
end EndpointModule101
-- End GaussianIncidentCounting.lean

-- Begin GaussianDirectionSum.lean
section EndpointModule102

/- A finite uniform reciprocal-sum estimate for Gaussian directions. -/
namespace Erdos773.GaussianDirectionSum
open Finset GaussianIncidentEncoding GaussianDirectionWeights GaussianRadialCounting
set_option maxHeartbeats 2000000
noncomputable section

def radial (u v : ℕ) : ℝ := (weight u v : ℝ)/((u:ℝ)^2+(v:ℝ)^2)

lemma radial_nonneg (u v : ℕ) : 0 ≤ radial u v := by unfold radial; positivity
lemma radial_symm (u v : ℕ) : radial u v = radial v u := by
  have hw : weight u v = weight v u := by unfold weight; split_ifs <;> omega
  simp only [radial,hw,add_comm]
lemma radial_diag (u : ℕ) : radial u u=0 := by simp [radial,weight]

lemma triangle_as_square (R : ℕ) :
    (∑ u ∈ Icc 1 R, ∑ v ∈ Icc 1 R, if v<u then radial u v else 0) = triangleSum R := by
  apply sum_congr rfl
  intro u hu
  rw [← sum_filter]
  have he : (Icc 1 R).filter (fun v => v<u)=Icc 1 (u-1) := by
    ext v
    simp only [mem_filter,mem_Icc]
    have := mem_Icc.mp hu
    omega
  rw [he]
  rfl

lemma square_sum (R : ℕ) :
    (∑ p ∈ (Icc 1 R) ×ˢ (Icc 1 R), radial p.1 p.2) = 2*triangleSum R := by
  rw [sum_product]
  have he (u v : ℕ) : radial u v =
      (if v<u then radial u v else 0)+(if u<v then radial v u else 0) := by
    rcases lt_trichotomy v u with h | h | h
    · simp [h,show ¬u<v by omega]
    · subst v; simp [radial_diag]
    · simp [h,show ¬v<u by omega,radial_symm u v]
  calc
    _ = ∑ u ∈ Icc 1 R, ∑ v ∈ Icc 1 R,
        ((if v<u then radial u v else 0)+(if u<v then radial v u else 0)) := by
      apply sum_congr rfl
      intro u hu
      exact sum_congr rfl (fun v hv => he u v)
    _ = 2*triangleSum R := by
      simp_rw [sum_add_distrib]
      rw [triangle_as_square,sum_comm,triangle_as_square]
      ring

lemma direction_box {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ directions N) :
    p.1 ≤ Nat.sqrt (2*N) ∧ p.2 ≤ Nat.sqrt (2*N) := by
  have hn := (mem_directions hp).2.2.2
  dsimp [normSq] at hn
  constructor <;> apply Nat.le_sqrt'.mpr <;> omega

lemma directions_card (N : ℕ) : (directions N).card ≤ 4*N := by
  have hs : directions N ⊆ (Icc 1 (Nat.sqrt (2*N))) ×ˢ (Icc 0 (Nat.sqrt (2*N))) := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := direction_box hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨(mem_directions hp).1,h₁⟩,
      mem_Icc.mpr ⟨Nat.zero_le _,h₂⟩⟩
  have hc := card_le_card hs
  rw [card_product,Nat.card_Icc,Nat.card_Icc] at hc
  simp only [Nat.add_sub_cancel,Nat.sub_zero] at hc
  have hs := Nat.sqrt_le' (2*N)
  have ht : Nat.sqrt (2*N) ≤ Nat.sqrt (2*N)^2 := Nat.le_pow (by omega)
  nlinarith

lemma reciprocal_sum_bound (N : ℕ) :
    (∑ p ∈ directions N, 1/(normSq p : ℝ)) ≤ 1+2*triangleSum (Nat.sqrt (2*N)) := by
  classical
  let R := Nat.sqrt (2*N)
  let B := (Icc 1 R) ×ˢ (Icc 1 R)
  have hs : directions N ⊆ insert (1,0) B := by
    intro p hp
    obtain ⟨hu,hcop,hpar,hn⟩ := mem_directions hp
    obtain ⟨h₁,h₂⟩ := direction_box hp
    by_cases hv : p.2=0
    · have he : p.1=1 := by simpa [hv] using hcop
      apply mem_insert.mpr
      left
      exact Prod.ext he hv
    · apply mem_insert_of_mem
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hu,h₁⟩,mem_Icc.mpr ⟨by omega,h₂⟩⟩
  have he : (∑ p ∈ directions N, 1/(normSq p : ℝ)) =
      ∑ p ∈ directions N, radial p.1 p.2 := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨hu,hcop,hpar,hn⟩ := mem_directions hp
    simp [radial,weight_of_coprime hcop hpar,normSq]
  rw [he]
  calc
    _ ≤ ∑ p ∈ insert (1,0) B, radial p.1 p.2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun p hp _ => radial_nonneg _ _)
    _ = 1+2*triangleSum R := by
      rw [sum_insert (by simp [B])]
      have hr : radial 1 0=1 := by norm_num [radial,weight]
      rw [hr,square_sum]

end
end Erdos773.GaussianDirectionSum
end EndpointModule102
-- End GaussianDirectionSum.lean

-- Begin GaussianIncidentDegree.lean
section EndpointModule103

/- A uniform O(N log N) bound, with leading coefficient below one third,
for the actual four-root square-collision degree. -/
namespace Erdos773.GaussianIncidentDegree
open Finset Filter GaussianIncidentEncoding GaussianDirectionSum GaussianRadialCounting
open SquareCollisionCodegrees
set_option maxHeartbeats 2000000
noncomputable section

lemma log_sqrt_bound {N : ℕ} (hN : 1 ≤ N) :
    2*Real.log (Nat.sqrt (2*N):ℝ) ≤ Real.log (2*(N:ℝ)) := by
  have hs : 0<Nat.sqrt (2*N) := Nat.sqrt_pos.mpr (by omega)
  have hsR : (0:ℝ)<Nat.sqrt (2*N) := by exact_mod_cast hs
  have hb : (Nat.sqrt (2*N):ℝ)^2 ≤ 2*(N:ℝ) := by exact_mod_cast Nat.sqrt_le' (2*N)
  have hl := Real.log_le_log (sq_pos_of_pos hsR) hb
  simpa only [Real.log_pow,Nat.cast_ofNat] using hl

lemma reciprocal_log_bound {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ directions N, 1/(normSq p:ℝ)) ≤ (83/250:ℝ)*Real.log (2*(N:ℝ))+28002 := by
  have hs := reciprocal_sum_bound N
  have ht := triangle_sum_bound (M := Nat.sqrt (2*N)) (Nat.sqrt_pos.mpr (by omega))
  have hl := log_sqrt_bound hN
  nlinarith only [hs,ht,hl]

/-- Finite bound, uniform in the incident root. -/
theorem finite_degree_bound {a N : ℕ} (ha : 0<a) (haN : a ≤ N) :
    (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ) ≤
      (N:ℝ)*((83/250:ℝ)*Real.log (2*(N:ℝ))+28006) := by
  have hd := GaussianIncidentCounting.degree_bound ha haN
  have he : (∑ p ∈ directions N, ((N:ℝ)/normSq p+1)) =
      (N:ℝ)*(∑ p ∈ directions N, 1/(normSq p:ℝ))+(directions N).card := by
    rw [sum_add_distrib,mul_sum]
    simp only [mul_one_div,sum_const,nsmul_eq_mul,mul_one]
  rw [he] at hd
  have hr := mul_le_mul_of_nonneg_left (reciprocal_log_bound (by omega : 1 ≤ N))
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hc : ((directions N).card:ℝ) ≤ 4*(N:ℝ) := by exact_mod_cast directions_card N
  nlinarith only [hd,hr,hc]

/-- A uniform eventual maximum-degree estimate for the actual four-support
square-collision hypergraph. This is not an independent-set bound. -/
theorem eventual_degree_bound : ∀ᶠ N : ℕ in atTop, ∀ a ∈ Icc 1 N,
    (HypergraphDegreeTrim.degree (edges (Icc 1 N)) a:ℝ) ≤
      (333/1000:ℝ)*(N:ℝ)*Real.log (N:ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (1000*((83/250:ℝ)*Real.log 2+28006))] with N hN hL
  intro a ha
  obtain ⟨ha,haN⟩ := mem_Icc.mp ha
  have h := finite_degree_bound ha haN
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.log_mul (by norm_num) hNR.ne'] at h
  have hh : (83/250:ℝ)*(Real.log 2+Real.log (N:ℝ))+28006 ≤
      (333/1000:ℝ)*Real.log (N:ℝ) := by linarith only [hL]
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  nlinarith only [h,hm]

end
end Erdos773.GaussianIncidentDegree
end EndpointModule103
-- End GaussianIncidentDegree.lean

-- Begin UniformSquareSamplingScales.lean
section EndpointModule104

/- Elementary scale bounds for uniform square-root sampling. -/
namespace Erdos773.UniformSquareSamplingScales
set_option maxHeartbeats 2000000
noncomputable section

def momentOrder (X : ℝ) : ℕ := ⌈X^(1/100:ℝ)⌉₊

lemma momentOrder_bounds {X : ℝ} (hX : 1 ≤ X) :
    X^(1/100:ℝ) ≤ (momentOrder X:ℝ) ∧ (momentOrder X:ℝ) ≤ 2*X^(1/100:ℝ) := by
  have hR : 1 ≤ X^(1/100:ℝ) := Real.one_le_rpow hX (by norm_num)
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (by positivity : 0 ≤ X^(1/100:ℝ))).le.trans (by linarith)⟩

lemma overlap_budget {X L : ℝ} (hX : 1 ≤ X) (hL : 0 ≤ L)
    (hsmall : 16000*L ≤ X^(1/100:ℝ)) :
    3*(momentOrder X:ℝ)^2*L^2 ≤ X/12000 := by
  have hR : 0 ≤ X^(1/100:ℝ) := Real.rpow_nonneg (by linarith) _
  have hq := (momentOrder_bounds hX).2
  have hs := mul_le_mul hq hsmall (by positivity : 0 ≤ 16000*L) (by positivity : 0 ≤ 2*X^(1/100:ℝ))
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ (momentOrder X:ℝ)*(16000*L)) hs 2
  have hfour : (X^(1/100:ℝ))^4 ≤ X := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ X)]
    exact (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ)*4 ≤ 1)).trans_eq (Real.rpow_one X)
  nlinarith only [hs2,hfour]

lemma tail_decay {X : ℝ} {q : ℕ} (hX : 0<X) (hq : 16000*Real.log X ≤ (q:ℝ)) :
    (3999/4000:ℝ)^q ≤ 1/X^4 := by
  have hb : (3999/4000:ℝ) ≤ Real.exp (-(1/4000:ℝ)) := by
    have hh := Real.add_one_le_exp (-(1/4000:ℝ))
    linarith only [hh]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3999/4000) hb q
  rw [← Real.exp_nat_mul] at hp
  have hexp : (q:ℝ)*(-(1/4000:ℝ)) ≤ -(4*Real.log X) := by linarith only [hq]
  have he : Real.exp (-(4*Real.log X)) = 1/X^4 := by
    rw [Real.exp_neg]
    have hh : Real.exp (4*Real.log X)=X^4 := by
      simpa only [Real.exp_log hX] using Real.exp_nat_mul (Real.log X) 4
    rw [hh,one_div]
  exact (hp.trans (Real.exp_le_exp.mpr hexp)).trans_eq he

lemma moment_ratio {X L : ℝ} (hX : 1 ≤ X) (hL : 0<L)
    (hsmall : 16000*L ≤ X^(1/100:ℝ)) :
    (((1/L)^3*((333/1000:ℝ)*X*L)+(3*momentOrder X:ℕ)*momentOrder X)/
      ((1999/6000:ℝ)*X/L^2)) ≤ 3999/4000 := by
  have hb := overlap_budget hX hL.le hsmall
  have hX0 : 0<X := by linarith
  apply (div_le_iff₀ (by positivity : 0<(1999/6000:ℝ)*X/L^2)).mpr
  have he : ((1/L)^3*((333/1000:ℝ)*X*L)+(3*momentOrder X:ℕ)*momentOrder X)*L^2 =
      (333/1000:ℝ)*X+3*(momentOrder X:ℝ)^2*L^2 := by
    push_cast
    field_simp
  have ht : ((3999/4000:ℝ)*((1999/6000:ℝ)*X/L^2))*L^2 =
      (3999/4000:ℝ)*(1999/6000:ℝ)*X := by field_simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp
  rw [he,ht]
  nlinarith only [hb,hX0]

/-- The total high-moment penalty is O(X^-2), smaller than the progression
    deletion cost. -/
lemma sampling_loss {X : ℝ} (hX : 1 ≤ X) (hL : 0<Real.log X)
    (hsmall : 16000*Real.log X ≤ X^(1/100:ℝ)) :
    (1/Real.log X)^3*(24*X*Real.log X)+X^2*
      ((((1/Real.log X)^3*((333/1000:ℝ)*X*Real.log X)+
        (3*momentOrder X:ℕ)*momentOrder X)/((1999/6000:ℝ)*X/(Real.log X)^2))^momentOrder X) ≤
      25*X/(Real.log X)^2 := by
  have hX0 : 0<X := by linarith
  have hratio := moment_ratio hX hL hsmall
  have hnon : 0 ≤ ((1/Real.log X)^3*((333/1000:ℝ)*X*Real.log X)+
      (3*momentOrder X:ℕ)*momentOrder X)/((1999/6000:ℝ)*X/(Real.log X)^2) := by positivity
  have hp := (pow_le_pow_left₀ hnon hratio (momentOrder X)).trans
    (tail_decay hX0 (hsmall.trans (momentOrder_bounds hX).1))
  have htail := mul_le_mul_of_nonneg_left hp (sq_nonneg X)
  have he : X^2*(1/X^4)=1/X^2 := by field_simp
  rw [he] at htail
  have hlog := Real.log_le_sub_one_of_pos hX0
  have hlogX : Real.log X ≤ X := by linarith only [hlog]
  have hs := pow_le_pow_left₀ hL.le hlogX 2
  have hX3 : X^2 ≤ X^3 := by nlinarith only [hX,mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hX)]
  have hlast : 1/X^2 ≤ X/(Real.log X)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hX0) (sq_pos_of_pos hL)).mpr
    nlinarith only [hs,hX3]
  have hap : (1/Real.log X)^3*(24*X*Real.log X)=24*X/(Real.log X)^2 := by field_simp
  rw [hap]
  have he25 : 25*X/(Real.log X)^2=24*X/(Real.log X)^2+X/(Real.log X)^2 := by ring
  rw [he25]
  exact add_le_add le_rfl (htail.trans hlast)

end
end Erdos773.UniformSquareSamplingScales
end EndpointModule104
-- End UniformSquareSamplingScales.lean

-- Begin UniformSquareSampling.lean
section EndpointModule105

/- Progression-free square-root samples with simultaneous control of every
four-support degree, without maximum-degree trimming. -/
namespace Erdos773.UniformSquareSampling
open Finset Filter SquareCollisionCodegrees SquareProgressionSupports HypergraphDegreeTrim
set_option maxHeartbeats 2000000
noncomputable section

theorem finite_selection (N K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hdegree : ∀ a ∈ Icc 1 N, (degree (edges (Icc 1 N)) a:ℝ) ≤ D)
    (hpair : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b → (pairEdges (Icc 1 N) a b).card ≤ K)
    (hpositive : 0 < p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B ⊆ Icc 1 N, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<T) ∧
      p*N-p^3*(progressions (Icc 1 N)).card-
        (N:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  classical
  obtain ⟨B,hB,hP,hcap,hcard⟩ := UniformAmbientSampling.finite_selection
    (Icc 1 N) (edges (Icc 1 N)) (progressions (Icc 1 N)) K q p T D hp hp1 hT
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_progressions.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he => (mem_progressions.mp he).2.1) hdegree hpair
    (by simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hpositive)
  refine ⟨B,hB,ap_free_of_avoids hB hP,?_,?_⟩
  · rw [ControlledSquareSampling.edges_restrict hB]
    exact hcap
  · simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hcard

open UniformSquareSamplingScales

/-- Finite sufficient conditions for a logarithmic-density sample with no
    maximum-degree trimming loss. -/
theorem finite_log_sampling (N : ℕ) (δ : ℝ) (hN : 1 ≤ N)
    (hδ : 0<δ) (hδ1 : δ<1) (hL : 2 ≤ Real.log (N:ℝ))
    (hlarge : 25/δ ≤ Real.log (N:ℝ))
    (hsmall : 16000*Real.log (N:ℝ) ≤ (N:ℝ)^(1/100:ℝ))
    (hdegree : ∀ a ∈ Icc 1 N, (degree (edges (Icc 1 N)) a:ℝ) ≤
      (333/1000:ℝ)*(N:ℝ)*Real.log N)
    (hpair : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card:ℝ) ≤ (N:ℝ)^(1/100:ℝ)) :
    ∃ B ⊆ Icc 1 N, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<(1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ (B.card:ℝ) := by
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0:ℝ)<N := by linarith only [hX1]
  have hL0 : 0<Real.log (N:ℝ) := by linarith only [hL]
  let p : ℝ := 1/Real.log (N:ℝ)
  let D : ℝ := (333/1000:ℝ)*(N:ℝ)*Real.log N
  let T : ℝ := (1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2
  let q := momentOrder (N:ℝ)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; exact (div_le_one hL0).mpr (by linarith)
  have hT : 0<T := by dsimp [T]; positivity
  have hAP := ControlledSquareSampling.progression_log_bound N (by omega) hL
  have hcost := sampling_loss hX1 hL0 hsmall
  have hAPmul := mul_le_mul_of_nonneg_left hAP (pow_nonneg hp 3)
  have htotal : p^3*(progressions (Icc 1 N)).card+
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q ≤ 25*(N:ℝ)/(Real.log N)^2 := by
    exact (add_le_add hAPmul le_rfl).trans hcost
  have h25 : 25 ≤ δ*Real.log (N:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hlarge
    linarith only [hh]
  have herror : 25*(N:ℝ)/(Real.log N)^2 ≤ δ*(N:ℝ)/Real.log N := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hL0).mpr
    have hh := mul_le_mul_of_nonneg_right h25 (show 0 ≤ (N:ℝ)*Real.log N by positivity)
    nlinarith only [hh]
  have htarget : (1-δ)*(N:ℝ)/Real.log N ≤ p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q := by
    dsimp [p] at htotal herror ⊢
    have he : (1-δ)*(N:ℝ)/Real.log N = (1/Real.log N)*(N:ℝ)-δ*(N:ℝ)/Real.log N := by ring
    rw [he]
    linarith only [htotal,herror]
  have hpos : 0 < p*N-p^3*(progressions (Icc 1 N)).card-
      (N:ℝ)^2*((p^3*D+(3*q:ℕ)*q)/T)^q := by
    apply lt_of_lt_of_le _ htarget
    have hgap : 0<1-δ := by linarith only [hδ1]
    positivity
  obtain ⟨B,hB,hAP,hcap,hcard⟩ := finite_selection N q q p T D hp hp1 hT hdegree
    (by
      intro a ha b hb hab
      have hh := (hpair a ha b hb hab).trans (momentOrder_bounds hX1).1
      exact_mod_cast hh) hpos
  exact ⟨B,hB,hAP,hcap,htarget.trans hcard⟩

/-- Actual progression-free samples of size (1-delta)N/log N, with a uniform
    degree coefficient strictly below one third. This is not a Sidon bound. -/
theorem logarithmic_sampling (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (∀ a ∈ Icc 1 N, (degree (edges B) a:ℝ)<(1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2) ∧
      (1-δ)*(N:ℝ)/Real.log N ≤ (B.card:ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/16000)
  filter_upwards [GaussianIncidentDegree.eventual_degree_bound,
    eventually_pair_codegree_bound (1/100) (by norm_num),ht.eventually_ge_atTop 2,
    ht.eventually_ge_atTop (25/δ),hsmall,eventually_ge_atTop 1] with N hdeg hpair hL hlarge hsmall hN
  have hX : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : 0 ≤ Real.log (N:ℝ) := by linarith only [hL]
  have hsmall' : Real.log (N:ℝ) ≤ (1/16000:ℝ)*(N:ℝ)^(1/100:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0,
      abs_of_nonneg (Real.rpow_nonneg hX _)] using hsmall
  exact finite_log_sampling N δ hN hδ hδ1 hL hlarge (by linarith only [hsmall']) hdeg hpair

end
end Erdos773.UniformSquareSampling
end EndpointModule105
-- End UniformSquareSampling.lean

-- Begin GreedyBatchSquareEndpoint.lean
section EndpointModule106

/- The coefficient-one two-thirds endpoint for Sidon subsets of squares.
This does not establish any exponent greater than two thirds. -/
namespace Erdos773.GreedyBatchSquareEndpoint
open Finset Filter SquareCollisionCodegrees HypergraphDegreeTrim
open GreedyBatchSquareScales GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

/-- An actual unit-coefficient endpoint, with all finite hypotheses supplied.
The near-linear conjecture remains a strictly stronger statement. -/
theorem eventual_endpoint : ∀ᶠ N : ℕ in atTop,
    (N:ℝ)^(2/3:ℝ)≤(maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  let M : ℕ := max 100000000000 (max 2000000 (3*increment (exponent+increment exponent)))
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^eta) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [eta])).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/160000)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/2)
  have hbudget := ((isLittleO_log_rpow_atTop (by norm_num [eta] : (0:ℝ)<eta)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/16)
  filter_upwards [hpow.eventually_ge_atTop (M:ℝ),hlog.eventually_ge_atTop 4000000000000000000,
    hsmall,hbudget,eventually_ge_atTop 1,
    UniformSquareSampling.logarithmic_sampling (1/100000) (by norm_num) (by norm_num),
    eventually_pair_codegree_bound eta (by norm_num [eta])]
    with N hM hL hs hb hN hsample hpair
  have hX0 : (0:ℝ)<N := by exact_mod_cast hN
  have hX1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0<Real.log (N:ℝ) := by linarith only [hL]
  have hL1 : 1≤Real.log (N:ℝ) := by linarith only [hL]
  have hmM : M≤root (N:ℝ) := by exact_mod_cast hM.trans (root_lower (N:ℝ))
  have hmEff : 100000000000≤root (N:ℝ) := (le_max_left _ _).trans hmM
  have hm : 2000000≤root (N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hmM)
  have hmV : 3*increment (exponent+increment exponent)≤root (N:ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmM)
  have hM2 : (2:ℝ)≤M := by exact_mod_cast (show 2≤M from (by omega : 2≤100000000000).trans (le_max_left _ _))
  have htwo : (2:ℝ)≤(N:ℝ)^eta := hM2.trans hM
  have hs' : Real.log (N:ℝ)≤(1/2:ℝ)*(N:ℝ)^(1/160000:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0.le,
      abs_of_nonneg (Real.rpow_nonneg hX0.le _)] using hs
  have hb' : Real.log (N:ℝ)≤(1/16:ℝ)*(N:ℝ)^eta := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0.le,
      abs_of_nonneg (Real.rpow_nonneg hX0.le _)] using hb
  have hT3 : (horizon (N:ℝ))^3≤(root (N:ℝ):ℝ)/16 := by
    rw [horizon_cube hL0.le]
    calc
      _ ≤ Real.log (N:ℝ) := by dsimp [c]; linarith only [hL0.le]
      _ ≤ (1/16:ℝ)*(N:ℝ)^eta := hb'
      _ ≤ _ := by have := root_lower (N:ℝ); linarith only [this]
  have hdU : scale (N:ℝ)≤(root (N:ℝ):ℝ)^exponent :=
    (scale_upper hX1 hL1).trans (volume hX0.le)
  have hvol : N≤root (N:ℝ)^exponent := by exact_mod_cast volume hX0.le
  obtain ⟨A,hA,hAP,hdegree,hcard⟩ := hsample
  have hdegree' (x : ℕ) (hx : x∈A) : (degree (edges A) x:ℝ)≤(scale (N:ℝ))^3 := by
    rw [scale_cube hX0.le]
    exact (hdegree x (hA hx)).le
  have hpair' : ∀ x∈A, ∀ y∈A, x≠y → (pairEdges A x y).card≤root (N:ℝ) := by
    intro x hx y hy hxy
    have hmono : ((pairEdges A x y).card:ℝ)≤(pairEdges (Icc 1 N) x y).card := by
      exact_mod_cast card_le_card (pairEdges_mono hA x y)
    exact_mod_cast (hmono.trans (hpair x (hA hx) y (hA hy) hxy)).trans (root_lower (N:ℝ))
  have hcert := GreedyBatchSquareCertificate.certificate N (root (N:ℝ)) exponent
    (scale (N:ℝ)) (horizon (N:ℝ)) (root (N:ℝ)) A hm hmV (scale_pos hX0 hL0) hdU
    (by omega) le_rfl (by have := horizon_large hL; linarith only [this]) hT3
    (terminal hX1 hm hL htwo hs') hA hvol hAP hdegree' hpair'
  have hcard' : loss*(N:ℝ)/Real.log N≤(A.card:ℝ) := by
    norm_num [loss] at hcard ⊢
    exact hcard
  exact (coefficient hX0 hL hmEff hcard').trans hcert

end
end Erdos773.GreedyBatchSquareEndpoint
end EndpointModule106
-- End GreedyBatchSquareEndpoint.lean

#print axioms Erdos773.GaussianDirectionWeights.row_formula
#print axioms Erdos773.GaussianDirectionWeights.weight_sum
#print axioms Erdos773.GreedyBatchSquareEndpoint.eventual_endpoint
