import Submission.GreedyBatchDegreeStep
import Submission.GreedyBatchSharedLoss
import Submission.GreedyBatchSharedWitnesses
import Submission.BernoulliEvents

/-! Uniform scalar tails for old-edge survival and new residual witnesses.
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

#print axioms old_degree_tail
#print axioms old_shared_tail
#print axioms promotion_tail
#print axioms shared_creation_tail
end
end Erdos773.GreedyBatchScalarTails
