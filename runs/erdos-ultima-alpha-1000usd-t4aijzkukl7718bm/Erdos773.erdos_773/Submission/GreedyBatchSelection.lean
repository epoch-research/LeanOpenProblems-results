import Submission.GreedyBatchState
import Submission.BernoulliEvents

/-! Selecting one good batch by a penalized continuation-density reward.
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

/-- Indexed local tests can be assembled into the preceding certificate
without assuming that their events are independent. -/
theorem exists_all (H : Finset (Finset α)) (p δ : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hδ : 0≤δ) (hδ1 : δ≤1)
    (S : Finset β) (Bad : β → Finset α → Prop) (b : β → ℝ)
    (hb : ∀ i∈S, prob p (Bad i)≤b i)
    (hpositive : 0<lowerReward H p δ-(Fintype.card α:ℝ)*(∑ i∈S, b i)) :
    ∃ R : Finset α, (∀ i∈S, ¬Bad i R) ∧
      lowerReward H p δ-(Fintype.card α:ℝ)*(∑ i∈S, b i)≤reward H δ R := by
  obtain ⟨R,hR,hr⟩ := exists_avoiding H p δ (∑ i∈S, b i) hp hp1 hδ hδ1
    (fun R => ∃ i∈S, Bad i R)
    ((cover_bound p hp hp1 S Bad _ (fun R h => h)).trans (sum_le_sum hb)) hpositive
  exact ⟨R,fun i hi hb => hR ⟨i,hi,hb⟩,hr⟩

#print axioms reward_upper
#print axioms exists_avoiding
#print axioms exists_all
end
end Erdos773.GreedyBatchSelection
