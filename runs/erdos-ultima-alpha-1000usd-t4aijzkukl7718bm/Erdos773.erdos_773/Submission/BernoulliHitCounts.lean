import Submission.IndexedBernoulliMoments
import Submission.WeightedBernoulliLowerTail

/-! Lower concentration for the number of indexed sets hit by independent
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
    simp [card_pos,← sum_filter,hitCount]
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

#print axioms hit_lower
#print axioms pairFamily_incidence
#print axioms linear_value
#print axioms weight_sum
#print axioms pair_tail
#print axioms lower_tail
end
end Erdos773.BernoulliHitCounts
