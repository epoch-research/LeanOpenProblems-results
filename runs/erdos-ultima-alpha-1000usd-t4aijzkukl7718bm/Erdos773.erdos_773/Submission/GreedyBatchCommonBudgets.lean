import Submission.GreedyMixedCommonProfiles
import Submission.IndexedBernoulliMoments

/-! Explicit mixed common-neighbor witness budgets for one Bernoulli batch.
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

#print axioms firstRank_card
#print axioms two_support_cover
#print axioms two_support_bound
#print axioms total_patterns_bound
#print axioms support_mass
#print axioms layer_tail
end
end Erdos773.GreedyBatchCommonBudgets
