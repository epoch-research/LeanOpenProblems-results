import Submission.GreedyBatchScalarTails
import Submission.GreedyBatchSharedStep
import Submission.GreedyBatchCommonBudgets
import Submission.GreedyBatchCommonStep
import Submission.GreedyBatchSelection
import Submission.GreedyBatchStructure

/-! A simultaneous finite batch certificate. All concentration hypotheses
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

#print axioms vertex_tail
#print axioms pair_tail
#print axioms bad_tail
#print axioms bounds_of_good
#print axioms exists_batch
end
end Erdos773.GreedyBatchCertificate
