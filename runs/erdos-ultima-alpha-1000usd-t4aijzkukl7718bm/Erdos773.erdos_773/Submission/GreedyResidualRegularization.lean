import Submission.MixedLayerRegularization
import Submission.FiniteHypergraphRestriction
import Submission.GreedyRestartAlteration
import Submission.GreedyCommonNeighbors

/-! Structural transport from an actual greedy residual to a mixed regular
model on copies of the available carrier. This is not a stochastic stage
or a stronger asymptotic independence bound. -/
namespace Erdos773.GreedyResidualRegularization
open Finset GreedyHypergraphState GreedyRestartAlteration
open HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (Adj common both)
open FiniteHypergraphRestriction (Carrier restrict up down)
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The lower rank bound follows from availability, even if the original
system already has short edges. -/
lemma rank_range {H : Finset (Finset α)} {I : Finset α}
    (hI : Independent H I) (hH : ∀ e∈H, e.card≤4) :
    ∀ f∈residual H I, 2≤f.card ∧ f.card≤4 := by
  intro f hf
  have hpos := card_pos.mpr (residual_nonempty hI hf)
  have hne : f.card≠1 := by
    intro he
    obtain ⟨x,hx⟩ := card_eq_one.mp he
    have hxQ : x∈available H I := residual_subset hf (by rw [hx]; simp)
    obtain ⟨e,he,hef⟩ := mem_image.mp hf
    apply (mem_available.mp hxQ).2 e (mem_filter.mp he).1
    intro a ha
    by_cases hai : a∈I
    · exact mem_insert_of_mem hai
    · have hm : a∈f := hef ▸ mem_sdiff.mpr ⟨ha,hai⟩
      rw [hx] at hm
      exact mem_insert.mpr (Or.inl (mem_singleton.mp hm))
  refine ⟨by omega,?_⟩
  obtain ⟨e,he,rfl⟩ := mem_image.mp hf
  exact (card_le_card sdiff_subset).trans (hH e (mem_filter.mp he).1)

/-- Identifying equal residual supports can only decrease degrees. -/
lemma degree_le (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (x : α) :
    degree (layer (residual H I) j) x ≤ (incident H I j x).card := by
  have hs : (layer (residual H I) j).filter (fun e => x∈e) ⊆
      (incident H I j x).image (fun e => e \ I) := by
    intro f hf
    obtain ⟨hf,hx⟩ := mem_filter.mp hf
    obtain ⟨hf,hj⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    obtain ⟨he,hQ⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨e,mem_incident.mpr ⟨he,hQ,hj,hx⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma pair_le (H : Finset (Finset α)) (I : Finset α) (x y : α) :
    pairDegree (residual H I) x y ≤ pairDegree H x y := by
  have hs : (residual H I).filter (fun e => x∈e ∧ y∈e) ⊆
      (H.filter (fun e => x∈e ∧ y∈e)).image (fun e => e \ I) := by
    intro f hf
    obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨(mem_filter.mp he).1,
      (mem_sdiff.mp hx).1,(mem_sdiff.mp hy).1⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma intersections {H : Finset (Finset α)} (I : Finset α) (K : ℕ)
    (hK : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤K) :
    ∀ e∈residual H I, ∀ f∈residual H I, e≠f → (e∩f).card≤K := by
  intro e he f hf hef
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
  have hab : a≠b := fun h => hef (congrArg (fun s => s \ I) h)
  apply (card_le_card (show (a \ I)∩(b \ I)⊆a∩b from ?_)).trans
    (hK a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab)
  intro x hx
  exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp hx).1).1,
    (mem_sdiff.mp (mem_inter.mp hx).2).1⟩

lemma adj_closes {H : Finset (Finset α)} {I : Finset α} {x : α}
    (hx : x∈available H I) (y : α) :
    Adj (residual H I) x y ↔ y∈closes H I x := by
  constructor
  · rintro ⟨hne,hf⟩
    have hy : y∈available H I := residual_subset hf (by simp)
    obtain ⟨e,he,hef⟩ := mem_image.mp hf
    exact mem_closes.mpr ⟨hy,hne.symm,e,(mem_filter.mp he).1,hef⟩
  · intro hy
    obtain ⟨hy,hne,e,he,hef⟩ := mem_closes.mp hy
    refine ⟨hne.symm,mem_image.mpr ⟨e,mem_filter.mpr ⟨he,?_⟩,hef⟩⟩
    rw [hef]
    simp [insert_subset_iff,hx,hy]

lemma common_eq {H : Finset (Finset α)} {I : Finset α} {x y : α}
    (hx : x∈available H I) (hy : y∈available H I) :
    common (residual H I) x y = GreedyCommonNeighbors.commonDegree H I x y := by
  unfold common GreedyCommonNeighbors.commonDegree
  congr 1
  ext z
  simp only [RegularizationCommonNeighbors.mem_both,adj_closes hx,adj_closes hy,mem_inter]

abbrev OnAvailable (H : Finset (Finset α)) (I : Finset α) :=
  restrict (available H I) (residual H I)

/-- One exact restart model. Its volume is 24*p^3*|Q|, NOT
24*p^3 times the original ambient volume. The output transfer extends the
old selected set and retains all shortened constraints. -/
theorem exists_restart_model (H : Finset (Finset α)) (I : Finset α)
    (hI : Independent H I) (hH : ∀ e∈H, e.card≤4)
    (D2 D3 D4 K C : ℕ)
    (h2 : ∀ x∈available H I, (incident H I 2 x).card≤D2)
    (h3 : ∀ x∈available H I, (incident H I 3 x).card≤D3)
    (h4 : ∀ x∈available H I, (incident H I 4 x).card≤D4)
    (hK : 1≤K) (hpair : ∀ x y, x≠y → pairDegree H x y≤K)
    (hinter : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ x∈available H I, ∀ y∈available H I, x≠y →
      GreedyCommonNeighbors.commonDegree H I x y≤C) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      MixedLayerRegularization.cap D2 D3 D4≤p ∧ p≤2*MixedLayerRegularization.cap D2 D3 D4 ∧
      ∃ G : Finset (Finset (MixedLayerRegularization.Model (Carrier (available H I)) p)),
        (∀ e∈G, 2≤e.card ∧ e.card≤4) ∧
        (∀ x, degree (layer G 2) x=D2) ∧
        (∀ x, degree (layer G 3) x=D3) ∧
        (∀ x, degree (layer G 4) x=D4) ∧
        (∀ x y, x≠y → pairDegree G x y≤K) ∧
        (∀ e∈G, ∀ f∈G, e≠f → (e∩f).card≤2) ∧
        (∀ x y, x≠y → common G x y≤C+3) ∧
        (∀ B, Independent G B → ∃ J⊆available H I,
          Independent H (I∪J) ∧ B.card≤24*p^3*J.card ∧ (I∪J).card=I.card+J.card) ∧
        (∀ B : ℕ, (∀ a b, a≠b → RegularizationSharedLinks.count (OnAvailable H I) a b≤B) →
          ∀ x y, x≠y → RegularizationSharedLinks.count G x y≤B) := by
  let Q := available H I
  have hR : ∀ e∈residual H I, e⊆Q := fun _ he => residual_subset he
  have hrank : ∀ e∈OnAvailable H I, 2≤e.card ∧ e.card≤4 := by
    intro e he
    have hh := rank_range hI hH _ ((FiniteHypergraphRestriction.mem_restrict hR).mp he)
    simpa only [FiniteHypergraphRestriction.up_card] using hh
  have hd (j D : ℕ) (hj : ∀ x∈Q, (incident H I j x).card≤D)
      (x : Carrier Q) : degree (layer (OnAvailable H I) j) x≤D := by
    rw [FiniteHypergraphRestriction.degree_eq hR]
    exact (degree_le H I j x.val).trans (hj x.val x.property)
  have hpa (x y : Carrier Q) (hxy : x≠y) : pairDegree (OnAvailable H I) x y≤K := by
    rw [FiniteHypergraphRestriction.pair_eq hR]
    exact (pair_le H I x.val y.val).trans (hpair _ _ (fun h => hxy (Subtype.ext h)))
  have hc (x y : Carrier Q) (hxy : x≠y) : common (OnAvailable H I) x y≤C := by
    rw [FiniteHypergraphRestriction.common_eq hR,common_eq x.property y.property]
    exact hcommon _ x.property _ y.property (fun h => hxy (Subtype.ext h))
  obtain ⟨p,hp,hpL,hpU,G,hr,hg2,hg3,hg4,hgp,hgi,hgc,ht,htwin⟩ :=
    MixedLayerRegularization.exists_regularization (OnAvailable H I) D2 D3 D4 K C
      hrank (hd 2 D2 h2) (hd 3 D3 h3) (hd 4 D4 h4) hK hpa
      (FiniteHypergraphRestriction.intersections hR 2 (intersections I 2 hinter)) hc
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,hpL,hpU,G,hr,hg2,hg3,hg4,hgp,hgi,hgc,?_,htwin⟩
  intro B hB
  obtain ⟨A,hA,hcard⟩ := ht B hB
  let J := up Q A
  have hJ : J⊆available H I := FiniteHypergraphRestriction.up_subset A
  have hj : Independent (residual H I) J :=
    (FiniteHypergraphRestriction.independent_iff hR A).mp hA
  refine ⟨J,hJ,(extension_iff hJ).mpr hj,?_,?_⟩
  · simpa only [J,FiniteHypergraphRestriction.up_card] using hcard
  · exact card_union_of_disjoint (((available_disjoint H I).mono_left hJ).symm)

#print axioms rank_range
#print axioms degree_le
#print axioms pair_le
#print axioms intersections
#print axioms common_eq
#print axioms exists_restart_model
end
end Erdos773.GreedyResidualRegularization
