import Submission.GaussianIncidentEncoding
import Submission.SquareSupportCounting
import Submission.HypergraphDegreeTrim

/-! A finite, multiplicity-safe upper bound for square-collision incident degrees. -/
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

#print axioms fiber_card
#print axioms representations_card_bound
#print axioms incident_cover
#print axioms degree_bound
end
end Erdos773.GaussianIncidentCounting
