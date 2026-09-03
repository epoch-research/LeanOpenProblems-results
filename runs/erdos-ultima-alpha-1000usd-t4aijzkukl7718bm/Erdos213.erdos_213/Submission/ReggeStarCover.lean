import Submission.ReggeCover
import Submission.ReggeStarParams

/-! A uniform covering obstruction for locally mixed, independently scaled
Regge outputs of cyclic quadrilaterals and equal-radius stars. This does not
assert that arbitrary integral-distance configurations have such sources. -/
open EuclideanGeometry
namespace Erdos213.ReggeStarCover
open ReggeMixed ReggeCircle ReggeStar InversionReduction CircleCoverReduction
noncomputable section
set_option maxHeartbeats 4000000

def anchor : ℝ² := !₂[1,0]
def third (c d : ℝ) : ℝ² := !₂[c,d]

def lengths (q p : ℝ²) : Edges :=
  ![1,dist q 0,dist p 0,dist q anchor,dist p anchor,dist p q]

def triple (q p : ℝ²) : Fin 3 → ℝ := ![dist p 0,dist p anchor,dist p q]

lemma anchor_ne_zero : anchor≠0 := by
  intro h
  have hh := congrArg (fun p : ℝ² => p 0) h
  norm_num [anchor] at hh

lemma third_eta (p : ℝ²) : third (p 0) (p 1)=p := by
  ext i
  fin_cases i <;> rfl

lemma lengths_realizes (q p : ℝ²) :
    Realizes (lengths q p) 1 0 (q 0) (q 1) (p 0) (p 1) := by
  dsimp [Realizes,lengths]
  simp only [distance_sq]
  simp [anchor]

lemma triple_realizes (q p : ℝ²) :
    AffineTrilateration.RealizesTriple (q 0) (q 1) p (triple q p) := by
  dsimp [AffineTrilateration.RealizesTriple,triple]
  simp only [distance_sq]
  simp [anchor]

def ScalenePoint (q : ℝ²) : Prop :=
  q 1≠0 ∧ 1≠dist q 0 ∧ 1≠dist q anchor ∧ dist q 0≠dist q anchor

lemma scalene_third_ne_zero {q : ℝ²} (h : ScalenePoint q) : q≠0 := by
  intro hh
  apply h.1
  simp [hh]

lemma scalene_third_ne_anchor {q : ℝ²} (h : ScalenePoint q) : q≠anchor := by
  intro hh
  apply h.1
  simp [hh,anchor]

def starCandidates (q : ℝ²) : Finset ℝ² :=
  ReggeStarParams.candidates (q 0) (q 1) (dist q 0) (dist q anchor)

lemma starCandidates_card (q : ℝ²) : (starCandidates q).card≤72 :=
  ReggeStarParams.candidates_card_le_seventy_two _ _ _ _

lemma mem_starCandidates {q p : ℝ²} (hq : ScalenePoint q)
    (h : StarLocus (lengths q p)) : p∈starCandidates q := by
  exact ReggeStarParams.mem_candidates (q 0) (q 1) (dist q 0) (dist q anchor)
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 p (triple q p) (triple_realizes q p) h

lemma coveredBy_singletons (A : Finset ℝ²) {k : ℕ} (hk : A.card≤k) :
    CoveredBy (A : Set ℝ²) k := by
  classical
  refine ⟨A.image (fun p => {p}),Finset.card_image_le.trans hk,?_,?_⟩
  · intro C hC
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
    exact generalized_of_cospherical (cospherical_singleton p)
  · intro p hp
    exact ⟨{p},Finset.mem_image.mpr ⟨p,hp,rfl⟩,by simp⟩

/-- The target set need not be finite. Each target point may use a different
source quadrilateral, Regge word, and scale. -/
theorem hybrid_fixed_scalene_cover {S : Set ℝ²} {q : ℝ²} (hq : ScalenePoint q)
    (hS : ∀ p∈S, p≠0 → p≠anchor → p≠q →
      Special (lengths q p) ∨ StarLocus (lengths q p)) : CoveredBy S 76 := by
  classical
  let T : Set ℝ² := {p∈S | p∉starCandidates q}
  have hT : CoveredBy T 4 := by
    apply ReggeCover.special_fixed_triangle_cover anchor_ne_zero
      (scalene_third_ne_zero hq) (scalene_third_ne_anchor hq).symm
    intro p hp hp0 hpA hpq
    have hh := hS p hp.1 hp0 hpA hpq
    rcases hh with hs | hs
    · exact ⟨lengths q p,lengths_realizes q p,hs⟩
    · exact False.elim (hp.2 (mem_starCandidates hq hs))
  have hC := coveredBy_singletons (starCandidates q) (starCandidates_card q)
  apply (hT.union hC).mono
  intro p hp
  by_cases hh : p∈starCandidates q
  · exact Or.inr hh
  · exact Or.inl ⟨hp,hh⟩

/-- The sharper cardinality bound uses each exceptional candidate only once,
not three times as in the generic circle-cover bound. It remains conditional. -/
theorem hybrid_weak_card_le_eighty_four {S : Finset ℝ²} {q : ℝ²}
    (hq : ScalenePoint q) (hweak : NoFourGeneralized (S : Set ℝ²))
    (hS : ∀ p∈S, p≠0 → p≠anchor → p≠q →
      Special (lengths q p) ∨ StarLocus (lengths q p)) : S.card≤84 := by
  classical
  let T := S \ starCandidates q
  have hT : T.card≤12 := by
    apply ReggeCover.special_weak_card_le_twelve anchor_ne_zero
      (scalene_third_ne_zero hq) (scalene_third_ne_anchor hq).symm
    · intro Q hQ hn
      apply hweak Q _ hn
      intro p hp
      exact (Finset.mem_sdiff.mp (hQ hp)).1
    · intro p hp hp0 hpA hpq
      obtain ⟨hpS,hpC⟩ := Finset.mem_sdiff.mp hp
      rcases hS p hpS hp0 hpA hpq with hs | hs
      · exact ⟨lengths q p,lengths_realizes q p,hs⟩
      · exact False.elim (hpC (mem_starCandidates hq hs))
  have hsub : S⊆T∪starCandidates q := by
    intro p hp
    by_cases hh : p∈starCandidates q
    · exact Finset.mem_union_right _ hh
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,hh⟩)
  have hc := starCandidates_card q
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

def isoscelesCover : Fin 4 → Set ℝ² :=
  ![{p | p 1=0}, {p | radiusSq p=1},
    {p | radiusSq p-2*p 0=0}, {p | 2*p 0-1=0}]

lemma isoscelesCover_generalized (i : Fin 4) : OnGeneralizedCircle (isoscelesCover i) := by
  fin_cases i
  · refine ⟨0,0,1,0,Or.inr (Or.inr (by norm_num)),?_⟩
    intro p hp
    change p 1=0 at hp
    simpa using hp
  · refine ⟨1,0,0,-1,Or.inl (by norm_num),?_⟩
    intro p hp
    change radiusSq p=1 at hp
    simpa using sub_eq_zero.mpr hp
  · refine ⟨1,-2,0,0,Or.inl (by norm_num),?_⟩
    intro p hp
    change radiusSq p-2*p 0=0 at hp
    linear_combination hp
  · refine ⟨0,2,0,-1,Or.inr (Or.inl (by norm_num)),?_⟩
    intro p hp
    change 2*p 0-1=0 at hp
    linear_combination hp

lemma mem_isoscelesCover {p : ℝ²} (h : ¬ScalenePoint p) :
    ∃ i, p∈isoscelesCover i := by
  by_cases hy : p 1=0
  · exact ⟨0,hy⟩
  have h0 : radiusSq p=dist p 0^2 := radiusSq_eq p
  have h1 : radiusSq p-2*p 0+1=dist p anchor^2 := by
    simp only [distance_sq,anchor,radiusSq,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  by_cases ha : 1=dist p 0
  · refine ⟨1,?_⟩
    change radiusSq p=1
    rw [h0,← ha]
    norm_num
  by_cases hb : 1=dist p anchor
  · refine ⟨2,?_⟩
    change radiusSq p-2*p 0=0
    rw [← hb] at h1
    linarith
  have hc : dist p 0=dist p anchor := by
    by_contra hh
    exact h ⟨hy,ha,hb,hh⟩
  refine ⟨3,?_⟩
  change 2*p 0-1=0
  rw [hc] at h0
  linarith

/-- Without a scalene triangle over the fixed baseline, a four-set cover is
purely geometric and needs no rational-distance or source hypothesis. -/
theorem no_scalene_cover {S : Set ℝ²} (h : ∀ p∈S, ¬ScalenePoint p) : CoveredBy S 4 := by
  classical
  refine ⟨Finset.univ.image isoscelesCover,?_,?_,?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro C hC
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hC
    exact isoscelesCover_generalized i
  · intro p hp
    obtain ⟨i,hi⟩ := mem_isoscelesCover (h p hp)
    exact ⟨isoscelesCover i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩

/-- No particular third anchor is fixed in advance. -/
theorem hybrid_fixed_pair_cover {S : Set ℝ²}
    (hS : ∀ q∈S, ∀ p∈S, p≠0 → p≠anchor → p≠q →
      Special (lengths q p) ∨ StarLocus (lengths q p)) : CoveredBy S 76 := by
  classical
  by_cases hh : ∃ q∈S, ScalenePoint q
  · obtain ⟨q,hq,hsc⟩ := hh
    exact hybrid_fixed_scalene_cover hsc (hS q hq)
  · have hn : ∀ p∈S, ¬ScalenePoint p := by
      intro p hp hs
      exact hh ⟨p,hp,hs⟩
    obtain ⟨F,hF,hgen,hcov⟩ := no_scalene_cover hn
    exact ⟨F,hF.trans (by norm_num),hgen,hcov⟩

/-- Three equal incident edges at any one of the four vertices. -/
def EqualStar (e : Edges) : Prop :=
  (e 0=e 1 ∧ e 0=e 2) ∨ (e 0=e 3 ∧ e 0=e 4) ∨
  (e 1=e 3 ∧ e 1=e 5) ∨ (e 2=e 4 ∧ e 2=e 5)

lemma star_of_equalStar {e : Edges} (h : EqualStar e) : StarLocus e := by
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact star_of_equal_radii h0 h1
  · refine ⟨4,?_⟩
    change 1*e 0+(-1)*e 4=0 ∧ 1*e 3+(-1)*e 4=0
    constructor <;> linarith
  · refine ⟨14,?_⟩
    change 1*e 1+(-1)*e 5=0 ∧ 1*e 3+(-1)*e 5=0
    constructor <;> linarith
  · refine ⟨23,?_⟩
    change 1*e 2+(-1)*e 5=0 ∧ 1*e 4+(-1)*e 5=0
    constructor <;> linarith

/-- This includes the two possible types of quadruple from a circle together
with its center. Different sources may be used for different target points. -/
def Source (e : Edges) : Prop := EqualStar e ∨
  ∃ x y u v z w : ℝ, Realizes e x y u v z w ∧ (∀ i, 0<e i) ∧
    ReggeCircle.circle x y u v z w=0

lemma hybrid_of_source {e f : Edges} (h : Source e) (ho : ReggeCircle.Orbit e f) :
    Special f ∨ StarLocus f := by
  rcases h with hs | ⟨x,y,u,v,z,w,he,hpos,hc⟩
  · exact Or.inr (star_orbit ho (star_of_equalStar hs))
  · exact Or.inl (special_orbit ho (special_of_circle e x y u v z w he hpos hc))

/-- Arbitrary independent local Regge words and real scales are allowed.
The fixed baseline is normalized to (0,0),(1,0). -/
theorem source_fixed_pair_cover {S : Set ℝ²}
    (hS : ∀ q∈S, ∀ p∈S, p≠0 → p≠anchor → p≠q →
      ∃ e : Edges, Source e ∧ ReggeCircle.Orbit e (lengths q p)) : CoveredBy S 76 := by
  apply hybrid_fixed_pair_cover
  intro q hq p hp hp0 hpA hpq
  obtain ⟨e,he,ho⟩ := hS q hq p hp hp0 hpA hpq
  exact hybrid_of_source he ho

/-- A uniform cardinality cap for the source-restricted family in weak general
position. It is not an upper bound for arbitrary rational-distance sets. -/
theorem source_weak_card_le_eighty_four {S : Finset ℝ²}
    (hweak : NoFourGeneralized (S : Set ℝ²))
    (hS : ∀ q∈S, ∀ p∈S, p≠0 → p≠anchor → p≠q →
      ∃ e : Edges, Source e ∧ ReggeCircle.Orbit e (lengths q p)) : S.card≤84 := by
  classical
  by_cases hh : ∃ q∈S, ScalenePoint q
  · obtain ⟨q,hq,hsc⟩ := hh
    apply hybrid_weak_card_le_eighty_four hsc hweak
    intro p hp hp0 hpA hpq
    obtain ⟨e,he,ho⟩ := hS q hq p hp hp0 hpA hpq
    exact hybrid_of_source he ho
  · have hn : ∀ p∈(S : Set ℝ²), ¬ScalenePoint p := by
      intro p hp hs
      exact hh ⟨p,hp,hs⟩
    have hc := weak_card_le_three_mul_cover hweak (no_scalene_cover hn)
    omega

/-- These are the six primitive lengths of an actual integral quadrilateral
from the certified heptad. Hence the additional source hypothesis is not
universal, even on four-point integral configurations. -/
theorem heptad_control_outside_source_orbits :
    ¬∃ e : Edges, Source e ∧ ReggeCircle.Orbit e
      ![22270,8636,16637,13746,11397,11049] := by
  rintro ⟨e,he,ho⟩
  rcases hybrid_of_source he ho with hs | hs
  · exact ReggeCover.heptad_edge_control_not_special hs
  · exact ReggeStar.heptad_edge_control_not_star hs

#print axioms lengths_realizes
#print axioms mem_starCandidates
#print axioms hybrid_fixed_scalene_cover
#print axioms hybrid_weak_card_le_eighty_four
#print axioms no_scalene_cover
#print axioms hybrid_fixed_pair_cover
#print axioms hybrid_of_source
#print axioms source_fixed_pair_cover
#print axioms source_weak_card_le_eighty_four
#print axioms heptad_control_outside_source_orbits
end
end Erdos213.ReggeStarCover
