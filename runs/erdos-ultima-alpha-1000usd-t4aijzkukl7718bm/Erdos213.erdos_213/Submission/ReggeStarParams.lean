import Submission.ReggeStar
import Submission.AffineTrilateration

/-! With a fixed scalene triangle, six of the star-orbit planes are impossible,
and the other eighteen give affine lines in signed-distance space. -/
open EuclideanGeometry
namespace Erdos213.ReggeStarParams
open Polynomial ReggeStar AffineTrilateration
noncomputable section
set_option maxHeartbeats 4000000

def slope : Fin 18 → Fin 3 → ℝ :=
  !![0,0,1;
    0,1,0;
    1,1,1;
    (1/3 : ℝ),(-1/3 : ℝ),1;
    0,0,1;
    1,1,1;
    -1,-3,1;
    1,0,0;
    (-1/3 : ℝ),(1/3 : ℝ),1;
    -1,3,1;
    0,1,0;
    0,1,1;
    1,0,0;
    -3,-1,1;
    1,0,1;
    1,1,0;
    3,-1,1;
    1,1,1]

def intercept (b c : ℝ) : Fin 18 → Fin 3 → ℝ :=
  !![(1)*(b),(2)*(1) + (-1)*(c),0;
    (1)*(1),0,(2)*(b) + (-1)*(c);
    (1)*(1) + (-2)*(b) + (1)*(c),(-1)*(1) + (-1)*(b) + (2)*(c),0;
    (1)*(1) + ((-2/3 : ℝ))*(b) + ((1/3 : ℝ))*(c),(1)*(1) + ((-1/3 : ℝ))*(b) + ((2/3 : ℝ))*(c),0;
    (2)*(1) + (-1)*(b),(1)*(c),0;
    (-1)*(1) + (2)*(b) + (-1)*(c),(1)*(1) + (1)*(b) + (-2)*(c),0;
    (-1)*(1) + (2)*(b) + (1)*(c),(-1)*(1) + (3)*(b) + (2)*(c),0;
    0,(1)*(1),(-1)*(b) + (2)*(c);
    (1)*(1) + ((2/3 : ℝ))*(b) + ((-1/3 : ℝ))*(c),(1)*(1) + ((1/3 : ℝ))*(b) + ((-2/3 : ℝ))*(c),0;
    (1)*(1) + (2)*(b) + (-1)*(c),(-1)*(1) + (-3)*(b) + (2)*(c),0;
    (-1)*(1) + (2)*(b),0,(1)*(c);
    ((1/2 : ℝ))*(1) + ((1/2 : ℝ))*(b),0,0;
    0,(-1)*(1) + (2)*(c),(1)*(b);
    (-1)*(1) + (2)*(b) + (3)*(c),(-1)*(1) + (1)*(b) + (2)*(c),0;
    0,((1/2 : ℝ))*(1) + ((1/2 : ℝ))*(c),0;
    0,0,((1/2 : ℝ))*(b) + ((1/2 : ℝ))*(c);
    (-1)*(1) + (2)*(b) + (-3)*(c),(1)*(1) + (-1)*(b) + (2)*(c),0;
    0,0,0]

def freeIndex : Fin 18 → Fin 3 := ![2,1,2,2,2,2,2,0,2,2,1,2,0,2,2,1,2,2]

def radii (b c : ℝ) (k : Fin 18) (j : Fin 3) : ℝ[X] :=
  C (intercept b c k j)+C (slope k j)*X

lemma radii_eval (b c : ℝ) (k : Fin 18) (j : Fin 3) (t : ℝ) :
    (radii b c k j).eval t=intercept b c k j+slope k j*t := by
  simp [radii]

lemma radii_degree (b c : ℝ) (k : Fin 18) (j : Fin 3) :
    (radii b c k j).natDegree≤1 := by
  unfold radii
  compute_degree!

lemma radii_free (b c : ℝ) (k : Fin 18) : radii b c k (freeIndex k)=X := by
  fin_cases k
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp
  · change C (0 : ℝ)+C (1 : ℝ)*X=X
    simp

lemma resolve_plane (b c : ℝ) (v : Fin 3 → ℝ)
    (h1b : 1≠b) (h1c : 1≠c) (hbc : b≠c)
    (h : StarLocus ![1,b,v 0,c,v 1,v 2]) :
    ∃ k : Fin 18, ∀ j, v j=(radii b c k j).eval (v (freeIndex k)) := by
  obtain ⟨i,hi⟩ := h
  fin_cases i
  · change (1)*(1) + (-1)*(v 0)=0 ∧ (1)*(b) + (-1)*(v 0)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply h1b
    linear_combination (1)*(h0) + (-1)*(h1)
  · change (2)*(1) + (-1)*(c) + (-1)*(v 1)=0 ∧ (1)*(b) + (-1)*(v 0)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨0,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(b))+(0)*v 2
      linear_combination (-1)*(h1)
    · rw [radii_eval]
      change v 1=((2)*(1) + (-1)*(c))+(0)*v 2
      linear_combination (-1)*(h0)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (-1)*(v 0)=0 ∧ (2)*(b) + (-1)*(c) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨1,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(1))+(0)*v 1
      linear_combination (-1)*(h0)
    · rw [radii_eval]
      change v 1=(0)+(1)*v 1
      ring
    · rw [radii_eval]
      change v 2=((2)*(b) + (-1)*(c))+(0)*v 1
      linear_combination (-1)*(h1)
  · change (1)*(1) + (-1)*(b)=0 ∧ (2)*(v 0) + (-1)*(v 1) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply h1b
    linear_combination (1)*(h0)
  · change (1)*(1) + (-1)*(v 1)=0 ∧ (1)*(c) + (-1)*(v 1)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply h1c
    linear_combination (1)*(h0) + (-1)*(h1)
  · change (3)*(1) + (-1)*(v 0) + (-3)*(c) + (2)*(v 1) + (-1)*(v 2)=0 ∧ (3)*(b) + (1)*(v 0) + (-3)*(c) + (1)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨2,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(1) + (-2)*(b) + (1)*(c))+(1)*v 2
      linear_combination ((-1/3 : ℝ))*(h0) + ((2/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 1=((-1)*(1) + (-1)*(b) + (2)*(c))+(1)*v 2
      linear_combination ((1/3 : ℝ))*(h0) + ((1/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (1)*(v 0) + (1)*(c) + (-2)*(v 1) + (-1)*(v 2)=0 ∧ (1)*(b) + (3)*(v 0) + (1)*(c) + (-3)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨3,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(1) + ((-2/3 : ℝ))*(b) + ((1/3 : ℝ))*(c))+((1/3 : ℝ))*v 2
      linear_combination (-1)*(h0) + ((2/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 1=((1)*(1) + ((-1/3 : ℝ))*(b) + ((2/3 : ℝ))*(c))+((-1/3 : ℝ))*v 2
      linear_combination (-1)*(h0) + ((1/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (2)*(1) + (-1)*(b) + (-1)*(v 0)=0 ∧ (1)*(c) + (-1)*(v 1)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨4,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((2)*(1) + (-1)*(b))+(0)*v 2
      linear_combination (-1)*(h0)
    · rw [radii_eval]
      change v 1=((1)*(c))+(0)*v 2
      linear_combination (-1)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (3)*(1) + (1)*(v 0) + (-3)*(c) + (-2)*(v 1) + (1)*(v 2)=0 ∧ (3)*(b) + (-1)*(v 0) + (-3)*(c) + (-1)*(v 1) + (2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨5,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((-1)*(1) + (2)*(b) + (-1)*(c))+(1)*v 2
      linear_combination ((1/3 : ℝ))*(h0) + ((-2/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 1=((1)*(1) + (1)*(b) + (-2)*(c))+(1)*v 2
      linear_combination ((-1/3 : ℝ))*(h0) + ((-1/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (3)*(v 0) + (1)*(c) + (-2)*(v 1) + (-3)*(v 2)=0 ∧ (1)*(b) + (1)*(v 0) + (1)*(c) + (-1)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨6,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((-1)*(1) + (2)*(b) + (1)*(c))+(-1)*v 2
      linear_combination (1)*(h0) + (-2)*(h1)
    · rw [radii_eval]
      change v 1=((-1)*(1) + (3)*(b) + (2)*(c))+(-3)*v 2
      linear_combination (1)*(h0) + (-3)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (-1)*(v 1)=0 ∧ (1)*(b) + (-2)*(c) + (1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨7,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(0)+(1)*v 0
      ring
    · rw [radii_eval]
      change v 1=((1)*(1))+(0)*v 0
      linear_combination (-1)*(h0)
    · rw [radii_eval]
      change v 2=((-1)*(b) + (2)*(c))+(0)*v 0
      linear_combination (1)*(h1)
  · change (1)*(1) + (1)*(v 0) + (-1)*(c) + (-2)*(v 1) + (1)*(v 2)=0 ∧ (1)*(b) + (-3)*(v 0) + (1)*(c) + (3)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨8,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(1) + ((2/3 : ℝ))*(b) + ((-1/3 : ℝ))*(c))+((-1/3 : ℝ))*v 2
      linear_combination (-1)*(h0) + ((-2/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 1=((1)*(1) + ((1/3 : ℝ))*(b) + ((-2/3 : ℝ))*(c))+((1/3 : ℝ))*v 2
      linear_combination (-1)*(h0) + ((-1/3 : ℝ))*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (-3)*(v 0) + (1)*(c) + (-2)*(v 1) + (3)*(v 2)=0 ∧ (1)*(b) + (1)*(v 0) + (-1)*(c) + (1)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨9,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((1)*(1) + (2)*(b) + (-1)*(c))+(-1)*v 2
      linear_combination (-1)*(h0) + (-2)*(h1)
    · rw [radii_eval]
      change v 1=((-1)*(1) + (-3)*(b) + (2)*(c))+(3)*v 2
      linear_combination (1)*(h0) + (3)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (-1)*(c)=0 ∧ (1)*(v 0) + (-2)*(v 1) + (1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply h1c
    linear_combination (1)*(h0)
  · change (1)*(b) + (-1)*(v 2)=0 ∧ (1)*(c) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply hbc
    linear_combination (1)*(h0) + (-1)*(h1)
  · change (1)*(1) + (-2)*(b) + (1)*(v 0)=0 ∧ (1)*(c) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨10,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((-1)*(1) + (2)*(b))+(0)*v 1
      linear_combination (1)*(h0)
    · rw [radii_eval]
      change v 1=(0)+(1)*v 1
      ring
    · rw [radii_eval]
      change v 2=((1)*(c))+(0)*v 1
      linear_combination (-1)*(h1)
  · change (1)*(1) + (1)*(b) + (-2)*(v 0)=0 ∧ (1)*(v 1) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨11,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(((1/2 : ℝ))*(1) + ((1/2 : ℝ))*(b))+(0)*v 2
      linear_combination ((-1/2 : ℝ))*(h0)
    · rw [radii_eval]
      change v 1=(0)+(1)*v 2
      linear_combination (1)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (-2)*(c) + (1)*(v 1)=0 ∧ (1)*(b) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨12,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(0)+(1)*v 0
      ring
    · rw [radii_eval]
      change v 1=((-1)*(1) + (2)*(c))+(0)*v 0
      linear_combination (1)*(h0)
    · rw [radii_eval]
      change v 2=((1)*(b))+(0)*v 0
      linear_combination (-1)*(h1)
  · change (1)*(b) + (-1)*(c)=0 ∧ (1)*(v 0) + (1)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    exfalso
    apply hbc
    linear_combination (1)*(h0)
  · change (1)*(1) + (-1)*(v 0) + (-1)*(c) + (2)*(v 1) + (-1)*(v 2)=0 ∧ (1)*(b) + (-1)*(v 0) + (1)*(c) + (1)*(v 1) + (-2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨13,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((-1)*(1) + (2)*(b) + (3)*(c))+(-3)*v 2
      linear_combination (1)*(h0) + (-2)*(h1)
    · rw [radii_eval]
      change v 1=((-1)*(1) + (1)*(b) + (2)*(c))+(-1)*v 2
      linear_combination (1)*(h0) + (-1)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(1) + (1)*(c) + (-2)*(v 1)=0 ∧ (1)*(v 0) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨14,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(0)+(1)*v 2
      linear_combination (1)*(h1)
    · rw [radii_eval]
      change v 1=(((1/2 : ℝ))*(1) + ((1/2 : ℝ))*(c))+(0)*v 2
      linear_combination ((-1/2 : ℝ))*(h0)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(b) + (1)*(c) + (-2)*(v 2)=0 ∧ (1)*(v 0) + (-1)*(v 1)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨15,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(0)+(1)*v 1
      linear_combination (1)*(h1)
    · rw [radii_eval]
      change v 1=(0)+(1)*v 1
      ring
    · rw [radii_eval]
      change v 2=(((1/2 : ℝ))*(b) + ((1/2 : ℝ))*(c))+(0)*v 1
      linear_combination ((-1/2 : ℝ))*(h0)
  · change (1)*(1) + (-1)*(v 0) + (1)*(c) + (-2)*(v 1) + (1)*(v 2)=0 ∧ (1)*(b) + (-1)*(v 0) + (-1)*(c) + (-1)*(v 1) + (2)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨16,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=((-1)*(1) + (2)*(b) + (-3)*(c))+(3)*v 2
      linear_combination (1)*(h0) + (-2)*(h1)
    · rw [radii_eval]
      change v 1=((1)*(1) + (-1)*(b) + (2)*(c))+(-1)*v 2
      linear_combination (-1)*(h0) + (1)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring
  · change (1)*(v 0) + (-1)*(v 2)=0 ∧ (1)*(v 1) + (-1)*(v 2)=0 at hi
    obtain ⟨h0,h1⟩ := hi
    refine ⟨17,?_⟩
    intro j
    fin_cases j
    · rw [radii_eval]
      change v 0=(0)+(1)*v 2
      linear_combination (1)*(h0)
    · rw [radii_eval]
      change v 1=(0)+(1)*v 2
      linear_combination (1)*(h1)
    · rw [radii_eval]
      change v 2=(0)+(1)*v 2
      ring

def candidates (c d b a : ℝ) : Finset ℝ² :=
  Finset.univ.biUnion (fun k : Fin 18 => AffineTrilateration.candidates c d (radii b a k))

lemma candidates_card_le_seventy_two (c d b a : ℝ) : (candidates c d b a).card≤72 := by
  calc
    _ ≤ ∑ k : Fin 18, (AffineTrilateration.candidates c d (radii b a k)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k : Fin 18, 4 := Finset.sum_le_sum (fun k _ =>
      candidates_card_le_four c d (radii b a k) (radii_degree b a k))
    _ = 72 := by norm_num

lemma mem_candidates (c d b a : ℝ) (hd : d≠0)
    (h1b : 1≠b) (h1a : 1≠a) (hba : b≠a)
    (p : ℝ²) (v : Fin 3 → ℝ) (hv : RealizesTriple c d p v)
    (hs : StarLocus ![1,b,v 0,a,v 1,v 2]) : p∈candidates c d b a := by
  obtain ⟨k,hk⟩ := resolve_plane b a v h1b h1a hba hs
  apply Finset.mem_biUnion.mpr
  refine ⟨k,Finset.mem_univ _,?_⟩
  apply AffineTrilateration.mem_candidates c d hd (radii b a k) (freeIndex k)
    (radii_free b a k) (v (freeIndex k)) p
  have hh : v=(fun j => (radii b a k j).eval (v (freeIndex k))) := funext hk
  rwa [← hh]

/-- Only points meeting the additional star-orbit hypothesis are bounded. -/
theorem star_fiber_card_le_seventy_two (c d b a : ℝ) (hd : d≠0)
    (h1b : 1≠b) (h1a : 1≠a) (hba : b≠a) (S : Finset ℝ²)
    (hS : ∀ p∈S, ∃ v : Fin 3 → ℝ, RealizesTriple c d p v ∧
      StarLocus ![1,b,v 0,a,v 1,v 2]) : S.card≤72 := by
  apply (Finset.card_le_card (t := candidates c d b a) ?_).trans
    (candidates_card_le_seventy_two c d b a)
  intro p hp
  obtain ⟨v,hv,hs⟩ := hS p hp
  exact mem_candidates c d b a hd h1b h1a hba p v hv hs

#print axioms resolve_plane
#print axioms radii_free
#print axioms candidates_card_le_seventy_two
#print axioms star_fiber_card_le_seventy_two
end
end Erdos213.ReggeStarParams
