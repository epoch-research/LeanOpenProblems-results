import FormalConjecturesUtil
import Submission.PolynomialTwoAnchors

/-! A line of signed distance triples meets the trilateration surface of
three noncollinear anchors in at most four points. No integrality assumptions. -/
open EuclideanGeometry
namespace Erdos213.AffineTrilateration
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000

lemma degrees_zero_of_product_constant (u v : ℝ[X]) (a : ℝ) (ha : a≠0)
    (h : u*v=C a) : u.natDegree=0 ∧ v.natDegree=0 := by
  have hu : u≠0 := by
    intro hh
    apply C_ne_zero.mpr ha
    simpa [hh] using h.symm
  have hv : v≠0 := by
    intro hh
    apply C_ne_zero.mpr ha
    simpa [hh] using h.symm
  have hd := congrArg natDegree h
  rw [natDegree_mul hu hv,natDegree_C] at hd
  omega

lemma three_anchor_constancy (x y : ℝ[X]) (c d : ℝ) (hd : d≠0)
    (r : Fin 3 → ℝ[X])
    (h0 : x^2+y^2=(r 0)^2)
    (h1 : (x-1)^2+y^2=(r 1)^2)
    (h2 : (x-C c)^2+(y-C d)^2=(r 2)^2) :
    x.natDegree=0 ∧ y.natDegree=0 := by
  have hs0 : IsSquare (x^2+C (1 : ℝ)*y^2) := by
    refine ⟨r 0,?_⟩
    simpa [pow_two] using h0
  have hs1 : IsSquare ((x-1)^2+C (1 : ℝ)*y^2) := by
    refine ⟨r 1,?_⟩
    simpa [pow_two] using h1
  rcases PolynomialTwoAnchors.two_anchor_classification x y 1 (by norm_num) hs0 hs1 with
    hy | hh
  · subst y
    let u := r 2+(x-C c)
    let v := r 2-(x-C c)
    have huv : u*v=C (d^2) := by
      dsimp [u,v]
      simp only [zero_sub,neg_sq,← map_pow] at h2
      linear_combination -h2
    obtain ⟨hu,hv⟩ := degrees_zero_of_product_constant u v (d^2) (pow_ne_zero _ hd) huv
    have hx : x=C (((u.coeff 0)-(v.coeff 0))/2+c) := by
      have he : (2 : ℝ[X])*x=u-v+C (2*c) := by dsimp [u,v]; simp only [map_mul,map_ofNat]; ring
      rw [eq_C_of_natDegree_eq_zero hu,eq_C_of_natDegree_eq_zero hv] at he
      apply mul_left_cancel₀ (show (2 : ℝ[X])≠0 by norm_num)
      calc
        (2 : ℝ[X])*x=C (u.coeff 0-v.coeff 0+2*c) := by
          simpa only [map_add,map_sub] using he
        _ = (2 : ℝ[X])*C ((u.coeff 0-v.coeff 0)/2+c) := by
          rw [show (2 : ℝ[X])=C (2 : ℝ) by simp only [map_ofNat],← map_mul]
          congr 1
          ring
    simp [hx]
  · exact hh

lemma radius_constant {x y r : ℝ[X]} {a b : ℝ}
    (hx : x.natDegree=0) (hy : y.natDegree=0)
    (h : (x-C a)^2+(y-C b)^2=r^2) : r.natDegree=0 := by
  rw [eq_C_of_natDegree_eq_zero hx,eq_C_of_natDegree_eq_zero hy] at h
  have hh := congrArg natDegree h
  simp only [← map_sub,← map_pow,← map_add,natDegree_C,natDegree_pow] at hh
  omega

def px (r : Fin 3 → ℝ[X]) : ℝ[X] := C (1/2 : ℝ)*((r 0)^2-(r 1)^2+1)
def py (c d : ℝ) (r : Fin 3 → ℝ[X]) : ℝ[X] :=
  C (1/(2*d))*((r 0)^2-(r 2)^2+C (c^2+d^2)-C (2*c)*px r)
def residual (c d : ℝ) (r : Fin 3 → ℝ[X]) : ℝ[X] :=
  (px r)^2+(py c d r)^2-(r 0)^2

lemma reconstruct_first (r : Fin 3 → ℝ[X]) :
    C (2 : ℝ)*px r=(r 0)^2-(r 1)^2+1 := by
  unfold px
  rw [← mul_assoc,← map_mul]
  norm_num

lemma reconstruct_second (c d : ℝ) (hd : d≠0) (r : Fin 3 → ℝ[X]) :
    C (2*d)*py c d r=(r 0)^2-(r 2)^2+C (c^2+d^2)-C (2*c)*px r := by
  unfold py
  rw [← mul_assoc,← map_mul]
  have hh : (2*d)*(1/(2*d))=1 := by field_simp
  rw [hh,map_one,one_mul]

lemma residual_ne_zero (c d : ℝ) (hd : d≠0) (r : Fin 3 → ℝ[X])
    (j : Fin 3) (hj : r j=X) : residual c d r≠0 := by
  intro h
  have h0 : (px r)^2+(py c d r)^2=(r 0)^2 := sub_eq_zero.mp h
  have h1 : (px r-1)^2+(py c d r)^2=(r 1)^2 := by
    have he := reconstruct_first r
    norm_num only [map_ofNat] at he
    linear_combination h0-he
  have h2 : (px r-C c)^2+(py c d r-C d)^2=(r 2)^2 := by
    have he := reconstruct_second c d hd r
    simp only [map_add,map_pow,map_mul,map_ofNat] at he
    linear_combination h0-he
  obtain ⟨hx,hy⟩ := three_anchor_constancy (px r) (py c d r) c d hd r h0 h1 h2
  have hc : ∀ i : Fin 3, (r i).natDegree=0 := by
    intro i
    fin_cases i
    · apply radius_constant (a := 0) (b := 0) hx hy
      simpa using h0
    · apply radius_constant (a := 1) (b := 0) hx hy
      simpa using h1
    · exact radius_constant hx hy h2
  have hh := hc j
  rw [hj,natDegree_X] at hh
  omega

lemma residual_degree_le_four (c d : ℝ) (r : Fin 3 → ℝ[X])
    (hr : ∀ i, (r i).natDegree≤1) : (residual c d r).natDegree≤4 := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  unfold residual py px
  compute_degree!
  omega

def RealizesTriple (c d : ℝ) (p : ℝ²) (v : Fin 3 → ℝ) : Prop :=
  (p 0)^2+(p 1)^2=(v 0)^2 ∧
  (p 0-1)^2+(p 1)^2=(v 1)^2 ∧
  (p 0-c)^2+(p 1-d)^2=(v 2)^2

def point (c d : ℝ) (r : Fin 3 → ℝ[X]) (t : ℝ) : ℝ² :=
  !₂[(px r).eval t,(py c d r).eval t]

lemma coordinates_of_realizes (c d : ℝ) (hd : d≠0) (r : Fin 3 → ℝ[X])
    (t : ℝ) (p : ℝ²) (h : RealizesTriple c d p (fun i => (r i).eval t)) :
    p=point c d r t := by
  obtain ⟨h0,h1,h2⟩ := h
  have he0 := congrArg (Polynomial.eval t) (reconstruct_first r)
  have he1 := congrArg (Polynomial.eval t) (reconstruct_second c d hd r)
  simp only [eval_mul,eval_C,eval_sub,eval_add,eval_one,eval_pow] at he0 he1
  have hx : p 0=(px r).eval t := by nlinarith
  have hy : p 1=(py c d r).eval t := by
    apply (mul_left_cancel₀ hd)
    linear_combination (h0-h2-he1)/2-c*hx
  ext i
  fin_cases i
  · exact hx
  · exact hy

lemma residual_root_of_realizes (c d : ℝ) (hd : d≠0) (r : Fin 3 → ℝ[X])
    (t : ℝ) (p : ℝ²) (h : RealizesTriple c d p (fun i => (r i).eval t)) :
    (residual c d r).IsRoot t := by
  have hp := coordinates_of_realizes c d hd r t p h
  have hh := h.1
  rw [hp] at hh
  change ((px r).eval t)^2+((py c d r).eval t)^2=((r 0).eval t)^2 at hh
  simpa only [Polynomial.IsRoot, residual,eval_sub,eval_add,eval_pow,sub_eq_zero] using hh

def candidates (c d : ℝ) (r : Fin 3 → ℝ[X]) : Finset ℝ² :=
  (residual c d r).roots.toFinset.image (point c d r)

lemma mem_candidates (c d : ℝ) (hd : d≠0) (r : Fin 3 → ℝ[X])
    (j : Fin 3) (hj : r j=X) (t : ℝ) (p : ℝ²)
    (h : RealizesTriple c d p (fun i => (r i).eval t)) : p∈candidates c d r := by
  apply Finset.mem_image.mpr
  refine ⟨t,?_,(coordinates_of_realizes c d hd r t p h).symm⟩
  rw [Multiset.mem_toFinset,mem_roots (residual_ne_zero c d hd r j hj)]
  exact residual_root_of_realizes c d hd r t p h

lemma candidates_card_le_four (c d : ℝ) (r : Fin 3 → ℝ[X])
    (hr : ∀ i, (r i).natDegree≤1) : (candidates c d r).card≤4 := by
  calc
    _ ≤ (residual c d r).roots.toFinset.card := Finset.card_image_le
    _ ≤ (residual c d r).roots.card := Multiset.toFinset_card_le _
    _ ≤ (residual c d r).natDegree := card_roots' _
    _ ≤ 4 := residual_degree_le_four c d r hr

/-- This cardinality bound concerns one affine line in signed-distance space,
not the union of arbitrary lines or arbitrary rational-distance sets. -/
theorem affine_distance_fiber_card_le_four (c d : ℝ) (hd : d≠0)
    (r : Fin 3 → ℝ[X]) (hr : ∀ i, (r i).natDegree≤1)
    (j : Fin 3) (hj : r j=X) (S : Finset ℝ²)
    (hS : ∀ p∈S, ∃ t, RealizesTriple c d p (fun i => (r i).eval t)) : S.card≤4 := by
  apply (Finset.card_le_card (t := candidates c d r) ?_).trans
    (candidates_card_le_four c d r hr)
  intro p hp
  obtain ⟨t,ht⟩ := hS p hp
  exact mem_candidates c d hd r j hj t p ht

#print axioms three_anchor_constancy
#print axioms residual_ne_zero
#print axioms residual_degree_le_four
#print axioms coordinates_of_realizes
#print axioms affine_distance_fiber_card_le_four
end
end Erdos213.AffineTrilateration
