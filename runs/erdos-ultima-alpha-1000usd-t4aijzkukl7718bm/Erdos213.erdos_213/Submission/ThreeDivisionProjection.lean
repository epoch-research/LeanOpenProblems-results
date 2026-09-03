import Submission.EndpointSwitching
import Submission.RationalEisenstein
import Submission.EquilateralMidpointProfile

/-! A complete obstruction for the eight signed y-coordinates of the explicit
full-three-torsion model, even after arbitrary positive real endpoint
reweighting. This restricted result does not settle Erdos 213. -/
namespace Erdos213.ThreeDivisionProjection
open RationalEisenstein EndpointSwitching
open scoped QuadraticAlgebra
set_option maxHeartbeats 3000000

def points (t : G) : Fin 8 → G :=
  ![4*t^3 - 4,
    -4*t^3 + 4,
    (-2*rr + 6)*t^2 + (-2*rr - 6)*t + 4*rr,
    (2*rr - 6)*t^2 + (2*rr + 6)*t - 4*rr,
    (2*rr + 6)*t^2 + (2*rr - 6)*t - 4*rr,
    (-2*rr - 6)*t^2 + (-2*rr + 6)*t + 4*rr,
    4*rr*t^2 + 4*rr*t + 4*rr,
    -4*rr*t^2 - 4*rr*t - 4*rr]

def atom (t : G) : Fin 7 → G :=
  ![t - 1, 2*t - rr + 1, 2*t + rr + 1, t + rr - 1, t + 2, t - rr - 1, t]

def A (t : G) (i : Fin 7) : ℚ := norm (atom t i)
def N (t : G) (i j : Fin 8) : ℚ := norm (points t i-points t j)

private lemma points_0 (t : G) : points t 0 = 4*t^3 - 4 := rfl
private lemma points_1 (t : G) : points t 1 = -4*t^3 + 4 := rfl
private lemma points_2 (t : G) : points t 2 = (-2*rr + 6)*t^2 + (-2*rr - 6)*t + 4*rr := rfl
private lemma points_3 (t : G) : points t 3 = (2*rr - 6)*t^2 + (2*rr + 6)*t - 4*rr := rfl
private lemma points_4 (t : G) : points t 4 = (2*rr + 6)*t^2 + (2*rr - 6)*t - 4*rr := rfl
private lemma points_5 (t : G) : points t 5 = (-2*rr - 6)*t^2 + (-2*rr + 6)*t + 4*rr := rfl
private lemma points_6 (t : G) : points t 6 = 4*rr*t^2 + 4*rr*t + 4*rr := rfl
private lemma points_7 (t : G) : points t 7 = -4*rr*t^2 - 4*rr*t - 4*rr := rfl
private lemma atom_0 (t : G) : atom t 0 = t - 1 := rfl
private lemma atom_1 (t : G) : atom t 1 = 2*t - rr + 1 := rfl
private lemma atom_2 (t : G) : atom t 2 = 2*t + rr + 1 := rfl
private lemma atom_3 (t : G) : atom t 3 = t + rr - 1 := rfl
private lemma atom_4 (t : G) : atom t 4 = t + 2 := rfl
private lemma atom_5 (t : G) : atom t 5 = t - rr - 1 := rfl
private lemma atom_6 (t : G) : atom t 6 = t := rfl

lemma N_sym (t : G) (i j : Fin 8) : N t i j = N t j i := by
  simp only [N,norm_components,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub]
  ring

lemma N_ne_zero {t : G} (hp : Function.Injective (points t)) {i j : Fin 8} (hij : i ≠ j) :
    N t i j ≠ 0 := norm_ne_zero (sub_ne_zero.mpr (hp.ne hij))

private lemma rr_pow3 : rr^3 = -3*rr := by rw [pow_succ,rr_sq]
private lemma rr_pow4 : rr^4 = 9 := by rw [show (4 : ℕ)=2*2 by rfl,pow_mul,rr_sq]; ring

private lemma edge_0_1 (t : G) : N t 0 1 = 4*A t 0*A t 1*A t 2 := by
  have he : points t 0-points t 1 = ((2)+(0)*rr)*(atom t 0)*(atom t 1)*(atom t 2) := by
    simp only [points_0,points_1,atom_0,atom_1,atom_2]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 1) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_0_2 (t : G) : N t 0 2 = 4*A t 0*A t 1*A t 3 := by
  have he : points t 0-points t 2 = ((2)+(0)*rr)*(atom t 0)*(atom t 1)*(atom t 3) := by
    simp only [points_0,points_2,atom_0,atom_1,atom_3]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 2) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_0_3 (t : G) : N t 0 3 = 4*A t 0*A t 1*A t 4 := by
  have he : points t 0-points t 3 = ((2)+(0)*rr)*(atom t 0)*(atom t 1)*(atom t 4) := by
    simp only [points_0,points_3,atom_0,atom_1,atom_4]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 3) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_0_4 (t : G) : N t 0 4 = 4*A t 0*A t 2*A t 5 := by
  have he : points t 0-points t 4 = ((2)+(0)*rr)*(atom t 0)*(atom t 2)*(atom t 5) := by
    simp only [points_0,points_4,atom_0,atom_2,atom_5]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 4) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_0_5 (t : G) : N t 0 5 = 4*A t 0*A t 2*A t 4 := by
  have he : points t 0-points t 5 = ((2)+(0)*rr)*(atom t 0)*(atom t 2)*(atom t 4) := by
    simp only [points_0,points_5,atom_0,atom_2,atom_4]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 5) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_0_7 (t : G) : N t 0 7 = 1*A t 1*A t 2*A t 3 := by
  have he : points t 0-points t 7 = ((1)+(0)*rr)*(atom t 1)*(atom t 2)*(atom t 3) := by
    simp only [points_0,points_7,atom_1,atom_2,atom_3]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((1)+(0)*rr) = 1 := by norm_num [norm_components,rr]
  change norm (points t 0-points t 7) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_1_2 (t : G) : N t 1 2 = 4*A t 0*A t 1*A t 4 := by
  have he : points t 1-points t 2 = ((-2)+(0)*rr)*(atom t 0)*(atom t 1)*(atom t 4) := by
    simp only [points_1,points_2,atom_0,atom_1,atom_4]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((-2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 1-points t 2) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_1_4 (t : G) : N t 1 4 = 4*A t 0*A t 2*A t 4 := by
  have he : points t 1-points t 4 = ((-2)+(0)*rr)*(atom t 0)*(atom t 2)*(atom t 4) := by
    simp only [points_1,points_4,atom_0,atom_2,atom_4]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((-2)+(0)*rr) = 4 := by norm_num [norm_components,rr]
  change norm (points t 1-points t 4) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_1_6 (t : G) : N t 1 6 = 1*A t 1*A t 2*A t 3 := by
  have he : points t 1-points t 6 = ((-1)+(0)*rr)*(atom t 1)*(atom t 2)*(atom t 3) := by
    simp only [points_1,points_6,atom_1,atom_2,atom_3]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((-1)+(0)*rr) = 1 := by norm_num [norm_components,rr]
  change norm (points t 1-points t 6) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_2_3 (t : G) : N t 2 3 = 48*A t 0*A t 1 := by
  have he : points t 2-points t 3 = ((6)+(-2)*rr)*(atom t 0)*(atom t 1) := by
    simp only [points_2,points_3,atom_0,atom_1]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((6)+(-2)*rr) = 48 := by norm_num [norm_components,rr]
  change norm (points t 2-points t 3) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_2_4 (t : G) : N t 2 4 = 48*A t 0*A t 4 := by
  have he : points t 2-points t 4 = ((0)+(-4)*rr)*(atom t 0)*(atom t 4) := by
    simp only [points_2,points_4,atom_0,atom_4]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((0)+(-4)*rr) = 48 := by norm_num [norm_components,rr]
  change norm (points t 2-points t 4) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_2_5 (t : G) : N t 2 5 = 144*A t 0*A t 6 := by
  have he : points t 2-points t 5 = ((12)+(0)*rr)*(atom t 0)*(atom t 6) := by
    simp only [points_2,points_5,atom_0,atom_6]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((12)+(0)*rr) = 144 := by norm_num [norm_components,rr]
  change norm (points t 2-points t 5) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_2_7 (t : G) : N t 2 7 = 12*A t 1*A t 3 := by
  have he : points t 2-points t 7 = ((3)+(1)*rr)*(atom t 1)*(atom t 3) := by
    simp only [points_2,points_7,atom_1,atom_3]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((3)+(1)*rr) = 12 := by norm_num [norm_components,rr]
  change norm (points t 2-points t 7) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_4_5 (t : G) : N t 4 5 = 48*A t 0*A t 2 := by
  have he : points t 4-points t 5 = ((6)+(2)*rr)*(atom t 0)*(atom t 2) := by
    simp only [points_4,points_5,atom_0,atom_2]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((6)+(2)*rr) = 48 := by norm_num [norm_components,rr]
  change norm (points t 4-points t 5) = _
  rw [he]
  simp only [map_mul,hc,A]

private lemma edge_6_7 (t : G) : N t 6 7 = 12*A t 1*A t 2 := by
  have he : points t 6-points t 7 = ((0)+(2)*rr)*(atom t 1)*(atom t 2) := by
    simp only [points_6,points_7,atom_1,atom_2]
    ring_nf <;> simp only [rr_sq,rr_pow3,rr_pow4] <;> ring
  have hc : norm ((0)+(2)*rr) = 12 := by norm_num [norm_components,rr]
  change norm (points t 6-points t 7) = _
  rw [he]
  simp only [map_mul,hc,A]

lemma A_ne_zero {t : G} (hp : Function.Injective (points t)) (i : Fin 7) : A t i ≠ 0 := by
  intro hz
  fin_cases i
  · change A t 0 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=1) (by decide)
    rw [edge_0_1] at h
    simp [hz] at h
  · change A t 1 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=1) (by decide)
    rw [edge_0_1] at h
    simp [hz] at h
  · change A t 2 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=1) (by decide)
    rw [edge_0_1] at h
    simp [hz] at h
  · change A t 3 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=2) (by decide)
    rw [edge_0_2] at h
    simp [hz] at h
  · change A t 4 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=3) (by decide)
    rw [edge_0_3] at h
    simp [hz] at h
  · change A t 5 = 0 at hz
    have h := N_ne_zero hp (i:=0) (j:=4) (by decide)
    rw [edge_0_4] at h
    simp [hz] at h
  · change A t 6 = 0 at hz
    have h := N_ne_zero hp (i:=2) (j:=5) (by decide)
    rw [edge_2_5] at h
    simp [hz] at h

/-- Each of the seven target norm classes is already detected by one
four-edge ratio. -/
theorem profile_of_weighted {t : G} (hp : Function.Injective (points t))
    (h : RealWeightedRational (N t)) :
    (∀ i : Fin 6, IsSquare (3*A t i.castSucc)) ∧ IsSquare (A t 6) := by
  have ha0 := A_ne_zero hp 0
  have ha1 := A_ne_zero hp 1
  have ha2 := A_ne_zero hp 2
  have ha3 := A_ne_zero hp 3
  have ha4 := A_ne_zero hp 4
  have ha5 := A_ne_zero hp 5
  have ha6 := A_ne_zero hp 6
  have h0 := four_edge_square (N t) h (a:=0) (b:=1) (c:=6) (d:=7)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he0 : N t 0 1*N t 6 7/(N t 1 6*N t 7 0) =
      (3*A t 0)*(4/A t 3)^2 := by
    rw [N_sym t 7 0,edge_0_1,edge_0_7,edge_1_6,edge_6_7]
    field_simp <;> norm_num
  rw [he0] at h0
  have ht0 : IsSquare (3*A t 0) := by
    convert h0.div (IsSquare.sq (4/A t 3)) using 1
    field_simp <;> norm_num
  have h1 := four_edge_square (N t) h (a:=0) (b:=1) (c:=4) (d:=5)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he1 : N t 0 1*N t 4 5/(N t 1 4*N t 5 0) =
      (3*A t 1)*(2/A t 4)^2 := by
    rw [N_sym t 5 0,edge_0_1,edge_0_5,edge_1_4,edge_4_5]
    field_simp <;> norm_num
  rw [he1] at h1
  have ht1 : IsSquare (3*A t 1) := by
    convert h1.div (IsSquare.sq (2/A t 4)) using 1
    field_simp <;> norm_num
  have h2 := four_edge_square (N t) h (a:=0) (b:=1) (c:=2) (d:=3)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he2 : N t 0 1*N t 2 3/(N t 1 2*N t 3 0) =
      (3*A t 2)*(2/A t 4)^2 := by
    rw [N_sym t 3 0,edge_0_1,edge_0_3,edge_1_2,edge_2_3]
    field_simp <;> norm_num
  rw [he2] at h2
  have ht2 : IsSquare (3*A t 2) := by
    convert h2.div (IsSquare.sq (2/A t 4)) using 1
    field_simp <;> norm_num
  have h3 := four_edge_square (N t) h (a:=0) (b:=1) (c:=4) (d:=2)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he3 : N t 0 1*N t 4 2/(N t 1 4*N t 2 0) =
      (3*A t 3)*(2/A t 3)^2 := by
    rw [N_sym t 4 2,N_sym t 2 0,edge_0_1,edge_0_2,edge_1_4,edge_2_4]
    field_simp <;> norm_num
  rw [he3] at h3
  have ht3 : IsSquare (3*A t 3) := by
    convert h3.div (IsSquare.sq (2/A t 3)) using 1
    field_simp <;> norm_num
  have h4 := four_edge_square (N t) h (a:=0) (b:=1) (c:=2) (d:=7)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he4 : N t 0 1*N t 2 7/(N t 1 2*N t 7 0) =
      (3*A t 4)*(2/A t 4)^2 := by
    rw [N_sym t 7 0,edge_0_1,edge_0_7,edge_1_2,edge_2_7]
    field_simp <;> norm_num
  rw [he4] at h4
  have ht4 : IsSquare (3*A t 4) := by
    convert h4.div (IsSquare.sq (2/A t 4)) using 1
    field_simp <;> norm_num
  have h5 := four_edge_square (N t) h (a:=0) (b:=1) (c:=2) (d:=4)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he5 : N t 0 1*N t 2 4/(N t 1 2*N t 4 0) =
      (3*A t 5)*(2/A t 5)^2 := by
    rw [N_sym t 4 0,edge_0_1,edge_0_4,edge_1_2,edge_2_4]
    field_simp <;> norm_num
  rw [he5] at h5
  have ht5 : IsSquare (3*A t 5) := by
    convert h5.div (IsSquare.sq (2/A t 5)) using 1
    field_simp <;> norm_num
  have h6 := four_edge_square (N t) h (a:=0) (b:=1) (c:=2) (d:=5)
    (by decide) (by decide) (by decide) (by decide)
    (N_ne_zero hp (by decide)) (N_ne_zero hp (by decide))
  have he6 : N t 0 1*N t 2 5/(N t 1 2*N t 5 0) =
      (A t 6)*(6/A t 4)^2 := by
    rw [N_sym t 5 0,edge_0_1,edge_0_5,edge_1_2,edge_2_5]
    field_simp <;> norm_num
  rw [he6] at h6
  have ht6 : IsSquare (A t 6) := by
    convert h6.div (IsSquare.sq (6/A t 4)) using 1
    field_simp <;> norm_num
  constructor
  · intro i
    fin_cases i
    · exact ht0
    · exact ht1
    · exact ht2
    · exact ht3
    · exact ht4
    · exact ht5
  · exact ht6

/-- All eight distinct projected points cannot acquire rational lengths
under arbitrary positive real endpoint factors. -/
theorem not_weighted (t : G) (hp : Function.Injective (points t)) :
    ¬ RealWeightedRational (N t) := by
  intro h
  obtain ⟨hroot,hcenter⟩ := profile_of_weighted hp h
  apply EquilateralMidpointProfile.no_rational_profile t.re t.im
  intro i
  fin_cases i
  · have hh := hcenter
    change IsSquare (A t 6) at hh
    have hh := hh.mul (IsSquare.sq (2 : ℚ))
    convert hh using 1
    change (2*t.re)^2+3*(2*t.im)^2 = (norm (t))*2^2
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 0
    change IsSquare (3*A t 0) at hh
    have hh := hh.mul (IsSquare.sq (2 : ℚ))
    convert hh using 1
    change 3*((2*t.re-2*1)^2+3*(2*t.im)^2) = (3*norm (t-1))*2^2
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 1
    change IsSquare (3*A t 1) at hh
    convert hh using 1
    change 3*((2*t.re+1)^2+3*(2*t.im-1)^2) = 3*norm (2*t-rr+1)
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 2
    change IsSquare (3*A t 2) at hh
    convert hh using 1
    change 3*((2*t.re+1)^2+3*(2*t.im+1)^2) = 3*norm (2*t+rr+1)
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 4
    change IsSquare (3*A t 4) at hh
    have hh := hh.mul (IsSquare.sq (2 : ℚ))
    convert hh using 1
    change 3*((2*t.re+4*1)^2+3*(2*t.im)^2) = (3*norm (t+2))*2^2
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 5
    change IsSquare (3*A t 5) at hh
    have hh := hh.mul (IsSquare.sq (2 : ℚ))
    convert hh using 1
    change 3*((2*t.re-2*1)^2+3*(2*t.im-2*1)^2) = (3*norm (t-rr-1))*2^2
    simp [norm_components,rr]
    <;> ring
  · have hh := hroot 3
    change IsSquare (3*A t 3) at hh
    have hh := hh.mul (IsSquare.sq (2 : ℚ))
    convert hh using 1
    change 3*((2*t.re-2*1)^2+3*(2*t.im+2*1)^2) = (3*norm (t+rr-1))*2^2
    simp [norm_components,rr]
    <;> ring

/-- Geometric version of the restricted obstruction. -/
theorem no_weighted_rational_lengths (t : G) (hp : Function.Injective (points t))
    (l : Fin 8 → ℝ) (hl : ∀ i, 0 < l i) :
    ¬ (∀ i j, i ≠ j → l i*l j*dist (toComplex (points t i)) (toComplex (points t j))
      ∈ Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  apply not_weighted t hp
  refine ⟨fun i => l i^2,fun i => sq_pos_of_pos (hl i),?_⟩
  intro i j hij
  obtain ⟨r,hr⟩ := h i j hij
  refine ⟨r,?_⟩
  rw [hr,mul_pow,mul_pow,dist_sq]
  rfl

/-- In particular no inversion with a finite image of every point, followed
by any positive real dilation, gives rational pairwise lengths. -/
theorem no_inverted_rational_lengths (t : G) (hp : Function.Injective (points t))
    (o : ℂ) (ho : ∀ i, toComplex (points t i) ≠ o) (a : ℝ) (ha : 0 < a) :
    ¬ (∀ i j, i ≠ j → a*
      dist (EuclideanGeometry.inversion o 1 (toComplex (points t i)))
        (EuclideanGeometry.inversion o 1 (toComplex (points t j)))
      ∈ Set.range ((↑) : ℚ → ℝ)) := by
  intro hd
  obtain ⟨l,hl,h⟩ := weights_of_inverted_lengths (fun i => toComplex (points t i)) o ho a ha hd
  exact no_weighted_rational_lengths t hp l hl h

#print axioms profile_of_weighted
#print axioms not_weighted
#print axioms no_weighted_rational_lengths
#print axioms no_inverted_rational_lengths
end Erdos213.ThreeDivisionProjection
