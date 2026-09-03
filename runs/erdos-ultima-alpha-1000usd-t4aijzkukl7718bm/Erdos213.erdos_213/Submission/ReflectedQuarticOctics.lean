import Submission.ReflectedPolynomialMotion

/-! Two exact squarefree octic obstructions arising from the degree-drop
branch of a reflected quartic motion. These are not point-set size bounds. -/
namespace Erdos213.ReflectedQuarticOctics
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000

lemma nonsquare_of_bezout_constant (p A B : ℝ[X]) (c : ℝ) (hc : c≠0)
    (hp : 0<p.natDegree) (hbez : A*p+B*derivative p=C c) : ¬IsSquare p := by
  rintro ⟨q,hq⟩
  have hqp : q∣p := by rw [hq]; exact dvd_mul_right q q
  have hqd : q∣derivative p := by
    rw [hq,derivative_mul]
    exact dvd_add (dvd_mul_left q _) (dvd_mul_right q _)
  have hqc : q∣C c := by
    rw [←hbez]
    exact dvd_add (dvd_mul_of_dvd_right hqp A) (dvd_mul_of_dvd_right hqd B)
  have hu : IsUnit q := isUnit_of_dvd_unit hqc (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))
  have hpu : IsUnit p := by rw [hq]; exact hu.mul hu
  exact not_isUnit_of_natDegree_pos p hp hpu

def firstOctic : ℝ[X] := 16*X^8-24*X^6+9*X^4-X^2+1

def secondOctic : ℝ[X] := 28672*X^8-20480*X^6+5248*X^4-1088*X^2+343

lemma firstOctic_nonsquare : ¬IsSquare firstOctic := by
  apply nonsquare_of_bezout_constant firstOctic
    (6528*X^6-3312*X^4+420*X^2+446)
    (-816*X^7+720*X^5-93*X^3-13*X) 446 (by norm_num)
  · have hd : firstOctic.natDegree=8 := by dsimp [firstOctic]; compute_degree!
    omega
  · simp [firstOctic,derivative_add,derivative_sub,derivative_mul,derivative_pow]
    simp only [map_ofNat]
    ring

lemma secondOctic_nonsquare : ¬IsSquare secondOctic := by
  apply nonsquare_of_bezout_constant secondOctic
    (143216640*X^6-46004736*X^4+17431936*X^2+5668864)
    (-17902080*X^7+8947392*X^5-3131672*X^3-86659*X) 1944420352 (by norm_num)
  · have hd : secondOctic.natDegree=8 := by dsimp [secondOctic]; compute_degree!
    omega
  · simp [secondOctic,derivative_add,derivative_sub,derivative_mul,derivative_pow]
    simp only [map_ofNat]
    ring

#print axioms nonsquare_of_bezout_constant
#print axioms firstOctic_nonsquare
#print axioms secondOctic_nonsquare
end
end Erdos213.ReflectedQuarticOctics
