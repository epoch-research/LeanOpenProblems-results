import Submission.CentralCircumcenters

/-! A rational phase-squaring attempt to supply the missing central
circumcenter distances. The main theorem is an algebraic reduction to the
quartic w² = L⁴+4, not a settlement of the point-set conjecture. -/
namespace Erdos213.CentralPhaseDoubling
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- Real and imaginary parts of (u+i*v)²/(r+i). -/
def phaseReal (r u v : ℚ) : ℚ := (r*(u^2-v^2)+2*u*v)/(r^2+1)
def phaseImag (r u v : ℚ) : ℚ := (2*r*u*v-(u^2-v^2))/(r^2+1)

lemma phase_norm (r u v : ℚ) (h : u^2+v^2=r^2+1) :
    phaseReal r u v^2+phaseImag r u v^2=r^2+1 := by
  have hm : r^2+1≠0 := by positivity
  dsimp [phaseReal,phaseImag]
  field_simp
  linear_combination (r^2+1)*(u^2+v^2+r^2+1)*h

/-- Away from the unit-radius boundary, making this phase-square's real
part equal to the first required normalized length forces a square of
L⁴+4. Here a²=L²-1 is precisely the rational tilt condition, with a=1/k. -/
theorem phase_doubling_requires_quartic {r u v L a : ℚ}
    (hr : r≠0) (hr1 : r^2≠1) (ha : a≠0) (haL : a^2=L^2-1)
    (hsum : u^2+v^2=r^2+1)
    (hdiff : v^2-u^2=L*(r^2-1))
    (hmatch : phaseReal r u v^2=1+(2/L^2-1)*(r^2-1)) :
    (a*(L^2+2)*(r^2-1)/(2*r))^2=L^4+4 := by
  have hL : L≠0 := by intro hz; rw [hz] at haL; nlinarith [sq_nonneg a]
  have hL1 : L^2-1≠0 := by rw [← haL]; exact pow_ne_zero 2 ha
  have hM : r^2+1≠0 := by positivity
  have hH : r^2-1≠0 := sub_ne_zero.mpr hr1
  let H := r^2-1
  let M := r^2+1
  let N := r*(u^2-v^2)+2*u*v
  have he : L^2*N^2=(L^2+(2-L^2)*H)*M^2 := by
    dsimp [phaseReal] at hmatch
    field_simp at hmatch
    dsimp [N,H,M]
    nlinarith only [hmatch]
  have hN : N= -r*L*H+2*u*v := by
    dsimp [N,H]
    linear_combination -r*hdiff
  have hprod : 4*u^2*v^2=M^2-L^2*H^2 := by
    dsimp [M,H]
    linear_combination (u^2+v^2+r^2+1)*hsum-
      (v^2-u^2+L*(r^2-1))*hdiff
  have hlin : L^4*H^2+(L^2-2)*M^2=4*r*L^3*u*v := by
    have hh : H*(L^4*H^2+(L^2-2)*M^2-4*r*L^3*u*v)=0 := by
      rw [hN] at he
      dsimp [H,M] at he hprod ⊢
      linear_combination he-L^2*hprod
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hH)
  have hfactor : (L^2-1)*M^2*
      ((L^2-1)*(L^2+2)^2*H^2-4*(L^4+4)*r^2)=0 := by
    dsimp [H,M] at hlin hprod ⊢
    linear_combination
      (L^4*(r^2-1)^2+(L^2-2)*(r^2+1)^2+4*r*L^3*u*v)*hlin+
      4*r^2*L^6*hprod
  have hc : (L^2-1)*(L^2+2)^2*H^2=4*(L^4+4)*r^2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero hL1 (pow_ne_zero 2 hM)))
  change (a*(L^2+2)*H/(2*r))^2=L^4+4
  calc
    (a*(L^2+2)*H/(2*r))^2 = ((L^2-1)*(L^2+2)^2*H^2)/(4*r^2) := by
      rw [div_pow,mul_pow,mul_pow,haL]
      ring
    _ = L^4+4 := by rw [hc]; field_simp

/-- A transparent conditional exclusion, separating the checked algebra
from the additional Diophantine theorem about the quartic. -/
theorem phase_doubling_excluded_of_quartic_obstruction {r u v L a : ℚ}
    (hr : r≠0) (hr1 : r^2≠1) (ha : a≠0) (haL : a^2=L^2-1)
    (hsum : u^2+v^2=r^2+1) (hdiff : v^2-u^2=L*(r^2-1))
    (hquartic : ¬IsSquare (L^4+4)) :
    phaseReal r u v^2≠1+(2/L^2-1)*(r^2-1) := by
  intro hmatch
  apply hquartic
  refine ⟨a*(L^2+2)*(r^2-1)/(2*r),?_⟩
  have hh := phase_doubling_requires_quartic hr hr1 ha haL hsum hdiff hmatch
  nlinarith only [hh]

/-- The r²=1 exception is real: at the degenerate source boundary the
phase-square is a rational representation satisfying the normalized test. -/
lemma boundary_control (L : ℚ) :
    phaseReal 1 1 1^2=1+(2/L^2-1)*((1 : ℚ)^2-1) ∧
    phaseImag 1 1 1^2=1 := by
  norm_num [phaseReal,phaseImag]

#print axioms phase_norm
#print axioms phase_doubling_requires_quartic
#print axioms phase_doubling_excluded_of_quartic_obstruction
#print axioms boundary_control
end Erdos213.CentralPhaseDoubling
