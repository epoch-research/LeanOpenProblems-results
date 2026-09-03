import Submission.PonceletOctagon

/-! Necessary arithmetic conditions for the intermediate aspect B=q^2.
This file neither constructs nor rules out an eight-point integral set. -/
namespace Erdos213.PonceletOctagon

lemma intermediate_radius (q s c : ℚ) (hc : c^2+s^2=1) :
    radiusSq (q^2) s c=den q s := by
  dsimp [radiusSq,den]
  linear_combination hc

lemma intermediate_quarter_radius (q s c d : ℚ) :
    radiusSq (q^2) (c/d) (-q^2*s/d) = (q/d)^2*radiusSq (q^2) s c := by
  dsimp [radiusSq]
  ring

lemma intermediate_dn (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) :
    d^2+q^2=r^2*radiusSq (q^2) s c := by
  dsimp [radiusSq]
  linear_combination hd-(1+q^2)*hc-(c^2+q^2*s^2)*hr

lemma intermediate_skip_two (q r s c d : ℚ) (hr : r^2=1+q^2)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1) (hd0 : d ≠ 0) :
    (c+q^2*s/d)^2+q^2*(s-c/d)^2=(r*den q s/d)^2 := by
  have h1 := intermediate_dn q r s c d hr hc hd
  rw [intermediate_radius q s c hc] at h1
  have h2 : c^2+q^2*s^2=den q s := intermediate_radius q s c hc
  calc
    _ = (c^2+q^2*s^2)*(d^2+q^2)/d^2 := by field_simp; ring
    _ = (den q s)*(r^2*den q s)/d^2 := by rw [h1,h2]
    _ = _ := by ring

lemma intermediate_radius_product (q r s c d : ℚ)
    (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (hr0 : r ≠ 0) (hD : den q s ≠ 0) :
    den q s * radiusSq (q^2) (stepS q r s c d) (stepC q r s c d) =
      2*q*d*stepD q s c d/r^2 := by
  dsimp [radiusSq,stepC,stepS,stepD]
  field_simp
  linear_combination q^2*((1+d^2)*hc-hd)

/-- If the first radius is rational, one obtains an Euler-brick face system
with an additional square condition involving q^4. This does not assert a
rational space diagonal or a perfect cuboid. -/
lemma intermediate_euler_faces (q r s c d e : ℚ) (hs : s ≠ 0)
    (hr : r^2=1+q^2) (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (he : radiusSq (q^2) s c=e^2) :
    (c/s)^2+1=(1/s)^2 ∧
    (c/s)^2+q^2=(e/s)^2 ∧
    (c/s)^2+q^4=(d/s)^2 ∧ 1+q^2=r^2 := by
  dsimp [radiusSq] at he
  refine ⟨?_,?_,?_,hr.symm⟩
  · field_simp
    linear_combination hc
  · field_simp
    linear_combination he
  · field_simp
    linear_combination hc-hd

lemma intermediate_radii_necessary (q r s c d e f : ℚ) (hq : q ≠ 0)
    (hr : r^2=1+q^2) (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (he : radiusSq (q^2) s c=e^2)
    (hf : radiusSq (q^2) (stepS q r s c d) (stepC q r s c d)=f^2) :
    d^2+q^2=r^2*e^2 ∧ (stepD q s c d)^2+q^2=r^2*f^2 ∧
      r^2*e^2*f^2=2*q*d*stepD q s c d := by
  obtain ⟨hr0,_,hD,_⟩ := nonzero_data q r s c d hq hr hc hd
  have h0 := intermediate_dn q r s c d hr hc hd
  have h1 := intermediate_dn q r (stepS q r s c d) (stepC q r s c d)
    (stepD q s c d) hr (step_circle q r s c d hr hc hd hr0 hD)
    (step_dn q r s c d hr hc hd hr0 hD)
  have h2 := intermediate_radius_product q r s c d hc hd hr0 hD
  rw [he] at h0
  rw [hf] at h1 h2
  have hden : den q s=e^2 := (intermediate_radius q s c hc).symm.trans he
  rw [hden] at h2
  refine ⟨h0,h1,?_⟩
  field_simp at h2
  linear_combination h2

lemma intermediate_biquartic (q r s c d e f : ℚ) (hq : q ≠ 0)
    (hr : r^2=1+q^2) (hc : c^2+s^2=1) (hd : d^2+(1-q^4)*s^2=1)
    (he : radiusSq (q^2) s c=e^2)
    (hf : radiusSq (q^2) (stepS q r s c d) (stepC q r s c d)=f^2) :
    r^4*e^4*f^4-4*q^2*(r^2*e^2-q^2)*(r^2*f^2-q^2)=0 := by
  obtain ⟨h0,h1,h2⟩ := intermediate_radii_necessary q r s c d e f hq hr hc hd he hf
  linear_combination (r^2*e^2*f^2+2*q*d*stepD q s c d)*h2 +
    4*q^2*(r^2*f^2-q^2)*h0+4*q^2*d^2*h1

#print axioms intermediate_skip_two
#print axioms intermediate_radius_product
#print axioms intermediate_euler_faces
#print axioms intermediate_radii_necessary
#print axioms intermediate_biquartic
end Erdos213.PonceletOctagon
