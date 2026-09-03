import Submission.CubicIntegralCertificates

/-! A quadratic inverse to the cubic parametrization on the ordered positive
chart. It yields parameter height bounds independent of the raw gcd factor.
No positive-density construction is asserted. -/

namespace Erdos1206.CubicBaseLocus

variable {R : Type*} [CommRing R]

def inverseA (x y z w : R) : R :=
  2*w*y-w*z-x*y+2*x*z-2*y^2+2*y*z-2*z^2

def inverseB (x y z w : R) : R :=
  2*(w^2-w*x+x^2-y^2+y*z-z^2)

def inverseT (x y z w : R) : R := 3*(w*z-x*y)

lemma inverse_cross_identities (a b t : R) :
    t*inverseA (A a b t) (B a b t) (C a b t) (D a b t) =
      a*inverseT (A a b t) (B a b t) (C a b t) (D a b t) ∧
    t*inverseB (A a b t) (B a b t) (C a b t) (D a b t) =
      b*inverseT (A a b t) (B a b t) (C a b t) (D a b t) := by
  dsimp [A,B,C,D,Q,inverseA,inverseB,inverseT]
  constructor <;> ring

lemma inverse_homogeneous (x y z w k : R) :
    inverseA (k*x) (k*y) (k*z) (k*w) = k^2*inverseA x y z w ∧
    inverseB (k*x) (k*y) (k*z) (k*w) = k^2*inverseB x y z w ∧
    inverseT (k*x) (k*y) (k*z) (k*w) = k^2*inverseT x y z w := by
  dsimp [inverseA,inverseB,inverseT]
  constructor; ring
  constructor <;> ring

lemma primitive_collinear_integer {a b t u v q : ℤ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (ht : 0 < t) (hq : 0 < q) (hu : t*u=a*q) (hv : t*v=b*q) :
    ∃ m : ℤ, 0 < m ∧ u=m*a ∧ v=m*b ∧ q=m*t := by
  let d := Int.gcd a b
  let α : ℤ := Int.gcdA a b * Int.gcdA (d : ℤ) t
  let β : ℤ := Int.gcdB a b * Int.gcdA (d : ℤ) t
  let γ : ℤ := Int.gcdB (d : ℤ) t
  have hdt : Int.gcd (d : ℤ) t = 1 := by simpa [Int.gcd_eq_natAbs,d] using hprim
  have hlin : a*α+b*β+t*γ=1 := by
    have hd := Int.gcd_eq_gcd_ab a b
    have hh := Int.gcd_eq_gcd_ab (d : ℤ) t
    rw [hdt] at hh
    calc
      _ = (d : ℤ)*Int.gcdA (d : ℤ) t+t*Int.gcdB (d : ℤ) t := by
        dsimp only [α,β,γ,d]
        rw [hd]
        ring
      _ = 1 := by simpa using hh.symm
  let m : ℤ := u*α+v*β+q*γ
  have htm : t*m=q := by
    calc
      _ = (t*u)*α+(t*v)*β+q*t*γ := by dsimp [m]; ring
      _ = q*(a*α+b*β+t*γ) := by rw [hu,hv]; ring
      _ = q := by rw [hlin,mul_one]
  have hm : 0 < m := by nlinarith
  refine ⟨m,hm,?_,?_,by linarith⟩
  · apply mul_left_cancel₀ ht.ne'
    nlinarith only [hu,congrArg (fun s : ℤ => a*s) htm]
  · apply mul_left_cancel₀ ht.ne'
    nlinarith only [hv,congrArg (fun s : ℤ => b*s) htm]

lemma inverseT_pos {x y z w : ℕ} (hxy : x < y) (hyz : y ≤ z) (hzw : z < w) :
    0 < inverseT (x : ℤ) y z w := by
  have hx : (0 : ℤ) ≤ x := by positivity
  have hz : (0 : ℤ) < z := by exact_mod_cast (show 0 < z by omega)
  have hwx : (0 : ℤ) < (w : ℤ)-x := sub_pos.mpr (by exact_mod_cast (show x < w by omega))
  have hzy : (0 : ℤ) ≤ (z : ℤ)-y := sub_nonneg.mpr (by exact_mod_cast hyz)
  have h₁ := mul_pos hwx hz
  have h₂ := mul_nonneg hx hzy
  dsimp [inverseT]
  nlinarith

/-- The primitive parameter vector divides its quadratic inverse vector by a
positive integer, even when the two middle roots coincide. -/
theorem certificate_inverse_integral {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hxy : x < y) (hyz : y ≤ z) (hzw : z < w)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    ∃ m : ℤ, 0 < m ∧ inverseA (x : ℤ) y z w=m*a ∧
      inverseB (x : ℤ) y z w=m*b ∧ inverseT (x : ℤ) y z w=m*t := by
  obtain ⟨hu,hv⟩ := inverse_cross_identities a b t
  obtain ⟨hiA,hiB,hiT⟩ := inverse_homogeneous (x : ℤ) y z w g
  rw [hA,hB,hC,hD,hiA,hiT] at hu
  rw [hA,hB,hC,hD,hiB,hiT] at hv
  have hgg : g^2 ≠ 0 := pow_ne_zero _ hg.ne'
  have hu' : t*inverseA (x : ℤ) y z w=a*inverseT (x : ℤ) y z w := by
    apply mul_left_cancel₀ hgg
    nlinarith only [hu]
  have hv' : t*inverseB (x : ℤ) y z w=b*inverseT (x : ℤ) y z w := by
    apply mul_left_cancel₀ hgg
    nlinarith only [hv]
  exact primitive_collinear_integer hprim ht (inverseT_pos hxy hyz hzw) hu' hv'

#print axioms certificate_inverse_integral


lemma inverse_bounds {x y z w H : ℤ}
    (hx : x ∈ Set.Icc 0 H) (hy : y ∈ Set.Icc 0 H)
    (hz : z ∈ Set.Icc 0 H) (hw : w ∈ Set.Icc 0 H) :
    |inverseA x y z w| ≤ 6*H^2 ∧ |inverseB x y z w| ≤ 6*H^2 ∧
      |inverseT x y z w| ≤ 3*H^2 := by
  have hH : 0 ≤ H := hx.1.trans hx.2
  have hprod (u v : ℤ) (hu : u ∈ Set.Icc 0 H) (hv : v ∈ Set.Icc 0 H) :
      0 ≤ u*v ∧ u*v ≤ H^2 := by
    exact ⟨mul_nonneg hu.1 hv.1,by nlinarith [mul_le_mul hu.2 hv.2 hv.1 hH]⟩
  have hxx := hprod x x hx hx
  have hyy := hprod y y hy hy
  have hzz := hprod z z hz hz
  have hww := hprod w w hw hw
  have hxy := hprod x y hx hy
  have hxz := hprod x z hx hz
  have hyz := hprod y z hy hz
  have hwx := hprod w x hw hx
  have hwy := hprod w y hw hy
  have hwz := hprod w z hw hz
  dsimp [inverseA,inverseB,inverseT]
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith
  · apply abs_le.mpr
    constructor <;> nlinarith

/-- Uniform quadratic height bounds for primitive parameters in the positive
ordered chart. Unlike the raw-form estimate, these bounds do not contain g. -/
theorem certificate_parameter_height {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hxy : x < y) (hyz : y ≤ z) (hzw : z < w)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    a.natAbs ≤ 6*w^2 ∧ b.natAbs ≤ 6*w^2 ∧ t.natAbs ≤ 3*w^2 := by
  obtain ⟨m,hm,hu,hv,hq⟩ := certificate_inverse_integral ht hg hprim hxy hyz hzw hA hB hC hD
  obtain ⟨hIA,hIB,hIT⟩ := inverse_bounds (H := (w : ℤ))
    (show (x : ℤ) ∈ Set.Icc 0 (w : ℤ) from ⟨by positivity,by exact_mod_cast (show x ≤ w by omega)⟩)
    (show (y : ℤ) ∈ Set.Icc 0 (w : ℤ) from ⟨by positivity,by exact_mod_cast (show y ≤ w by omega)⟩)
    (show (z : ℤ) ∈ Set.Icc 0 (w : ℤ) from ⟨by positivity,by exact_mod_cast hzw.le⟩)
    (show (w : ℤ) ∈ Set.Icc 0 (w : ℤ) from ⟨by positivity,le_rfl⟩)
  have hscale (v : ℤ) : |v| ≤ |m*v| := by
    rw [abs_mul,abs_of_pos hm]
    have hm1 : 1 ≤ m := by omega
    nlinarith [abs_nonneg v]
  have ha' : (a.natAbs : ℤ) ≤ 6*(w : ℤ)^2 := by
    rw [Int.natCast_natAbs]
    exact (hscale a).trans (hu ▸ hIA)
  have hb' : (b.natAbs : ℤ) ≤ 6*(w : ℤ)^2 := by
    rw [Int.natCast_natAbs]
    exact (hscale b).trans (hv ▸ hIB)
  have ht' : (t.natAbs : ℤ) ≤ 3*(w : ℤ)^2 := by
    rw [Int.natCast_natAbs]
    exact (hscale t).trans (hq ▸ hIT)
  exact ⟨by exact_mod_cast ha',by exact_mod_cast hb',by exact_mod_cast ht'⟩

/-- The common positive divisor of the quadratic inverse coordinates. -/
def inverseGcd (x y z w : ℤ) : ℕ :=
  Nat.gcd (Int.gcd (inverseA x y z w) (inverseB x y z w)) (inverseT x y z w).natAbs

/-- The primitive parameter triple is recovered by exact division of the
quadratic inverse coordinates; in particular it is unique. -/
theorem certificate_parameters_recover {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hxy : x < y) (hyz : y ≤ z) (hzw : z < w)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    a = inverseA (x : ℤ) y z w / inverseGcd (x : ℤ) y z w ∧
    b = inverseB (x : ℤ) y z w / inverseGcd (x : ℤ) y z w ∧
    t = inverseT (x : ℤ) y z w / inverseGcd (x : ℤ) y z w := by
  obtain ⟨m,hm,hu,hv,hq⟩ := certificate_inverse_integral ht hg hprim hxy hyz hzw hA hB hC hD
  have hG : inverseGcd (x : ℤ) y z w = m.natAbs := by
    rw [inverseGcd,hu,hv,hq,Int.gcd_mul_left,Int.natAbs_mul,Nat.gcd_mul_left,hprim,mul_one]
  simp [hG,hu,hv,hq,abs_of_pos hm,hm.ne']

#print axioms certificate_parameter_height
#print axioms certificate_parameters_recover

end Erdos1206.CubicBaseLocus
