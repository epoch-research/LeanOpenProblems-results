import Submission.CubicParametrizationAllCollisions
import Submission.CubicPrimePowerCancellation

/-! Integral certificates for primitive cubic collisions. The common factor of
the raw cubic forms is retained; no bound on its size is assumed. -/

namespace Erdos1206

lemma primitive_triple_normalization (a b t : ℤ) (ht : 0 < t) :
    ∃ a' b' t' : ℤ, ∃ g : ℕ, 0 < g ∧ 0 < t' ∧
      Nat.gcd (Int.gcd a' b') t'.natAbs = 1 ∧
      a = (g : ℤ)*a' ∧ b = (g : ℤ)*b' ∧ t = (g : ℤ)*t' := by
  let g := Nat.gcd (Int.gcd a b) t.natAbs
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr ht.ne')
  have hga : (g : ℤ) ∣ a :=
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_left a b)
  have hgb : (g : ℤ) ∣ b :=
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_right a b)
  have hgt : (g : ℤ) ∣ t := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  let a' := a / (g : ℤ)
  let b' := b / (g : ℤ)
  let t' := t / (g : ℤ)
  have ha : a = (g : ℤ)*a' := (Int.mul_ediv_cancel' hga).symm
  have hb : b = (g : ℤ)*b' := (Int.mul_ediv_cancel' hgb).symm
  have htt : t = (g : ℤ)*t' := (Int.mul_ediv_cancel' hgt).symm
  have he : g * 1 = g * Nat.gcd (Int.gcd a' b') t'.natAbs := by
    calc
      g * 1 = Nat.gcd (Int.gcd a b) t.natAbs := by simp [g]
      _ = _ := by rw [ha,hb,htt,Int.gcd_mul_left,Int.natAbs_mul,Int.natAbs_natCast,
        Nat.gcd_mul_left]
  exact ⟨a',b',t',g,hg,Int.ediv_pos_of_pos_of_dvd ht (by positivity) hgt,
    (Nat.mul_left_cancel hg he).symm,ha,hb,htt⟩

/-- Any two rationals admit a primitive homogeneous integer lift with a
positive last coordinate. -/
lemma rational_pair_primitive_lift (r s : ℚ) :
    ∃ a b t : ℤ, 0 < t ∧ Nat.gcd (Int.gcd a b) t.natAbs = 1 ∧
      (a : ℚ) = t*r ∧ (b : ℚ) = t*s := by
  let a : ℤ := r.num*s.den
  let b : ℤ := s.num*r.den
  let t : ℤ := (r.den : ℤ)*s.den
  have ht : 0 < t := by dsimp [t]; exact_mod_cast Nat.mul_pos r.den_pos s.den_pos
  have ha : (a : ℚ) = t*r := by
    dsimp [a,t]
    push_cast
    rw [mul_right_comm, Rat.den_mul_eq_num]
  have hb : (b : ℚ) = t*s := by
    dsimp [b,t]
    push_cast
    rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
  obtain ⟨a',b',t',g,hg,ht',hp,haa,hbb,htt⟩ := primitive_triple_normalization a b t ht
  have hgQ : (g : ℚ) ≠ 0 := by positivity
  rw [haa,htt] at ha
  rw [hbb,htt] at hb
  push_cast at ha hb
  refine ⟨a',b',t',ht',hp,?_,?_⟩
  · exact mul_left_cancel₀ hgQ (by simpa only [mul_assoc] using ha)
  · exact mul_left_cancel₀ hgQ (by simpa only [mul_assoc] using hb)

lemma integer_scalar_of_primitive_four {x y z w : ℕ}
    (hp : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    {X Y Z W : ℤ} {q : ℚ}
    (hx : q*x=X) (hy : q*y=Y) (hz : q*z=Z) (hw : q*w=W) :
    ∃ g : ℤ, (g : ℚ) = q := by
  let u := Nat.gcd x y
  let v := Nat.gcd z w
  let a : ℤ := Nat.gcdA x y * Nat.gcdA u v
  let b : ℤ := Nat.gcdB x y * Nat.gcdA u v
  let c : ℤ := Nat.gcdA z w * Nat.gcdB u v
  let d : ℤ := Nat.gcdB z w * Nat.gcdB u v
  have hlin : (x : ℤ)*a+y*b+z*c+w*d=1 := by
    have h₁ := Nat.gcd_eq_gcd_ab x y
    have h₂ := Nat.gcd_eq_gcd_ab z w
    have h₃ := Nat.gcd_eq_gcd_ab u v
    have hpuv : Nat.gcd u v = 1 := hp
    rw [hpuv] at h₃
    calc
      _ = (u : ℤ)*Nat.gcdA u v+(v : ℤ)*Nat.gcdB u v := by
        dsimp only [a,b,c,d,u,v]
        rw [h₁,h₂]
        ring
      _ = 1 := by simpa using h₃.symm
  refine ⟨X*a+Y*b+Z*c+W*d,?_⟩
  have hlinQ : (x : ℚ)*(a : ℚ)+y*b+z*c+w*d=1 := by exact_mod_cast hlin
  push_cast
  rw [← hx,← hy,← hz,← hw]
  calc
    _ = q*((x : ℚ)*(a : ℚ)+y*b+z*c+w*d) := by ring
    _ = q := by rw [hlinQ,mul_one]

namespace CubicBaseLocus

lemma homogeneous {K : Type*} [CommRing K] (a b t k : K) :
    A (k*a) (k*b) (k*t) = k^3*A a b t ∧
    B (k*a) (k*b) (k*t) = k^3*B a b t ∧
    C (k*a) (k*b) (k*t) = k^3*C a b t ∧
    D (k*a) (k*b) (k*t) = k^3*D a b t := by
  dsimp [A,B,C,D,Q]
  constructor; ring
  constructor; ring
  constructor <;> ring

lemma int_cast_coordinates (a b t : ℤ) :
    ((A a b t : ℤ) : ℚ) = A (a : ℚ) b t ∧
    ((B a b t : ℤ) : ℚ) = B (a : ℚ) b t ∧
    ((C a b t : ℤ) : ℚ) = C (a : ℚ) b t ∧
    ((D a b t : ℤ) : ℚ) = D (a : ℚ) b t := by
  simp [A,B,C,D,Q]

/-- Every primitive ordered natural collision has primitive integer parameters.
The raw forms are exactly `g` times the roots, for a positive integer `g`. -/
theorem primitive_collision_integral_certificate {x y z w : ℕ}
    (hxy : x < y) (hyz : y ≤ z) (hzw : z < w)
    (he : x^3+w^3=y^3+z^3)
    (hp : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1) :
    ∃ a b t g : ℤ, 0 < b ∧ 0 < t ∧ 0 < g ∧
      Nat.gcd (Int.gcd a b) t.natAbs = 1 ∧
      A a b t = g*x ∧ B a b t = g*y ∧ C a b t = g*z ∧ D a b t = g*w := by
  obtain ⟨r,s,k,hs,hk,hx,hy,hz,hw⟩ :=
    CubicParametrization.complete_weak_order (y := (y : ℚ)) (z := (z : ℚ)) (w := (w : ℚ)) (show (0 : ℚ) ≤ x by positivity)
      (by exact_mod_cast hxy) (by exact_mod_cast hyz) (by exact_mod_cast hzw)
      (by exact_mod_cast he)
  change (x : ℚ) = k*A r s 1 at hx
  change (y : ℚ) = k*B r s 1 at hy
  change (z : ℚ) = k*C r s 1 at hz
  change (w : ℚ) = k*D r s 1 at hw
  obtain ⟨a,b,t,ht,hprim,ha,hb⟩ := rational_pair_primitive_lift r s
  have hbpos : 0 < b := by
    have hbQ : (0 : ℚ) < b := by rw [hb]; positivity
    exact_mod_cast hbQ
  obtain ⟨hA,hB,hC,hD⟩ := homogeneous r s 1 (t : ℚ)
  rw [← ha,← hb,mul_one] at hA hB hC hD
  obtain ⟨hcA,hcB,hcC,hcD⟩ := int_cast_coordinates a b t
  let q : ℚ := (t : ℚ)^3/k
  have hq : 0 < q := by dsimp [q]; positivity
  have hX : q*x=((A a b t : ℤ) : ℚ) := by rw [hx,hcA,hA]; dsimp [q]; field_simp
  have hY : q*y=((B a b t : ℤ) : ℚ) := by rw [hy,hcB,hB]; dsimp [q]; field_simp
  have hZ : q*z=((C a b t : ℤ) : ℚ) := by rw [hz,hcC,hC]; dsimp [q]; field_simp
  have hW : q*w=((D a b t : ℤ) : ℚ) := by rw [hw,hcD,hD]; dsimp [q]; field_simp
  obtain ⟨g,hg⟩ := integer_scalar_of_primitive_four hp hX hY hZ hW
  have hgpos : 0 < g := by rw [← hg] at hq; exact_mod_cast hq
  rw [← hg] at hX hY hZ hW
  refine ⟨a,b,t,g,hbpos,ht,hgpos,hprim,?_,?_,?_,?_⟩
  · exact_mod_cast hX.symm
  · exact_mod_cast hY.symm
  · exact_mod_cast hZ.symm
  · exact_mod_cast hW.symm

#print axioms primitive_collision_integral_certificate


lemma triple_primitive_at_prime {a b t : ℤ}
    (h : Nat.gcd (Int.gcd a b) t.natAbs = 1) {p : ℕ} (hp : p.Prime) :
    ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ t) := by
  rintro ⟨ha,hb,ht⟩
  have h₁ : p ∣ Int.gcd a b :=
    Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd ha hb)
  have h₂ : p ∣ t.natAbs := Int.natCast_dvd.mp ht
  have hh := Nat.dvd_gcd h₁ h₂
  rw [h] at hh
  exact hp.not_dvd_one hh

lemma certificate_gcd_exact {a b t g : ℤ} {x y z w : ℕ}
    (hp : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w) :
    Nat.gcd (Int.gcd (A a b t) (B a b t)) (Int.gcd (C a b t) (D a b t)) =
      g.natAbs := by
  rw [hA,hB,hC,hD,Int.gcd_mul_left,Int.gcd_mul_left,
    Int.gcd_natCast_natCast,Int.gcd_natCast_natCast,Nat.gcd_mul_left,hp,mul_one]

lemma certificate_prime_support {a b t g : ℤ} {x y z w : ℕ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    {p : ℕ} (hp : p.Prime) (hpg : (p : ℤ) ∣ g) :
    p = 2 ∨ p = 3 ∨ p % 3 = 1 := by
  apply common_prime_split_or_small hp (triple_primitive_at_prime hprim hp)
  · rw [hA]; exact hpg.mul_right _
  · rw [hB]; exact hpg.mul_right _
  · rw [hC]; exact hpg.mul_right _
  · rw [hD]; exact hpg.mul_right _

/-- For an integral certificate of primitive roots, the base-locus criterion is
an exact test for each prime power dividing the cancellation factor itself. -/
lemma certificate_prime_power_iff {a b t g : ℤ} {x y z w : ℕ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (k : ℕ) :
    ((p : ℤ)^k ∣ g) ↔
      (((p : ℤ)^k ∣ t ∧ (p : ℤ)^k ∣ Q a b) ∨
        ((p : ℤ)^k ∣ b ∧ (p : ℤ)^k ∣ t^2+3*a^2) ∨
        ((p : ℤ)^k ∣ 2*a-b ∧ (p : ℤ)^k ∣ t^2+3*a^2)) := by
  rw [← common_prime_power_iff hp hp2 hp3 (triple_primitive_at_prime hprim hp) k]
  constructor
  · intro hd
    rw [hA,hB,hC,hD]
    exact ⟨hd.mul_right _,hd.mul_right _,hd.mul_right _,hd.mul_right _⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    have hl : p^k ∣ Int.gcd (A a b t) (B a b t) := by
      apply Int.natCast_dvd_natCast.mp
      exact_mod_cast Int.dvd_coe_gcd h₁ h₂
    have hr : p^k ∣ Int.gcd (C a b t) (D a b t) := by
      apply Int.natCast_dvd_natCast.mp
      exact_mod_cast Int.dvd_coe_gcd h₃ h₄
    have hh := Nat.dvd_gcd hl hr
    rw [certificate_gcd_exact hpRoots hA hB hC hD] at hh
    exact_mod_cast Int.natCast_dvd.mpr hh

#print axioms certificate_gcd_exact
#print axioms certificate_prime_support
#print axioms certificate_prime_power_iff

end CubicBaseLocus
end Erdos1206
