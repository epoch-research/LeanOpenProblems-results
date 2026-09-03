import Submission.CubicBaseLocus

/-! Exact first-order congruences at one of the three quadratic base loci.
These are local arithmetic facts, not a density construction. -/
namespace Erdos1206.CubicCancellationLines
open CubicBaseLocus

lemma first_identity (a b t : ℤ) :
    a*C a b t+b*A a b t =
      Q a b*(-3*Q a b+3*a*t-t^2)+t^2*(a+b)*(t-b) := by
  dsimp [A,C,Q]
  ring

lemma second_identity (a b t : ℤ) :
    a*D a b t+(a-b)*B a b t =
      t*(2*a-b)*(3*Q a b+b*t+t^2) := by
  dsimp [B,D,Q]
  ring

/-- Dividing out any common factor lying at the `t = Q = 0` base locus
leaves two linear congruences between the reduced coordinates. -/
theorem reduced_relations {g a b t x y z w : ℤ} (hg : g ≠ 0)
    (ht : g ∣ t) (hq : g ∣ Q a b)
    (hx : A a b t = g*x) (hy : B a b t = g*y)
    (hz : C a b t = g*z) (hw : D a b t = g*w) :
    g ∣ a*z+b*x ∧ g ∣ a*w+(a-b)*y := by
  obtain ⟨u,hu⟩ := ht
  obtain ⟨v,hv⟩ := hq
  have h₁ := first_identity a b t
  have h₂ := second_identity a b t
  rw [hx,hz,hu,hv] at h₁
  rw [hy,hw,hu,hv] at h₂
  constructor
  · refine ⟨v*(-3*v+3*a*u-g*u^2)+u^2*(a+b)*(g*u-b), ?_⟩
    apply mul_left_cancel₀ hg
    linear_combination h₁
  · refine ⟨u*(2*a-b)*(3*v+b*u+g*u^2), ?_⟩
    apply mul_left_cancel₀ hg
    linear_combination h₂

/-- Over a field, the reduced coordinates lie on a nontrivial Fermat line.
This version isolates the conclusion independently of prime-power bookkeeping. -/
theorem field_line {F : Type*} [Field F] {a b x y z w : F}
    (h3 : (3:F) ≠ 0) (ha : a ≠ 0) (hq : Q a b = 0)
    (h₁ : a*z+b*x = 0) (h₂ : a*w+(a-b)*y = 0) :
    ∃ r : F, r^3 = 1 ∧ r ≠ 1 ∧ z = r*x ∧ y = r*w := by
  refine ⟨-b/a, ?_, ?_, ?_, ?_⟩
  · rw [div_pow]
    apply (div_eq_one_iff_eq (pow_ne_zero 3 ha)).mpr
    have hfac : (-b)^3-a^3 = -(a+b)*Q a b := by dsimp [Q]; ring
    rw [hq,mul_zero] at hfac
    exact sub_eq_zero.mp hfac
  · intro hr
    have hab : -b=a := (div_eq_one_iff_eq ha).mp hr
    have hq' : (3:F)*a^2=0 := by
      dsimp [Q] at hq
      have hb' : b = -a := by linear_combination -hab
      rw [hb'] at hq
      linear_combination hq
    exact ha (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hq').resolve_left h3))
  · have he : z = (-b*x)/a := by
      apply (eq_div_iff ha).mpr
      linear_combination h₁
    simpa only [div_mul_eq_mul_div] using he
  · have hrel : a*(a*y+b*w) = 0 := by
      dsimp [Q] at hq
      linear_combination b*h₂+y*hq
    have he : y = (-b*w)/a := by
      apply (eq_div_iff ha).mpr
      linear_combination (mul_eq_zero.mp hrel).resolve_left ha
    simpa only [div_mul_eq_mul_div] using he

/-- A cancellation prime in this chart forces a nontrivial cubic-root-of-unity
ratio between two pairs of reduced roots. -/
theorem cancellation_prime_line {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {g a b t x y z w : ℤ} (hg : g ≠ 0) (hpg : (p:ℤ) ∣ g)
    (ha : ¬ (p:ℤ) ∣ a) (ht : g ∣ t) (hq : g ∣ Q a b)
    (hx : A a b t = g*x) (hy : B a b t = g*y)
    (hz : C a b t = g*z) (hw : D a b t = g*w) :
    ∃ r : ZMod p, r^3 = 1 ∧ r ≠ 1 ∧
      (z:ZMod p) = r*(x:ZMod p) ∧ (y:ZMod p) = r*(w:ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h₁,h₂⟩ := reduced_relations hg ht hq hx hy hz hw
  have h₁' := (ZMod.intCast_zmod_eq_zero_iff_dvd (a*z+b*x) p).mpr (hpg.trans h₁)
  have h₂' := (ZMod.intCast_zmod_eq_zero_iff_dvd (a*w+(a-b)*y) p).mpr (hpg.trans h₂)
  have hq' : Q (a:ZMod p) (b:ZMod p) = 0 := by
    simpa only [Q,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (Q a b) p).mpr (hpg.trans hq)
  have ha' : (a:ZMod p) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).not.mpr ha
  have h3 : (3:ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  exact field_line h3 ha' hq' (by simpa using h₁') (by simpa using h₂')

#print axioms reduced_relations
#print axioms field_line
#print axioms cancellation_prime_line
end Erdos1206.CubicCancellationLines
