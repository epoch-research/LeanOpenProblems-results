import FormalConjecturesUtil

/-! A residue-class restriction on rational rotations. This excludes only
bounded denominators; it does not assert that the residue class is Sidon. -/
namespace Erdos773.PrimeResidueRotation
set_option maxHeartbeats 1000000

lemma prime_not_dvd_two {l : ℕ} (hl2 : 2 < l) :
    ¬ (l : ℤ) ∣ 2 := by
  intro hd
  have hh : l ∣ 2 := by exact_mod_cast hd
  have hh' := Nat.le_of_dvd (by decide : 0 < 2) hh
  omega

/-- If three roots are 1 modulo an odd prime, one numerator of any
rational rotation between them is divisible by that prime. -/
theorem divides_leg {l : ℕ} (hl : l.Prime) (hl2 : 2 < l)
    {a b c p r q : ℤ}
    (ha : a ≡ 1 [ZMOD (l : ℤ)]) (hb : b ≡ 1 [ZMOD (l : ℤ)])
    (hc : c ≡ 1 [ZMOD (l : ℤ)])
    (hpyth : q^2 = p^2+r^2) (he : p*a+r*b=q*c) :
    (l : ℤ) ∣ p ∨ (l : ℤ) ∣ r := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hm : p+r ≡ q [ZMOD (l : ℤ)] := by
    have h₁ := ((Int.ModEq.refl p).mul ha).add ((Int.ModEq.refl r).mul hb)
    have h₂ := (Int.ModEq.refl q).mul hc
    simp only [mul_one] at h₁ h₂
    exact h₁.symm.trans (he ▸ h₂)
  have hd : (l : ℤ) ∣ p+r-q := by
    have hh := hm.dvd
    simpa only [neg_sub] using (dvd_neg.mpr hh)
  have hprod : (l : ℤ) ∣ 2*(p*r) := by
    convert dvd_mul_of_dvd_left hd (p+r+q) using 1; nlinarith only [hpyth]
  exact hp.dvd_mul.mp ((hp.dvd_mul.mp hprod).resolve_left (prime_not_dvd_two hl2))

lemma square_bound_of_divisor {l : ℕ} {x : ℤ}
    (hx : x ≠ 0) (hd : (l : ℤ) ∣ x) : (l : ℤ)^2 ≤ x^2 := by
  have h := Int.natAbs_le_of_dvd_ne_zero hd hx
  have hh : (l : ℤ) ≤ |x| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  have hl0 : (0 : ℤ) ≤ l := by positivity
  have hx0 := abs_nonneg x
  nlinarith only [hh, hl0, hx0, sq_abs x]

/-- The Gaussian parameters of a nondegenerate rotation through roots in
one prime residue class have norm at least half the prime squared.
The signs of both numerator coordinates may be chosen independently. -/
theorem denominator_lower {l : ℕ} (hl : l.Prime) (hl2 : 2 < l)
    {a b c p r u v : ℤ}
    (ha : a ≡ 1 [ZMOD (l : ℤ)]) (hb : b ≡ 1 [ZMOD (l : ℤ)])
    (hc : c ≡ 1 [ZMOD (l : ℤ)])
    (hu : u ≠ 0) (hv : v ≠ 0) (hsub : u-v ≠ 0) (hadd : u+v ≠ 0)
    (hp : p = u^2-v^2 ∨ p = -(u^2-v^2))
    (hr : r = 2*u*v ∨ r = -(2*u*v))
    (he : p*a+r*b=(u^2+v^2)*c) :
    (l : ℤ)^2 ≤ 2*(u^2+v^2) := by
  have hprime : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hpyth : (u^2+v^2)^2 = p^2+r^2 := by
    rcases hp with rfl | rfl <;> rcases hr with rfl | rfl <;> ring
  have hd := divides_leg hl hl2 ha hb hc hpyth he
  rcases hd with hd | hd
  · have hf : (l : ℤ) ∣ (u-v)*(u+v) := by
      have hh : (l : ℤ) ∣ u^2-v^2 := by
        rcases hp with rfl | rfl
        · exact hd
        · exact dvd_neg.mp hd
      convert hh using 1; ring
    rcases hprime.dvd_mul.mp hf with hh | hh
    · have hb := square_bound_of_divisor hsub hh
      nlinarith only [hb, sq_nonneg (u+v)]
    · have hb := square_bound_of_divisor hadd hh
      nlinarith only [hb, sq_nonneg (u-v)]
  · have hf : (l : ℤ) ∣ 2*(u*v) := by
      have hh : (l : ℤ) ∣ 2*u*v := by
        rcases hr with rfl | rfl
        · exact hd
        · exact dvd_neg.mp hd
      simpa only [mul_assoc] using hh
    have hh := (hprime.dvd_mul.mp hf).resolve_left (prime_not_dvd_two hl2)
    rcases hprime.dvd_mul.mp hh with hh | hh
    · have hb := square_bound_of_divisor hu hh
      nlinarith only [hb, sq_nonneg u, sq_nonneg v]
    · have hb := square_bound_of_divisor hv hh
      nlinarith only [hb, sq_nonneg u, sq_nonneg v]

/-- An explicit carrier; no claim of full Sidonness is made. -/
def roots (l K : ℕ) : Finset ℕ :=
  (Finset.range K).image (fun k => l*k+1)

lemma roots_card {l : ℕ} (hl : 0 < l) (K : ℕ) : (roots l K).card = K := by
  rw [roots, Finset.card_image_of_injective]
  · exact Finset.card_range K
  · intro a b he
    exact Nat.eq_of_mul_eq_mul_left hl (Nat.add_right_cancel he)

lemma roots_subset {l : ℕ} (hl : 0 < l) (K : ℕ) :
    roots l K ⊆ Finset.Icc 1 (l*K) := by
  intro a ha
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
  have hk' := Finset.mem_range.mp hk
  have hm := Nat.mul_le_mul_left l (show k+1 ≤ K by omega)
  apply Finset.mem_Icc.mpr
  constructor <;> nlinarith

lemma roots_residue {l K a : ℕ} (ha : a ∈ roots l K) :
    (a : ℤ) ≡ 1 [ZMOD (l : ℤ)] := by
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(k : ℤ), ?_⟩
  push_cast
  ring

/-- The carrier has K positive roots below l*K, and has no rotation of
the displayed nondegenerate type with denominator smaller than l²/2. -/
theorem roots_no_small_rotation {l K : ℕ} (hl : l.Prime) (hl2 : 2 < l)
    {a b c : ℕ} (ha : a ∈ roots l K) (hb : b ∈ roots l K)
    (hc : c ∈ roots l K) {p r u v : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hsub : u-v ≠ 0) (hadd : u+v ≠ 0)
    (hp : p = u^2-v^2 ∨ p = -(u^2-v^2))
    (hr : r = 2*u*v ∨ r = -(2*u*v))
    (hsmall : 2*(u^2+v^2) < (l : ℤ)^2) :
    p*a+r*b ≠ (u^2+v^2)*c := by
  intro he
  exact (not_le_of_gt hsmall) (denominator_lower hl hl2
    (roots_residue ha) (roots_residue hb) (roots_residue hc)
    hu hv hsub hadd hp hr he)

/-- The residue carrier already contains a four-distinct-root collision
at height 10*l²+7*l+1. This limits the preceding construction, not the
maximum Sidon subset of all squares. No primality assumption is needed. -/
theorem residue_carrier_not_sidon {l K : ℕ} (hl : 0 < l)
    (hK : 10*l+8 ≤ K) :
    ¬ IsSidon (((roots l K).image (fun n => n^2)) : Set ℕ) := by
  let a := l*3+1
  let b := l*(10*l+7)+1
  let c := l*(8*l+5)+1
  let d := l*(6*l+5)+1
  have hm (i : ℕ) (hi : i < K) : (l*i+1)^2 ∈
      ((roots l K).image (fun n => n^2) : Set ℕ) := by
    simp only [Finset.mem_coe]
    apply Finset.mem_image.mpr
    refine ⟨l*i+1, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have ha : a^2 ∈ ((roots l K).image (fun n => n^2) : Set ℕ) :=
    hm 3 (by omega)
  have hb : b^2 ∈ ((roots l K).image (fun n => n^2) : Set ℕ) :=
    hm (10*l+7) (by omega)
  have hc : c^2 ∈ ((roots l K).image (fun n => n^2) : Set ℕ) :=
    hm (8*l+5) (by omega)
  have hd : d^2 ∈ ((roots l K).image (fun n => n^2) : Set ℕ) :=
    hm (6*l+5) (by omega)
  have he : a^2+b^2=c^2+d^2 := by dsimp [a,b,c,d]; ring
  have hac : a < c := by dsimp [a,c]; nlinarith
  have had : a < d := by dsimp [a,d]; nlinarith
  have hac' := Nat.pow_lt_pow_left hac (by decide : 2 ≠ 0)
  have had' := Nat.pow_lt_pow_left had (by decide : 2 ≠ 0)
  intro hs
  rcases hs (a^2) ha (c^2) hc (b^2) hb (d^2) hd he with hh | hh
  · omega
  · omega

/-- An explicit collision of four different positive roots in the residue
class, at a height quadratic in the modulus. -/
theorem quadratic_height_collision {l : ℕ} (hl : 0 < l) :
    ∃ a b c d : ℕ, a ∈ Finset.Icc 1 (10*l^2+7*l+1) ∧
      b ∈ Finset.Icc 1 (10*l^2+7*l+1) ∧ c ∈ Finset.Icc 1 (10*l^2+7*l+1) ∧
      d ∈ Finset.Icc 1 (10*l^2+7*l+1) ∧ a ≡ 1 [MOD l] ∧ b ≡ 1 [MOD l] ∧ c ≡ 1 [MOD l] ∧ d ≡ 1 [MOD l] ∧
      a < d ∧ d < c ∧ c < b ∧ a^2+b^2=c^2+d^2 := by
  refine ⟨l*3+1, l*(10*l+7)+1, l*(8*l+5)+1, l*(6*l+5)+1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr; constructor <;> nlinarith
  · apply Finset.mem_Icc.mpr; constructor <;> nlinarith
  · apply Finset.mem_Icc.mpr; constructor <;> nlinarith
  · apply Finset.mem_Icc.mpr; constructor <;> nlinarith
  · simp only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  · simp only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  · simp only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  · simp only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  · nlinarith
  · nlinarith
  · nlinarith
  · ring

#print axioms residue_carrier_not_sidon
#print axioms quadratic_height_collision
#print axioms roots_card
#print axioms roots_subset
#print axioms roots_no_small_rotation
#print axioms divides_leg
#print axioms denominator_lower
end Erdos773.PrimeResidueRotation
