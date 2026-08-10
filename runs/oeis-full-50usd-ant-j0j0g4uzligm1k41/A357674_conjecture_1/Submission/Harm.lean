import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/-! Harmonic sum congruences. We work toward Wolstenholme-type results. -/

namespace Harm

/-- Power sum of `i`-th powers over a finite field `ZMod p` is 0 when `i < p-1`. -/
theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] (i : ℕ) (hip : i < p - 1) :
    ∑ x : ZMod p, x ^ i = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by rwa [ZMod.card])

theorem cast_injOn (p : ℕ) [Fact p.Prime] :
    Set.InjOn (fun j : ℕ => (j : ZMod p)) (Finset.Icc 1 (p-1)) := by
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  have hp := Fact.out (p := p.Prime)
  rw [ZMod.natCast_eq_natCast_iff] at hab
  have : a < p := by omega
  have : b < p := by omega
  exact (Nat.ModEq.eq_of_lt_of_lt hab ‹a<p› ‹b<p›)

/-- `Icc 1 (p-1)` cast into `ZMod p` is the nonzero elements. -/
theorem image_cast (p : ℕ) [Fact p.Prime] :
    (Finset.Icc 1 (p-1)).image (fun j : ℕ => (j : ZMod p)) = Finset.univ.erase 0 := by
  have hp := Fact.out (p := p.Prime)
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  · rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card,
      Finset.card_image_of_injOn (cast_injOn p), Nat.card_Icc]
    omega

theorem sum_inv_pow_eq (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod p))⁻¹ ^ r = ∑ x : ZMod p, x ^ r := by
  have hinv : ∑ x : ZMod p, x ^ r = ∑ x : ZMod p, (x⁻¹) ^ r := by
    apply Finset.sum_equiv (Equiv.mk (fun x : ZMod p => x⁻¹) (fun x => x⁻¹) inv_inv inv_inv)
    · simp
    · intro i _; simp
  have hzero : ((0 : ZMod p)⁻¹) ^ r = 0 := by simp [zero_pow (by omega : r ≠ 0)]
  calc ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod p))⁻¹ ^ r
      = ∑ x ∈ (Finset.Icc 1 (p-1)).image (fun j : ℕ => (j : ZMod p)), x⁻¹ ^ r := by
        rw [Finset.sum_image (fun a ha b hb => cast_injOn p ha hb)]
    _ = ∑ x ∈ Finset.univ.erase 0, x⁻¹ ^ r := by rw [image_cast]
    _ = ∑ x : ZMod p, x⁻¹ ^ r := Finset.sum_erase _ hzero
    _ = ∑ x : ZMod p, x ^ r := hinv.symm

/-- Harmonic sum of inverse `r`-th powers over `1..p-1` in a ring `ZMod N`. -/
def H (p N r : ℕ) : ZMod N := ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod N))⁻¹ ^ r

/-- `j` (with `1 ≤ j ≤ p-1`) is a unit in `ZMod (p^k)`. -/
theorem isUnit_cast (p k j : ℕ) [Fact p.Prime] (hj1 : 1 ≤ j) (hj2 : j ≤ p - 1) :
    IsUnit ((j : ZMod (p^k))) := by
  have hp := Fact.out (p := p.Prime)
  rw [ZMod.isUnit_iff_coprime]
  have hndvd : ¬ p ∣ j := by
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd
    have := hp.two_le; omega
  exact (((hp.coprime_iff_not_dvd).mpr hndvd).symm).pow_right k

/-- Casting a harmonic sum down from `ZMod (p^k)` to `ZMod (p^m)`. -/
theorem castHom_H (p k m r : ℕ) [Fact p.Prime] (hmk : p^m ∣ p^k) :
    (ZMod.castHom hmk (ZMod (p^m))) (H p (p^k) r) = H p (p^m) r := by
  unfold H
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  rw [map_pow]
  congr 1
  have ha := isUnit_cast p k j hj.1 hj.2
  have h1 : (j : ZMod (p^k)) * ((j : ZMod (p^k)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have h2 := congrArg (ZMod.castHom hmk (ZMod (p^m))) h1
  rw [map_mul, map_one, map_natCast] at h2
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h2).symm

/-- If `H` casts to 0 mod `p^m`, then `p^m` divides it in `ZMod (p^k)`. -/
theorem dvd_of_castHom_zero (p k m : ℕ) [NeZero (p^k)] (hmk : p^m ∣ p^k) (x : ZMod (p^k))
    (h : ZMod.castHom hmk (ZMod (p^m)) x = 0) : (p : ZMod (p^k))^m ∣ x := by
  have hx : ((x.val : ℕ) : ZMod (p^k)) = x := ZMod.natCast_zmod_val x
  rw [← hx, map_natCast, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨(t : ZMod (p^k)), ?_⟩
  rw [← hx, ht]
  push_cast
  ring

/-- `H_r ≡ 0 mod p` for `2 ≤ r < p-1`. -/
theorem H_dvd_p (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r) (hrp : r < p - 1) :
    (p : ZMod (p^5)) ∣ H p (p^5) r := by
  haveI : NeZero (p^5) := ⟨pow_ne_zero 5 (Fact.out (p := p.Prime)).ne_zero⟩
  have hdvd : p^1 ∣ p^5 := pow_dvd_pow p (by omega)
  have := dvd_of_castHom_zero p 5 1 hdvd (H p (p^5) r) ?_
  · simpa using this
  · rw [castHom_H]
    show H p (p^1) r = 0
    rw [pow_one]
    unfold H
    rw [sum_inv_pow_eq p r hr, sum_pow_zmod p r hrp]

/-- Reflection `j ↦ p-j` on `Icc 1 (p-1)`. -/
theorem refl_sum {M : Type*} [AddCommMonoid M] (p : ℕ) (hp : 1 ≤ p) (f : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 (p-1), f j = ∑ j ∈ Finset.Icc 1 (p-1), f (p - j) := by
  apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha
    rw [Nat.sub_sub_self (by omega)]

section Reflection
variable (p k : ℕ) [Fact p.Prime]

/-- `a⁻¹ + b⁻¹ = (a+b) * (ab)⁻¹` for units. -/
theorem inv_add_inv {R : Type*} [CommRing R] [Inv R] (a b : R) (ha : a * a⁻¹ = 1)
    (hb : b * b⁻¹ = 1) (hab : (a*b) * (a*b)⁻¹ = 1) :
    a⁻¹ + b⁻¹ = (a + b) * (a*b)⁻¹ := by
  have key : (a⁻¹ + b⁻¹) * (a*b) = (a + b) := by
    have e1 : a⁻¹ * a = 1 := by rw [mul_comm]; exact ha
    have e2 : b⁻¹ * b = 1 := by rw [mul_comm]; exact hb
    calc (a⁻¹ + b⁻¹) * (a*b) = (a⁻¹*a)*b + (b⁻¹*b)*a := by ring
      _ = 1*b + 1*a := by rw [e1, e2]
      _ = a + b := by ring
  calc a⁻¹ + b⁻¹ = (a⁻¹ + b⁻¹) * ((a*b) * (a*b)⁻¹) := by rw [hab, mul_one]
    _ = ((a⁻¹ + b⁻¹) * (a*b)) * (a*b)⁻¹ := by ring
    _ = (a + b) * (a*b)⁻¹ := by rw [key]

/-- Casting the inverse of a unit `(a : ZMod (p^k))` down to `ZMod (p^m)`. -/
theorem castHom_inv (p k m : ℕ) [Fact p.Prime] (hmk : p^m ∣ p^k) (a : ℕ)
    (ha : IsUnit ((a : ZMod (p^k)))) :
    ZMod.castHom hmk (ZMod (p^m)) ((a : ZMod (p^k)))⁻¹ = ((a : ZMod (p^m)))⁻¹ := by
  have h1 : (a : ZMod (p^k)) * ((a : ZMod (p^k)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have h2 := congrArg (ZMod.castHom hmk (ZMod (p^m))) h1
  rw [map_mul, map_one, map_natCast] at h2
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h2).symm

/-- The "paired" sum `∑ 1/(j(p-j))` is divisible by `p` in `ZMod (p^2)`. -/
theorem paired_dvd_p (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (p : ZMod (p^2)) ∣ ∑ j ∈ Finset.Icc 1 (p-1), (((j * (p - j) : ℕ) : ZMod (p^2)))⁻¹ := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero⟩
  have := dvd_of_castHom_zero p 2 1 (pow_dvd_pow p (by omega))
    (∑ j ∈ Finset.Icc 1 (p-1), (((j * (p - j) : ℕ) : ZMod (p^2)))⁻¹) ?_
  · simpa using this
  · rw [map_sum]
    have hpe : (p^1 : ℕ) = p := pow_one p
    have hkey : ∀ j ∈ Finset.Icc 1 (p-1),
        ZMod.castHom (pow_dvd_pow p (by omega : 1 ≤ 2)) (ZMod (p^1))
          (((j * (p - j) : ℕ) : ZMod (p^2)))⁻¹
        = - (((j : ZMod (p^1)))⁻¹)^2 := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hu : IsUnit (((j * (p-j) : ℕ) : ZMod (p^2))) := by
        rw [Nat.cast_mul]; exact (isUnit_cast p 2 j hj.1 hj.2).mul
          (isUnit_cast p 2 (p-j) (by omega) (by omega))
      have huj : IsUnit ((j : ZMod (p^1))) := isUnit_cast p 1 j hj.1 hj.2
      rw [castHom_inv p 2 1 _ _ hu]
      have hc : (((j * (p-j) : ℕ)) : ZMod (p^1)) = -((j : ZMod (p^1)))^2 := by
        have hp0 : (p : ZMod (p^1)) = 0 := by rw [hpe]; exact ZMod.natCast_self p
        rw [Nat.cast_mul, Nat.cast_sub (by omega : j ≤ p), hp0]; ring
      rw [hc]
      have hsq : (((j : ZMod (p^1)))^2)⁻¹ = (((j : ZMod (p^1)))⁻¹)^2 := by
        apply ZMod.inv_eq_of_mul_eq_one
        have h1 : (j : ZMod (p^1)) * ((j : ZMod (p^1)))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ huj
        calc ((j : ZMod (p^1)))^2 * (((j : ZMod (p^1)))⁻¹)^2
            = ((j : ZMod (p^1)) * ((j : ZMod (p^1)))⁻¹)^2 := by ring
          _ = 1 := by rw [h1, one_pow]
      have hneg : (-((j : ZMod (p^1)))^2)⁻¹ = -(((j : ZMod (p^1)))^2)⁻¹ := by
        apply ZMod.inv_eq_of_mul_eq_one
        have h1 : ((j : ZMod (p^1)))^2 * (((j : ZMod (p^1)))^2)⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (huj.pow 2)
        calc (-((j : ZMod (p^1)))^2) * (-(((j : ZMod (p^1)))^2)⁻¹)
            = ((j : ZMod (p^1)))^2 * (((j : ZMod (p^1)))^2)⁻¹ := by ring
          _ = 1 := h1
      rw [hneg, hsq]
    rw [Finset.sum_congr rfl hkey, Finset.sum_neg_distrib]
    have hH : ∑ j ∈ Finset.Icc 1 (p-1), (((j : ZMod (p^1)))⁻¹)^2 = 0 := by
      have : ∑ j ∈ Finset.Icc 1 (p-1), (((j : ZMod (p^1)))⁻¹)^2 = H p (p^1) 2 := rfl
      rw [this, hpe]
      unfold H
      rw [sum_inv_pow_eq p 2 (by norm_num), sum_pow_zmod p 2 (by omega)]
    rw [hH, neg_zero]

/-- Reflection identity: `2 * H1 = p * (paired sum)` in `ZMod (p^2)`. -/
theorem two_H1_eq (p : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    2 * H p (p^2) 1 = (p : ZMod (p^2)) * ∑ j ∈ Finset.Icc 1 (p-1), (((j * (p - j) : ℕ) : ZMod (p^2)))⁻¹ := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero⟩
  have hrefl : H p (p^2) 1 = ∑ j ∈ Finset.Icc 1 (p-1), (((p - j : ℕ) : ZMod (p^2)))⁻¹ := by
    unfold H
    simp only [pow_one]
    exact refl_sum p hp (fun j => ((j : ZMod (p^2)))⁻¹)
  have hH1 : H p (p^2) 1 = ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod (p^2)))⁻¹ := by
    unfold H; simp only [pow_one]
  have h2 : 2 * H p (p^2) 1 = ∑ j ∈ Finset.Icc 1 (p-1),
      (((j : ZMod (p^2)))⁻¹ + (((p - j : ℕ) : ZMod (p^2)))⁻¹) := by
    rw [two_mul, Finset.sum_add_distrib, ← hH1, ← hrefl]
  rw [h2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have huj : (j : ZMod (p^2)) * ((j : ZMod (p^2)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_cast p 2 j hj.1 hj.2)
  have hupj : ((p - j : ℕ) : ZMod (p^2)) * (((p - j : ℕ) : ZMod (p^2)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_cast p 2 (p-j) (by omega) (by omega))
  have hprodb : ((j : ZMod (p^2)) * ((p - j : ℕ) : ZMod (p^2)))
      * ((j : ZMod (p^2)) * ((p - j : ℕ) : ZMod (p^2)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _
      ((isUnit_cast p 2 j hj.1 hj.2).mul (isUnit_cast p 2 (p-j) (by omega) (by omega)))
  rw [inv_add_inv _ _ huj hupj hprodb]
  have hsum : (j : ZMod (p^2)) + ((p - j : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) := by
    rw [← Nat.cast_add, show j + (p - j) = p by omega]
  rw [hsum, Nat.cast_mul]

/-- `p^2 ∣ H1` in `ZMod (p^5)` (Wolstenholme). -/
theorem H1_dvd (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (p : ZMod (p^5))^2 ∣ H p (p^5) 1 := by
  haveI : NeZero (p^5) := ⟨pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero⟩
  apply dvd_of_castHom_zero p 5 2 (pow_dvd_pow p (by omega))
  rw [castHom_H]
  -- goal: H p (p^2) 1 = 0
  have hodd : (2 : ZMod (p^2)) * H p (p^2) 1 = 0 := by
    rw [two_H1_eq p (by omega)]
    obtain ⟨t, ht⟩ := paired_dvd_p p hp
    rw [ht]
    have : (p : ZMod (p^2)) * ((p : ZMod (p^2)) * t) = (p : ZMod (p^2))^2 * t := by ring
    rw [this]
    have hp2 : ((p : ZMod (p^2)))^2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hp2, zero_mul]
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    have hc : ((2:ℕ) : ZMod (p^2)) = 2 := by push_cast; ring
    rw [← hc, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out (p:=p.Prime))).mpr (by omega)).pow_right 2
  exact h2unit.mul_right_eq_zero.mp hodd

end Reflection

end Harm
