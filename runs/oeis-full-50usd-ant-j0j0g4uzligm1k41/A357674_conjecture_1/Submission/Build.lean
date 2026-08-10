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

namespace A357674dev

open Harm

/-- Product expansion mod p^5: higher symmetric terms vanish. -/
theorem prod_expand5 (p : ℕ) [Fact p.Prime] (a : ℕ → ZMod (p^5))
    (hp : 7 ≤ p) (hdvd : ∀ i ∈ Icc 1 (p-1), (p : ZMod (p^5)) ∣ a i) :
    ∏ i ∈ Icc 1 (p-1), (1 + a i)
      = ∑ m ∈ range 5, ∑ t ∈ (Icc 1 (p-1)).powersetCard m, ∏ j ∈ t, a j := by
  rw [Finset.prod_one_add, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range, Nat.card_Icc] at hx ⊢
    omega
  · intro i _ hni
    rw [Finset.mem_range, not_lt] at hni
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨hts, htc⟩ := ht
    have hdv : (p : ZMod (p^5))^i ∣ ∏ j ∈ t, a j := by
      rw [← htc, ← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd (fun _ => (p:ZMod (p^5))) a
        (fun j hj => hdvd j (hts hj))
    have h0 : (p : ZMod (p^5))^i = 0 := by
      have h5 : (p : ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      calc (p : ZMod (p^5))^i = (p : ZMod (p^5))^5 * (p : ZMod (p^5))^(i-5) := by
            rw [← pow_add]; congr 1; omega
        _ = 0 := by rw [h5, zero_mul]
    rw [h0] at hdv
    exact zero_dvd_iff.mp hdv

end A357674dev

namespace A357674dev
open Harm

theorem sum_image_insert {R : Type*} [CommRing R] (a : ℕ) (s : Finset ℕ)
    (ha : a ∉ s) (n : ℕ) (f : ℕ → R) :
    ∑ t ∈ (s.powersetCard n).image (insert a), ∏ i ∈ t, f i
      = f a * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i := by
  classical
  have hinj : ∀ x ∈ s.powersetCard n, ∀ y ∈ s.powersetCard n,
      insert a x = insert a y → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_powersetCard] at hx hy
    have hax : a ∉ x := fun h => ha (hx.1 h)
    have hay : a ∉ y := fun h => ha (hy.1 h)
    rw [← Finset.erase_insert hax, hxy, Finset.erase_insert hay]
  rw [Finset.sum_image hinj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.prod_insert (fun h => ha (ht.1 h))]

theorem esymm_recur {R : Type*} [CommRing R] (a : ℕ) (s : Finset ℕ)
    (ha : a ∉ s) (n : ℕ) (f : ℕ → R) :
    ∑ t ∈ (insert a s).powersetCard (n+1), ∏ i ∈ t, f i
      = (∑ t ∈ s.powersetCard (n+1), ∏ i ∈ t, f i)
        + f a * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i := by
  classical
  have hdisj : Disjoint (s.powersetCard (n+1)) ((s.powersetCard n).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t ht htm
    rw [Finset.mem_image] at htm
    obtain ⟨u, _, rfl⟩ := htm
    rw [Finset.mem_powersetCard] at ht
    exact ha (ht.1 (Finset.mem_insert_self a u))
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj, sum_image_insert a s ha n f]

theorem two_esymm2 {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
      = (∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [show (∅:Finset ℕ).powersetCard 2 = ∅ from rfl]; simp
  | insert a s ha ih =>
    have hinj : ∀ x ∈ s.powersetCard 1, ∀ y ∈ s.powersetCard 1,
        insert a x = insert a y → x = y := by
      intro x hx y hy hxy
      rw [Finset.mem_powersetCard] at hx hy
      have hax : a ∉ x := fun h => ha (hx.1 h)
      have hay : a ∉ y := fun h => ha (hy.1 h)
      rw [← Finset.erase_insert hax, hxy, Finset.erase_insert hay]
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert a)) := by
      rw [Finset.disjoint_left]
      intro t ht htm
      rw [Finset.mem_image] at htm
      obtain ⟨u, _, rfl⟩ := htm
      rw [Finset.mem_powersetCard] at ht
      exact ha (ht.1 (Finset.mem_insert_self a u))
    have h1 : ∑ t ∈ (s.powersetCard 1).image (insert a), ∏ i ∈ t, f i
        = f a * ∑ i ∈ s, f i := by
      rw [Finset.sum_image hinj, Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Function.Embedding.coeFn_mk]
      rw [Finset.prod_insert (by simp only [Finset.mem_singleton]; rintro rfl; exact ha hi),
        Finset.prod_singleton]
    rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj, h1,
        Finset.sum_insert ha, Finset.sum_insert ha]
    ring_nf
    ring_nf at ih
    linear_combination ih

theorem esymm1 {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, f i = ∑ i ∈ s, f i := by
  rw [Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem six_esymm3 {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    6 * ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, f i
      = (∑ i ∈ s, f i)^3 - 3*(∑ i ∈ s, f i)*(∑ i ∈ s, (f i)^2) + 2*∑ i ∈ s, (f i)^3 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [show (∅:Finset ℕ).powersetCard 3 = ∅ from rfl]; simp
  | insert a s ha ih =>
    rw [esymm_recur a s ha 2 f, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have he2 := two_esymm2 s f
    linear_combination ih + 3 * f a * he2

theorem twentyfour_esymm4 {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    24 * ∑ t ∈ s.powersetCard 4, ∏ i ∈ t, f i
      = (∑ i ∈ s, f i)^4 - 6*(∑ i ∈ s, f i)^2*(∑ i ∈ s, (f i)^2)
        + 3*(∑ i ∈ s, (f i)^2)^2 + 8*(∑ i ∈ s, f i)*(∑ i ∈ s, (f i)^3)
        - 6*∑ i ∈ s, (f i)^4 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [show (∅:Finset ℕ).powersetCard 4 = ∅ from rfl]; simp
  | insert a s ha ih =>
    rw [esymm_recur a s ha 3 f, Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.sum_insert ha, Finset.sum_insert ha]
    have he3 := six_esymm3 s f
    linear_combination ih + 4 * f a * he3

end A357674dev

namespace A357674dev
open Harm

/-- `∏_{j ∈ Icc 1 m} (a + j) * a! = (a + m)!`. -/
theorem prod_Icc_shift_factorial (a m : ℕ) :
    (∏ j ∈ Icc 1 m, (a + j)) * a ! = (a + m)! := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [mul_comm (∏ j ∈ Icc 1 n, (a + j)) (a + (n+1)), mul_assoc, ih]
    rw [show a + (n + 1) = (a + n) + 1 by ring, Nat.factorial_succ]

theorem choose_prod_nat (p : ℕ) (hp : 1 ≤ p) :
    (3 * p).choose p * (p - 1)! = 3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i) := by
  have key : ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!)
           = (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!) := by
    have hL : ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!) = (3 * p)! := by
      have h1 : (p - 1)! * p = p ! := by
        rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
      calc ((3 * p).choose p * (p - 1)!) * (p * (2 * p)!)
          = (3 * p).choose p * ((p - 1)! * p) * (2 * p)! := by ring
        _ = (3 * p).choose p * p ! * (2 * p)! := by rw [h1]
        _ = (3 * p).choose p * p ! * (3 * p - p)! := by congr 2; omega
        _ = (3 * p)! := Nat.choose_mul_factorial_mul_factorial (by omega)
    have hR : (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!) = (3 * p)! := by
      have hlast : ∏ i ∈ Icc 1 p, (2 * p + i)
          = (∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (2 * p + p) := by
        have h := Finset.prod_Icc_succ_top (a := 1) (b := p - 1)
          (f := fun i => 2 * p + i) (by omega)
        rw [show p - 1 + 1 = p by omega] at h
        exact h
      have hfull : (∏ i ∈ Icc 1 p, (2 * p + i)) * (2 * p)! = (3 * p)! := by
        have := prod_Icc_shift_factorial (2 * p) p
        rwa [show 2 * p + p = 3 * p by ring] at this
      calc (3 * ∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (p * (2 * p)!)
          = ((∏ i ∈ Icc 1 (p - 1), (2 * p + i)) * (2 * p + p)) * (2 * p)! := by ring_nf
        _ = (∏ i ∈ Icc 1 p, (2 * p + i)) * (2 * p)! := by rw [hlast]
        _ = (3 * p)! := hfull
    rw [hL, hR]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

theorem S1_eq (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ range (2 * p + 1), (p + k - 1).choose k = (3 * p).choose p := by
  have hstep : ∀ k ∈ range (2 * p + 1), (p + k - 1).choose k = (p - 1 + k).choose (p - 1) := by
    intro k _
    have he : p + k - 1 = p - 1 + k := by omega
    rw [he, ← Nat.choose_symm (show k ≤ p - 1 + k by omega)]
    congr 1; omega
  rw [Finset.sum_congr rfl hstep]
  have hreindex : ∑ k ∈ range (2 * p + 1), (p - 1 + k).choose (p - 1)
      = ∑ m ∈ Icc (p - 1) (3 * p - 1), m.choose (p - 1) := by
    apply Finset.sum_nbij' (fun k => p - 1 + k) (fun m => m - (p - 1))
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; omega
    · intro k hk; rfl
  rw [hreindex, Nat.sum_Icc_choose]
  congr 1 <;> omega

/-- Cast form of S1: `C(3p,p) = 3 * ∏(1 + 2p/i)` in `ZMod (p^5)`. -/
theorem S1cast (p : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    ((3 * p).choose p : ZMod (p^5))
      = 3 * ∏ i ∈ Icc 1 (p-1), (1 + 2*(p:ZMod (p^5))*((i:ZMod (p^5))⁻¹)) := by
  set F : ZMod (p^5) := ∏ i ∈ Icc 1 (p-1), (i:ZMod (p^5)) with hFdef
  have hunit : ∀ i ∈ Icc 1 (p-1), IsUnit ((i:ZMod (p^5))) := by
    intro i hi; simp only [mem_Icc] at hi; exact isUnit_cast p 5 i hi.1 hi.2
  have hFunit : IsUnit F := by
    rw [hFdef]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one hunit
  -- cast the nat identity
  have hcast : ((3 * p).choose p : ZMod (p^5)) * ((p-1)! : ZMod (p^5))
      = 3 * ∏ i ∈ Icc 1 (p-1), ((2*p+i : ℕ) : ZMod (p^5)) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p^5))) (choose_prod_nat p hp)
    push_cast at this ⊢
    convert this using 2
  -- (p-1)! cast = F
  have hFfact : ((p-1)! : ZMod (p^5)) = F := by
    have := prod_Icc_shift_factorial 0 (p-1)
    simp only [Nat.zero_add, Nat.factorial_zero, mul_one] at this
    rw [hFdef, ← this]; push_cast; rfl
  -- ∏(2p+i) = F * P
  have hsplit : ∏ i ∈ Icc 1 (p-1), ((2*p+i : ℕ) : ZMod (p^5))
      = F * ∏ i ∈ Icc 1 (p-1), (1 + 2*(p:ZMod (p^5))*((i:ZMod (p^5))⁻¹)) := by
    rw [hFdef, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hu : (i:ZMod (p^5)) * ((i:ZMod (p^5))⁻¹) = 1 := ZMod.mul_inv_of_unit _ (hunit i hi)
    push_cast
    linear_combination (-2*(p:ZMod (p^5))) * hu
  rw [hFfact] at hcast
  rw [hsplit] at hcast
  -- hcast : C * F = 3 * (F * P) = (3*P)*F
  apply hFunit.mul_right_cancel
  rw [hcast]; ring

end A357674dev

namespace Harm

/-- Per-term reflection identity for the cube sum, in `ZMod (p^2)`. -/
theorem refl_inv3_term (p j : ℕ) [Fact p.Prime] (hj1 : 1 ≤ j) (hj2 : j ≤ p-1) :
    ((j:ZMod (p^2)))⁻¹^3 + (((p-j:ℕ):ZMod (p^2)))⁻¹^3
      = -3*(p:ZMod (p^2))*((j:ZMod (p^2)))⁻¹^4 := by
  set x := (j:ZMod (p^2)) with hx
  set P := (p:ZMod (p^2)) with hP
  have hu : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_cast p 2 j hj1 hj2)
  have hP2 : P * P = 0 := by
    have h : ((p*p:ℕ):ZMod (p^2)) = 0 := by rw [show p*p = p^2 by ring]; exact ZMod.natCast_self _
    push_cast at h; rw [hP]; exact h
  have hpj : ((p-j:ℕ):ZMod (p^2)) = P - x := by
    rw [Nat.cast_sub (by omega : j ≤ p)]
  have hunit2 : IsUnit (P - x) := by
    rw [← hpj]; exact isUnit_cast p 2 (p-j) (by omega) (by omega)
  have hwform : (P - x)⁻¹ = -(x⁻¹ + P*x⁻¹*x⁻¹) := by
    apply ZMod.inv_eq_of_mul_eq_one
    linear_combination (P*x⁻¹+1)*hu - x⁻¹*x⁻¹*hP2
  rw [hpj, hwform]
  linear_combination (-(3*x⁻¹^5 + P*x⁻¹^6))*hP2

/-- `p^2 ∣ H3` in `ZMod (p^5)`. -/
theorem H3_dvd (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (p:ZMod (p^5))^2 ∣ H p (p^5) 3 := by
  haveI : NeZero (p^5) := ⟨pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero⟩
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero⟩
  apply dvd_of_castHom_zero p 5 2 (pow_dvd_pow p (by omega))
  rw [castHom_H]
  -- goal: H p (p^2) 3 = 0
  have hP2 : (p:ZMod (p^2)) * (p:ZMod (p^2)) = 0 := by
    have h : ((p*p:ℕ):ZMod (p^2)) = 0 := by rw [show p*p = p^2 by ring]; exact ZMod.natCast_self _
    push_cast at h; exact h
  have hb : (p:ZMod (p^2)) ∣ H p (p^2) 4 := by
    have hh := dvd_of_castHom_zero p 2 1 (pow_dvd_pow p (by omega)) (H p (p^2) 4) ?_
    · simpa using hh
    · rw [castHom_H]; show H p (p^1) 4 = 0
      rw [pow_one]; unfold H
      rw [sum_inv_pow_eq p 4 (by omega), sum_pow_zmod p 4 (by omega)]
  have key : (2:ZMod (p^2)) * H p (p^2) 3 = -3*(p:ZMod (p^2)) * H p (p^2) 4 := by
    unfold H
    rw [two_mul]
    nth_rewrite 2 [refl_sum p (by omega) (fun j => ((j:ZMod (p^2)))⁻¹^3)]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mem_Icc] at hj
    rw [refl_inv3_term p j hj.1 hj.2]
  have h0 : (2:ZMod (p^2)) * H p (p^2) 3 = 0 := by
    rw [key]; obtain ⟨s, hs⟩ := hb; rw [hs]
    have : -3*(p:ZMod (p^2))*((p:ZMod (p^2))*s) = -3*((p:ZMod (p^2))*(p:ZMod (p^2)))*s := by ring
    rw [this, hP2, mul_zero, zero_mul]
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    have hc : ((2:ℕ) : ZMod (p^2)) = 2 := by push_cast; ring
    rw [← hc, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out (p:=p.Prime))).mpr (by omega)).pow_right 2
  exact h2unit.mul_right_eq_zero.mp h0

end Harm

namespace A357674dev
open Harm

theorem powersetCard_const_mul {R : Type*} [CommRing R] (s : Finset ℕ) (m : ℕ) (c : R)
    (u : ℕ → R) :
    ∑ t ∈ s.powersetCard m, ∏ j ∈ t, (c * u j)
      = c^m * ∑ t ∈ s.powersetCard m, ∏ j ∈ t, u j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2]

/-- The S1 supercongruence form: `C(3p,p) ≡ 3 + 6p H1 - 6p² H2 (mod p⁵)`. -/
theorem S1_form (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((3*p).choose p : ZMod (p^5))
      = 3 + 6*(p:ZMod (p^5))*H p (p^5) 1 - 6*(p:ZMod (p^5))^2*H p (p^5) 2 := by
  have hp1 : 1 ≤ p := by omega
  rw [S1cast p hp1]
  set q := (p:ZMod (p^5)) with hq
  set f : ℕ → ZMod (p^5) := fun i => (i:ZMod (p^5))⁻¹ with hf
  have hdvd : ∀ i ∈ Icc 1 (p-1), q ∣ 2*q*(f i) := fun i _ => ⟨2*(f i), by ring⟩
  have hexp := prod_expand5 p (fun i => 2*q*(f i)) (by omega) hdvd
  have hprod : (∏ i ∈ Icc 1 (p-1), (1 + 2*q*((i:ZMod (p^5))⁻¹)))
      = ∑ m ∈ range 5, (2*q)^m * (∑ t ∈ (Icc 1 (p-1)).powersetCard m, ∏ j ∈ t, f j) := by
    rw [show (∏ i ∈ Icc 1 (p-1), (1 + 2*q*((i:ZMod (p^5))⁻¹)))
          = ∏ i ∈ Icc 1 (p-1), (1 + (fun i => 2*q*(f i)) i) from rfl, hexp]
    apply Finset.sum_congr rfl
    intro m _
    exact powersetCard_const_mul (Icc 1 (p-1)) m (2*q) f
  rw [hprod]
  -- power sums = harmonic sums
  have hPS : ∀ r, 1 ≤ r → ∑ i ∈ Icc 1 (p-1), (f i)^r = H p (p^5) r := by
    intro r _; rfl
  have hs1 : ∑ i ∈ Icc 1 (p-1), f i = H p (p^5) 1 := by
    rw [← hPS 1 (by omega)]; apply Finset.sum_congr rfl; intro i _; rw [pow_one]
  -- esymm to H
  have he0 : ∑ t ∈ (Icc 1 (p-1)).powersetCard 0, ∏ j ∈ t, f j = 1 := by
    simp [Finset.powersetCard_zero]
  have he1 : ∑ t ∈ (Icc 1 (p-1)).powersetCard 1, ∏ j ∈ t, f j = H p (p^5) 1 := by
    rw [esymm1]; exact hs1
  have he2 : 2 * ∑ t ∈ (Icc 1 (p-1)).powersetCard 2, ∏ j ∈ t, f j
      = (H p (p^5) 1)^2 - H p (p^5) 2 := by
    rw [two_esymm2, hs1, hPS 2 (by omega)]
  have he3 : 6 * ∑ t ∈ (Icc 1 (p-1)).powersetCard 3, ∏ j ∈ t, f j
      = (H p (p^5) 1)^3 - 3*(H p (p^5) 1)*(H p (p^5) 2) + 2*H p (p^5) 3 := by
    rw [six_esymm3, hs1, hPS 2 (by omega), hPS 3 (by omega)]
  have he4 : 24 * ∑ t ∈ (Icc 1 (p-1)).powersetCard 4, ∏ j ∈ t, f j
      = (H p (p^5) 1)^4 - 6*(H p (p^5) 1)^2*(H p (p^5) 2)
      + 3*(H p (p^5) 2)^2 + 8*(H p (p^5) 1)*(H p (p^5) 3) - 6*H p (p^5) 4 := by
    rw [twentyfour_esymm4, hs1, hPS 2 (by omega), hPS 3 (by omega), hPS 4 (by omega)]
  -- divisibilities
  obtain ⟨A, hA⟩ := H1_dvd p (by omega)
  obtain ⟨B, hB⟩ := H_dvd_p p 2 (by omega) (by omega)
  obtain ⟨C, hC⟩ := H3_dvd p hp
  obtain ⟨D, hD⟩ := H_dvd_p p 4 (by omega) (by omega)
  have pN5 : q^5 = 0 := by rw [hq, ← Nat.cast_pow]; exact ZMod.natCast_self _
  -- expand range 5 sum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [hA, hB, hC, hD] at he1 he2 he3 he4 ⊢
  linear_combination 3*he0 + (6*q)*he1 + (6*q^2)*he2 + (4*q^3)*he3 + (2*q^4)*he4
    + (6*q*A^2 + 4*q^4*A^3 - 12*q*A*B + 8*C + 2*q^7*A^4 - 12*q^4*A^2*B + 6*q*B^2
        + 16*q^3*A*C - 12*D)*pN5

/-- Nat identity for `c_k = C(p+k-1,k)`: `c_k * (p-1)! = ∏_{i=1}^{p-1}(k+i)`. -/
theorem choose_c_nat (p k : ℕ) (hp : 1 ≤ p) :
    (p + k - 1).choose k * (p - 1)! = ∏ i ∈ Icc 1 (p - 1), (k + i) := by
  have hshift : (∏ i ∈ Icc 1 (p-1), (k + i)) * k ! = (k + (p-1))! :=
    prod_Icc_shift_factorial k (p-1)
  have hchoose : (p + k - 1).choose k * (k ! * (p-1)!) = (p + k - 1)! := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ p + k - 1 by omega)
    rw [show p + k - 1 - k = p - 1 by omega] at this
    rw [← this]; ring
  have hkp : k + (p - 1) = p + k - 1 := by omega
  rw [hkp] at hshift
  -- choose * (p-1)! * k! = ∏(k+i) * k!
  apply Nat.eq_of_mul_eq_mul_right (show 0 < k ! from Nat.factorial_pos k)
  calc (p + k - 1).choose k * (p-1)! * k !
      = (p + k - 1).choose k * (k ! * (p-1)!) := by ring
    _ = (p + k - 1)! := hchoose
    _ = (∏ i ∈ Icc 1 (p-1), (k + i)) * k ! := hshift.symm

/-- Cast form of `c_k`. -/
theorem choose_c_cast (p k : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    ((p + k - 1).choose k : ZMod (p^5))
      = ∏ i ∈ Icc 1 (p-1), (1 + (k:ZMod (p^5))*((i:ZMod (p^5))⁻¹)) := by
  set F : ZMod (p^5) := ∏ i ∈ Icc 1 (p-1), (i:ZMod (p^5)) with hFdef
  have hunit : ∀ i ∈ Icc 1 (p-1), IsUnit ((i:ZMod (p^5))) := by
    intro i hi; simp only [mem_Icc] at hi; exact isUnit_cast p 5 i hi.1 hi.2
  have hFunit : IsUnit F := by
    rw [hFdef]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one hunit
  have hcast : ((p + k - 1).choose k : ZMod (p^5)) * ((p-1)! : ZMod (p^5))
      = ∏ i ∈ Icc 1 (p-1), ((k+i : ℕ) : ZMod (p^5)) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p^5))) (choose_c_nat p k hp)
    push_cast at this ⊢
    convert this using 2
  have hFfact : ((p-1)! : ZMod (p^5)) = F := by
    have := prod_Icc_shift_factorial 0 (p-1)
    simp only [Nat.zero_add, Nat.factorial_zero, mul_one] at this
    rw [hFdef, ← this]; push_cast; rfl
  have hsplit : ∏ i ∈ Icc 1 (p-1), ((k+i : ℕ) : ZMod (p^5))
      = F * ∏ i ∈ Icc 1 (p-1), (1 + (k:ZMod (p^5))*((i:ZMod (p^5))⁻¹)) := by
    rw [hFdef, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hu : (i:ZMod (p^5)) * ((i:ZMod (p^5))⁻¹) = 1 := ZMod.mul_inv_of_unit _ (hunit i hi)
    push_cast
    linear_combination (-(k:ZMod (p^5))) * hu
  rw [hFfact, hsplit] at hcast
  apply hFunit.mul_right_cancel
  rw [hcast]; ring

end A357674dev

namespace Harm

/-- Inverse of `P - x` expanded mod `p^5`. -/
theorem inv_sub_expand (p j : ℕ) [Fact p.Prime] (hj1 : 1 ≤ j) (hj2 : j ≤ p-1) :
    (((p:ZMod (p^5)) - (j:ZMod (p^5)))⁻¹)
      = -(((j:ZMod (p^5)))⁻¹ + (p:ZMod (p^5))*((j:ZMod (p^5)))⁻¹^2
        + (p:ZMod (p^5))^2*((j:ZMod (p^5)))⁻¹^3 + (p:ZMod (p^5))^3*((j:ZMod (p^5)))⁻¹^4
        + (p:ZMod (p^5))^4*((j:ZMod (p^5)))⁻¹^5) := by
  set x := (j:ZMod (p^5)) with hx
  set P := (p:ZMod (p^5)) with hP
  have hu : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_cast p 5 j hj1 hj2)
  have hP5 : P^5 = 0 := by rw [hP, ← Nat.cast_pow]; exact ZMod.natCast_self _
  apply ZMod.inv_eq_of_mul_eq_one
  linear_combination (1 + P*x⁻¹ + P^2*x⁻¹^2 + P^3*x⁻¹^3 + P^4*x⁻¹^4)*hu - x⁻¹^5*hP5

/-- Per-term reflection for `H1`. -/
theorem refl_H1_term (p j : ℕ) [Fact p.Prime] (hj1 : 1 ≤ j) (hj2 : j ≤ p-1) :
    ((j:ZMod (p^5)))⁻¹ + (((p-j:ℕ):ZMod (p^5)))⁻¹
      = -((p:ZMod (p^5))*((j:ZMod (p^5)))⁻¹^2 + (p:ZMod (p^5))^2*((j:ZMod (p^5)))⁻¹^3
        + (p:ZMod (p^5))^3*((j:ZMod (p^5)))⁻¹^4 + (p:ZMod (p^5))^4*((j:ZMod (p^5)))⁻¹^5) := by
  have hpj : ((p-j:ℕ):ZMod (p^5)) = (p:ZMod (p^5)) - (j:ZMod (p^5)) := by
    rw [Nat.cast_sub (by omega : j ≤ p)]
  rw [hpj, inv_sub_expand p j hj1 hj2]; ring

/-- Reflection identity: `2 H1 = -(p H2 + p² H3 + p³ H4 + p⁴ H5)` in `ZMod (p^5)`. -/
theorem refl_H1 (p : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    2 * H p (p^5) 1 = -((p:ZMod (p^5))*H p (p^5) 2 + (p:ZMod (p^5))^2*H p (p^5) 3
      + (p:ZMod (p^5))^3*H p (p^5) 4 + (p:ZMod (p^5))^4*H p (p^5) 5) := by
  have hH1 : H p (p^5) 1 = ∑ j ∈ Icc 1 (p-1), ((j:ZMod (p^5)))⁻¹ := by
    unfold H; apply Finset.sum_congr rfl; intro j _; rw [pow_one]
  rw [two_mul]
  nth_rewrite 2 [hH1]
  nth_rewrite 1 [hH1]
  nth_rewrite 2 [refl_sum p (by omega) (fun j => ((j:ZMod (p^5)))⁻¹)]
  rw [← Finset.sum_add_distrib]
  have hRHS : (p:ZMod (p^5))*H p (p^5) 2 + (p:ZMod (p^5))^2*H p (p^5) 3
      + (p:ZMod (p^5))^3*H p (p^5) 4 + (p:ZMod (p^5))^4*H p (p^5) 5
      = ∑ j ∈ Icc 1 (p-1), ((p:ZMod (p^5))*((j:ZMod (p^5)))⁻¹^2
        + (p:ZMod (p^5))^2*((j:ZMod (p^5)))⁻¹^3 + (p:ZMod (p^5))^3*((j:ZMod (p^5)))⁻¹^4
        + (p:ZMod (p^5))^4*((j:ZMod (p^5)))⁻¹^5) := by
    unfold H
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hRHS, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mem_Icc] at hj
  rw [refl_H1_term p j hj.1 hj.2]

end Harm

namespace Harm

/-- The doubling map `j ↦ 2j mod p` is injective on `Icc 1 (p-1)`. -/
theorem double_injOn (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    Set.InjOn (fun j => 2*j % p) (Finset.Icc 1 (p-1)) := by
  have hpr := Fact.out (p := p.Prime)
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  simp only [] at hab
  have hm : 2*a ≡ 2*b [MOD p] := hab
  have hco : Nat.gcd p 2 = 1 := (Nat.coprime_primes hpr Nat.prime_two).mpr (by omega)
  have : a ≡ b [MOD p] := Nat.ModEq.cancel_left_of_coprime hco hm
  exact Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega)

/-- The doubling map's image is all of `Icc 1 (p-1)`. -/
theorem double_image (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (Finset.Icc 1 (p-1)).image (fun j => 2*j % p) = Finset.Icc 1 (p-1) := by
  have hpr := Fact.out (p := p.Prime)
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx ⊢
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hx
    have hlt : 2*j % p < p := Nat.mod_lt _ (by omega)
    have hne : 2*j % p ≠ 0 := by
      intro hzero
      have hdvd : p ∣ 2*j := Nat.dvd_of_mod_eq_zero hzero
      rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
    omega
  · rw [Finset.card_image_of_injOn (double_injOn p hp)]

/-- Reindexing a sum by the doubling bijection. -/
theorem double_reindex (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) {M : Type*} [AddCommMonoid M]
    (g : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 (p-1), g (2*j % p) = ∑ j ∈ Finset.Icc 1 (p-1), g j := by
  rw [← Finset.sum_image (g := fun j => 2*j % p)
        (fun a ha b hb => double_injOn p hp ha hb), double_image p hp]

/-- Per-term mult-by-2 expansion for `u²` in `ZMod (p^3)`. -/
theorem double_term (p j : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hj1 : 1 ≤ j) (hj2 : j ≤ p-1) :
    16 * (((2*j % p : ℕ) : ZMod (p^3))⁻¹)^2
      = 4*((j:ZMod (p^3))⁻¹)^2
        + 4*((2*j/p : ℕ):ZMod (p^3))*(p:ZMod (p^3))*((j:ZMod (p^3))⁻¹)^3
        + 3*((2*j/p : ℕ):ZMod (p^3))*(p:ZMod (p^3))^2*((j:ZMod (p^3))⁻¹)^4 := by
  set x := (j:ZMod (p^3)) with hxd
  set P := (p:ZMod (p^3)) with hPd
  set c := ((2*j/p : ℕ):ZMod (p^3)) with hcd
  set y := (((2*j % p : ℕ)):ZMod (p^3)) with hyd
  have hx : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_cast p 3 j hj1 hj2)
  have hyu : IsUnit y := by
    rw [hyd]
    have hlt : 2*j % p < p := Nat.mod_lt _ (by omega)
    have hpr := Fact.out (p := p.Prime)
    have hne : 2*j % p ≠ 0 := by
      intro hzero
      have hdvd : p ∣ 2*j := Nat.dvd_of_mod_eq_zero hzero
      rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
    exact isUnit_cast p 3 (2*j % p) (by omega) (by omega)
  have hyinv : y * y⁻¹ = 1 := ZMod.mul_inv_of_unit _ hyu
  have hd2 : 2*j/p < 2 := Nat.div_lt_of_lt_mul (by omega : 2*j < p*2)
  set q := 2*j/p with hqd
  clear_value q
  have hnn : q*q = q := by rcases (by omega : q = 0 ∨ q = 1) with h | h <;> rw [h]
  have hcc : c * c = c := by rw [hcd, ← Nat.cast_mul, hnn]
  have hP3 : P^3 = 0 := by rw [hPd, ← Nat.cast_pow]; exact ZMod.natCast_self _
  have hdm := Nat.div_add_mod (2*j) p
  have hyrel : y = 2*x - c*P := by
    have hc := congrArg (fun n : ℕ => (n:ZMod (p^3))) hdm
    push_cast at hc
    rw [hyd, hxd, hcd, hPd, hqd]
    linear_combination hc
  -- Q = 4w + 2cPw² + cP²w³,  y * Q = 8
  have hQ : y * (4*x⁻¹+2*c*P*x⁻¹^2+c*P^2*x⁻¹^3) = 8 := by
    rw [hyrel]
    linear_combination (8+4*c*P*x⁻¹+2*c*P^2*x⁻¹^2)*hx + (-2*P^2*x⁻¹^2)*hcc + (-c^2*x⁻¹^3)*hP3
  have hQv : (4*x⁻¹+2*c*P*x⁻¹^2+c*P^2*x⁻¹^3) = 8*y⁻¹ := by
    apply hyu.mul_left_cancel
    rw [hQ, show y*(8*y⁻¹)=8*(y*y⁻¹) by ring, hyinv, mul_one]
  have hQ2 : (4*x⁻¹+2*c*P*x⁻¹^2+c*P^2*x⁻¹^3)^2
      = 4*(4*x⁻¹^2 + 4*c*P*x⁻¹^3 + 3*c*P^2*x⁻¹^4) := by
    linear_combination (4*P^2*x⁻¹^4)*hcc + (4*c^2*x⁻¹^5+c^2*P*x⁻¹^6)*hP3
  have h64 : 64 * y⁻¹^2 = 4*(4*x⁻¹^2 + 4*c*P*x⁻¹^3 + 3*c*P^2*x⁻¹^4) := by
    rw [← hQ2, hQv]; ring
  have hpr := Fact.out (p := p.Prime)
  have h4u : IsUnit (4 : ZMod (p^3)) := by
    have hc4 : ((4:ℕ):ZMod (p^3)) = 4 := by push_cast; ring
    rw [← hc4, ZMod.isUnit_iff_coprime]
    have : Nat.Coprime 4 p := by
      have := ((Nat.coprime_primes Nat.prime_two hpr).mpr (show 2 ≠ p by omega)).pow_left 2
      simpa using this
    exact this.pow_right 3
  apply h4u.mul_left_cancel
  rw [show (4:ZMod (p^3))*(16*y⁻¹^2) = 64*y⁻¹^2 by ring, h64]

/-- Multiplication-by-2 congruence for `H₂` in `ZMod (p^3)`:
`12 H₂ = 4p·S₃ + 3p²·S₄` where `S_r = ∑_{2j>p} u_j^r`. -/
theorem multby2_H2 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    12 * H p (p^3) 2
      = 4*(p:ZMod (p^3)) * (∑ j ∈ Icc 1 (p-1), ((2*j/p:ℕ):ZMod (p^3))*((j:ZMod (p^3))⁻¹)^3)
        + 3*(p:ZMod (p^3))^2 * (∑ j ∈ Icc 1 (p-1), ((2*j/p:ℕ):ZMod (p^3))*((j:ZMod (p^3))⁻¹)^4) := by
  set P := (p:ZMod (p^3)) with hPd
  have hreidx : H p (p^3) 2 = ∑ j ∈ Icc 1 (p-1), (((2*j%p:ℕ):ZMod (p^3))⁻¹)^2 :=
    (double_reindex p hp (fun n => ((n:ZMod (p^3))⁻¹)^2)).symm
  have key : 16 * H p (p^3) 2 = ∑ j ∈ Icc 1 (p-1),
      (4*((j:ZMod (p^3))⁻¹)^2 + 4*((2*j/p:ℕ):ZMod (p^3))*P*((j:ZMod (p^3))⁻¹)^3
        + 3*((2*j/p:ℕ):ZMod (p^3))*P^2*((j:ZMod (p^3))⁻¹)^4) := by
    rw [hreidx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mem_Icc] at hj
    rw [hPd]
    exact double_term p j hp hj.1 hj.2
  have hsum : (∑ j ∈ Icc 1 (p-1),
      (4*((j:ZMod (p^3))⁻¹)^2 + 4*((2*j/p:ℕ):ZMod (p^3))*P*((j:ZMod (p^3))⁻¹)^3
        + 3*((2*j/p:ℕ):ZMod (p^3))*P^2*((j:ZMod (p^3))⁻¹)^4))
      = 4 * H p (p^3) 2
        + 4*P*(∑ j ∈ Icc 1 (p-1), ((2*j/p:ℕ):ZMod (p^3))*((j:ZMod (p^3))⁻¹)^3)
        + 3*P^2*(∑ j ∈ Icc 1 (p-1), ((2*j/p:ℕ):ZMod (p^3))*((j:ZMod (p^3))⁻¹)^4) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · rw [← Finset.mul_sum]; rfl
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hsum] at key
  linear_combination key

/-- Stuffle (off-diagonal) relation: `∑_{i≠j} f_i f_j² = (∑f)(∑f²) − ∑ f³`. -/
theorem stuffle_offdiag {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, f i * (f j)^2
      = (∑ i ∈ s, f i) * (∑ i ∈ s, (f i)^2) - ∑ i ∈ s, (f i)^3 := by
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.add_sum_erase s (fun j => f i * (f j)^2) hi]
  ring

/-- Factored nat identity for `c_k` (1 ≤ k ≤ p-1): isolates the single factor of `p`. -/
theorem choose_c_factored_nat (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    (∏ i ∈ Icc 1 (p-1), (k+i)) * k ! = p ! * ∏ s ∈ Icc 1 (k-1), (p+s) := by
  have hL := A357674dev.prod_Icc_shift_factorial k (p-1)
  have hR := A357674dev.prod_Icc_shift_factorial p (k-1)
  rw [hL, show p ! * (∏ s ∈ Icc 1 (k-1), (p+s)) = (∏ s ∈ Icc 1 (k-1), (p+s)) * p ! from by ring,
    hR]
  congr 1; omega

namespace Harm
/-- `p³ ∣ H₁·H₂` in `ZMod (p^5)` (used to kill `H₁H₂` terms in the assembly). -/
theorem H1H2_dvd (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (p:ZMod (p^5))^3 ∣ H p (p^5) 1 * H p (p^5) 2 := by
  obtain ⟨A, hA⟩ := H1_dvd p (by omega)
  obtain ⟨B, hB⟩ := H_dvd_p p 2 (by omega) (by omega)
  exact ⟨A * B, by rw [hA, hB]; ring⟩
end Harm

/-- For `1 ≤ k ≤ p-1`, the central term `c_k = C(p+k-1,k)` is divisible by `p`. -/
theorem c_k_dvd_p (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hk2 : k ≤ p-1) :
    p ∣ (p+k-1).choose k := by
  have h1 := A357674dev.choose_c_nat p k (by omega)
  have h2 := choose_c_factored_nat p k (by omega) hk1
  have hpf : p ! = p * (p-1)! := (Nat.mul_factorial_pred (by omega : p ≠ 0)).symm
  have key : (p+k-1).choose k * k ! * (p-1)! = (p * ∏ s ∈ Icc 1 (k-1), (p+s)) * (p-1)! := by
    rw [show (p+k-1).choose k * k ! * (p-1)! = ((p+k-1).choose k * (p-1)!) * k ! from by ring,
        h1, h2, hpf]; ring
  have hfact : (p+k-1).choose k * k ! = p * ∏ s ∈ Icc 1 (k-1), (p+s) :=
    Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (p-1)) key
  have hcop : Nat.Coprime p (k !) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, hp.dvd_factorial]; omega
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop ⟨_, hfact⟩

/-- Cast version: `p ∣ c_k` in `ZMod (p^5)` for `1 ≤ k ≤ p-1`. -/
theorem c_k_cast_dvd (p k : ℕ) [Fact p.Prime] (hk1 : 1 ≤ k) (hk2 : k ≤ p-1) :
    (p:ZMod (p^5)) ∣ ((p+k-1).choose k : ZMod (p^5)) := by
  obtain ⟨m, hm⟩ := c_k_dvd_p p k (Fact.out) hk1 hk2
  exact ⟨m, by rw [hm]; push_cast; ring⟩

theorem p5_zero (p : ℕ) [Fact p.Prime] : (p:ZMod (p^5))^5 = 0 := by
  rw [← Nat.cast_pow]; exact ZMod.natCast_self _
