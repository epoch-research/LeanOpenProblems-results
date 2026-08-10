import Mathlib

open Finset

namespace Wolst

/-- Reindexing lemma: summing a function `f` over the casts of `1, …, p-1`
into `ZMod p` is the same as summing `f` over all of `ZMod p`, provided
`f 0 = 0`. -/
theorem sumIcc_eq_sumUniv (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) (hf : f 0 = 0) :
    ∑ k ∈ Finset.Icc 1 (p - 1), f (k : ZMod p) = ∑ x : ZMod p, f x := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have herase : ∑ x : ZMod p, f x = ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), f x :=
    (Finset.sum_erase Finset.univ hf).symm
  rw [herase]
  refine Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · -- hi : (k : ZMod p) ∈ univ.erase 0
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    have hlt : a < p := by
      have := (Fact.out (p := p.Prime)).two_le; omega
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · -- hj : x.val ∈ Icc 1 (p-1)
    intro x hx
    rw [Finset.mem_erase] at hx
    simp only [Finset.mem_Icc]
    have hp2 := (Fact.out (p := p.Prime)).two_le
    have hne : x ≠ 0 := hx.1
    have hval_lt : x.val < p := ZMod.val_lt x
    have hval_ne : x.val ≠ 0 := by
      rw [Ne, ZMod.val_eq_zero]; exact hne
    omega
  · -- left_inv : (↑a).val = a
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hlt : a < p := by
      have := (Fact.out (p := p.Prime)).two_le; omega
    exact ZMod.val_cast_of_lt hlt
  · -- right_inv : ((x.val : ℕ) : ZMod p) = x
    intro x hx
    exact ZMod.natCast_zmod_val x
  · -- h : f (↑a) = f (↑a)
    intro a ha
    rfl

/-- **Wolstenholme's theorem, weak form (W2').**
For a prime `p ≥ 5`, the sum of the squares of the inverses of `1, …, p-1`
vanishes modulo `p`. -/
theorem sum_inv_sq (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  -- Sum of squares over the whole field is zero (since `2 < p - 1`).
  have hcard : ∑ x : ZMod p, x ^ 2 = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2
    rw [ZMod.card]; omega
  -- The map `x ↦ x⁻¹` is a bijection of `ZMod p`.
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    rw [← hcard]
    exact Equiv.sum_comp
      (Equiv.mk (fun x => x⁻¹) (fun x => x⁻¹) (fun x => inv_inv x) (fun x => inv_inv x))
      (fun y => y ^ 2)
  rw [sumIcc_eq_sumUniv p (fun x => (x⁻¹) ^ 2) (by simp)]
  exact hinv

/-- **Wolstenholme's theorem (W1').**
For a prime `p ≥ 5`, the sum of the inverses of `1, …, p-1` vanishes
modulo `p²`. -/
theorem sum_inv (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ = 0 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne'⟩
  -- The reduction homomorphism `ZMod (p^2) → ZMod p`.
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  set φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom hdvd (ZMod p) with hφ
  -- Units: any `1 ≤ m ≤ p-1` casts to a unit in `ZMod (p^2)`.
  have hunitR : ∀ m : ℕ, 1 ≤ m → m ≤ p - 1 → IsUnit ((m : ℕ) : ZMod (p ^ 2)) := by
    intro m hm1 hm2
    rw [ZMod.isUnit_iff_coprime]
    have hnd : ¬ p ∣ m := by
      intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.Coprime.pow_right 2 (((Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr hnd).symm)
  -- `φ` sends the inverse of a unit to the inverse of its image.
  have phi_inv : ∀ a : ZMod (p ^ 2), IsUnit a → φ a⁻¹ = (φ a)⁻¹ := by
    intro a ha
    have h1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
    have h2 : φ a * φ a⁻¹ = 1 := by rw [← map_mul, h1, map_one]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  -- cast of `p - k` modulo `p`.
  have hcast_pk : ∀ k : ℕ, k ≤ p → ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
    intro k hk
    rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub]
  -- The kernel step: if `φ y = 0` then `p * y = 0` in `ZMod (p^2)`.
  have hker : ∀ y : ZMod (p ^ 2), φ y = 0 → (p : ZMod (p ^ 2)) * y = 0 := by
    intro y hy
    have e1 : ((y.val : ℕ) : ZMod p) = 0 := by
      have hh : φ ((y.val : ℕ) : ZMod (p ^ 2)) = ((y.val : ℕ) : ZMod p) := map_natCast φ y.val
      rw [ZMod.natCast_zmod_val] at hh
      rw [← hh, hy]
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).mp e1
    calc (p : ZMod (p ^ 2)) * y
        = (p : ZMod (p ^ 2)) * ((y.val : ℕ) : ZMod (p ^ 2)) := by rw [ZMod.natCast_zmod_val]
      _ = ((p * y.val : ℕ) : ZMod (p ^ 2)) := by push_cast; ring
      _ = ((p ^ 2 * m : ℕ) : ZMod (p ^ 2)) := by rw [hm]; push_cast; ring
      _ = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * (m : ZMod (p ^ 2)) := by push_cast; ring
      _ = 0 := by rw [ZMod.natCast_self]; ring
  -- Reindexing `k ↦ p - k`.
  have hreindex : (∑ k ∈ Finset.Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹)
      = (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹) := by
    refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; rfl
  -- Pairing identity.
  have hpair : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
        = (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hKu := hunitR k hk.1 hk.2
    have hMu := hunitR (p - k) (by omega) (by omega)
    have hK : (k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2)) = 1 := ZMod.inv_mul_of_unit _ hKu
    have hM : ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2)) = 1 :=
      ZMod.inv_mul_of_unit _ hMu
    have hMK : ((p - k : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : k ≤ p)]
    have expand : (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
        * (((p - k : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))
        = (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
      have hh : (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
          * (((p - k : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2)))
          = (k : ZMod (p ^ 2))⁻¹ * (((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2)))
            + ((k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
        ring
      rw [hh, hM, hK, mul_one, one_mul]
    rw [hMK] at expand
    rw [← expand]; ring
  -- `φ Q = 0` by (W2').
  have hφQ : φ (∑ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) = 0 := by
    rw [map_sum]
    have step : ∀ k ∈ Finset.Icc 1 (p - 1),
        φ ((k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹)
          = -(((k : ZMod p))⁻¹) ^ 2 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [map_mul, phi_inv _ (hunitR k hk.1 hk.2), phi_inv _ (hunitR (p - k) (by omega) (by omega))]
      rw [map_natCast, map_natCast, hcast_pk k (by omega), inv_neg]
      ring
    rw [Finset.sum_congr rfl step]
    rw [Finset.sum_neg_distrib, sum_inv_sq p hp5, neg_zero]
  -- Assemble.
  have hpq0 : (p : ZMod (p ^ 2))
      * (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) = 0 :=
    hker _ hφQ
  have hSS : (∑ k ∈ Finset.Icc 1 (p - 1),
        ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹))
      = (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹)
        + (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹) := by
    rw [Finset.sum_add_distrib, hreindex]
  have key : (∑ k ∈ Finset.Icc 1 (p - 1),
        ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹))
      = (p : ZMod (p ^ 2))
        * (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hpair
  have hSum0 : (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹)
      + (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹) = 0 := by
    rw [← hSS, key]; exact hpq0
  -- `2` is a unit in `ZMod (p^2)`.
  have h2unit : IsUnit (2 : ZMod (p ^ 2)) := by
    have hcast : ((2 : ℕ) : ZMod (p ^ 2)) = (2 : ZMod (p ^ 2)) := by norm_num
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hnd : ¬ p ∣ 2 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    exact Nat.Coprime.pow_right 2 (((Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr hnd).symm)
  have hfin : (2 : ZMod (p ^ 2)) * (∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹) = 0 := by
    rw [two_mul]; exact hSum0
  exact (h2unit.mul_right_eq_zero).mp hfin

end Wolst
