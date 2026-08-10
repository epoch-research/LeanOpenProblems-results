import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: sequence definition (statement kept verbatim).
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

section T2_sec
open Nat Finset BigOperators

lemma sum_Icc_erase {p : ℕ} [Fact p.Prime] (g : ZMod p → ZMod p) :
    ∑ i ∈ Finset.Icc 1 (p-1), g ((i:ℕ):ZMod p) = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), g x := by
  apply Finset.sum_nbij' (fun i => ((i:ℕ):ZMod p)) (fun x => x.val)
  · intro i hi; rw [Finset.mem_Icc] at hi
    rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hi.1 (by omega)
  · intro x hx; rw [Finset.mem_erase] at hx; rw [Finset.mem_Icc]
    have hv : x.val < p := ZMod.val_lt x
    have : x.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact hx.1
    omega
  · intro i hi; rw [Finset.mem_Icc] at hi; rw [ZMod.val_natCast_of_lt (by omega)]
  · intro x hx; rw [ZMod.natCast_zmod_val]
  · intro i hi; rfl

lemma sum_inv_pow_zero {p : ℕ} [Fact p.Prime] (j : ℕ) (hj : 0 < j) (hj2 : j < p - 1) :
    ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod p)⁻¹)^j = 0 := by
  rw [sum_Icc_erase (fun x => x⁻¹^j)]
  -- reindex inverse
  have hbij : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), (x⁻¹)^j
            = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^j := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro x hx; rw [Finset.mem_erase] at hx ⊢
      exact ⟨inv_ne_zero hx.1, Finset.mem_univ _⟩
    · intro x hx; rw [Finset.mem_erase] at hx ⊢
      exact ⟨inv_ne_zero hx.1, Finset.mem_univ _⟩
    · intro x hx; rw [Finset.mem_erase] at hx; rw [inv_inv]
    · intro x hx; rw [Finset.mem_erase] at hx; rw [inv_inv]
    · intro x hx; rfl
  rw [hbij]
  -- extend to full univ
  have h0 : (0:ZMod p)^j = 0 := zero_pow hj.ne'
  have : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^j = ∑ x : ZMod p, x^j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:ZMod p)), h0, add_zero]
  rw [this]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [show (p:ℕ) - 1 = Fintype.card (ZMod p) - 1 by rw [hcard]] at hj2
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) j hj2
end T2_sec

section HSums_sec

namespace HSums

open Finset BigOperators

variable (p : ℕ)

/-- j-th harmonic sum over 1..p-1 in ZMod(p^5). -/
noncomputable def H (p j : ℕ) : ZMod (p^5) := ∑ i ∈ Finset.Icc 1 (p-1), ((i:ZMod (p^5))⁻¹)^j

/-- `q p = (p : ZMod (p^5))`. -/
noncomputable def q (p : ℕ) : ZMod (p ^ 5) := (p : ZMod (p ^ 5))

/-- `q p ^ 5 = 0`. -/
lemma q_pow_five (p : ℕ) : (q p) ^ 5 = 0 := by
  show ((p : ZMod (p ^ 5))) ^ 5 = 0
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 5)

/-- In `ZMod n`, if `a` is a unit and `a * b = 1` then `a⁻¹ = b`. -/
lemma inv_eq_of {n : ℕ} (a b : ZMod n) (ha : IsUnit a) (h : a * b = 1) : a⁻¹ = b := by
  calc a⁻¹ = a⁻¹ * (a * b) := by rw [h, mul_one]
    _ = (a⁻¹ * a) * b := by rw [mul_assoc]
    _ = 1 * b := by rw [ZMod.inv_mul_of_unit a ha]
    _ = b := one_mul b

/-- For a prime `p` and `1 ≤ i < p`, the cast of `i` is a unit in `ZMod (p^5)`. -/
lemma isUnit_cast {p : ℕ} (hp : p.Prime) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < p) :
    IsUnit ((i : ℕ) : ZMod (p ^ 5)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hnd : ¬ p ∣ i := Nat.not_dvd_of_pos_of_lt (by omega) h2
  exact ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right 5

/-- An element of `ZMod (p^5)` mapping to `0` under the reduction to `ZMod p` is divisible by `q p`. -/
lemma dvd_of_cast_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 5)) (h : p ∣ p ^ 5)
    (hx : (ZMod.castHom h (ZMod p)) x = 0) : ∃ c, x = q p * c := by
  haveI : NeZero (p ^ 5) := ⟨pow_ne_zero 5 hp.pos.ne'⟩
  have hval : (p : ℕ) ∣ x.val := by
    have key : ((x.val : ℕ) : ZMod p) = 0 := by
      have h1 : (ZMod.castHom h (ZMod p)) ((x.val : ℕ) : ZMod (p ^ 5)) = ((x.val : ℕ) : ZMod p) :=
        map_natCast _ x.val
      rw [ZMod.natCast_zmod_val] at h1
      rw [← h1]; exact hx
    exact (ZMod.natCast_eq_zero_iff x.val p).mp key
  obtain ⟨d, hd⟩ := hval
  refine ⟨(d : ZMod (p ^ 5)), ?_⟩
  have hxv : x = ((p * d : ℕ) : ZMod (p ^ 5)) := by rw [← hd, ZMod.natCast_zmod_val]
  rw [hxv]
  show ((p * d : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) * (d : ZMod (p ^ 5))
  push_cast; ring

/-- `p ∣ H₂`. -/
lemma H_two_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ∃ c : ZMod (p ^ 5), H p 2 = q p * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine dvd_of_cast_zero hp _ D ?_
  have step : (ZMod.castHom D (ZMod p)) (H p 2)
      = ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ℕ) : ZMod p)⁻¹) ^ 2 := by
    rw [H, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [map_pow]
    congr 1
    have hunit : IsUnit ((i : ℕ) : ZMod (p ^ 5)) := isUnit_cast hp i (by omega) (by omega)
    have hmul : ((i : ℕ) : ZMod (p ^ 5)) * ((i : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    have hc := congrArg (ZMod.castHom D (ZMod p)) hmul
    rw [map_mul, map_one, map_natCast] at hc
    -- hc : ((i:ℕ):ZMod p) * (castHom D (ZMod p)) (((i:ℕ):ZMod (p^5))⁻¹) = 1
    have hi0 : ((i : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    calc (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)
        = ((i : ℕ) : ZMod p)⁻¹ * (((i : ℕ) : ZMod p) *
            (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hi0, one_mul]
      _ = ((i : ℕ) : ZMod p)⁻¹ * 1 := by rw [hc]
      _ = ((i : ℕ) : ZMod p)⁻¹ := mul_one _
  rw [step]
  exact sum_inv_pow_zero 2 (by norm_num) (by omega)

/-- `p ∣ H₄`. -/
lemma H_four_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ∃ c : ZMod (p ^ 5), H p 4 = q p * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine dvd_of_cast_zero hp _ D ?_
  have step : (ZMod.castHom D (ZMod p)) (H p 4)
      = ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ℕ) : ZMod p)⁻¹) ^ 4 := by
    rw [H, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [map_pow]
    congr 1
    have hunit : IsUnit ((i : ℕ) : ZMod (p ^ 5)) := isUnit_cast hp i (by omega) (by omega)
    have hmul : ((i : ℕ) : ZMod (p ^ 5)) * ((i : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    have hc := congrArg (ZMod.castHom D (ZMod p)) hmul
    rw [map_mul, map_one, map_natCast] at hc
    have hi0 : ((i : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    calc (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)
        = ((i : ℕ) : ZMod p)⁻¹ * (((i : ℕ) : ZMod p) *
            (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hi0, one_mul]
      _ = ((i : ℕ) : ZMod p)⁻¹ * 1 := by rw [hc]
      _ = ((i : ℕ) : ZMod p)⁻¹ := mul_one _
  rw [step]
  exact sum_inv_pow_zero 4 (by norm_num) (by omega)

/-- The reflection `i ↦ p - i` reindexes the harmonic sums. -/
lemma hbij {p : ℕ} (hp7 : 7 ≤ p) (j : ℕ) :
    ∑ i ∈ Finset.Icc 1 (p - 1), ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ j = H p j := by
  rw [H]
  apply Finset.sum_nbij' (fun i => p - i) (fun i => p - i)
  · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rw [Finset.mem_Icc] at ha; omega
  · intro a ha; rw [Finset.mem_Icc] at ha; omega
  · intro a _; rfl

/-- Per-term inverse expansion via the terminating geometric series. -/
lemma inv_sub_expand {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (i : ℕ) (hi : i ∈ Finset.Icc 1 (p - 1)) :
    ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹)
      = -(((i : ℕ) : ZMod (p ^ 5))⁻¹ + q p * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2
          + (q p) ^ 2 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3
          + (q p) ^ 3 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4
          + (q p) ^ 4 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5) := by
  rw [Finset.mem_Icc] at hi
  have hile : i ≤ p := by omega
  have hunit : IsUnit ((i : ℕ) : ZMod (p ^ 5)) := isUnit_cast hp i (by omega) (by omega)
  have hunit2 : IsUnit (((p - i : ℕ)) : ZMod (p ^ 5)) := isUnit_cast hp (p - i) (by omega) (by omega)
  have hcu : ((i : ℕ) : ZMod (p ^ 5)) * ((i : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hq5 : (q p) ^ 5 = 0 := q_pow_five p
  have hcast : (((p - i : ℕ)) : ZMod (p ^ 5)) = q p - ((i : ℕ) : ZMod (p ^ 5)) := by
    show (((p - i : ℕ)) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) - ((i : ℕ) : ZMod (p ^ 5))
    exact Nat.cast_sub hile
  rw [hcast] at hunit2 ⊢
  refine inv_eq_of _ _ hunit2 ?_
  linear_combination (1 + q p * ((i : ℕ) : ZMod (p ^ 5))⁻¹
      + (q p) ^ 2 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2
      + (q p) ^ 3 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3
      + (q p) ^ 4 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4) * hcu
      - (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5 * hq5

/-- Pairing identity: `2·H₁ = -(q·H₂ + q²·H₃ + q³·H₄ + q⁴·H₅)`. -/
lemma key1 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    2 * H p 1 = -(q p * H p 2 + (q p) ^ 2 * H p 3 + (q p) ^ 3 * H p 4 + (q p) ^ 4 * H p 5) := by
  have hpair : ∀ i ∈ Finset.Icc 1 (p - 1),
      (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1 + ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 1
      = -(q p * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2
          + (q p) ^ 2 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3
          + (q p) ^ 3 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4
          + (q p) ^ 4 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5) := by
    intro i hi
    rw [inv_sub_expand hp hp7 i hi]
    ring
  have e1 : H p 1 = ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1 := rfl
  have e2 : H p 1 = ∑ i ∈ Finset.Icc 1 (p - 1), ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 1 :=
    (hbij hp7 1).symm
  have main : H p 1 + H p 1
      = ∑ i ∈ Finset.Icc 1 (p - 1),
          ((((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1 + ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 1) := by
    rw [Finset.sum_add_distrib, ← e1, ← e2]
  rw [two_mul, main, Finset.sum_congr rfl hpair]
  rw [H, H, H, H, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]

/-- Pairing identity for cubes: `2·H₃ = -(3q·H₄ + 6q²·H₅ + 10q³·H₆ + 15q⁴·H₇)`. -/
lemma key3 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    2 * H p 3 = -(3 * q p * H p 4 + 6 * (q p) ^ 2 * H p 5
      + 10 * (q p) ^ 3 * H p 6 + 15 * (q p) ^ 4 * H p 7) := by
  have hq5 : (q p) ^ 5 = 0 := q_pow_five p
  have hpair : ∀ i ∈ Finset.Icc 1 (p - 1),
      (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 + ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 3
      = -(3 * q p * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4
          + 6 * (q p) ^ 2 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5
          + 10 * (q p) ^ 3 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 6
          + 15 * (q p) ^ 4 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 7) := by
    intro i hi
    rw [inv_sub_expand hp hp7 i hi]
    linear_combination (-(q p) ^ 7 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 15
        - 3 * (q p) ^ 6 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 14
        - 6 * (q p) ^ 5 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 13
        - 10 * (q p) ^ 4 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 12
        - 15 * (q p) ^ 3 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 11
        - 18 * (q p) ^ 2 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 10
        - 19 * (q p) * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 9
        - 18 * (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 8) * hq5
  have e1 : H p 3 = ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 := rfl
  have e2 : H p 3 = ∑ i ∈ Finset.Icc 1 (p - 1), ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 3 :=
    (hbij hp7 3).symm
  have main : H p 3 + H p 3
      = ∑ i ∈ Finset.Icc 1 (p - 1),
          ((((i : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 + ((((p - i : ℕ)) : ZMod (p ^ 5))⁻¹) ^ 3) := by
    rw [Finset.sum_add_distrib, ← e1, ← e2]
  rw [two_mul, main, Finset.sum_congr rfl hpair]
  rw [H, H, H, H, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]

/-- `2` is a unit in `ZMod (p^5)` for `p ≥ 7`. -/
lemma two_isUnit {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : IsUnit (2 : ZMod (p ^ 5)) := by
  have h2 : ((2 : ℕ) : ZMod (p ^ 5)) = 2 := by push_cast; ring
  rw [← h2, ZMod.isUnit_iff_coprime]
  exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right 5

/-- Wolstenholme: `p² ∣ H₁`. -/
lemma H_one_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ c : ZMod (p ^ 5), H p 1 = (q p) ^ 2 * c := by
  obtain ⟨c2, hc2⟩ := H_two_dvd hp hp7
  have hk := key1 hp hp7
  have h2inv : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
    ZMod.inv_mul_of_unit _ (two_isUnit hp hp7)
  refine ⟨(2 : ZMod (p ^ 5))⁻¹ * (-(c2 + H p 3 + q p * H p 4 + (q p) ^ 2 * H p 5)), ?_⟩
  have hstep : (2 : ZMod (p ^ 5)) * H p 1
      = (q p) ^ 2 * (-(c2 + H p 3 + q p * H p 4 + (q p) ^ 2 * H p 5)) := by
    rw [hk, hc2]; ring
  calc H p 1 = (2 : ZMod (p ^ 5))⁻¹ * ((2 : ZMod (p ^ 5)) * H p 1) := by
        rw [← mul_assoc, h2inv, one_mul]
    _ = (2 : ZMod (p ^ 5))⁻¹ * ((q p) ^ 2 * (-(c2 + H p 3 + q p * H p 4 + (q p) ^ 2 * H p 5))) := by
        rw [hstep]
    _ = (q p) ^ 2 * ((2 : ZMod (p ^ 5))⁻¹ * (-(c2 + H p 3 + q p * H p 4 + (q p) ^ 2 * H p 5))) := by
        ring

/-- `p² ∣ H₃`. -/
lemma H_three_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ c : ZMod (p ^ 5), H p 3 = (q p) ^ 2 * c := by
  obtain ⟨c4, hc4⟩ := H_four_dvd hp hp7
  have hk := key3 hp hp7
  have h2inv : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
    ZMod.inv_mul_of_unit _ (two_isUnit hp hp7)
  refine ⟨(2 : ZMod (p ^ 5))⁻¹ *
    (-(3 * c4 + 6 * H p 5 + 10 * q p * H p 6 + 15 * (q p) ^ 2 * H p 7)), ?_⟩
  have hstep : (2 : ZMod (p ^ 5)) * H p 3
      = (q p) ^ 2 * (-(3 * c4 + 6 * H p 5 + 10 * q p * H p 6 + 15 * (q p) ^ 2 * H p 7)) := by
    rw [hk, hc4]; ring
  calc H p 3 = (2 : ZMod (p ^ 5))⁻¹ * ((2 : ZMod (p ^ 5)) * H p 3) := by
        rw [← mul_assoc, h2inv, one_mul]
    _ = (2 : ZMod (p ^ 5))⁻¹ * ((q p) ^ 2 *
          (-(3 * c4 + 6 * H p 5 + 10 * q p * H p 6 + 15 * (q p) ^ 2 * H p 7))) := by rw [hstep]
    _ = (q p) ^ 2 * ((2 : ZMod (p ^ 5))⁻¹ *
          (-(3 * c4 + 6 * H p 5 + 10 * q p * H p 6 + 15 * (q p) ^ 2 * H p 7))) := by ring

/-- Expansion E1 (valid mod `q⁴`): explicit witness for the `q⁴` error term. -/
lemma H_one_expand {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ c : ZMod (p ^ 5), H p 1
      = -(q p * (2 : ZMod (p ^ 5))⁻¹) * (H p 2 + q p * H p 3 + (q p) ^ 2 * H p 4)
        + (q p) ^ 4 * c := by
  have hk := key1 hp hp7
  have h2inv : (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) = 1 :=
    ZMod.inv_mul_of_unit _ (two_isUnit hp hp7)
  refine ⟨-((2 : ZMod (p ^ 5))⁻¹ * H p 5), ?_⟩
  calc H p 1 = (2 : ZMod (p ^ 5))⁻¹ * ((2 : ZMod (p ^ 5)) * H p 1) := by
        rw [← mul_assoc, h2inv, one_mul]
    _ = (2 : ZMod (p ^ 5))⁻¹ *
          (-(q p * H p 2 + (q p) ^ 2 * H p 3 + (q p) ^ 3 * H p 4 + (q p) ^ 4 * H p 5)) := by
        rw [hk]
    _ = -(q p * (2 : ZMod (p ^ 5))⁻¹) * (H p 2 + q p * H p 3 + (q p) ^ 2 * H p 4)
          + (q p) ^ 4 * (-((2 : ZMod (p ^ 5))⁻¹ * H p 5)) := by ring

end HSums
end HSums_sec

section HDefs_sec

/-!
Shared definitions for the S2 decomposition and the star-lemmas.
All in namespace `HSums` alongside `H`, `q`.
-/

open Finset BigOperators

namespace HSums

/-- Partial harmonic sum `∑_{i=1}^m 1/i` in `ZMod (p^5)`. -/
noncomputable def h1 (p m : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 m, ((i : ZMod (p ^ 5))⁻¹)

/-- Partial second harmonic sum `∑_{i=1}^m 1/i²` in `ZMod (p^5)`. -/
noncomputable def h2 (p m : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 m, ((i : ZMod (p ^ 5))⁻¹) ^ 2

/-- `Ta = ∑_{k=1}^{p-1} h1(k-1)/k²`. -/
noncomputable def Ta (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2

/-- `Tbc = ∑_{k=1}^{p-1} (10 h1(k-1)² - 13 h2(k-1) - 16 h1(k-1)/k + 12/k²)/k²`. -/
noncomputable def Tbc (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    (10 * (h1 p (k - 1)) ^ 2 - 13 * (h2 p (k - 1))
      - 16 * (h1 p (k - 1)) * ((k : ZMod (p ^ 5))⁻¹)
      + 12 * ((k : ZMod (p ^ 5))⁻¹) ^ 2) * ((k : ZMod (p ^ 5))⁻¹) ^ 2

/-- The two summations of A357674 (n). -/
def S1 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), (n + k - 1).choose k
def S2 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), ((n + k - 1).choose k) ^ 2

end HSums
end HDefs_sec

section F2_sec

open Finset BigOperators MvPolynomial

namespace F2

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R]

/-- Newton's identity (degree 2), transported through `aeval`. -/
theorem newton2 (v : σ → R) (E P : ℕ → R)
    (hE : ∀ k, E k = ∑ t ∈ powersetCard k univ, ∏ i ∈ t, v i)
    (hP : ∀ k, P k = ∑ i, (v i) ^ k) :
    (2 : R) * E 2 = E 1 * P 1 - E 0 * P 2 := by
  have h := congrArg (aeval v) (MvPolynomial.mul_esymm_eq_sum σ R 2)
  rw [show ((Finset.antidiagonal 2).filter (fun a => a.1 < 2)) = {((0 : ℕ), (2 : ℕ)), (1, 1)}
        from by decide,
     Finset.sum_insert (by decide), Finset.sum_singleton] at h
  simp only [esymm, psum, map_mul, map_natCast, map_pow, map_neg, map_one, map_add, map_sum,
    map_prod, aeval_X, ← hE, ← hP] at h
  push_cast at h
  rw [h]; ring

/-- Newton's identity (degree 3), transported through `aeval`. -/
theorem newton3 (v : σ → R) (E P : ℕ → R)
    (hE : ∀ k, E k = ∑ t ∈ powersetCard k univ, ∏ i ∈ t, v i)
    (hP : ∀ k, P k = ∑ i, (v i) ^ k) :
    (3 : R) * E 3 = E 0 * P 3 - E 1 * P 2 + E 2 * P 1 := by
  have h := congrArg (aeval v) (MvPolynomial.mul_esymm_eq_sum σ R 3)
  rw [show ((Finset.antidiagonal 3).filter (fun a => a.1 < 3))
        = {((0 : ℕ), (3 : ℕ)), (1, 2), (2, 1)} from by decide,
     Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
  simp only [esymm, psum, map_mul, map_natCast, map_pow, map_neg, map_one, map_add, map_sum,
    map_prod, aeval_X, ← hE, ← hP] at h
  push_cast at h
  rw [h]; ring

/-- Newton's identity (degree 4), transported through `aeval`. -/
theorem newton4 (v : σ → R) (E P : ℕ → R)
    (hE : ∀ k, E k = ∑ t ∈ powersetCard k univ, ∏ i ∈ t, v i)
    (hP : ∀ k, P k = ∑ i, (v i) ^ k) :
    (4 : R) * E 4 = -(E 0 * P 4) + E 1 * P 3 - E 2 * P 2 + E 3 * P 1 := by
  have h := congrArg (aeval v) (MvPolynomial.mul_esymm_eq_sum σ R 4)
  rw [show ((Finset.antidiagonal 4).filter (fun a => a.1 < 4))
        = {((0 : ℕ), (4 : ℕ)), (1, 3), (2, 2), (3, 1)} from by decide,
     Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
     Finset.sum_singleton] at h
  simp only [esymm, psum, map_mul, map_natCast, map_pow, map_neg, map_one, map_add, map_sum,
    map_prod, aeval_X, ← hE, ← hP] at h
  push_cast at h
  rw [h]; ring

/-- The product `∏ (1 + c v i)` expands as `∑ c^k e_k`. -/
theorem prod_one_add_expand (v : σ → R) (c : R) :
    ∏ x, (1 + c * v x) = ∑ k ∈ range ((univ : Finset σ).card + 1),
      c ^ k * (∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i) := by
  rw [Finset.prod_one_add, powerset_card_disjiUnion, Finset.sum_disjiUnion]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

end F2

open F2

/-- Expansion of the product form of the central binomial coefficient in `ZMod (p^5)`. -/
theorem L_expand (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∏ i ∈ Finset.Icc 1 (p - 1), (1 + 2 * (HSums.q p) * ((i : ZMod (p ^ 5))⁻¹))
      = 1 + 2 * (HSums.q p) * (HSums.H p 1) - 2 * (HSums.q p) ^ 2 * (HSums.H p 2) := by
  set R := ZMod (p ^ 5) with hR
  set q := HSums.q p with hq
  -- work over the subtype of `Icc 1 (p-1)`
  let σ := ↥(Finset.Icc 1 (p - 1))
  let v : σ → R := fun x => (((x : ℕ) : R))⁻¹
  let E : ℕ → R := fun k => ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i
  let P : ℕ → R := fun k => ∑ i, (v i) ^ k
  have hE : ∀ k, E k = ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i := fun _ => rfl
  have hP : ∀ k, P k = ∑ i, (v i) ^ k := fun _ => rfl
  -- P k = H p k
  have hPH : ∀ k, P k = HSums.H p k := by
    intro k
    rw [hP, HSums.H]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 (p - 1)) (fun n => (((n : ℕ) : R))⁻¹ ^ k)]
  -- L as a product over σ
  have hprod : ∏ i ∈ Finset.Icc 1 (p - 1), (1 + 2 * q * ((i : R)⁻¹))
      = ∏ x : σ, (1 + (2 * q) * v x) := by
    rw [← Finset.prod_coe_sort (Finset.Icc 1 (p - 1)) (fun n => 1 + 2 * q * (((n : ℕ) : R))⁻¹)]
  -- expand
  have hcardσ : (univ : Finset σ).card = p - 1 := by
    rw [Finset.card_univ, Fintype.card_coe, Nat.card_Icc]; omega
  rw [hprod, prod_one_add_expand v (2 * q)]
  -- reduce to range 5
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  have hreduce : ∑ k ∈ range ((univ : Finset σ).card + 1),
        (2 * q) ^ k * (∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i)
      = ∑ k ∈ range 5, (2 * q) ^ k * E k := by
    symm
    apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    have : (2 * q) ^ k = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [pow_add, mul_pow, hq5]; ring
    rw [this, zero_mul]
  rw [hreduce]
  -- expand the range-5 sum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- E 0 = 1
  have hE0 : E 0 = 1 := by rw [hE]; simp [Finset.powersetCard_zero]
  -- E 1 = P 1
  have hE1P1 : E 1 = P 1 := by
    rw [hE, hP]; simp [Finset.powersetCard_one, Finset.sum_map, pow_one]
  -- Newton relations
  have hn2 := newton2 v E P hE hP
  have hn3 := newton3 v E P hE hP
  have hn4 := newton4 v E P hE hP
  -- divisibilities
  obtain ⟨a, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨b, hH2⟩ := HSums.H_two_dvd hp hp7
  obtain ⟨cc, hH3⟩ := HSums.H_three_dvd hp hp7
  obtain ⟨d, hH4⟩ := HSums.H_four_dvd hp hp7
  -- E 1 = H p 1
  have hE1H : E 1 = HSums.H p 1 := by rw [hE1P1, hPH 1]
  -- rewrite P into H, and substitute E 0, E 1, in the Newton relations
  rw [hPH 1, hPH 2, hE1H, hE0] at hn2
  rw [hPH 3, hPH 2, hPH 1, hE0, hE1H] at hn3
  rw [hPH 4, hPH 3, hPH 2, hPH 1, hE0, hE1H] at hn4
  -- fold `HSums.q p` to `q`
  rw [← hq] at hH1 hH2 hH3 hH4
  -- units
  have h3u : IsUnit (3 : R) := by
    rw [show (3 : R) = ((3 : ℕ) : R) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right 5
  have h4u : IsUnit (4 : R) := by
    rw [show (4 : R) = ((4 : ℕ) : R) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact ((this.pow_left 2).pow_right 5)
  -- q^3 E 3 = 0
  have hq3E3 : q ^ 3 * E 3 = 0 := by
    have h3z : (3 : R) * (q ^ 3 * E 3) = 0 := by
      rw [hH1, hH2, hH3] at hn3
      linear_combination (q ^ 3) * hn3 + (cc - q * a * b + a * E 2) * hq5
    exact (h3u.mul_right_eq_zero).mp h3z
  -- q^4 E 4 = 0
  have hq4E4 : q ^ 4 * E 4 = 0 := by
    have h4z : (4 : R) * (q ^ 4 * E 4) = 0 := by
      rw [hH1, hH2, hH3, hH4] at hn4
      linear_combination (q ^ 4) * hn4 + (-d + q ^ 3 * a * cc - b * E 2 + q * a * E 3) * hq5
    exact (h4u.mul_right_eq_zero).mp h4z
  -- q^2 * H1^2 vanishes, giving the E 2 term
  have hv2 : (2 * q) ^ 2 * E 2 = -(2 * q ^ 2 * HSums.H p 2) := by
    rw [hH1] at hn2
    linear_combination (2 * q ^ 2) * hn2 + (2 * q * a ^ 2) * hq5
  have hv3 : (2 * q) ^ 3 * E 3 = 0 := by
    have : (2 * q) ^ 3 * E 3 = 8 * (q ^ 3 * E 3) := by ring
    rw [this, hq3E3, mul_zero]
  have hv4 : (2 * q) ^ 4 * E 4 = 0 := by
    have : (2 * q) ^ 4 * E 4 = 16 * (q ^ 4 * E 4) := by ring
    rw [this, hq4E4, mul_zero]
  -- assemble
  rw [hE0, hE1H, hv2, hv3, hv4]
  ring

/-- The ℕ product identity behind the central binomial coefficient. -/
theorem choose_prod_nat (p : ℕ) (hp7 : 7 ≤ p) :
    (3 * p).choose p * (∏ i ∈ Finset.Icc 1 (p - 1), i)
      = 3 * (∏ i ∈ Finset.Icc 1 (p - 1), (i + 2 * p)) := by
  rw [show (∏ i ∈ Finset.Icc 1 (p - 1), i) = (p - 1).factorial from by
        rw [show Finset.Icc 1 (p - 1) = Finset.Ico 1 p from by
              ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
            Finset.prod_Ico_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial]
        exact Finset.prod_congr rfl (fun i _ => by ring),
      show (∏ i ∈ Finset.Icc 1 (p - 1), (i + 2 * p)) = (2 * p + 1).ascFactorial (p - 1) from by
        rw [Nat.ascFactorial_eq_prod_range,
            show Finset.Icc 1 (p - 1) = Finset.Ico 1 p from by
              ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
            Finset.prod_Ico_eq_prod_range]
        exact Finset.prod_congr (by congr 1) (fun i _ => by ring)]
  have hchoose : (3 * p).choose p * p.factorial * (2 * p).factorial = (3 * p).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show p ≤ 3 * p from by omega)
    rwa [show 3 * p - p = 2 * p from by omega] at this
  have hasc : (2 * p).factorial * (2 * p + 1).ascFactorial (p - 1) = (3 * p - 1).factorial := by
    have := Nat.factorial_mul_ascFactorial (2 * p) (p - 1)
    rwa [show 2 * p + (p - 1) = 3 * p - 1 from by omega] at this
  have hfac_p : p.factorial = p * (p - 1).factorial := by
    conv_lhs => rw [show p = (p - 1) + 1 from by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hfac_3p : (3 * p).factorial = (3 * p) * (3 * p - 1).factorial := by
    conv_lhs => rw [show 3 * p = (3 * p - 1) + 1 from by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (2 * p))
  apply Nat.eq_of_mul_eq_mul_left (show 0 < p from by omega)
  calc p * ((2 * p).factorial * ((3 * p).choose p * (p - 1).factorial))
      = (3 * p).choose p * p.factorial * (2 * p).factorial := by rw [hfac_p]; ring
    _ = (3 * p).factorial := hchoose
    _ = (3 * p) * (3 * p - 1).factorial := hfac_3p
    _ = (3 * p) * ((2 * p).factorial * (2 * p + 1).ascFactorial (p - 1)) := by rw [hasc]
    _ = p * ((2 * p).factorial * (3 * (2 * p + 1).ascFactorial (p - 1))) := by ring

/-- **F2 expansion** of the central binomial coefficient `C(3p, p)` modulo `p^5`. -/
theorem S1_expand (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((3 * p).choose p : ZMod (p ^ 5))
      = 3 + 6 * (HSums.q p) * (HSums.H p 1) - 6 * (HSums.q p) ^ 2 * (HSums.H p 2) := by
  have hnat := choose_prod_nat p hp7
  -- cast to ZMod (p^5)
  have hcast : ((3 * p).choose p : ZMod (p ^ 5)) * ∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℕ) : ZMod (p ^ 5))
      = 3 * ∏ i ∈ Finset.Icc 1 (p - 1),
          (((i : ℕ) : ZMod (p ^ 5)) + 2 * (p : ZMod (p ^ 5))) := by
    have h := congrArg (fun n : ℕ => (n : ZMod (p ^ 5))) hnat
    push_cast at h
    convert h using 3
  -- Step A: divide by the (unit) product
  have hA : ((3 * p).choose p : ZMod (p ^ 5))
      = 3 * ∏ i ∈ Finset.Icc 1 (p - 1), (1 + 2 * (HSums.q p) * ((i : ZMod (p ^ 5))⁻¹)) := by
    have hterm : ∀ i ∈ Finset.Icc 1 (p - 1),
        (((i : ℕ) : ZMod (p ^ 5)) + 2 * (p : ZMod (p ^ 5)))
          = ((i : ℕ) : ZMod (p ^ 5)) * (1 + 2 * (HSums.q p) * ((i : ZMod (p ^ 5))⁻¹)) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hu : ((i : ℕ) : ZMod (p ^ 5)) * ((i : ZMod (p ^ 5))⁻¹) = 1 :=
        ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp i (by omega) (by omega))
      show ((i : ℕ) : ZMod (p ^ 5)) + 2 * (p : ZMod (p ^ 5))
        = ((i : ℕ) : ZMod (p ^ 5)) * (1 + 2 * (p : ZMod (p ^ 5)) * ((i : ZMod (p ^ 5))⁻¹))
      linear_combination (-(2 * (p : ZMod (p ^ 5)))) * hu
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib] at hcast
    have huunit : IsUnit (∏ i ∈ Finset.Icc 1 (p - 1), ((i : ℕ) : ZMod (p ^ 5))) :=
      IsUnit.prod_iff.mpr (fun i hi => by
        rw [Finset.mem_Icc] at hi; exact HSums.isUnit_cast hp i (by omega) (by omega))
    apply (IsUnit.mul_right_inj huunit).mp
    linear_combination hcast
  rw [hA, L_expand p hp hp7]; ring

/-- **Wolstenholme corollary** modulo `p^3`: `C(3p, p) ≡ 3 (mod p^3)`. -/
theorem choose_3p_p_wol (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ m : ℕ, (3 * p).choose p = 3 + p ^ 3 * m := by
  have hS := S1_expand p hp hp7
  obtain ⟨a, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨b, hH2⟩ := HSums.H_two_dvd hp hp7
  have hS2 : ((3 * p).choose p : ZMod (p ^ 5)) = 3 + (HSums.q p) ^ 3 * (6 * a - 6 * b) := by
    rw [hS, hH1, hH2]; ring
  have hdvd : p ^ 3 ∣ p ^ 5 := pow_dvd_pow p (by omega)
  -- push to ZMod (p^3)
  have hcast : ((3 * p).choose p : ZMod (p ^ 3)) = 3 := by
    have hc := congrArg (ZMod.castHom hdvd (ZMod (p ^ 3))) hS2
    rw [map_natCast, map_add, map_mul, map_pow, map_ofNat] at hc
    rw [show (ZMod.castHom hdvd (ZMod (p ^ 3))) (HSums.q p) = (p : ZMod (p ^ 3)) from by
          rw [HSums.q, map_natCast]] at hc
    rw [show ((p : ZMod (p ^ 3))) ^ 3 = 0 from by
          rw [← Nat.cast_pow]; exact ZMod.natCast_self _] at hc
    rw [hc]; ring
  -- convert to a `Nat.ModEq`
  have hmod : (3 * p).choose p ≡ 3 [MOD p ^ 3] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (show ((3 * p).choose p : ZMod (p ^ 3)) = ((3 : ℕ) : ZMod (p ^ 3)) from by
        rw [hcast]; norm_num)
  -- lower bound `3 ≤ C(3p, p)`
  have hge : 3 ≤ (3 * p).choose p := by
    have hnat := choose_prod_nat p hp7
    have hFpos : 0 < ∏ i ∈ Finset.Icc 1 (p - 1), i :=
      Finset.prod_pos (fun i hi => by rw [Finset.mem_Icc] at hi; omega)
    have hGF : (∏ i ∈ Finset.Icc 1 (p - 1), i)
        ≤ ∏ i ∈ Finset.Icc 1 (p - 1), (i + 2 * p) :=
      Finset.prod_le_prod' (fun i _ => by omega)
    have hstep : 3 * (∏ i ∈ Finset.Icc 1 (p - 1), i)
        ≤ (3 * p).choose p * (∏ i ∈ Finset.Icc 1 (p - 1), i) := by
      rw [hnat]; exact Nat.mul_le_mul_left 3 hGF
    exact Nat.le_of_mul_le_mul_right (by linarith [hstep]) hFpos
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hge] at hmod
  obtain ⟨m, hm⟩ := hmod
  exact ⟨m, by omega⟩
end F2_sec

section Nielsen_sec

namespace Nielsen
section
open Nat Finset BigOperators Polynomial

noncomputable def L (p : ℚ[X]) : ℚ := p.sum (fun i a => a / ((i : ℚ) + 1))

lemma L_zero : L 0 = 0 := by simp [L]

lemma L_add (p q : ℚ[X]) : L (p + q) = L p + L q := by
  unfold L
  rw [Polynomial.sum_add_index]
  · intro i; simp
  · intro i a b; rw [add_div]

lemma L_monomial (n : ℕ) (a : ℚ) : L (monomial n a) = a / ((n : ℚ) + 1) := by
  unfold L
  rw [Polynomial.sum_monomial_index]
  simp

lemma L_smul (c : ℚ) (p : ℚ[X]) : L (c • p) = c * L p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [smul_add, L_add, L_add, hp, hq, mul_add]
  | monomial n a =>
    rw [smul_monomial, L_monomial, L_monomial]
    rw [smul_eq_mul, mul_div_assoc]

/-- L as an additive hom, for `map_sum`. -/
noncomputable def Lhom : ℚ[X] →+ ℚ where
  toFun := L
  map_zero' := L_zero
  map_add' := L_add

@[simp] lemma Lhom_apply (p : ℚ[X]) : Lhom p = L p := rfl

lemma L_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    L (∑ i ∈ s, f i) = ∑ i ∈ s, L (f i) := by
  have h := map_sum Lhom f s
  simp only [Lhom_apply] at h
  exact h

/-- FTC: `L (derivative q) = q.eval 1 - q.eval 0`. -/
lemma L_derivative (q : ℚ[X]) : L (derivative q) = q.eval 1 - q.eval 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [derivative_add, L_add, hp, hq, eval_add, eval_add]; ring
  | monomial n a =>
    rw [derivative_monomial, L_monomial, eval_monomial, eval_monomial]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [one_pow, zero_pow (by omega : m + 1 ≠ 0)]
      field_simp
      ring
lemma L_C_mul (c : ℚ) (p : ℚ[X]) : L (C c * p) = c * L p := by
  rw [← Polynomial.smul_eq_C_mul, L_smul]

lemma L_bernoulli (n : ℕ) : L (Polynomial.bernoulli n) = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
    rw [if_pos rfl, Polynomial.bernoulli_zero]
    have : (1 : ℚ[X]) = monomial 0 1 := by rw [monomial_zero_one]
    rw [this, L_monomial]; norm_num
  | succ m =>
    rw [if_neg (by omega : m + 1 ≠ 0)]
    have hd := derivative_bernoulli_add_one (m + 1)
    have key : L (derivative (Polynomial.bernoulli (m + 2))) = 0 := by
      rw [L_derivative, Polynomial.bernoulli_eval_one, Polynomial.bernoulli_eval_zero,
        bernoulli_eq_bernoulli'_of_ne_one (by omega : m + 2 ≠ 1), sub_self]
    rw [show m + 1 + 1 = m + 2 by rfl] at hd
    rw [hd] at key
    have hC : ((↑(m + 1) : ℚ[X]) + 1) = C ((m : ℚ) + 2) := by
      rw [show ((m : ℚ) + 2) = ((m + 1 : ℕ) : ℚ) + 1 by push_cast; ring,
        map_add, map_one, Polynomial.C_eq_natCast]
    rw [hC, L_C_mul] at key
    have hne : ((m : ℚ) + 2) ≠ 0 := by positivity
    exact (mul_eq_zero.1 key).resolve_left hne

/-- The convolution polynomial `P N = ∑ B_m(x) B_{N-m}(x)`. -/
noncomputable def P (N : ℕ) : ℚ[X] :=
  ∑ m ∈ range (N + 1), Polynomial.bernoulli m * Polynomial.bernoulli (N - m)

/-- Derivative recursion: `derivative (P (n+1)) = (n+2) • P n`. -/
lemma derivative_P (n : ℕ) :
    derivative (P (n + 1)) = ((n : ℚ) + 2) • P n := by
  unfold P
  rw [derivative_sum]
  have h1 : ∀ m ∈ range (n + 2),
      derivative (Polynomial.bernoulli m * Polynomial.bernoulli (n + 1 - m))
        = (m : ℚ[X]) * Polynomial.bernoulli (m - 1) * Polynomial.bernoulli (n + 1 - m)
          + ((n + 1 - m : ℕ) : ℚ[X]) * Polynomial.bernoulli m * Polynomial.bernoulli (n - m) := by
    intro m _
    rw [derivative_mul, derivative_bernoulli, derivative_bernoulli,
        show n + 1 - m - 1 = n - m from by omega]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hA : (∑ m ∈ range (n + 2),
        (m : ℚ[X]) * Polynomial.bernoulli (m - 1) * Polynomial.bernoulli (n + 1 - m))
      = ∑ k ∈ range (n + 1),
        (↑(k + 1) : ℚ[X]) * Polynomial.bernoulli k * Polynomial.bernoulli (n - k) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_sub_cancel, show n + 1 - (k + 1) = n - k from by omega]
  have hB : (∑ m ∈ range (n + 2),
        ((n + 1 - m : ℕ) : ℚ[X]) * Polynomial.bernoulli m * Polynomial.bernoulli (n - m))
      = ∑ m ∈ range (n + 1),
        ((n + 1 - m : ℕ) : ℚ[X]) * Polynomial.bernoulli m * Polynomial.bernoulli (n - m) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  rw [hA, hB, ← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hcoef : ((↑(k + 1) : ℚ[X]) + ↑(n + 1 - k)) = C ((n : ℚ) + 2) := by
    have he : (n : ℚ) + 2 = ((k + 1 : ℕ) : ℚ) + ((n + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ n + 1)]; push_cast; ring
    rw [he, map_add, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
  rw [Polynomial.smul_eq_C_mul, ← hcoef]
  ring
noncomputable def α (m : ℕ) : ℚ := L (P m)

noncomputable def Q (N : ℕ) : ℚ[X] :=
  ∑ j ∈ range (N + 1), (((N + 1).choose j : ℚ) * α (N - j)) • Polynomial.bernoulli j

lemma natCast_succ_poly (i : ℕ) : ((↑(i + 1) : ℚ[X])) = C ((i : ℚ) + 1) := by
  rw [map_add, map_one, Polynomial.C_eq_natCast]; push_cast; ring

lemma derivative_Q (n : ℕ) : derivative (Q (n + 1)) = ((n : ℚ) + 2) • Q n := by
  unfold Q
  rw [derivative_sum]
  have h1 : ∀ j ∈ range (n + 2),
      derivative ((((n + 2).choose j : ℚ) * α (n + 1 - j)) • Polynomial.bernoulli j)
        = (((n + 2).choose j : ℚ) * α (n + 1 - j)) • ((j : ℚ[X]) * Polynomial.bernoulli (j - 1)) := by
    intro j _
    rw [derivative_smul, derivative_bernoulli]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, smul_zero, add_zero]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show n + 1 - (i + 1) = n - i from by omega, Nat.add_sub_cancel, natCast_succ_poly,
    ← Polynomial.smul_eq_C_mul, smul_smul, smul_smul]
  congr 1
  -- scalar identity
  have h := Nat.add_one_mul_choose_eq (n + 1) i
  rw [show n + 1 + 1 = n + 2 from rfl] at h
  -- h : (n+2) * (n+1).choose i = (n+2).choose (i+1) * (i+1)
  have hc := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hc
  -- hc : (↑n+2) * ↑((n+1).choose i) = ↑((n+2).choose (i+1)) * (↑i+1)
  linear_combination (-α (n - i)) * hc
lemma L_sub (p q : ℚ[X]) : L (p - q) = L p - L q := by
  have h := map_sub Lhom p q
  simp only [Lhom_apply] at h
  exact h

lemma L_one : L 1 = 1 := by
  rw [show (1 : ℚ[X]) = monomial 0 1 from (monomial_zero_one).symm, L_monomial]; norm_num

lemma L_C (c : ℚ) : L (C c) = c := by
  rw [← Polynomial.monomial_zero_left, L_monomial]; norm_num

lemma L_Q (m : ℕ) : L (Q m) = α m := by
  unfold Q
  rw [L_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [L_smul, L_bernoulli])]
  rw [Finset.sum_eq_single 0
      (fun j _ hj0 => by rw [if_neg hj0, mul_zero])
      (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos m)) h)]
  simp

lemma P0 : P 0 = 1 := by unfold P; simp [Polynomial.bernoulli_zero]

lemma α0 : α 0 = 1 := by unfold α; rw [P0, L_one]

theorem P_eq_Q (N : ℕ) : P N = Q N := by
  induction N with
  | zero =>
    unfold Q
    rw [Finset.sum_range_one, P0, α0]
    simp [Polynomial.bernoulli_zero]
  | succ n ih =>
    set d := P (n + 1) - Q (n + 1) with hd
    have hderiv : derivative d = 0 := by
      rw [hd, derivative_sub, derivative_P, derivative_Q, ← smul_sub, ih, sub_self, smul_zero]
    have hconst : d = C (d.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hderiv
    have hL : L d = 0 := by
      rw [hd, L_sub, L_Q, sub_eq_zero]; rfl
    have hc0 : d.coeff 0 = 0 := by rw [hconst, L_C] at hL; exact hL
    have hzero : d = 0 := by rw [hconst, hc0, map_zero]
    rw [hd] at hzero
    exact sub_eq_zero.mp hzero
lemma bernoulli'_eq (n : ℕ) :
    bernoulli' n = _root_.bernoulli n + (if n = 1 then 1 else 0) := by
  by_cases h : n = 1
  · subst h; rw [if_pos rfl, bernoulli'_one, _root_.bernoulli_one]; norm_num
  · rw [if_neg h, add_zero, bernoulli_eq_bernoulli'_of_ne_one h]

lemma P_eval_diff (m : ℕ) (hm : 2 ≤ m) :
    (P (m + 1)).eval 1 - (P (m + 1)).eval 0 = 2 * _root_.bernoulli m := by
  unfold P
  rw [show m + 1 + 1 = m + 2 from rfl, eval_finset_sum, eval_finset_sum,
      ← Finset.sum_sub_distrib]
  simp only [eval_mul]
  have key : ∀ k ∈ range (m + 2),
      (Polynomial.bernoulli k).eval 1 * (Polynomial.bernoulli (m + 1 - k)).eval 1
        - (Polynomial.bernoulli k).eval 0 * (Polynomial.bernoulli (m + 1 - k)).eval 0
      = (if k = 1 then _root_.bernoulli (m + 1 - k) else 0)
        + (if m + 1 - k = 1 then _root_.bernoulli k else 0)
        + (if k = 1 then (if m + 1 - k = 1 then (1 : ℚ) else 0) else 0) := by
    intro k _
    rw [Polynomial.bernoulli_eval_one, Polynomial.bernoulli_eval_one,
        Polynomial.bernoulli_eval_zero, Polynomial.bernoulli_eval_zero,
        bernoulli'_eq k, bernoulli'_eq (m + 1 - k)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (∑ k ∈ range (m + 2), if k = 1 then _root_.bernoulli (m + 1 - k) else 0)
      = _root_.bernoulli m := by
    rw [Finset.sum_ite_eq' (range (m + 2)) 1 (fun k => _root_.bernoulli (m + 1 - k)),
        if_pos (Finset.mem_range.2 (by omega)), show m + 1 - 1 = m from by omega]
  have h2 : (∑ k ∈ range (m + 2), if m + 1 - k = 1 then _root_.bernoulli k else 0)
      = _root_.bernoulli m := by
    rw [Finset.sum_eq_single m]
    · rw [if_pos (by omega)]
    · intro k hk hkm
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have h3 : (∑ k ∈ range (m + 2),
      if k = 1 then (if m + 1 - k = 1 then (1 : ℚ) else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with hk hmk
    · exfalso; omega
    · rfl
    · rfl
  rw [h1, h2, h3]; ring

lemma alpha_rec (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℚ) + 2) * α m = 2 * _root_.bernoulli m := by
  have hderiv := derivative_P m
  have h := congrArg L hderiv
  rw [L_derivative, L_smul, P_eval_diff m hm] at h
  exact h.symm

lemma α1 : α 1 = 0 := by
  unfold α P
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [Polynomial.bernoulli_zero, Polynomial.bernoulli_one, one_mul, mul_one, L_add,
      L_sub, L_C, show (X : ℚ[X]) = monomial 1 1 from (monomial_one_one_eq_X).symm,
      L_monomial]
  norm_num
/-- `C = P N` evaluated at 0, expanded in the Bernoulli basis. -/
lemma C_eq_sum (N : ℕ) :
    ∑ k ∈ range (N + 1), _root_.bernoulli k * _root_.bernoulli (N - k)
      = ∑ j ∈ range (N + 1), ((N + 1).choose j : ℚ) * α (N - j) * _root_.bernoulli j := by
  have h1 : (P N).eval 0
      = ∑ k ∈ range (N + 1), _root_.bernoulli k * _root_.bernoulli (N - k) := by
    unfold P; rw [eval_finset_sum]
    simp only [eval_mul, Polynomial.bernoulli_eval_zero]
  have h2 : (Q N).eval 0
      = ∑ j ∈ range (N + 1), ((N + 1).choose j : ℚ) * α (N - j) * _root_.bernoulli j := by
    unfold Q; rw [eval_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_smul, Polynomial.bernoulli_eval_zero, smul_eq_mul]
  rw [← h1, ← h2, P_eq_Q]

/-- Congruence `C(p-2, j) ≡ (-1)^j (j+1)  (mod p)`. -/
lemma choose_zmod (p : ℕ) [Fact p.Prime] :
    ∀ j : ℕ, j ≤ p - 2 → ((p - 2).choose j : ZMod p) = (-1) ^ j * ((j : ZMod p) + 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  intro j
  induction j with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hile : i ≤ p - 2 := by omega
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) (Nat.choose_succ_right_eq (p - 2) i)
    push_cast at hcast
    -- hcast : ↑((p-2).choose (i+1)) * (↑i + 1) = ↑((p-2).choose i) * ↑(p-2-i)
    have hsub : ((p - 2 - i : ℕ) : ZMod p) = -((i : ZMod p) + 2) := by
      have hsum : (p - 2 - i) + (i + 2) = p := by omega
      have h := congrArg (Nat.cast : ℕ → ZMod p) hsum
      push_cast [ZMod.natCast_self] at h
      exact eq_neg_of_add_eq_zero_left h
    have hne : ((i : ZMod p) + 1) ≠ 0 := by
      have h1 : ((i : ZMod p) + 1) = ((i + 1 : ℕ) : ZMod p) := by push_cast; ring
      rw [h1, Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    apply mul_right_cancel₀ hne
    rw [hcast, ih hile, hsub]
    push_cast
    ring

lemma dvd_choose_add (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (j : ℕ) (hj : j ≤ p - 5)
    (hje : Even j) : p ∣ ((p - 2).choose j + (p - 1 - j)) := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, choose_zmod p j (by omega)]
  have hpj : ((p - 1 - j : ℕ) : ZMod p) = -((j : ZMod p) + 1) := by
    have hsum : (p - 1 - j) + (j + 1) = p := by omega
    have h := congrArg (Nat.cast : ℕ → ZMod p) hsum
    push_cast [ZMod.natCast_self] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [hpj, hje.neg_one_pow]
  ring

/-! ### p-integrality of Bernoulli numbers -/

lemma val_sum_nonneg {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (F : ι → ℚ)
    (h : ∀ i ∈ s, 0 ≤ padicValRat p (F i)) : 0 ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [padicValRat.zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hxv : 0 ≤ padicValRat p (F a) := h a (Finset.mem_insert_self a s)
    have hyv : 0 ≤ padicValRat p (∑ i ∈ s, F i) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    by_cases hxy : F a + ∑ i ∈ s, F i = 0
    · rw [hxy, padicValRat.zero]
    · exact le_trans (le_min hxv hyv) (padicValRat.min_le_padicValRat_add (p := p) hxy)

lemma bernoulli_padic_nonneg (p : ℕ) (hp : p.Prime) (hp2 : 2 ≤ p) :
    ∀ k, k < p - 1 → 0 ≤ padicValRat p (_root_.bernoulli k) := by
  haveI := Fact.mk hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp [_root_.bernoulli_zero, padicValRat.one]
    by_cases hbk : _root_.bernoulli k = 0
    · rw [hbk, padicValRat.zero]
    have hsum := _root_.sum_bernoulli (k + 1)
    rw [if_neg (by omega : k + 1 ≠ 1), Finset.sum_range_succ] at hsum
    have hchoose : ((k + 1).choose k : ℚ) = (k + 1 : ℚ) := by
      rw [Nat.choose_succ_self_right]; push_cast; ring
    rw [hchoose] at hsum
    set s := ∑ i ∈ Finset.range k, ((k + 1).choose i : ℚ) * _root_.bernoulli i with hsdef
    have heq : (k + 1 : ℚ) * _root_.bernoulli k = -s := by rw [hsdef]; linarith [hsum]
    have hsval : 0 ≤ padicValRat p s := by
      apply val_sum_nonneg p (Finset.range k)
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hci : ((k + 1).choose i : ℚ) = 0
      · rw [hci, zero_mul, padicValRat.zero]
      by_cases hbi : _root_.bernoulli i = 0
      · rw [hbi, mul_zero, padicValRat.zero]
      rw [padicValRat.mul hci hbi]
      have h1 : 0 ≤ padicValRat p ((k + 1).choose i : ℚ) := by
        rw [padicValRat.of_nat]; exact_mod_cast Nat.zero_le _
      have h2 : 0 ≤ padicValRat p (_root_.bernoulli i) := ih i hi (by omega)
      linarith
    have hk1ne : (k + 1 : ℚ) ≠ 0 := by positivity
    have hval_k1 : padicValRat p (k + 1 : ℚ) = 0 := by
      rw [show ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat]
      norm_cast
      exact padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have hprod : padicValRat p ((k + 1 : ℚ) * _root_.bernoulli k)
        = padicValRat p (_root_.bernoulli k) := by
      rw [padicValRat.mul hk1ne hbk, hval_k1, zero_add]
    rw [heq, padicValRat.neg] at hprod
    rw [← hprod]; exact hsval

lemma norm_le_one_of_val_nonneg (p : ℕ) [Fact p.Prime] {q : ℚ}
    (h : 0 ≤ padicValRat p q) : padicNorm p q ≤ 1 := by
  by_cases hq : q = 0
  · rw [hq, padicNorm.zero]; norm_num
  · calc padicNorm p q = (p : ℚ) ^ (-padicValRat p q) := padicNorm.eq_zpow_of_nonzero hq
      _ ≤ (p : ℚ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by omega)
      _ = 1 := by norm_num

lemma bern_le (p : ℕ) (hp : p.Prime) [Fact p.Prime] {k : ℕ} (hk : k < p - 1) :
    padicNorm p (_root_.bernoulli k) ≤ 1 :=
  norm_le_one_of_val_nonneg p (bernoulli_padic_nonneg p hp hp.two_le k hk)

lemma norm3 (p : ℕ) [Fact p.Prime] {a b c : ℚ}
    (ha : padicNorm p a ≤ 1) (hb : padicNorm p b ≤ 1) (hc : padicNorm p c ≤ 1) :
    padicNorm p (a * b * c) ≤ 1 := by
  rw [padicNorm.mul, padicNorm.mul]
  exact mul_le_one₀ (mul_le_one₀ ha (padicNorm.nonneg _) hb) (padicNorm.nonneg _) hc

theorem C_padicNorm (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    padicNorm p (∑ k ∈ Finset.range (p - 2), _root_.bernoulli k * _root_.bernoulli (p - 3 - k))
      ≤ (p : ℚ) ^ (-1 : ℤ) := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 4 := ⟨p - 4, by omega⟩
  have hm3 : 3 ≤ m := by omega
  -- m is odd, so bernoulli m = 0
  have hp_odd : Odd (m + 4) := hp.odd_of_ne_two (by omega)
  have hm_odd : Odd m := by obtain ⟨t, ht⟩ := hp_odd; exact ⟨t - 2, by omega⟩
  have hBm : _root_.bernoulli m = 0 := bernoulli_eq_zero_of_odd hm_odd (by omega)
  -- put the goal in canonical form and expand via `C_eq_sum`
  show padicNorm (m + 4) (∑ k ∈ Finset.range (m + 2),
      _root_.bernoulli k * _root_.bernoulli ((m + 1) - k)) ≤ ((m + 4 : ℕ) : ℚ) ^ (-1 : ℤ)
  have hconv := C_eq_sum (m + 1)
  simp only [show (m + 1) + 1 = m + 2 from rfl] at hconv
  rw [hconv]
  set Csum := ∑ j ∈ Finset.range (m + 2),
      ((m + 2).choose j : ℚ) * α ((m + 1) - j) * _root_.bernoulli j with hCs
  -- the two peeling identities
  have hf : Csum = (∑ j ∈ Finset.range m,
        ((m + 2).choose j : ℚ) * α ((m + 1) - j) * _root_.bernoulli j)
        + ((m + 2 : ℕ) : ℚ) * _root_.bernoulli (m + 1) := by
    rw [hCs, Finset.sum_range_succ, Finset.sum_range_succ,
        show (m + 1) - m = 1 from by omega, α1,
        show (m + 1) - (m + 1) = 0 from by omega, α0, Nat.choose_succ_self_right]
    push_cast; ring
  have hg : Csum = (∑ j ∈ Finset.range m,
        _root_.bernoulli j * _root_.bernoulli ((m + 1) - j)) + _root_.bernoulli (m + 1) := by
    rw [← hconv, Finset.sum_range_succ, Finset.sum_range_succ,
        show (m + 1) - m = 1 from by omega, hBm,
        show (m + 1) - (m + 1) = 0 from by omega, _root_.bernoulli_zero]
    ring
  -- main identity: 3 Csum = p B + ∑ TERM
  have hident : 3 * Csum = ((m + 4 : ℕ) : ℚ) * _root_.bernoulli (m + 1)
      + ∑ j ∈ Finset.range m,
          (((m + 2).choose j : ℚ) * α ((m + 1) - j) * _root_.bernoulli j
            + 2 * (_root_.bernoulli j * _root_.bernoulli ((m + 1) - j))) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast
    push_cast at hf hg
    linear_combination hf + 2 * hg
  -- reduce goal to `3 * Csum`
  have hn3 : padicNorm (m + 4) (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicNorm.nat_eq_one_iff]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have hn2 : padicNorm (m + 4) (2 : ℚ) ≤ 1 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]; exact padicNorm.of_nat 2
  have e3 : padicNorm (m + 4) (3 * Csum) = padicNorm (m + 4) Csum := by
    rw [padicNorm.mul, hn3, one_mul]
  rw [← e3, hident]
  -- bound `p B + ∑ TERM`
  refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
  · -- padicNorm (p * B_{m+1}) ≤ p^{-1}
    rw [padicNorm.mul, padicNorm.padicNorm_p_of_prime, zpow_neg_one]
    calc ((m + 4 : ℕ) : ℚ)⁻¹ * padicNorm (m + 4) (_root_.bernoulli (m + 1))
        ≤ ((m + 4 : ℕ) : ℚ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (bern_le _ hp (by omega)) (by positivity)
      _ = ((m + 4 : ℕ) : ℚ)⁻¹ := mul_one _
  · -- padicNorm (∑ TERM) ≤ p^{-1}
    apply padicNorm.sum_le'
    · intro j hj
      rw [Finset.mem_range] at hj
      -- key identity for the term (multiply by the p-unit (m+1-j+2))
      have hac := alpha_rec ((m + 1) - j) (by omega)
      have key : (((m + 1) - j + 2 : ℕ) : ℚ) *
          (((m + 2).choose j : ℚ) * α ((m + 1) - j) * _root_.bernoulli j
            + 2 * (_root_.bernoulli j * _root_.bernoulli ((m + 1) - j)))
          = _root_.bernoulli j * _root_.bernoulli ((m + 1) - j) * 2
              * (((m + 2).choose j + ((m + 1) - j + 2) : ℕ) : ℚ) := by
        have hcc : (((m + 1) - j + 2 : ℕ) : ℚ) = ((((m + 1) - j : ℕ)) : ℚ) + 2 := by
          push_cast; ring
        rw [hcc, Nat.cast_add, hcc]
        linear_combination (((m + 2).choose j : ℚ) * _root_.bernoulli j) * hac
      have hc_norm : padicNorm (m + 4) (((m + 1) - j + 2 : ℕ) : ℚ) = 1 := by
        rw [padicNorm.nat_eq_one_iff]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      have hnorm_eq : padicNorm (m + 4)
          (((m + 2).choose j : ℚ) * α ((m + 1) - j) * _root_.bernoulli j
            + 2 * (_root_.bernoulli j * _root_.bernoulli ((m + 1) - j)))
          = padicNorm (m + 4) (_root_.bernoulli j * _root_.bernoulli ((m + 1) - j) * 2
              * (((m + 2).choose j + ((m + 1) - j + 2) : ℕ) : ℚ)) := by
        have h := congrArg (padicNorm (m + 4)) key
        rw [padicNorm.mul, hc_norm, one_mul] at h
        exact h
      rw [hnorm_eq]
      rcases Nat.even_or_odd j with hje | hjo
      · -- even j: use divisibility
        have hdvd : (m + 4) ∣ ((m + 2).choose j + ((m + 1) - j + 2)) := by
          have h := dvd_choose_add (m + 4) (by omega) j (by omega) hje
          rw [show m + 4 - 1 - j = (m + 1) - j + 2 from by omega] at h
          exact h
        obtain ⟨t, ht⟩ := hdvd
        have hnormsum : padicNorm (m + 4)
            (((m + 2).choose j + ((m + 1) - j + 2) : ℕ) : ℚ) ≤ ((m + 4 : ℕ) : ℚ) ^ (-1 : ℤ) := by
          rw [ht, Nat.cast_mul, padicNorm.mul, padicNorm.padicNorm_p_of_prime, zpow_neg_one]
          calc ((m + 4 : ℕ) : ℚ)⁻¹ * padicNorm (m + 4) ((t : ℕ) : ℚ)
              ≤ ((m + 4 : ℕ) : ℚ)⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left (padicNorm.of_nat _) (by positivity)
            _ = ((m + 4 : ℕ) : ℚ)⁻¹ := mul_one _
        rw [padicNorm.mul]
        calc padicNorm (m + 4)
              (_root_.bernoulli j * _root_.bernoulli ((m + 1) - j) * 2)
              * padicNorm (m + 4) (((m + 2).choose j + ((m + 1) - j + 2) : ℕ) : ℚ)
            ≤ 1 * ((m + 4 : ℕ) : ℚ) ^ (-1 : ℤ) :=
              mul_le_mul (norm3 _ (bern_le _ hp (by omega)) (bern_le _ hp (by omega)) hn2)
                hnormsum (padicNorm.nonneg _) (by norm_num)
          _ = ((m + 4 : ℕ) : ℚ) ^ (-1 : ℤ) := one_mul _
      · -- odd j: the product of Bernoulli numbers vanishes
        have hz : _root_.bernoulli j * _root_.bernoulli ((m + 1) - j) = 0 := by
          rcases eq_or_ne j 1 with rfl | hj1
          · rw [show (m + 1) - 1 = m from by omega, hBm, mul_zero]
          · have h1j : 1 < j := by obtain ⟨t, ht⟩ := hjo; omega
            rw [bernoulli_eq_zero_of_odd hjo h1j, zero_mul]
        rw [show _root_.bernoulli j * _root_.bernoulli ((m + 1) - j) * 2
              * (((m + 2).choose j + ((m + 1) - j + 2) : ℕ) : ℚ) = 0 from by rw [hz]; ring,
            padicNorm.zero]
        positivity
    · positivity
end
end Nielsen


open Finset in
theorem C_padicNorm (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    padicNorm p (∑ k ∈ Finset.range (p-2), bernoulli k * bernoulli (p-3-k)) ≤ (p:ℚ)^(-1:ℤ) :=
  Nielsen.C_padicNorm p hp hp7

end Nielsen_sec

section MZV4_sec
open Nat Finset BigOperators

namespace MZV4

/-- Fermat inverse: in `ZMod p`, `x⁻¹ = x^(p-2)` for `x ≠ 0`. -/
lemma inv_eq_pow {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) :
    x⁻¹ = x ^ (p - 2) := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hpow : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  refine inv_eq_of_mul_eq_one_right ?_
  have e : p - 1 = (p - 2) + 1 := by omega
  rw [← hpow, e]; ring

/-- Reindexing: a sum over `Icc 1 (p-1)` of `g` of the cast equals the sum over
nonzero residues. -/
lemma sum_Icc_erase {p : ℕ} [Fact p.Prime] (g : ZMod p → ZMod p) :
    ∑ i ∈ Finset.Icc 1 (p-1), g ((i:ℕ):ZMod p)
      = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), g x := by
  apply Finset.sum_nbij' (fun i => ((i:ℕ):ZMod p)) (fun x => x.val)
  · intro i hi; rw [Finset.mem_Icc] at hi
    rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hi.1 (by omega)
  · intro x hx; rw [Finset.mem_erase] at hx; rw [Finset.mem_Icc]
    have hv : x.val < p := ZMod.val_lt x
    have : x.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact hx.1
    omega
  · intro i hi; rw [Finset.mem_Icc] at hi; rw [ZMod.val_natCast_of_lt (by omega)]
  · intro x hx; rw [ZMod.natCast_zmod_val]
  · intro i hi; rfl

/-- **Power-sum / Wolstenholme vanishing**: `∑_{i=1}^{p-1} (1/i)^j ≡ 0 (mod p)`
for `0 < j < p-1`. -/
lemma sum_inv_pow_zero {p : ℕ} [Fact p.Prime] (j : ℕ) (hj : 0 < j) (hj2 : j < p - 1) :
    ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod p)⁻¹)^j = 0 := by
  rw [sum_Icc_erase (fun x => x⁻¹^j)]
  have hbij : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), (x⁻¹)^j
            = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^j := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro x hx; rw [Finset.mem_erase] at hx ⊢
      exact ⟨inv_ne_zero hx.1, Finset.mem_univ _⟩
    · intro x hx; rw [Finset.mem_erase] at hx ⊢
      exact ⟨inv_ne_zero hx.1, Finset.mem_univ _⟩
    · intro x hx; rw [Finset.mem_erase] at hx; rw [inv_inv]
    · intro x hx; rw [Finset.mem_erase] at hx; rw [inv_inv]
    · intro x hx; rfl
  rw [hbij]
  have h0 : (0:ZMod p)^j = 0 := zero_pow hj.ne'
  have : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^j = ∑ x : ZMod p, x^j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:ZMod p)), h0, add_zero]
  rw [this]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [show (p:ℕ) - 1 = Fintype.card (ZMod p) - 1 by rw [hcard]] at hj2
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) j hj2

/-- The Bernoulli number `B_{p-4}` vanishes for `p ≥ 7` prime, since `p-4` is odd and `> 1`. -/
lemma bernoulli_pminus4_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : p ≥ 7) :
    bernoulli (p - 4) = 0 := by
  have hodd : Odd (p - 4) := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · rcases h with ⟨m, hm⟩; exact ⟨m - 2, by omega⟩
  exact bernoulli_eq_zero_of_odd hodd (by omega)

end MZV4

end MZV4_sec

section Kernel_sec

open Nat Finset BigOperators

namespace Kernel

/-- Helper: a finite sum of rationals each with nonnegative `p`-adic valuation
has nonnegative `p`-adic valuation. -/
lemma val_sum_nonneg {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (F : ι → ℚ)
    (h : ∀ i ∈ s, 0 ≤ padicValRat p (F i)) :
    0 ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [padicValRat.zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    set x := F a with hx
    set y := ∑ i ∈ s, F i with hy
    have hxv : 0 ≤ padicValRat p x := h a (Finset.mem_insert_self a s)
    have hyv : 0 ≤ padicValRat p y :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    by_cases hxy : x + y = 0
    · rw [hxy, padicValRat.zero]
    · have hmin := padicValRat.min_le_padicValRat_add (p := p) hxy
      calc (0 : ℤ) ≤ min (padicValRat p x) (padicValRat p y) := le_min hxv hyv
        _ ≤ padicValRat p (x + y) := hmin

/-- The `p`-adic valuation of `(n : ℚ)` is `0` when `0 < n < p`. -/
lemma val_nat_eq_zero (p : ℕ) (hp : p.Prime) {n : ℕ} (hn0 : 0 < n) (hnp : n < p) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  norm_cast
  apply padicValNat.eq_zero_of_not_dvd
  exact Nat.not_dvd_of_pos_of_lt hn0 hnp

/-- **Step 1: weak `p`-integrality of Bernoulli numbers.**
For `k < p - 1`, the `p`-adic valuation of `bernoulli k` is nonnegative. -/
lemma bernoulli_padic_nonneg (p : ℕ) (hp : p.Prime) (hp2 : 2 ≤ p) :
    ∀ k, k < p - 1 → 0 ≤ padicValRat p (bernoulli k) := by
  haveI := Fact.mk hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [bernoulli_zero, padicValRat.one]
    -- k ≥ 1
    by_cases hbk : bernoulli k = 0
    · rw [hbk, padicValRat.zero]
    -- The recurrence from `sum_bernoulli (k+1)`.
    have hsum := sum_bernoulli (k + 1)
    have hne1 : k + 1 ≠ 1 := by omega
    rw [if_neg hne1] at hsum
    rw [Finset.sum_range_succ] at hsum
    -- last term: C(k+1,k) * bernoulli k = (k+1) * bernoulli k
    have hchoose : ((k + 1).choose k : ℚ) = (k + 1 : ℚ) := by
      rw [Nat.choose_succ_self_right]
      push_cast; ring
    rw [hchoose] at hsum
    -- so (k+1) * bernoulli k = - ∑_{i<k} C(k+1,i) bernoulli i
    set s := ∑ i ∈ Finset.range k, ((k + 1).choose i : ℚ) * bernoulli i with hsdef
    have heq : (k + 1 : ℚ) * bernoulli k = -s := by
      rw [hsdef]; linarith [hsum]
    -- valuation of s is nonneg
    have hsval : 0 ≤ padicValRat p s := by
      apply val_sum_nonneg p (Finset.range k)
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hci : ((k + 1).choose i : ℚ) = 0
      · rw [hci, zero_mul, padicValRat.zero]
      by_cases hbi : bernoulli i = 0
      · rw [hbi, mul_zero, padicValRat.zero]
      rw [padicValRat.mul hci hbi]
      have h1 : 0 ≤ padicValRat p ((k + 1).choose i : ℚ) := by
        rw [padicValRat.of_nat]; exact_mod_cast Nat.zero_le _
      have h2 : 0 ≤ padicValRat p (bernoulli i) := ih i hi (by omega)
      linarith
    -- valuation of (k+1) is zero
    have hk1ne : (k + 1 : ℚ) ≠ 0 := by positivity
    have hval_k1 : padicValRat p (k + 1 : ℚ) = 0 := by
      have := val_nat_eq_zero p hp (n := k + 1) (by omega) (by omega)
      simpa using this
    -- combine
    have hprod : padicValRat p ((k + 1 : ℚ) * bernoulli k) = padicValRat p (bernoulli k) := by
      rw [padicValRat.mul hk1ne hbk, hval_k1, zero_add]
    have hrhs : padicValRat p (-s) = padicValRat p s := padicValRat.neg s
    rw [heq, hrhs] at hprod
    rw [← hprod]
    exact hsval

/-- Exact-signature restatement of Step 1 for `p ≥ 7`. -/
lemma bernoulli_padic_nonneg' (p : ℕ) (hp : p.Prime) (hp7 : p ≥ 7)
    (k : ℕ) (hk : k < p - 1) : 0 ≤ padicValRat p (bernoulli k) :=
  bernoulli_padic_nonneg p hp (by omega) k hk

/-- **p-integrality of the Bernoulli convolution.**  The convolution
`∑_{i} B_i B_{p-3-i}` is a `p`-integer (nonnegative `p`-adic valuation).
This is the `0 ≤` part; the genuine supercongruence upgrades it to `1 ≤`. -/
lemma conv_padic_nonneg (p : ℕ) (hp : p.Prime) (hp7 : p ≥ 7) :
    0 ≤ padicValRat p
      (∑ i ∈ Finset.range (p - 2), bernoulli i * bernoulli (p - 3 - i)) := by
  haveI := Fact.mk hp
  apply val_sum_nonneg
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases h1 : bernoulli i = 0
  · rw [h1, zero_mul, padicValRat.zero]
  by_cases h2 : bernoulli (p - 3 - i) = 0
  · rw [h2, mul_zero, padicValRat.zero]
  rw [padicValRat.mul h1 h2]
  have e1 : 0 ≤ padicValRat p (bernoulli i) :=
    bernoulli_padic_nonneg p hp (by omega) i (by omega)
  have e2 : 0 ≤ padicValRat p (bernoulli (p - 3 - i)) :=
    bernoulli_padic_nonneg p hp (by omega) (p - 3 - i) (by omega)
  linarith

/-! ### padicNorm helpers (handle the zero case cleanly) -/

lemma norm_le_zpow_of_val_ge (p : ℕ) [Fact p.Prime] {q : ℚ} {c : ℤ}
    (h : q = 0 ∨ c ≤ padicValRat p q) : padicNorm p q ≤ (p : ℚ) ^ (-c) := by
  have hp1 : (1 : ℚ) ≤ (p : ℚ) := by
    have := (Fact.out : p.Prime).two_le; exact_mod_cast le_trans (by norm_num) this
  rcases h with h0 | hge
  · subst h0; rw [padicNorm.zero]; positivity
  · by_cases hq : q = 0
    · subst hq; rw [padicNorm.zero]; positivity
    · rw [padicNorm.eq_zpow_of_nonzero hq]
      apply zpow_le_zpow_right₀ hp1
      omega

lemma norm_le_one_of_val_nonneg (p : ℕ) [Fact p.Prime] {q : ℚ}
    (h : 0 ≤ padicValRat p q) : padicNorm p q ≤ 1 := by
  have := norm_le_zpow_of_val_ge p (q := q) (c := 0) (Or.inr h)
  simpa using this

lemma val_ge_of_norm_le_zpow (p : ℕ) [Fact p.Prime] {q : ℚ} {c : ℤ}
    (hq : q ≠ 0) (h : padicNorm p q ≤ (p : ℚ) ^ (-c)) : c ≤ padicValRat p q := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by
    have := (Fact.out : p.Prime).one_lt; exact_mod_cast this
  rw [padicNorm.eq_zpow_of_nonzero hq] at h
  rw [zpow_le_zpow_iff_right₀ hp1] at h
  omega

lemma norm_p_pow (p : ℕ) [Fact p.Prime] (m : ℕ) :
    padicNorm p ((p : ℚ) ^ m) = (p : ℚ) ^ (-(m : ℤ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p_of_prime,
        Nat.cast_succ, neg_add, zpow_add₀ hp0, zpow_neg_one]

/-- power sum `S p i = ∑_{a=0}^{p-1} a^i`. -/
noncomputable def S (p i : ℕ) : ℚ := ∑ a ∈ Finset.range p, (a : ℚ) ^ i

/-- **Lemma E (remainder).** For `1 ≤ i ≤ p-3`, `S p i - p·B i` has `p`-adic valuation ≥ 2. -/
lemma faulhaber_rem_norm (p : ℕ) (hp : p.Prime) [Fact p.Prime] (i : ℕ)
    (hip : i ≤ p - 3) (hp7 : p ≥ 7) :
    padicNorm p (S p i - (p : ℚ) * bernoulli i) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hS : S p i = ∑ j ∈ Finset.range (i + 1),
      bernoulli j * ((i + 1).choose j) * (p : ℚ) ^ (i + 1 - j) / (i + 1) := by
    rw [S, sum_range_pow]
  have htop : bernoulli i * ((i + 1).choose i : ℚ) * (p : ℚ) ^ (i + 1 - i) / (i + 1)
      = (p : ℚ) * bernoulli i := by
    rw [Nat.choose_succ_self_right]
    have h1 : i + 1 - i = 1 := by omega
    rw [h1]; push_cast; field_simp
  rw [hS, sum_range_succ, htop, add_sub_cancel_right]
  apply padicNorm.sum_le'
  · intro j hj
    rw [Finset.mem_range] at hj
    -- bound each term
    rw [padicNorm.div, padicNorm.mul, padicNorm.mul]
    have hb : padicNorm p (bernoulli j) ≤ 1 := by
      apply norm_le_one_of_val_nonneg
      exact bernoulli_padic_nonneg p hp (by omega) j (by omega)
    have hc : padicNorm p ((i + 1).choose j : ℚ) ≤ 1 := by
      exact_mod_cast padicNorm.of_nat _
    have hpm : padicNorm p ((p : ℚ) ^ (i + 1 - j)) = (p : ℚ) ^ (-(i + 1 - j : ℕ) : ℤ) :=
      norm_p_pow p _
    have hden : padicNorm p ((i + 1 : ℚ)) = 1 := by
      have : ((i + 1 : ℕ) : ℚ) = (i + 1 : ℚ) := by push_cast; ring
      rw [← this]
      rw [padicNorm.nat_eq_one_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [hden, div_one, hpm]
    -- now: |B j| * |C| * p^(-(i+1-j)) ≤ p^(-2)
    have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.one_lt.le
    have hle : (-(↑(i + 1 - j) : ℤ)) ≤ -2 := by omega
    have hexp : (p : ℚ) ^ (-(i + 1 - j : ℕ) : ℤ) ≤ (p : ℚ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ hp1 hle
    calc padicNorm p (bernoulli j) * padicNorm p ((i + 1).choose j : ℚ)
            * (p : ℚ) ^ (-(i + 1 - j : ℕ) : ℤ)
        ≤ 1 * 1 * (p : ℚ) ^ (-2 : ℤ) := by
          gcongr
          exact padicNorm.nonneg _
      _ = (p : ℚ) ^ (-2 : ℤ) := by ring
  · positivity

lemma pne (p : ℕ) [Fact p.Prime] : (p : ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma norm_mul_le_zpow (p : ℕ) [Fact p.Prime] {q r : ℚ} {m n : ℤ}
    (hq : padicNorm p q ≤ (p : ℚ) ^ m) (hr : padicNorm p r ≤ (p : ℚ) ^ n) :
    padicNorm p (q * r) ≤ (p : ℚ) ^ (m + n) := by
  rw [padicNorm.mul, zpow_add₀ (pne p)]
  exact mul_le_mul hq hr (padicNorm.nonneg _) (by positivity)

lemma norm_p_eq (p : ℕ) [Fact p.Prime] : padicNorm p (p : ℚ) = (p : ℚ) ^ (-1 : ℤ) := by
  have := norm_p_pow p 1; simpa using this

lemma norm_bernoulli_le (p : ℕ) (hp : p.Prime) [Fact p.Prime] {k : ℕ} (hk : k < p - 1) :
    padicNorm p (bernoulli k) ≤ (p : ℚ) ^ (0 : ℤ) := by
  simpa using norm_le_one_of_val_nonneg p (bernoulli_padic_nonneg p hp (by omega) k hk)

/-- `S p i` has `p`-adic valuation ≥ 1 for `i ≤ p-3`. -/
lemma norm_S_le (p : ℕ) (hp : p.Prime) [Fact p.Prime] (i : ℕ)
    (hip : i ≤ p - 3) (hp7 : p ≥ 7) :
    padicNorm p (S p i) ≤ (p : ℚ) ^ (-1 : ℤ) := by
  have hrem : padicNorm p (S p i - (p : ℚ) * bernoulli i) ≤ (p : ℚ) ^ (-2 : ℤ) :=
    faulhaber_rem_norm p hp i hip hp7
  have hpb : padicNorm p ((p : ℚ) * bernoulli i) ≤ (p : ℚ) ^ (-1 : ℤ) := by
    have := norm_mul_le_zpow p (norm_p_eq p).le (norm_bernoulli_le p hp (k := i) (by omega))
    simpa using this
  have hsplit : S p i = (S p i - (p : ℚ) * bernoulli i) + (p : ℚ) * bernoulli i := by ring
  rw [hsplit]
  refine le_trans padicNorm.nonarchimedean (max_le ?_ hpb)
  refine le_trans hrem ?_
  apply zpow_le_zpow_right₀ (by exact_mod_cast hp.one_lt.le)
  norm_num

/-- **Reduction lemma.** The supercongruence `v_p(∑ Sᵢ·S_{p-3-i}) ≥ 3` implies
`v_p(∑ Bᵢ·B_{p-3-i}) ≥ 1` (in `padicNorm` form). -/
lemma reduction (p : ℕ) (hp : p.Prime) [Fact p.Prime] (hp7 : p ≥ 7)
    (hSig : padicNorm p (∑ i ∈ Finset.range (p - 2), S p i * S p (p - 3 - i))
      ≤ (p : ℚ) ^ (-3 : ℤ)) :
    padicNorm p (∑ i ∈ Finset.range (p - 2), bernoulli i * bernoulli (p - 3 - i))
      ≤ (p : ℚ) ^ (-1 : ℤ) := by
  set C := ∑ i ∈ Finset.range (p - 2), bernoulli i * bernoulli (p - 3 - i) with hC
  set Sig := ∑ i ∈ Finset.range (p - 2), S p i * S p (p - 3 - i) with hSigdef
  -- key: |Sig - p^2 * C| ≤ p^{-3}
  have hdiff : padicNorm p (Sig - (p : ℚ) ^ 2 * C) ≤ (p : ℚ) ^ (-3 : ℤ) := by
    have hrw : Sig - (p : ℚ) ^ 2 * C
        = ∑ i ∈ Finset.range (p - 2),
            (S p i * S p (p - 3 - i)
              - (p : ℚ) ^ 2 * (bernoulli i * bernoulli (p - 3 - i))) := by
      rw [hSigdef, hC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hrw]
    apply padicNorm.sum_le'
    · intro i hi
      rw [Finset.mem_range] at hi
      have identity : S p i * S p (p - 3 - i)
            - (p : ℚ) ^ 2 * (bernoulli i * bernoulli (p - 3 - i))
          = S p i * (S p (p - 3 - i) - (p : ℚ) * bernoulli (p - 3 - i))
            + (S p i - (p : ℚ) * bernoulli i) * ((p : ℚ) * bernoulli (p - 3 - i)) := by ring
      rw [identity]
      refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
      · -- |S_i * R_{p-3-i}| ≤ p^{-1} * p^{-2} = p^{-3}
        have h1 := norm_S_le p hp i (by omega) hp7
        have h2 := faulhaber_rem_norm p hp (p - 3 - i) (by omega) hp7
        have := norm_mul_le_zpow p h1 h2
        simpa using this
      · -- |R_i * (p * B_{p-3-i})| ≤ p^{-2} * p^{-1} = p^{-3}
        have h1 := faulhaber_rem_norm p hp i (by omega) hp7
        have h2 : padicNorm p ((p : ℚ) * bernoulli (p - 3 - i)) ≤ (p : ℚ) ^ (-1 : ℤ) := by
          have := norm_mul_le_zpow p (norm_p_eq p).le
            (norm_bernoulli_le p hp (k := p - 3 - i) (by omega))
          simpa using this
        have := norm_mul_le_zpow p h1 h2
        simpa using this
    · positivity
  -- p^2 * C = Sig - (Sig - p^2 C)
  have hpC : padicNorm p ((p : ℚ) ^ 2 * C) ≤ (p : ℚ) ^ (-3 : ℤ) := by
    have e : (p : ℚ) ^ 2 * C = Sig - (Sig - (p : ℚ) ^ 2 * C) := by ring
    rw [e]
    exact le_trans padicNorm.sub (max_le hSig hdiff)
  rw [padicNorm.mul] at hpC
  have hp2 : padicNorm p ((p : ℚ) ^ 2) = (p : ℚ) ^ (-2 : ℤ) := by
    have := norm_p_pow p 2; simpa using this
  rw [hp2, show (-3 : ℤ) = -2 + -1 by ring, zpow_add₀ (pne p)] at hpC
  exact le_of_mul_le_mul_left hpC (by
    have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
    positivity)

end Kernel
end Kernel_sec

section Star6_sec
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

open Finset BigOperators

namespace Star6

/-- Reduction of a cast inverse. -/
lemma phinv {p : ℕ} (hp : p.Prime) (D : p ∣ p ^ 5) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < p) :
    (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹) = ((i : ℕ) : ZMod p)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit ((i : ℕ) : ZMod (p ^ 5)) := HSums.isUnit_cast hp i hi1 hi2
  have hmul : ((i : ℕ) : ZMod (p ^ 5)) * ((i : ℕ) : ZMod (p ^ 5))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hc := congrArg (ZMod.castHom D (ZMod p)) hmul
  rw [map_mul, map_one, map_natCast] at hc
  have hi0 : ((i : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hi1 hi2
  calc (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)
      = ((i : ℕ) : ZMod p)⁻¹ * (((i : ℕ) : ZMod p) *
          (ZMod.castHom D (ZMod p)) (((i : ℕ) : ZMod (p ^ 5))⁻¹)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hi0, one_mul]
    _ = ((i : ℕ) : ZMod p)⁻¹ * 1 := by rw [hc]
    _ = ((i : ℕ) : ZMod p)⁻¹ := mul_one _

/-- ZMod p partial harmonic sums / aggregate sums. -/
noncomputable def T1' (p : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 (p - 1), (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2 * ((k : ZMod p)⁻¹) ^ 2

noncomputable def A22' (p : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 (p - 1), (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2

noncomputable def A13' (p : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 (p - 1), (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) * ((k : ZMod p)⁻¹) ^ 3

noncomputable def H4' (p : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4

lemma castHom_h1 {p : ℕ} (hp : p.Prime) (D : p ∣ p ^ 5) (m : ℕ) (hm : m < p) :
    (ZMod.castHom D (ZMod p)) (HSums.h1 p m) = ∑ i ∈ Icc 1 m, ((i : ZMod p)⁻¹) := by
  rw [HSums.h1, map_sum]
  apply Finset.sum_congr rfl
  intro i hi; rw [mem_Icc] at hi
  exact phinv hp D i hi.1 (by omega)

lemma castHom_h2 {p : ℕ} (hp : p.Prime) (D : p ∣ p ^ 5) (m : ℕ) (hm : m < p) :
    (ZMod.castHom D (ZMod p)) (HSums.h2 p m) = ∑ i ∈ Icc 1 m, ((i : ZMod p)⁻¹) ^ 2 := by
  rw [HSums.h2, map_sum]
  apply Finset.sum_congr rfl
  intro i hi; rw [mem_Icc] at hi
  rw [map_pow, phinv hp D i hi.1 (by omega)]

/-- The main reduction of `φ(Tbc)`. -/
lemma castHom_Tbc {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (D : p ∣ p ^ 5) :
    (ZMod.castHom D (ZMod p)) (HSums.Tbc p)
      = 10 * T1' p - 13 * A22' p - 16 * A13' p + 12 * H4' p := by
  rw [HSums.Tbc, map_sum]
  have hstep : ∀ k ∈ Icc 1 (p - 1),
      (ZMod.castHom D (ZMod p))
        ((10 * (HSums.h1 p (k - 1)) ^ 2 - 13 * (HSums.h2 p (k - 1))
          - 16 * (HSums.h1 p (k - 1)) * ((k : ZMod (p ^ 5))⁻¹)
          + 12 * ((k : ZMod (p ^ 5))⁻¹) ^ 2) * ((k : ZMod (p ^ 5))⁻¹) ^ 2)
      = 10 * ((∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2 * ((k : ZMod p)⁻¹) ^ 2)
        - 13 * ((∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2)
        - 16 * ((∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) * ((k : ZMod p)⁻¹) ^ 3)
        + 12 * (((k : ZMod p)⁻¹) ^ 4) := by
    intro k hk; rw [mem_Icc] at hk
    have hkp : k < p := by omega
    have hm : k - 1 < p := by omega
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
    rw [castHom_h1 hp D _ hm, castHom_h2 hp D _ hm, phinv hp D k (by omega) hkp]
    ring
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

lemma H4'_zero {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) : H4' p = 0 := by
  rw [H4']
  exact sum_inv_pow_zero 4 (by norm_num) (by omega)

/-- `(p-k)⁻¹ = -k⁻¹` in `ZMod p`. -/
lemma nu_neg {p : ℕ} [Fact p.Prime] (k : ℕ) (_hk1 : 1 ≤ k) (hk2 : k ≤ p - 1) :
    (((p - k : ℕ)) : ZMod p)⁻¹ = -(((k : ℕ) : ZMod p)⁻¹) := by
  have hkp : k ≤ p := by omega
  have : (((p - k : ℕ)) : ZMod p) = -((k : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hkp, ZMod.natCast_self]; ring
  rw [this, inv_neg]

/-- Reindexing the outer sum by `k ↦ p - k`. -/
lemma outer_reindex {p : ℕ} (hp7 : 7 ≤ p) (G : ℕ → ZMod p) :
    ∑ k ∈ Icc 1 (p - 1), G k = ∑ k ∈ Icc 1 (p - 1), G (p - k) := by
  apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
  · intro a ha; rw [mem_Icc] at ha ⊢; omega
  · intro a ha; rw [mem_Icc] at ha ⊢; omega
  · intro a ha; rw [mem_Icc] at ha; omega
  · intro a ha; rw [mem_Icc] at ha; omega
  · intro a ha; rw [mem_Icc] at ha; congr 1; omega

/-- Peel off the top term of a partial sum on `Icc 1 k`. -/
lemma sum_Icc_split {p : ℕ} (f : ℕ → ZMod p) (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Icc 1 k, f i = (∑ i ∈ Icc 1 (k - 1), f i) + f k := by
  conv_lhs => rw [show k = (k - 1) + 1 from by omega]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (k - 1) + 1)]
  rw [show (k - 1) + 1 = k from by omega]

/-- Reflection identity for partial power sums. -/
lemma reflect_j {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (j : ℕ) (hj : 0 < j) (hj2 : j < p - 1)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 1) :
    ∑ i ∈ Icc 1 (p - 1 - k), ((i : ZMod p)⁻¹) ^ j
      = (-1) ^ (j + 1) * ∑ i ∈ Icc 1 k, ((i : ZMod p)⁻¹) ^ j := by
  have hHj : ∑ i ∈ Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ j = 0 :=
    sum_inv_pow_zero j hj (by omega)
  have hdisj : Disjoint (Icc 1 (p - 1 - k)) (Icc (p - k) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx hy; rw [mem_Icc] at hx hy; omega
  have hset : Icc 1 (p - 1) = Icc 1 (p - 1 - k) ∪ Icc (p - k) (p - 1) := by
    ext x; simp only [mem_union, mem_Icc]; omega
  have hre0 : ∑ i ∈ Icc (p - k) (p - 1), ((i : ZMod p)⁻¹) ^ j
      = ∑ i ∈ Icc 1 k, (-(((i : ℕ) : ZMod p)⁻¹)) ^ j := by
    apply Finset.sum_nbij' (fun i => p - i) (fun i => p - i)
    · intro a ha; rw [mem_Icc] at ha ⊢; omega
    · intro a ha; rw [mem_Icc] at ha ⊢; omega
    · intro a ha; rw [mem_Icc] at ha; omega
    · intro a ha; rw [mem_Icc] at ha; omega
    · intro a ha; rw [mem_Icc] at ha
      rw [nu_neg a (by omega) (by omega), neg_neg]
  have hre : ∑ i ∈ Icc (p - k) (p - 1), ((i : ZMod p)⁻¹) ^ j
      = (-1) ^ j * ∑ i ∈ Icc 1 k, ((i : ZMod p)⁻¹) ^ j := by
    rw [hre0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; rw [neg_pow]
  rw [hset, Finset.sum_union hdisj, hre] at hHj
  have hj1 : ((-1 : ZMod p)) ^ (j + 1) = -(((-1 : ZMod p)) ^ j) := by rw [pow_succ]; ring
  rw [hj1]; linear_combination hHj

/-- `(2 : ZMod p) ≠ 0` for `p ≥ 7`. -/
lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma A22'_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : A22' p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey : A22' p = -A22' p - H4' p := by
    conv_lhs => rw [A22',
      outer_reindex hp7 (fun k => (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2)]
    rw [A22', H4', ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk; rw [mem_Icc] at hk
    have e1 : (p - k) - 1 = p - 1 - k := by omega
    rw [e1, reflect_j hp7 2 (by norm_num) (by omega) k hk.1 hk.2,
      sum_Icc_split (fun i => ((i : ZMod p)⁻¹) ^ 2) k hk.1, nu_neg k hk.1 hk.2]
    ring
  rw [H4'_zero hp7] at hkey
  have h2 : A22' p + A22' p = 0 := by linear_combination hkey
  have : (2 : ZMod p) * A22' p = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hp7)

lemma reflect_1 {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 1) :
    ∑ i ∈ Icc 1 (p - 1 - k), ((i : ZMod p)⁻¹) = ∑ i ∈ Icc 1 k, ((i : ZMod p)⁻¹) := by
  have h := reflect_j hp7 1 (by norm_num) (by omega) k hk1 hk2
  simpa using h

lemma A13'_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : A13' p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey : A13' p = -A13' p - H4' p := by
    conv_lhs => rw [A13',
      outer_reindex hp7 (fun k => (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) * ((k : ZMod p)⁻¹) ^ 3)]
    rw [A13', H4', ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk; rw [mem_Icc] at hk
    have e1 : (p - k) - 1 = p - 1 - k := by omega
    rw [e1, reflect_1 hp7 k hk.1 hk.2,
      sum_Icc_split (fun i => ((i : ZMod p)⁻¹)) k hk.1, nu_neg k hk.1 hk.2]
    ring
  rw [H4'_zero hp7] at hkey
  have h2 : A13' p + A13' p = 0 := by linear_combination hkey
  have : (2 : ZMod p) * A13' p = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hp7)

/-- Bridge: a rational with `padicNorm ≤ p⁻¹` casts to `0` in `ZMod p`. -/
lemma bridge {p : ℕ} [Fact p.Prime] (x : ℚ) (hx : padicNorm p x ≤ (p : ℚ) ^ (-1 : ℤ)) :
    (x : ZMod p) = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hp : p.Prime := Fact.out
    have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
    rw [padicNorm.eq_zpow_of_nonzero hx0] at hx
    have hvle : -padicValRat p x ≤ -1 := (zpow_le_zpow_iff_right₀ hp1).mp hx
    have hv1 : (1 : ℤ) ≤ padicValRat p x := by linarith
    have hnum : (p : ℤ) ∣ x.num := by
      have hdef := padicValRat_def p x
      have hvv : (1 : ℤ) ≤ (padicValInt p x.num : ℤ) := by
        rw [hdef] at hv1
        have hn : (0 : ℤ) ≤ (padicValNat p x.den : ℤ) := Nat.cast_nonneg _
        omega
      have hd := (padicValInt_dvd_iff 1 x.num).mpr (Or.inr (by exact_mod_cast hvv))
      simpa using hd
    rw [Rat.cast_def]
    have hz : (x.num : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hnum
    rw [hz, zero_div]

/-- `C̄ = 0` in `ZMod p`. -/
lemma Cbar_zero {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((∑ k ∈ Finset.range (p - 2), bernoulli k * bernoulli (p - 3 - k) : ℚ) : ZMod p) = 0 :=
  bridge _ (C_padicNorm p hp hp7)

/-- The explicit natural number whose class mod `p` is `T1'`.
`N_k = ∑_{i=1}^{k-1} i^{p-2}` is the integer partial power sum with `(N_k : ZMod p) = h̄₁(k-1)`,
and `M = ∑_{k=1}^{p-1} N_k² · (k^{p-2})²`. -/
def Mnat (p : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 (p - 1), (∑ i ∈ Icc 1 (k - 1), i ^ (p - 2)) ^ 2 * (k ^ (p - 2)) ^ 2

/-- `T1'` is the reduction mod `p` of the explicit integer `Mnat p`
(using Fermat `x⁻¹ = x^{p-2}`). -/
lemma T1'_eq {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) : T1' p = ((Mnat p : ℕ) : ZMod p) := by
  rw [T1', Mnat, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk; rw [mem_Icc] at hk
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hinner : (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹))
      = ((∑ i ∈ Icc 1 (k - 1), i ^ (p - 2) : ℕ) : ZMod p) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi; rw [mem_Icc] at hi
    have hi0 : ((i : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [MZV4.inv_eq_pow hi0, Nat.cast_pow]
  rw [hinner, MZV4.inv_eq_pow hk0]
  push_cast
  ring

-- (p-1 : ZMod p) = -1
lemma natCast_pred_eq {p : ℕ} [Fact p.Prime] (hp2 : 2 ≤ p) :
    ((p - 1 : ℕ) : ZMod p) = -1 := by
  have h1 : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [h1, ZMod.natCast_self]; ring

-- choose cast: (p-1).choose r ≡ (-1)^r mod p
lemma choose_cast {p : ℕ} [Fact p.Prime] (hp2 : 2 ≤ p) :
    ∀ r, r ≤ p - 1 → (((p - 1).choose r : ℕ) : ZMod p) = (-1) ^ r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hrec : (p - 1).choose (k + 1) * (k + 1) = (p - 1).choose k * (p - 1 - k) :=
      Nat.choose_succ_right_eq (p - 1) k
    have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hrec
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
    have hpk : ((p - 1 - k : ℕ) : ZMod p) = -((k : ZMod p) + 1) := by
      have : ((p - 1 - k : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) - (k : ZMod p) := by
        rw [Nat.cast_sub (by omega)]
      rw [this, natCast_pred_eq hp2]; ring
    rw [hpk, ih (by omega)] at hcast
    -- hcast : C(k+1)*(k+1) = (-1)^k * (-((k)+1))
    have hk1 : ((k : ZMod p) + 1) ≠ 0 := by
      have : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simpa using this
    have : (((p - 1).choose (k + 1) : ℕ) : ZMod p) * ((k : ZMod p) + 1)
        = (-1) ^ (k + 1) * ((k : ZMod p) + 1) := by
      rw [hcast]; ring
    exact mul_right_cancel₀ hk1 this

-- power sum over Icc 1 (p-1)
lemma sum_pow_Icc {p : ℕ} [Fact p.Prime] (M : ℕ) (hM : 0 < M) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ℕ) : ZMod p) ^ M
      = if (p - 1) ∣ M then -1 else 0 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  by_cases hdvd : (p - 1) ∣ M
  · rw [if_pos hdvd]
    -- each term is 1
    obtain ⟨t, ht⟩ := hdvd
    have hterm : ∀ k ∈ Icc 1 (p - 1), ((k : ℕ) : ZMod p) ^ M = 1 := by
      intro k hk; rw [mem_Icc] at hk
      have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one hk0, one_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc]
    have : (p - 1 + 1 - 1) = p - 1 := by omega
    rw [this, nsmul_eq_mul, mul_one, natCast_pred_eq hp2]
  · rw [if_neg hdvd]
    -- reduce M mod (p-1)
    set r := M % (p - 1) with hr
    have hp1 : 0 < p - 1 := by omega
    have hrlt : r < p - 1 := Nat.mod_lt _ hp1
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hdvd
      · exact h
    have hMr : M = (p - 1) * (M / (p - 1)) + r := (Nat.div_add_mod M (p - 1)).symm
    have hterm : ∀ k ∈ Icc 1 (p - 1), ((k : ℕ) : ZMod p) ^ M = ((k : ℕ) : ZMod p) ^ r := by
      intro k hk; rw [mem_Icc] at hk
      have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      conv_lhs => rw [hMr, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hk0, one_pow, one_mul]
    rw [Finset.sum_congr rfl hterm]
    -- now ∑ k^r = 0 since 0 < r < p-1
    rw [MZV4.sum_Icc_erase (fun x => x ^ r)]
    have h0 : (0 : ZMod p) ^ r = 0 := zero_pow hr0.ne'
    have hall : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), x ^ r = ∑ x : ZMod p, x ^ r := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), h0, add_zero]
    rw [hall]
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have : r < Fintype.card (ZMod p) - 1 := by rw [hcard]; omega
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) r this

-- Bernoulli denominators are coprime to p for r < p-1.
lemma bernoulli_den_ndvd {p : ℕ} (hp : p.Prime) [Fact p.Prime] {r : ℕ} (hr : r < p - 1) :
    ¬ (p ∣ (bernoulli r).den) := by
  intro hdvd
  have hnonneg : 0 ≤ padicValRat p (bernoulli r) :=
    Kernel.bernoulli_padic_nonneg p hp (by omega) r hr
  set q := bernoulli r with hq
  have hden0 : q.den ≠ 0 := q.den_nz
  -- padicValNat p q.den ≥ 1
  have hden_ge : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd hden0 hdvd
  -- q ≠ 0 (else den = 1, contradiction with p ∣ 1)
  have hqne : q ≠ 0 := by
    intro h; rw [h] at hdvd
    have : (0 : ℚ).den = 1 := rfl
    rw [this] at hdvd
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd)
  -- num coprime to den ⟹ p ∤ num.natAbs
  have hnumne : q.num ≠ 0 := Rat.num_ne_zero.mpr hqne
  have hcop : q.num.natAbs.Coprime q.den := q.reduced
  have hpnum : ¬ p ∣ q.num.natAbs := by
    intro h
    have hdvd_gcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h hdvd
    rw [hcop] at hdvd_gcd
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd_gcd)
  have hnum_val : padicValInt p q.num = 0 := by
    rw [padicValInt, padicValNat.eq_zero_of_not_dvd hpnum]
  have hdef := padicValRat_def p q
  have hv : padicValRat p q = -(padicValNat p q.den : ℤ) := by
    rw [hdef, hnum_val]; simp
  rw [hv] at hnonneg
  have h1 : (1 : ℤ) ≤ (padicValNat p q.den : ℤ) := by exact_mod_cast hden_ge
  omega

/-- If `q.den ∣ D` then `D * q` is an integer. -/
lemma mul_den_eq_one (D : ℕ) (q : ℚ) (h : (q.den : ℤ) ∣ (D : ℤ)) :
    ((D : ℚ) * q).den = 1 := by
  obtain ⟨t, ht⟩ := h
  have key : (q.den : ℚ) * q = (q.num : ℚ) := Rat.den_mul_eq_num q
  have hD : (D : ℚ) = (q.den : ℚ) * (t : ℚ) := by exact_mod_cast ht
  have : (D : ℚ) * q = ((q.num * t : ℤ) : ℚ) := by
    rw [hD]; push_cast
    rw [mul_comm (q.den : ℚ) (t : ℚ), mul_assoc, key]; ring
  rw [this, Rat.den_intCast]

noncomputable def Dp (p : ℕ) : ℕ := ∏ r ∈ Finset.range (p - 1), (bernoulli r).den

noncomputable def bc (p r : ℕ) : ℤ := ((Dp p : ℚ) * bernoulli r).num

lemma Dp_pos (p : ℕ) : 0 < Dp p := by
  rw [Dp]; apply Finset.prod_pos
  intro r _; exact (bernoulli r).pos

lemma den_dvd_Dp {p r : ℕ} (hr : r ∈ Finset.range (p - 1)) :
    (bernoulli r).den ∣ Dp p := by
  rw [Dp]; exact Finset.dvd_prod_of_mem _ hr

lemma bc_spec {p r : ℕ} (hr : r ∈ Finset.range (p - 1)) :
    ((bc p r : ℤ) : ℚ) = (Dp p : ℚ) * bernoulli r := by
  have hden1 : ((Dp p : ℚ) * bernoulli r).den = 1 := by
    apply mul_den_eq_one
    exact_mod_cast den_dvd_Dp hr
  rw [bc]
  exact (Rat.den_eq_one_iff _).mp hden1

lemma p_ndvd_Dp {p : ℕ} (hp : p.Prime) [Fact p.Prime] : ¬ p ∣ Dp p := by
  rw [Dp, Prime.dvd_finset_prod_iff hp.prime]
  rintro ⟨r, hr, hd⟩
  rw [Finset.mem_range] at hr
  exact bernoulli_den_ndvd hp hr hd

lemma Dp_cast_ne {p : ℕ} (hp : p.Prime) [Fact p.Prime] : ((Dp p : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact p_ndvd_Dp hp

noncomputable def Ninner (p k : ℕ) : ℕ := ∑ i ∈ Finset.range k, i ^ (p - 2)

-- rational Faulhaber, multiplied by (p-1)
lemma faulhaber_rat {p : ℕ} (hp2 : 2 ≤ p) (k : ℕ) :
    ((p - 1 : ℕ) : ℚ) * (∑ i ∈ Finset.range k, (i : ℚ) ^ (p - 2))
      = ∑ r ∈ Finset.range (p - 1),
          bernoulli r * (((p - 1).choose r : ℕ) : ℚ) * (k : ℚ) ^ (p - 1 - r) := by
  have hpow := sum_range_pow k (p - 2)
  rw [hpow, Finset.mul_sum]
  have he : (p - 2) + 1 = p - 1 := by omega
  have hdenne : ((p - 2 : ℕ) : ℚ) + 1 ≠ 0 := by
    have : (0 : ℚ) ≤ ((p - 2 : ℕ) : ℚ) := by positivity
    positivity
  rw [he]
  apply Finset.sum_congr rfl
  intro r hr
  have hcast : ((p - 2 : ℕ) : ℚ) + 1 = ((p - 1 : ℕ) : ℚ) := by
    rw [← he]; push_cast; ring
  rw [hcast]
  have hne : ((p - 1 : ℕ) : ℚ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; omega
  field_simp

lemma Ninner_cast (p k : ℕ) :
    ((Ninner p k : ℕ) : ℚ) = ∑ i ∈ Finset.range k, (i : ℚ) ^ (p - 2) := by
  rw [Ninner]; push_cast; rfl

-- integer Faulhaber identity
lemma faulhaber_int {p : ℕ} (hp2 : 2 ≤ p) (k : ℕ) :
    ((Dp p : ℤ) * ((p - 1 : ℕ) : ℤ) * ((Ninner p k : ℕ) : ℤ))
      = ∑ r ∈ Finset.range (p - 1),
          bc p r * (((p - 1).choose r : ℕ) : ℤ) * (k : ℤ) ^ (p - 1 - r) := by
  have hq : ((Dp p : ℤ) : ℚ) * (((p - 1 : ℕ) : ℤ) : ℚ) * (((Ninner p k : ℕ) : ℤ) : ℚ)
      = ∑ r ∈ Finset.range (p - 1),
          ((bc p r : ℤ) : ℚ) * ((((p - 1).choose r : ℕ) : ℤ) : ℚ) * (((k : ℤ) : ℚ)) ^ (p - 1 - r) := by
    have hR : ∑ r ∈ Finset.range (p - 1),
          ((bc p r : ℤ) : ℚ) * ((((p - 1).choose r : ℕ) : ℤ) : ℚ) * (((k : ℤ) : ℚ)) ^ (p - 1 - r)
        = (Dp p : ℚ) * ∑ r ∈ Finset.range (p - 1),
            bernoulli r * (((p - 1).choose r : ℕ) : ℚ) * (k : ℚ) ^ (p - 1 - r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [bc_spec hr]
      push_cast
      ring
    rw [hR, ← faulhaber_rat hp2 k, Ninner]
    push_cast
    ring
  exact_mod_cast hq

noncomputable def gam (p r : ℕ) : ZMod p := (Dp p : ZMod p)⁻¹ * ((bc p r : ℤ) : ZMod p)

lemma faulhaber_zmod {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) (k : ℕ) :
    ((Ninner p k : ℕ) : ZMod p)
      = ∑ r ∈ Finset.range (p - 1), (-1) ^ (r + 1) * gam p r * (k : ZMod p) ^ (p - 1 - r) := by
  have hp2 : 2 ≤ p := by omega
  have hDp : (Dp p : ZMod p) ≠ 0 := Dp_cast_ne hp
  -- cast the integer identity into ZMod p
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) (faulhaber_int hp2 k)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_pow] at hz
  -- rewrite (p-1) cast = -1 and choose = (-1)^r
  rw [natCast_pred_eq hp2] at hz
  have hchoose : ∀ r ∈ Finset.range (p - 1),
      ((bc p r : ℤ) : ZMod p) * (((p - 1).choose r : ℕ) : ZMod p) * (k : ZMod p) ^ (p - 1 - r)
        = ((bc p r : ℤ) : ZMod p) * (-1) ^ r * (k : ZMod p) ^ (p - 1 - r) := by
    intro r hr; rw [Finset.mem_range] at hr
    rw [choose_cast hp2 r (by omega)]
  rw [Finset.sum_congr rfl hchoose] at hz
  set S := ∑ r ∈ Finset.range (p - 1),
      ((bc p r : ℤ) : ZMod p) * (-1) ^ r * (k : ZMod p) ^ (p - 1 - r) with hS
  -- hz : Dp * (-1) * Ninner = S
  have hgoal : ∑ r ∈ Finset.range (p - 1), (-1) ^ (r + 1) * gam p r * (k : ZMod p) ^ (p - 1 - r)
      = -(Dp p : ZMod p)⁻¹ * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _; rw [gam]; ring
  rw [hgoal, ← hz]
  rw [show -(Dp p : ZMod p)⁻¹ * ((Dp p : ZMod p) * (-1) * ((Ninner p k : ℕ) : ZMod p))
        = ((Dp p : ZMod p)⁻¹ * (Dp p : ZMod p)) * ((Ninner p k : ℕ) : ZMod p) by ring]
  rw [inv_mul_cancel₀ hDp, one_mul]

lemma Ninner_Icc {p : ℕ} (hp3 : 3 ≤ p) (k : ℕ) :
    Ninner p k = ∑ i ∈ Icc 1 (k - 1), i ^ (p - 2) := by
  rw [Ninner]
  have hIco : Finset.Ico 1 k = Icc 1 (k - 1) := val_inj.mp rfl
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [← hIco, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk,
        zero_pow (show p - 2 ≠ 0 by omega), zero_add]

lemma gam_pm2_zero {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) :
    gam p (p - 2) = 0 := by
  have hodd : Odd (p - 2) := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · rcases h with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
  have hb0 : bernoulli (p - 2) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
  have : bc p (p - 2) = 0 := by
    rw [bc, hb0, mul_zero]; rfl
  rw [gam, this]; simp

lemma hbar_eq {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) = ((Ninner p k : ℕ) : ZMod p) := by
  rw [Ninner_Icc (by omega) k, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi; rw [mem_Icc] at hi
  have hi0 : ((i : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  rw [MZV4.inv_eq_pow hi0, Nat.cast_pow]

-- per-term expansion
lemma T1p_key {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) :
    ∀ k ∈ Icc 1 (p - 1),
      (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2 * ((k : ZMod p)⁻¹) ^ 2
        = ∑ r ∈ Finset.range (p - 1), ∑ s ∈ Finset.range (p - 1),
            ((-1) ^ (r + 1) * gam p r * (k : ZMod p) ^ (p - 1 - r)) *
            ((-1) ^ (s + 1) * gam p s * (k : ZMod p) ^ (p - 1 - s)) *
            ((k : ZMod p) ^ (p - 2)) ^ 2 := by
  intro k hk; rw [mem_Icc] at hk
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  rw [hbar_eq hp7 k hk.2, faulhaber_zmod hp hp7 k, MZV4.inv_eq_pow hk0]
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]

lemma T1p_eq_ps {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) :
    T1' p = ∑ r ∈ Finset.range (p - 1), ∑ s ∈ Finset.range (p - 1),
        ((-1) ^ (r + 1) * gam p r * ((-1) ^ (s + 1) * gam p s)) *
          (if (p - 1) ∣ ((p - 1 - r) + (p - 1 - s) + 2 * (p - 2)) then (-1 : ZMod p) else 0) := by
  rw [T1', Finset.sum_congr rfl (T1p_key hp hp7), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  -- goal: ∑ k ∈ Icc 1 (p-1), TERM(k,r,s) = coeff * (if ...)
  have hterm : ∀ k : ℕ,
      ((-1) ^ (r + 1) * gam p r * (k : ZMod p) ^ (p - 1 - r)) *
        ((-1) ^ (s + 1) * gam p s * (k : ZMod p) ^ (p - 1 - s)) *
        ((k : ZMod p) ^ (p - 2)) ^ 2
      = ((-1) ^ (r + 1) * gam p r * ((-1) ^ (s + 1) * gam p s)) *
          (k : ZMod p) ^ ((p - 1 - r) + (p - 1 - s) + 2 * (p - 2)) := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum,
      sum_pow_Icc _ (by omega)]

lemma gam_conv_zero {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) :
    ∑ r ∈ Finset.range (p - 2), gam p r * gam p (p - 3 - r) = 0 := by
  set Eint : ℤ := ∑ r ∈ Finset.range (p - 2), bc p r * bc p (p - 3 - r) with hEdef
  have hcast : ∑ r ∈ Finset.range (p - 2), gam p r * gam p (p - 3 - r)
      = ((Dp p : ZMod p)⁻¹) ^ 2 * ((Eint : ℤ) : ZMod p) := by
    rw [hEdef, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _; rw [gam, gam, Int.cast_mul]; ring
  rw [hcast]
  have hQ : ((Eint : ℤ) : ℚ)
      = (Dp p : ℚ) ^ 2 * (∑ k ∈ Finset.range (p - 2), bernoulli k * bernoulli (p - 3 - k)) := by
    rw [hEdef]; push_cast [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr; rw [Finset.mem_range] at hr
    rw [bc_spec (Finset.mem_range.mpr (by omega : r < p - 1)),
        bc_spec (Finset.mem_range.mpr (by omega : p - 3 - r < p - 1))]
    ring
  have hE0 : ((Eint : ℤ) : ZMod p) = 0 := by
    have hz : (((Eint : ℤ) : ℚ) : ZMod p) = 0 := by
      apply bridge
      rw [hQ, padicNorm.mul]
      calc padicNorm p ((Dp p : ℚ) ^ 2)
            * padicNorm p (∑ k ∈ Finset.range (p - 2), bernoulli k * bernoulli (p - 3 - k))
          ≤ 1 * (p : ℚ) ^ (-1 : ℤ) := by
            apply mul_le_mul _ (C_padicNorm p hp hp7) (padicNorm.nonneg _) (by norm_num)
            rw [sq, padicNorm.mul]
            have := padicNorm.of_nat (p := p) (Dp p)
            nlinarith [padicNorm.nonneg (p := p) ((Dp p : ℚ))]
        _ = (p : ℚ) ^ (-1 : ℤ) := one_mul _
    rwa [Rat.cast_intCast] at hz
  rw [hE0, mul_zero]

lemma hcond (p r s : ℕ) (hp7 : 7 ≤ p) (hr : r ≤ p - 3) (hs : s ≤ p - 3) :
    ((p - 1) ∣ ((p - 1 - r) + (p - 1 - s) + 2 * (p - 2))) ↔ (r + s = p - 3) := by
  have hElo : 2 * p ≤ (p - 1 - r) + (p - 1 - s) + 2 * (p - 2) := by omega
  have hEhi : (p - 1 - r) + (p - 1 - s) + 2 * (p - 2) < (p - 1) * 4 := by omega
  constructor
  · intro hd
    obtain ⟨m, hm⟩ := hd
    rw [hm] at hElo hEhi
    have h4 : m < 4 := Nat.lt_of_mul_lt_mul_left hEhi
    have h3 : 3 ≤ m := by
      by_contra h; push_neg at h
      have : (p - 1) * m ≤ (p - 1) * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
    have hm3 : m = 3 := by omega
    rw [hm3] at hm; omega
  · intro h; exact ⟨3, by omega⟩

lemma T1p_zero {p : ℕ} (hp : p.Prime) [Fact p.Prime] (hp7 : 7 ≤ p) : T1' p = 0 := by
  have hgam2 : gam p (p - 2) = 0 := gam_pm2_zero hp hp7
  have hev : Even (p - 1) := by
    rcases hp.odd_of_ne_two (by omega) with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hsub : Finset.range (p - 2) ⊆ Finset.range (p - 1) := by
    intro x hx; rw [Finset.mem_range] at *; omega
  rw [T1p_eq_ps hp hp7]
  have hmain : ∑ r ∈ Finset.range (p - 1), ∑ s ∈ Finset.range (p - 1),
        ((-1) ^ (r + 1) * gam p r * ((-1) ^ (s + 1) * gam p s)) *
          (if (p - 1) ∣ ((p - 1 - r) + (p - 1 - s) + 2 * (p - 2)) then (-1 : ZMod p) else 0)
      = ∑ r ∈ Finset.range (p - 2), -(gam p r * gam p (p - 3 - r)) := by
    rw [← Finset.sum_subset hsub (fun r hr hr2 => by
        rw [Finset.mem_range] at hr; simp only [Finset.mem_range, not_lt] at hr2
        have hrp2 : r = p - 2 := by omega
        apply Finset.sum_eq_zero; intro s _; rw [hrp2, hgam2]; ring)]
    apply Finset.sum_congr rfl
    intro r hr; rw [Finset.mem_range] at hr
    rw [← Finset.sum_subset hsub (fun s hs hs2 => by
        rw [Finset.mem_range] at hs; simp only [Finset.mem_range, not_lt] at hs2
        have hsp2 : s = p - 2 := by omega
        rw [hsp2, hgam2]; ring)]
    rw [Finset.sum_eq_single (p - 3 - r)]
    · rw [if_pos ((hcond p r (p - 3 - r) hp7 (by omega) (by omega)).mpr (by omega))]
      have hsign : (-1 : ZMod p) ^ (r + 1) * (-1 : ZMod p) ^ ((p - 3 - r) + 1) = 1 := by
        rw [← pow_add, show (r + 1) + ((p - 3 - r) + 1) = p - 1 from by omega]
        exact hev.neg_one_pow
      calc ((-1 : ZMod p) ^ (r + 1) * gam p r * ((-1) ^ ((p - 3 - r) + 1) * gam p (p - 3 - r))) * (-1)
          = ((-1 : ZMod p) ^ (r + 1) * (-1) ^ ((p - 3 - r) + 1)) *
              (gam p r * gam p (p - 3 - r)) * (-1) := by ring
        _ = 1 * (gam p r * gam p (p - 3 - r)) * (-1) := by rw [hsign]
        _ = -(gam p r * gam p (p - 3 - r)) := by ring
    · intro b hb hbne; rw [Finset.mem_range] at hb
      rw [if_neg (fun hdvd => hbne (by
        have := (hcond p r b hp7 (by omega) (by omega)).mp hdvd; omega))]
      ring
    · intro hcontra
      exact absurd (Finset.mem_range.mpr (by omega : p - 3 - r < p - 2)) hcontra
  rw [hmain, Finset.sum_neg_distrib, gam_conv_zero hp hp7, neg_zero]

/-- **Remaining Faulhaber / Bernoulli-convolution supercongruence.**
This is the statement `p ∣ M`, equivalently `T1' ≡ 0 (mod p)`.  Numerically verified for
`p = 7,…,29`.  It is exactly the finite multiple harmonic sum identity
`T1' ≡ -∑_{i} B_i B_{p-3-i} (mod p)` (Faulhaber expansion of the partial power sums
`N_k` in terms of Bernoulli numbers), combined with `Cbar_zero`.  Transferring the
rational Faulhaber identity `Finset.sum_range_pow` to `ZMod p` is the genuine
number-theoretic core (a Wolstenholme-type supercongruence), of the same nature as the
`sigma_supercong` gap left open in `Submission/Kernel.lean`. -/
lemma Mnat_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : p ∣ Mnat p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : T1' p = 0 := T1p_zero hp hp7
  rw [T1'_eq hp7] at h
  rwa [ZMod.natCast_eq_zero_iff] at h

lemma T1'_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : T1' p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [T1'_eq hp7, ZMod.natCast_eq_zero_iff]
  exact Mnat_dvd hp hp7

theorem Tbc_dvd (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ c : ZMod (p ^ 5), HSums.Tbc p = HSums.q p * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine HSums.dvd_of_cast_zero hp _ D ?_
  rw [castHom_Tbc hp hp7 D, T1'_zero hp hp7, A22'_zero hp hp7, A13'_zero hp hp7, H4'_zero hp7]
  ring

end Star6
end Star6_sec

section Star5_sec

open Nat Finset BigOperators

namespace Star5
open HSums

/-- Reindex the triangular double sum `∑_{k}∑_{i<k} F i (k-i)` to `∑_{i}∑_{j, i+j≤p-1} F i j`. -/
lemma triangle_reindex {A : Type*} [AddCommMonoid A] (p : ℕ) (F : ℕ → ℕ → A) :
    ∑ k ∈ Icc 1 (p - 1), ∑ i ∈ Icc 1 (k - 1), F i (k - i)
      = ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i), F i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun x => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ))
    (fun y => (⟨y.1 + y.2, y.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨k, i⟩ hx
    simp only [Finset.mem_sigma, mem_Icc] at hx ⊢; omega
  · rintro ⟨i, j⟩ hy
    simp only [Finset.mem_sigma, mem_Icc] at hy ⊢; omega
  · rintro ⟨k, i⟩ hx
    simp only [Finset.mem_sigma, mem_Icc] at hx
    have h : i + (k - i) = k := by omega
    simp only [h]
  · rintro ⟨i, j⟩ hy
    simp only [Finset.mem_sigma, mem_Icc] at hy
    have h : (i + j) - i = j := by omega
    simp only [h]
  · rintro ⟨k, i⟩ hx; rfl

/-- Swap `i ↔ j` in the triangular double sum. -/
lemma triangle_swap {A : Type*} [AddCommMonoid A] (p : ℕ) (F : ℕ → ℕ → A) :
    ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i), F i j
      = ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i), F j i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun x => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ))
    (fun y => (⟨y.2, y.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨i, j⟩ hx; simp only [Finset.mem_sigma, mem_Icc] at hx ⊢; omega
  · rintro ⟨i, j⟩ hy; simp only [Finset.mem_sigma, mem_Icc] at hy ⊢; omega
  · rintro ⟨i, j⟩ hx; rfl
  · rintro ⟨i, j⟩ hy; rfl
  · rintro ⟨i, j⟩ hx; rfl

/-- Pairing identity: `∑_{i=1}^{s-1} 1/(i(s-i)) = (1/s)·2·∑_{i=1}^{s-1} 1/i`. -/
lemma pair_sum {N : ℕ} (s : ℕ) (hs : IsUnit ((s : ℕ) : ZMod N))
    (hunits : ∀ i, 1 ≤ i → i ≤ s - 1 → IsUnit ((i : ℕ) : ZMod N)) :
    ∑ i ∈ Icc 1 (s - 1), ((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹)
      = (s : ZMod N)⁻¹ * 2 * (∑ i ∈ Icc 1 (s - 1), ((i : ZMod N)⁻¹)) := by
  have hpt : ∀ i ∈ Icc 1 (s - 1), ((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹)
      = (s : ZMod N)⁻¹ * (((i : ZMod N)⁻¹) + (((s - i : ℕ) : ZMod N)⁻¹)) := by
    intro i hi; rw [mem_Icc] at hi
    have hui := ZMod.mul_inv_of_unit _ (hunits i hi.1 hi.2)
    have hus := ZMod.mul_inv_of_unit _ (hunits (s - i) (by omega) (by omega))
    have hsinv := ZMod.inv_mul_of_unit _ hs
    have hcast : ((s : ℕ) : ZMod N) = ((i : ℕ) : ZMod N) + (((s - i : ℕ)) : ZMod N) := by
      rw [← Nat.cast_add]; congr 1; omega
    have KEY : ((s : ℕ) : ZMod N) * (((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹))
        = ((i : ZMod N)⁻¹) + (((s - i : ℕ) : ZMod N)⁻¹) := by
      linear_combination (((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹)) * hcast
        + (((s - i : ℕ) : ZMod N)⁻¹) * hui + ((i : ZMod N)⁻¹) * hus
    calc ((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹)
        = (s : ZMod N)⁻¹ * (((s : ℕ) : ZMod N)
            * (((i : ZMod N)⁻¹) * (((s - i : ℕ) : ZMod N)⁻¹))) := by
          rw [← mul_assoc, hsinv, one_mul]
      _ = (s : ZMod N)⁻¹ * (((i : ZMod N)⁻¹) + (((s - i : ℕ) : ZMod N)⁻¹)) := by rw [KEY]
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hrefl : ∑ i ∈ Icc 1 (s - 1), (((s - i : ℕ) : ZMod N)⁻¹)
      = ∑ i ∈ Icc 1 (s - 1), ((i : ZMod N)⁻¹) := by
    apply Finset.sum_nbij' (fun i => s - i) (fun i => s - i)
    · intro a ha; rw [mem_Icc] at ha ⊢; omega
    · intro a ha; rw [mem_Icc] at ha ⊢; omega
    · intro a ha; rw [mem_Icc] at ha; omega
    · intro a ha; rw [mem_Icc] at ha; omega
    · intro a ha; rfl
  rw [hrefl]; ring

/-- Recursion for the partial harmonic sum. -/
lemma h1_rec {p : ℕ} (k : ℕ) (hk : 1 ≤ k) :
    HSums.h1 p k = HSums.h1 p (k - 1) + ((k : ZMod (p ^ 5))⁻¹) := by
  have hk1 : k = (k - 1) + 1 := by omega
  conv_lhs => rw [HSums.h1, hk1]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (k - 1) + 1)]
  rw [HSums.h1]
  congr 1
  rw [← hk1]

/-- `H p 1 = h1 p (p-1)`. -/
lemma H1_eq (p : ℕ) : H p 1 = HSums.h1 p (p - 1) := by
  rw [H, HSums.h1]; apply Finset.sum_congr rfl; intro i _; rw [pow_one]

/-- The square of the first harmonic sum: `H1² = H2 + 2·∑ h1(k-1)/k`. -/
lemma H1sq (p : ℕ) :
    (H p 1) ^ 2 = H p 2
      + 2 * ∑ k ∈ Icc 1 (p - 1), HSums.h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹) := by
  have key_term : ∀ k ∈ Icc 1 (p - 1),
      HSums.h1 p k ^ 2 - HSums.h1 p (k - 1) ^ 2
        = 2 * (HSums.h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹)) + ((k : ZMod (p ^ 5))⁻¹) ^ 2 := by
    intro k hk; rw [mem_Icc] at hk
    have hrec := h1_rec (p := p) k hk.1
    rw [hrec]; ring
  have htel : ∑ k ∈ Icc 1 (p - 1), (HSums.h1 p k ^ 2 - HSums.h1 p (k - 1) ^ 2)
      = HSums.h1 p (p - 1) ^ 2 := by
    calc ∑ k ∈ Icc 1 (p - 1), (HSums.h1 p k ^ 2 - HSums.h1 p (k - 1) ^ 2)
        = ∑ x ∈ range (p - 1), (HSums.h1 p (x + 1) ^ 2 - HSums.h1 p x ^ 2) := by
          rw [show Icc 1 (p - 1) = Finset.Ico 1 ((p - 1) + 1) from rfl,
            Finset.sum_Ico_eq_sum_range]
          apply Finset.sum_congr rfl; intro x _
          rw [Nat.add_comm 1 x, Nat.add_sub_cancel]
      _ = HSums.h1 p (p - 1) ^ 2 - HSums.h1 p 0 ^ 2 :=
          Finset.sum_range_sub (fun m => HSums.h1 p m ^ 2) (p - 1)
      _ = HSums.h1 p (p - 1) ^ 2 := by
          rw [show HSums.h1 p 0 = 0 from by rw [HSums.h1]; simp]; ring
  have hcomb : ∑ k ∈ Icc 1 (p - 1),
      (2 * (HSums.h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹)) + ((k : ZMod (p ^ 5))⁻¹) ^ 2)
      = HSums.h1 p (p - 1) ^ 2 := by
    rw [← htel]; exact (Finset.sum_congr rfl key_term).symm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    show (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 5))⁻¹) ^ 2) = H p 2 from rfl] at hcomb
  rw [H1_eq p]
  linear_combination -hcomb

/-- `V = ∑_{i,j≥1, i+j≤p-1} 1/(ij) = H1² - H2`. -/
lemma V_eq {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
        ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹)
      = (H p 1) ^ 2 - H p 2 := by
  have hV2W : (∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
        ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹))
      = 2 * ∑ k ∈ Icc 1 (p - 1), HSums.h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹) := by
    rw [← triangle_reindex p (fun i j => (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk; rw [mem_Icc] at hk
    rw [pair_sum k (HSums.isUnit_cast hp k (by omega) (by omega))
      (fun i h1 h2 => HSums.isUnit_cast hp i h1 (by omega))]
    rw [show (∑ i ∈ Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹)) = HSums.h1 p (k - 1) from rfl]
    ring
  rw [hV2W]
  linear_combination -(H1sq p)

/-- The double sum `U = ∑_{i,j≥1, i+j≤p-1} 1/(ij(i+j))`. -/
noncomputable def Da (p : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
    (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * ((i + j : ℕ) : ZMod (p ^ 5))⁻¹

/-- The composition sum `Sₙ' = ∑_{i,j≥1, i+j≤p-1} 1/(i·j·l^n)`, with `l = p-i-j`. -/
noncomputable def Ssum (p n : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
    (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ n

/-- A cast is a unit in `ZMod p` (field). -/
lemma isUnit_castp {p : ℕ} [Fact p.Prime] (i : ℕ) (h1 : 1 ≤ i) (h2 : i < p) :
    IsUnit ((i : ℕ) : ZMod p) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt h1 h2

/-- **Step 1** : `2·Ta = U`. -/
lemma Ta_U {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : 2 * Ta p = Da p := by
  have step : ∀ k ∈ Icc 1 (p - 1),
      2 * (HSums.h1 p (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2)
        = ∑ i ∈ Icc 1 (k - 1),
            (i : ZMod (p ^ 5))⁻¹ * ((k - i : ℕ) : ZMod (p ^ 5))⁻¹
              * ((i + (k - i) : ℕ) : ZMod (p ^ 5))⁻¹ := by
    intro k hk; rw [mem_Icc] at hk
    have hF : ∀ i ∈ Icc 1 (k - 1),
        (i : ZMod (p ^ 5))⁻¹ * ((k - i : ℕ) : ZMod (p ^ 5))⁻¹
            * ((i + (k - i) : ℕ) : ZMod (p ^ 5))⁻¹
          = ((i : ZMod (p ^ 5))⁻¹ * ((k - i : ℕ) : ZMod (p ^ 5))⁻¹) * ((k : ZMod (p ^ 5))⁻¹) := by
      intro i hi; rw [mem_Icc] at hi
      have h : i + (k - i) = k := by omega
      rw [h]
    rw [Finset.sum_congr rfl hF, ← Finset.sum_mul,
      pair_sum k (HSums.isUnit_cast hp k (by omega) (by omega))
        (fun i h1 h2 => HSums.isUnit_cast hp i h1 (by omega)),
      show (∑ i ∈ Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹)) = HSums.h1 p (k - 1) from rfl]
    ring
  rw [Da, ← triangle_reindex p
    (fun i j => (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * ((i + j : ℕ) : ZMod (p ^ 5))⁻¹),
    Ta, Finset.mul_sum, Finset.sum_congr rfl step]

/-- **Step 2** : the expansion `U = -(S + q·S2' + q²·S3' + q³·S4' + q⁴·S5')`. -/
lemma Da_expand {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    Da p = -(Ssum p 1 + q p * Ssum p 2 + (q p) ^ 2 * Ssum p 3
      + (q p) ^ 3 * Ssum p 4 + (q p) ^ 4 * Ssum p 5) := by
  have hpt : ∀ i ∈ Icc 1 (p - 1), ∀ j ∈ Icc 1 (p - 1 - i),
      (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * ((i + j : ℕ) : ZMod (p ^ 5))⁻¹
      = -((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1
          + q p * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
              * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2)
          + (q p) ^ 2 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
              * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3)
          + (q p) ^ 3 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
              * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4)
          + (q p) ^ 4 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
              * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5)) := by
    intro i hi j hj; rw [mem_Icc] at hi hj
    have hl : (p - i - j) ∈ Icc 1 (p - 1) := by rw [mem_Icc]; omega
    have hexp := HSums.inv_sub_expand hp hp7 (p - i - j) hl
    have hpij : p - (p - i - j) = i + j := by omega
    rw [hpij] at hexp
    rw [hexp]; ring
  have hcomb : Ssum p 1 + q p * Ssum p 2 + (q p) ^ 2 * Ssum p 3
      + (q p) ^ 3 * Ssum p 4 + (q p) ^ 4 * Ssum p 5
      = ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
          ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹ * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1
            + q p * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
                * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 2)
            + (q p) ^ 2 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
                * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3)
            + (q p) ^ 3 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
                * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 4)
            + (q p) ^ 4 * ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
                * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 5)) := by
    simp only [Ssum, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Da, Finset.sum_congr rfl
    (fun i hi => Finset.sum_congr rfl (fun j hj => hpt i hi j hj)), hcomb]
  simp only [Finset.sum_neg_distrib]

/-- `∑_{i,j} 1/(i·l) = V`, where `l = p-i-j`. -/
lemma il_eq_V {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
        (i : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
      = (H p 1) ^ 2 - H p 2 := by
  rw [← V_eq hp hp7]
  apply Finset.sum_congr rfl; intro i hi; rw [mem_Icc] at hi
  apply Finset.sum_nbij' (fun j => p - i - j) (fun j => p - i - j)
  · intro a ha; rw [mem_Icc] at ha ⊢; omega
  · intro a ha; rw [mem_Icc] at ha ⊢; omega
  · intro a ha; rw [mem_Icc] at ha; omega
  · intro a ha; rw [mem_Icc] at ha; omega
  · intro a ha; rfl

/-- `∑_{i,j} 1/(j·l) = V`, where `l = p-i-j`. -/
lemma jl_eq_V {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
        (j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
      = (H p 1) ^ 2 - H p 2 := by
  rw [← il_eq_V hp hp7,
    triangle_swap p (fun i j => (j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹)]
  apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
  rw [show p - j - i = p - i - j from by omega]

/-- **Step 3** : `q·S = 3(H1² - H2)`. -/
lemma qS_eq {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    q p * Ssum p 1 = 3 * ((H p 1) ^ 2 - H p 2) := by
  rw [Ssum, Finset.mul_sum]
  have hpt : ∀ i ∈ Icc 1 (p - 1),
      q p * (∑ j ∈ Icc 1 (p - 1 - i),
          (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹
            * (((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) ^ 1)
      = ∑ j ∈ Icc 1 (p - 1 - i),
          ((j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
            + (i : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
            + (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹) := by
    intro i hi; rw [mem_Icc] at hi; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj; rw [mem_Icc] at hj
    have hui := ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp i (by omega) (by omega))
    have huj := ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp j (by omega) (by omega))
    have hul := ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp (p - i - j) (by omega) (by omega))
    have hq : q p = (i : ZMod (p ^ 5)) + (j : ZMod (p ^ 5)) + ((p - i - j : ℕ) : ZMod (p ^ 5)) := by
      have hh : ((i + j + (p - i - j) : ℕ) : ZMod (p ^ 5)) = (p : ZMod (p ^ 5)) := by
        congr 1; omega
      rw [q, ← hh]; push_cast; ring
    rw [pow_one, hq]
    linear_combination ((j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) * hui
      + ((i : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹) * huj
      + ((i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹) * hul
  rw [Finset.sum_congr rfl hpt]
  rw [show (∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
        ((j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
          + (i : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹
          + (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹))
      = (∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
          (j : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹)
        + (∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
          (i : ZMod (p ^ 5))⁻¹ * ((p - i - j : ℕ) : ZMod (p ^ 5))⁻¹)
        + (∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
          (i : ZMod (p ^ 5))⁻¹ * (j : ZMod (p ^ 5))⁻¹)
      from by simp only [Finset.sum_add_distrib]]
  rw [jl_eq_V hp hp7, il_eq_V hp hp7, V_eq hp hp7]
  ring

/-- **Step 4** : `S2' ≡ 0 (mod q)`, i.e. `p ∣ S2'`. -/
lemma Ssum2_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ s2 : ZMod (p ^ 5), Ssum p 2 = q p * s2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine HSums.dvd_of_cast_zero hp _ D ?_
  have himg : (ZMod.castHom D (ZMod p)) (Ssum p 2)
      = ∑ i ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 (p - 1 - i),
          ((i : ZMod p)⁻¹ * (j : ZMod p)⁻¹ * (((i + j : ℕ) : ZMod p)⁻¹) ^ 2) := by
    rw [Ssum, map_sum]
    apply Finset.sum_congr rfl; intro i hi; rw [mem_Icc] at hi
    rw [map_sum]
    apply Finset.sum_congr rfl; intro j hj; rw [mem_Icc] at hj
    rw [map_mul, map_mul, map_pow, Star6.phinv hp D i (by omega) (by omega),
      Star6.phinv hp D j (by omega) (by omega),
      Star6.phinv hp D (p - i - j) (by omega) (by omega)]
    have hcast : ((p - i - j : ℕ) : ZMod p) = -((i + j : ℕ) : ZMod p) := by
      have h1 : (p - i - j : ℕ) = p - (i + j) := by omega
      rw [h1, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hcast, inv_neg, neg_sq]
  rw [himg,
    ← triangle_reindex p (fun i j => (i : ZMod p)⁻¹ * (j : ZMod p)⁻¹ * (((i + j : ℕ) : ZMod p)⁻¹) ^ 2)]
  have hC : (∑ k ∈ Icc 1 (p - 1), ∑ i ∈ Icc 1 (k - 1),
        (i : ZMod p)⁻¹ * ((k - i : ℕ) : ZMod p)⁻¹ * (((i + (k - i) : ℕ) : ZMod p)⁻¹) ^ 2)
      = 2 * Star6.A13' p := by
    rw [Star6.A13', Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk; rw [mem_Icc] at hk
    have hF : ∀ i ∈ Icc 1 (k - 1),
        (i : ZMod p)⁻¹ * ((k - i : ℕ) : ZMod p)⁻¹ * (((i + (k - i) : ℕ) : ZMod p)⁻¹) ^ 2
          = ((i : ZMod p)⁻¹ * ((k - i : ℕ) : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 2 := by
      intro i hi; rw [mem_Icc] at hi
      have h : i + (k - i) = k := by omega
      rw [h]
    rw [Finset.sum_congr rfl hF, ← Finset.sum_mul,
      pair_sum k (isUnit_castp k (by omega) (by omega))
        (fun i h1 h2 => isUnit_castp i h1 (by omega))]
    ring
  rw [hC, Star6.A13'_zero hp hp7, mul_zero]

/-- **★5** : `2·q·Ta ≡ 3·H2  (mod q^3)`. -/
theorem Ta_cong (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ d : ZMod (p ^ 5), 2 * (q p) * (Ta p) = 3 * (H p 2) + (q p) ^ 3 * d := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨s2, hs2⟩ := Ssum2_dvd hp hp7
  have hTaU : 2 * Ta p = Da p := Ta_U hp hp7
  have hexp : Da p = -(Ssum p 1 + q p * Ssum p 2 + (q p) ^ 2 * Ssum p 3
      + (q p) ^ 3 * Ssum p 4 + (q p) ^ 4 * Ssum p 5) := Da_expand hp hp7
  have hqS : q p * Ssum p 1 = 3 * ((H p 1) ^ 2 - H p 2) := qS_eq hp hp7
  have hq5 : (q p) ^ 5 = 0 := HSums.q_pow_five p
  have h2qTa : 2 * (q p) * (Ta p) = q p * Da p := by
    rw [← hTaU]; ring
  refine ⟨-3 * (q p) * c ^ 2 - s2 - Ssum p 3 - q p * Ssum p 4, ?_⟩
  rw [h2qTa, hexp]
  linear_combination (-1 : ZMod (p ^ 5)) * hqS + (-(q p ^ 2)) * hs2
    + (-3 * (H p 1 + (q p) ^ 2 * c)) * hc + (-(Ssum p 5)) * hq5

end Star5
end Star5_sec

section F3_sec

open Nat Finset BigOperators MvPolynomial

namespace F3
open HSums F2

/-! ## Foundation: the product form of `(p+k-1).choose k` in `ZMod (p^5)`. -/

theorem f_prod_nat (p k : ℕ) (hp1 : 1 ≤ p) :
    (p + k - 1).choose k * k.factorial = p.ascFactorial k := by
  have hk : k ≤ p + k - 1 := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  rw [show p + k - 1 - k = p - 1 from by omega] at h1
  have h2 := Nat.factorial_mul_ascFactorial (p-1) k
  rw [show p - 1 + 1 = p from by omega, show p - 1 + k = p + k - 1 from by omega] at h2
  have hpos : 0 < (p-1)! := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (p + k - 1).choose k * k.factorial * (p-1)! = (p+k-1)! := h1
    _ = (p-1)! * p.ascFactorial k := h2.symm
    _ = p.ascFactorial k * (p-1)! := by ring

theorem ascF_split (p k : ℕ) (hk1 : 1 ≤ k) :
    p.ascFactorial k = p * ∏ i ∈ Finset.Icc 1 (k-1), (p+i) := by
  rw [Nat.ascFactorial_eq_prod_range]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  simp only [Nat.zero_add] at *
  rw [Finset.prod_range_succ']
  rw [show n + 1 - 1 = n from by omega]
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _; ring

theorem f_prod_nat2 (p k : ℕ) (hp1 : 1 ≤ p) :
    (p + k - 1).choose k * (p-1).factorial = ∏ j ∈ Finset.Icc 1 (p-1), (k + j) := by
  have hprod : (∏ j ∈ Finset.Icc 1 (p-1), (k+j)) = (k+1).ascFactorial (p-1) := by
    rw [Nat.ascFactorial_eq_prod_range,
        show Finset.Icc 1 (p-1) = Finset.Ico 1 p from by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
        Finset.prod_Ico_eq_prod_range]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  rw [hprod]
  have hk : k ≤ p + k - 1 := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  rw [show p + k - 1 - k = p - 1 from by omega] at h1
  have h2 := Nat.factorial_mul_ascFactorial k (p-1)
  rw [show k + (p-1) = p + k - 1 from by omega] at h2
  have hpos : 0 < k.factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc k.factorial * ((p + k - 1).choose k * (p-1).factorial)
      = (p+k-1).choose k * k.factorial * (p-1).factorial := by ring
    _ = (p+k-1)! := h1
    _ = k.factorial * (k+1).ascFactorial (p-1) := h2.symm

theorem fact_eq_prod (p : ℕ) : (p-1).factorial = ∏ j ∈ Finset.Icc 1 (p-1), j := by
  rw [show Finset.Icc 1 (p-1) = Finset.Ico 1 p from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.prod_Ico_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial]
  exact Finset.prod_congr rfl (fun i _ => by ring)

/-- Unified product form: `(p+k-1).choose k = ∏_{j=1}^{p-1}(1 + k·j⁻¹)` in `ZMod (p^5)`. -/
theorem key_prod (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((p + k - 1).choose k : ZMod (p^5))
      = ∏ j ∈ Finset.Icc 1 (p-1), (1 + (k : ZMod (p^5)) * ((j : ZMod (p^5))⁻¹)) := by
  set R := ZMod (p^5)
  have hnat := f_prod_nat2 p k (by omega)
  have hcast : ((p+k-1).choose k : R) * ∏ j ∈ Finset.Icc 1 (p-1), ((j:ℕ) : R)
      = ∏ j ∈ Finset.Icc 1 (p-1), (((k:ℕ):R) + ((j:ℕ):R)) := by
    have h := congrArg (fun n : ℕ => (n : R)) hnat
    push_cast at h
    rw [fact_eq_prod p] at h
    push_cast at h
    convert h using 2
  have hterm : ∀ j ∈ Finset.Icc 1 (p-1),
      (((k:ℕ):R) + ((j:ℕ):R)) = ((j:ℕ):R) * (1 + (k:R) * ((j:R)⁻¹)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hu : ((j:ℕ):R) * ((j:R)⁻¹) = 1 :=
      ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp j (by omega) (by omega))
    have : (k:R) = ((k:ℕ):R) := rfl
    rw [this]
    linear_combination (-(((k:ℕ):R))) * hu
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib] at hcast
  have huunit : IsUnit (∏ j ∈ Finset.Icc 1 (p-1), ((j:ℕ) : R)) :=
    IsUnit.prod_iff.mpr (fun j hj => by
      rw [Finset.mem_Icc] at hj; exact HSums.isUnit_cast hp j (by omega) (by omega))
  apply (IsUnit.mul_right_inj huunit).mp
  rw [mul_comm _ (((p + k - 1).choose k : R)),
      mul_comm _ (∏ j ∈ Finset.Icc 1 (p-1), (1 + (k:R) * ((j:R)⁻¹)))]
  linear_combination hcast

/-- Factorization pulling out the single factor of `p`: for `1 ≤ k ≤ p-1`,
`(p+k-1).choose k = q · k⁻¹ · ∏_{i=1}^{k-1}(1 + q·i⁻¹)`. -/
theorem fk_form (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk1 : 1 ≤ k) (hk2 : k ≤ p-1) :
    ((p + k - 1).choose k : ZMod (p^5))
      = HSums.q p * ((k:ZMod (p^5))⁻¹)
        * ∏ i ∈ Finset.Icc 1 (k-1), (1 + HSums.q p * ((i:ZMod (p^5))⁻¹)) := by
  set R := ZMod (p^5)
  have hnat := f_prod_nat p k (by omega)
  rw [ascF_split p k hk1] at hnat
  have hcast : ((p+k-1).choose k : R) * (k.factorial : R)
      = (HSums.q p) * ∏ i ∈ Finset.Icc 1 (k-1), ((p:R) + (i:R)) := by
    have h := congrArg (fun n : ℕ => (n : R)) hnat
    push_cast at h
    convert h using 2
  have hterm : ∀ i ∈ Finset.Icc 1 (k-1), ((p:R) + (i:R)) = (i:R) * (1 + HSums.q p * ((i:R)⁻¹)) := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : ((i:ℕ):R) * ((i:R)⁻¹) = 1 :=
      ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp i (by omega) (by omega))
    show (p:R) + (i:R) = (i:R) * (1 + HSums.q p * ((i:R)⁻¹))
    have : HSums.q p = (p:R) := rfl
    rw [this]
    linear_combination (-(p:R)) * hu
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib] at hcast
  have hfact : (k.factorial : R) = (k:R) * ∏ i ∈ Finset.Icc 1 (k-1), (i:R) := by
    have hkf : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [show k = (k-1)+1 from by omega]
      rw [Nat.factorial_succ]; congr 1; omega
    rw [hkf]; push_cast
    congr 1
    rw [show (k-1).factorial = ∏ i ∈ Finset.Icc 1 (k-1), i from by
          rw [show Finset.Icc 1 (k-1) = Finset.Ico 1 k from by
                ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
              Finset.prod_Ico_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial]
          exact Finset.prod_congr rfl (fun i _ => by ring)]
    push_cast; rfl
  rw [hfact] at hcast
  have hkunit : IsUnit ((k:ℕ):R) := HSums.isUnit_cast hp k (by omega) (by omega)
  have hpunit : IsUnit (∏ i ∈ Finset.Icc 1 (k-1), ((i:ℕ):R)) :=
    IsUnit.prod_iff.mpr (fun i hi => by
      rw [Finset.mem_Icc] at hi; exact HSums.isUnit_cast hp i (by omega) (by omega))
  have hkinv : (k:R) * ((k:R)⁻¹) = 1 := ZMod.mul_inv_of_unit _ hkunit
  have hunit2 : IsUnit ((k:R) * ∏ i ∈ Finset.Icc 1 (k-1), ((i:ℕ):R)) := hkunit.mul hpunit
  apply (IsUnit.mul_left_inj hunit2).mp
  rw [hcast]
  linear_combination (- HSums.q p * (∏ i ∈ Finset.Icc 1 (k-1), (1 + HSums.q p * ((i:R)⁻¹)))
      * (∏ i ∈ Finset.Icc 1 (k-1), ((i:ℕ):R))) * hkinv

/-- Expansion (second order) of `∏(1 + (q·a)·i⁻¹)` over the full range. -/
theorem prodq (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (aa : ZMod (p^5)) :
    ∏ i ∈ Finset.Icc 1 (p - 1), (1 + (HSums.q p * aa) * ((i : ZMod (p ^ 5))⁻¹))
      = 1 + (HSums.q p * aa) * (HSums.H p 1)
        - (2 : ZMod (p^5))⁻¹ * (HSums.q p * aa) ^ 2 * (HSums.H p 2) := by
  set q := HSums.q p with hq
  set c : ZMod (p^5) := q * aa with hc
  let σ := ↥(Finset.Icc 1 (p - 1))
  let v : σ → ZMod (p^5) := fun x => (((x : ℕ) : ZMod (p^5)))⁻¹
  let E : ℕ → ZMod (p^5) := fun k => ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i
  let P : ℕ → ZMod (p^5) := fun k => ∑ i, (v i) ^ k
  have hE : ∀ k, E k = ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i := fun _ => rfl
  have hP : ∀ k, P k = ∑ i, (v i) ^ k := fun _ => rfl
  have hPH : ∀ k, P k = HSums.H p k := by
    intro k
    rw [hP, HSums.H]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 (p - 1)) (fun n => (((n : ℕ) : ZMod (p^5)))⁻¹ ^ k)]
  have hprod : ∏ i ∈ Finset.Icc 1 (p - 1), (1 + c * ((i : ZMod (p^5))⁻¹))
      = ∏ x : σ, (1 + c * v x) := by
    rw [← Finset.prod_coe_sort (Finset.Icc 1 (p - 1)) (fun n => 1 + c * (((n : ℕ) : ZMod (p^5)))⁻¹)]
  have hcardσ : (univ : Finset σ).card = p - 1 := by
    rw [Finset.card_univ, Fintype.card_coe, Nat.card_Icc]; omega
  rw [hprod, prod_one_add_expand v c]
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  have hreduce : ∑ k ∈ range ((univ : Finset σ).card + 1),
        c ^ k * (∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i)
      = ∑ k ∈ range 5, c ^ k * E k := by
    symm
    apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    have : c ^ k = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hc, mul_pow, pow_add, hq5]; ring
    rw [this, zero_mul]
  rw [hreduce]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hE0 : E 0 = 1 := by rw [hE]; simp [Finset.powersetCard_zero]
  have hE1P1 : E 1 = P 1 := by
    rw [hE, hP]; simp [Finset.powersetCard_one, Finset.sum_map, pow_one]
  have hn2 := newton2 v E P hE hP
  have hn3 := newton3 v E P hE hP
  have hn4 := newton4 v E P hE hP
  obtain ⟨a1, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨b, hH2⟩ := HSums.H_two_dvd hp hp7
  obtain ⟨cc, hH3⟩ := HSums.H_three_dvd hp hp7
  obtain ⟨d, hH4⟩ := HSums.H_four_dvd hp hp7
  have hE1H : E 1 = HSums.H p 1 := by rw [hE1P1, hPH 1]
  rw [hPH 1, hPH 2, hE1H, hE0] at hn2
  rw [hPH 3, hPH 2, hPH 1, hE0, hE1H] at hn3
  rw [hPH 4, hPH 3, hPH 2, hPH 1, hE0, hE1H] at hn4
  rw [← hq] at hH1 hH2 hH3 hH4
  have h3u : IsUnit (3 : ZMod (p^5)) := by
    rw [show (3 : ZMod (p^5)) = ((3 : ℕ) : ZMod (p^5)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right 5
  have h4u : IsUnit (4 : ZMod (p^5)) := by
    rw [show (4 : ZMod (p^5)) = ((4 : ℕ) : ZMod (p^5)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact ((this.pow_left 2).pow_right 5)
  have hq3E3 : q ^ 3 * E 3 = 0 := by
    have h3z : (3 : ZMod (p^5)) * (q ^ 3 * E 3) = 0 := by
      rw [hH1, hH2, hH3] at hn3
      linear_combination (q ^ 3) * hn3 + (cc - q * a1 * b + a1 * E 2) * hq5
    exact (h3u.mul_right_eq_zero).mp h3z
  have hq4E4 : q ^ 4 * E 4 = 0 := by
    have h4z : (4 : ZMod (p^5)) * (q ^ 4 * E 4) = 0 := by
      rw [hH1, hH2, hH3, hH4] at hn4
      linear_combination (q ^ 4) * hn4 + (-d + q ^ 3 * a1 * cc - b * E 2 + q * a1 * E 3) * hq5
    exact (h4u.mul_right_eq_zero).mp h4z
  have h2u : IsUnit (2 : ZMod (p^5)) := HSums.two_isUnit hp hp7
  have h2inv : (2:ZMod (p^5))⁻¹ * (2:ZMod (p^5)) = 1 := ZMod.inv_mul_of_unit _ h2u
  have hcH1 : c ^ 2 * (HSums.H p 1)^2 = 0 := by
    rw [hc, hH1]; linear_combination (aa^2 * a1^2 * q) * hq5
  have hv2 : c ^ 2 * E 2 = -((2:ZMod (p^5))⁻¹ * c ^ 2 * HSums.H p 2) := by
    have hstep : (2:ZMod (p^5)) * (c^2 * E 2) = - (c^2 * HSums.H p 2) := by
      linear_combination (c^2) * hn2 + hcH1
    calc c^2 * E 2 = (2:ZMod (p^5))⁻¹ * ((2:ZMod (p^5)) * (c^2 * E 2)) := by
          rw [← mul_assoc, h2inv, one_mul]
      _ = (2:ZMod (p^5))⁻¹ * (-(c^2 * HSums.H p 2)) := by rw [hstep]
      _ = -((2:ZMod (p^5))⁻¹ * c^2 * HSums.H p 2) := by ring
  have hv3 : c ^ 3 * E 3 = 0 := by
    rw [hc]; have : (q*aa)^3 * E 3 = aa^3 * (q^3 * E 3) := by ring
    rw [this, hq3E3, mul_zero]
  have hv4 : c ^ 4 * E 4 = 0 := by
    rw [hc]; have : (q*aa)^4 * E 4 = aa^4 * (q^4 * E 4) := by ring
    rw [this, hq4E4, mul_zero]
  rw [hE0, hE1H, hv2, hv3, hv4]
  ring

/-- Square of the partial product, multiplied by `q²` (Part B core). -/
theorem Pm_sq (p m : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hm : m ≤ p - 1) :
    (HSums.q p)^2 * (∏ i ∈ Finset.Icc 1 m, (1 + HSums.q p * ((i:ZMod (p^5))⁻¹)))^2
      = (HSums.q p)^2 + 2*(HSums.q p)^3 * HSums.h1 p m
        + (HSums.q p)^4 * (2*(HSums.h1 p m)^2 - HSums.h2 p m) := by
  set q := HSums.q p with hq
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  let σ := ↥(Finset.Icc 1 m)
  let v : σ → ZMod (p^5) := fun x => (((x : ℕ) : ZMod (p^5)))⁻¹
  let E : ℕ → ZMod (p^5) := fun k => ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i
  let P : ℕ → ZMod (p^5) := fun k => ∑ i, (v i) ^ k
  have hE : ∀ k, E k = ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i := fun _ => rfl
  have hP : ∀ k, P k = ∑ i, (v i) ^ k := fun _ => rfl
  have hcardσ : (univ : Finset σ).card = m := by
    rw [Finset.card_univ, Fintype.card_coe, Nat.card_Icc]; omega
  have hPh1 : P 1 = HSums.h1 p m := by
    rw [hP, HSums.h1]
    simp only [pow_one]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 m) (fun n => (((n : ℕ) : ZMod (p^5)))⁻¹)]
  have hPh2 : P 2 = HSums.h2 p m := by
    rw [hP, HSums.h2]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 m) (fun n => (((n : ℕ) : ZMod (p^5)))⁻¹ ^ 2)]
  have hprod : ∏ i ∈ Finset.Icc 1 m, (1 + q * ((i : ZMod (p^5))⁻¹)) = ∏ x : σ, (1 + q * v x) := by
    rw [← Finset.prod_coe_sort (Finset.Icc 1 m) (fun n => 1 + q * (((n : ℕ) : ZMod (p^5)))⁻¹)]
  rw [hprod, prod_one_add_expand v q]
  rw [hcardσ]
  have hEzero : ∀ j, m < j → E j = 0 := by
    intro j hj; rw [hE, Finset.powersetCard_eq_empty.mpr (by rw [hcardσ]; omega), Finset.sum_empty]
  have hreduce : ∑ k ∈ range (m+1), q ^ k * E k = ∑ k ∈ range 5, q ^ k * E k := by
    rcases le_total (m+1) 5 with hc | hc
    · apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      rw [hEzero k (by omega), mul_zero]
    · symm
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      have : q ^ k = 0 := by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [pow_add, hq5]; ring
      rw [this, zero_mul]
  rw [hreduce]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hE0 : E 0 = 1 := by rw [hE]; simp [Finset.powersetCard_zero]
  have hE1P1 : E 1 = P 1 := by
    rw [hE, hP]; simp [Finset.powersetCard_one, Finset.sum_map, pow_one]
  have hn2 := newton2 v E P hE hP
  rw [hE0, hE1P1, hPh1, hPh2] at hn2
  rw [hE0, hE1P1, hPh1]
  set h1v := HSums.h1 p m with hh1
  set h2v := HSums.h2 p m with hh2
  set t := (2:ZMod (p^5))⁻¹ with ht
  have h2u : IsUnit (2 : ZMod (p^5)) := HSums.two_isUnit hp hp7
  have h2inv : t * (2:ZMod (p^5)) = 1 := by rw [ht]; exact ZMod.inv_mul_of_unit _ h2u
  have hE2 : E 2 = t * (h1v * h1v - h2v) := by
    have h : (2:ZMod (p^5)) * E 2 = h1v * h1v - h2v := by linear_combination hn2
    calc E 2 = t * ((2:ZMod (p^5)) * E 2) := by rw [← mul_assoc, h2inv, one_mul]
      _ = t * (h1v * h1v - h2v) := by rw [h]
  rw [hE2]
  set A := 1 + q * h1v + q^2 * (t * (h1v*h1v - h2v)) with hA
  linear_combination (2*A*(E 3 + q*E 4) + q^3*(E 3 + q*E 4)^2
      + 2*h1v*t*(h1v*h1v - h2v) + q*t^2*(h1v*h1v - h2v)^2) * hq5
      + (q^4*(h1v*h1v - h2v)) * h2inv

/-! ## Part A (endpoints). -/

theorem partA (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (((p+0-1).choose 0 : ZMod (p^5)))^2 + ((p+p-1).choose p : ZMod (p^5))^2
      + ((p+2*p-1).choose (2*p) : ZMod (p^5))^2
      = 3 + 6 * HSums.q p * HSums.H p 1 - 5 * (HSums.q p)^2 * HSums.H p 2 := by
  set q := HSums.q p with hq
  set t2 := (2 : ZMod (p^5))⁻¹ with ht2
  have hpcast : ((p:ℕ) : ZMod (p^5)) = q := rfl
  have h2pcast : ((2*p:ℕ) : ZMod (p^5)) = q * 2 := by
    rw [show ((2*p:ℕ):ZMod (p^5)) = 2 * ((p:ℕ):ZMod (p^5)) from by push_cast; ring, hpcast]; ring
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  obtain ⟨a1, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨b, hH2⟩ := HSums.H_two_dvd hp hp7
  rw [← hq] at hH1 hH2
  have h2u : IsUnit (2 : ZMod (p^5)) := HSums.two_isUnit hp hp7
  have h2inv : t2 * (2:ZMod (p^5)) = 1 := by rw [ht2]; exact ZMod.inv_mul_of_unit _ h2u
  have hf0 : ((p+0-1).choose 0 : ZMod (p^5)) = 1 := by rw [Nat.choose_zero_right]; norm_num
  have hfp : ((p+p-1).choose p : ZMod (p^5)) = 1 + q * HSums.H p 1 - t2 * q^2 * HSums.H p 2 := by
    have hpp := prodq p hp hp7 1
    simp only [mul_one] at hpp
    rw [← hq, ← ht2] at hpp
    rw [key_prod p p hp hp7, hpcast]
    exact hpp
  have hf2p : ((p+2*p-1).choose (2*p) : ZMod (p^5))
      = 1 + 2*q * HSums.H p 1 - 2 * q^2 * HSums.H p 2 := by
    have hpp := prodq p hp hp7 2
    rw [← hq, ← ht2] at hpp
    rw [key_prod p (2*p) hp hp7, h2pcast, hpp]
    linear_combination (-2 * q^2 * HSums.H p 2) * h2inv
  have sqp : ((p+p-1).choose p : ZMod (p^5))^2 = 1 + 2*q*HSums.H p 1 - q^2*HSums.H p 2 := by
    rw [hfp, hH1, hH2]
    linear_combination ((a1 - t2*b)^2 * q) * hq5 - (q^3 * b) * h2inv
  have sq2p : ((p+2*p-1).choose (2*p) : ZMod (p^5))^2
      = 1 + 4*q*HSums.H p 1 - 4*q^2*HSums.H p 2 := by
    rw [hf2p, hH1, hH2]
    linear_combination (4*(a1 - b)^2 * q) * hq5
  rw [hf0, sqp, sq2p]; ring

/-! ## Part B (low range). -/

theorem termB (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk1 : 1 ≤ k) (hk2 : k ≤ p-1) :
    ((p+k-1).choose k : ZMod (p^5))^2
      = (HSums.q p)^2 * ((k:ZMod (p^5))⁻¹)^2
        + 2*(HSums.q p)^3 * HSums.h1 p (k-1) * ((k:ZMod (p^5))⁻¹)^2
        + (HSums.q p)^4 * (2*(HSums.h1 p (k-1))^2 - HSums.h2 p (k-1)) * ((k:ZMod (p^5))⁻¹)^2 := by
  rw [fk_form p k hp hp7 hk1 hk2]
  have hps := Pm_sq p (k-1) hp hp7 (by omega)
  linear_combination ((k:ZMod (p^5))⁻¹)^2 * hps

/-- The `q⁴` coefficient of Part B. -/
noncomputable def Tb (p : ℕ) : ZMod (p^5) :=
  ∑ k ∈ Finset.Icc 1 (p-1), (2*(HSums.h1 p (k-1))^2 - HSums.h2 p (k-1)) * ((k:ZMod (p^5))⁻¹)^2

theorem partB (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p-1), ((p+k-1).choose k : ZMod (p^5))^2
      = (HSums.q p)^2 * HSums.H p 2 + 2*(HSums.q p)^3 * HSums.Ta p + (HSums.q p)^4 * Tb p := by
  rw [Finset.sum_congr rfl (fun k hk => termB p k hp hp7
        (by rw [Finset.mem_Icc] at hk; omega) (by rw [Finset.mem_Icc] at hk; omega))]
  rw [Tb]
  symm
  rw [HSums.H, HSums.Ta, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _; ring

theorem Tb_dvd (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : ∃ c, Tb p = HSums.q p * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine HSums.dvd_of_cast_zero hp _ D ?_
  rw [Tb, map_sum]
  have hstep : ∀ k ∈ Finset.Icc 1 (p-1),
      (ZMod.castHom D (ZMod p)) ((2*(HSums.h1 p (k-1))^2 - HSums.h2 p (k-1)) * ((k:ZMod (p^5))⁻¹)^2)
      = 2 * ((∑ i ∈ Icc 1 (k-1), ((i : ZMod p)⁻¹)) ^ 2 * ((k : ZMod p)⁻¹) ^ 2)
        - ((∑ i ∈ Icc 1 (k-1), ((i : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2) := by
    intro k hk; rw [mem_Icc] at hk
    have hm : k - 1 < p := by omega
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    rw [Star6.castHom_h1 hp D _ hm, Star6.castHom_h2 hp D _ hm, Star6.phinv hp D k (by omega) (by omega)]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [show (∑ k ∈ Icc 1 (p-1), (∑ i ∈ Icc 1 (k-1), ((i : ZMod p)⁻¹))^2 * ((k:ZMod p)⁻¹)^2)
        = Star6.T1' p from rfl,
      show (∑ k ∈ Icc 1 (p-1), (∑ i ∈ Icc 1 (k-1), ((i : ZMod p)⁻¹)^2) * ((k:ZMod p)⁻¹)^2)
        = Star6.A22' p from rfl]
  rw [Star6.T1'_zero hp hp7, Star6.A22'_zero hp hp7]
  ring

/-! ## Part C helper lemmas. -/

/-- `1 + x` is a unit when `x^5 = 0`. -/
theorem isUnit_one_add_nilp {p : ℕ} (x : ZMod (p^5)) (hx : x^5 = 0) : IsUnit (1 + x) := by
  refine isUnit_of_mul_eq_one (a := 1 + x) (1 - x + x^2 - x^3 + x^4) ?_
  linear_combination hx

/-- Generalized squared partial product (coefficient `q·a`). -/
theorem Pm_sq_gen (p m : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hm : m ≤ p - 1) (a : ZMod (p^5)) :
    (HSums.q p)^2 * (∏ i ∈ Finset.Icc 1 m, (1 + (HSums.q p * a) * ((i:ZMod (p^5))⁻¹)))^2
      = (HSums.q p)^2 + 2*(HSums.q p)^3 * a * HSums.h1 p m
        + (HSums.q p)^4 * a^2 * (2*(HSums.h1 p m)^2 - HSums.h2 p m) := by
  set q := HSums.q p with hq
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  let σ := ↥(Finset.Icc 1 m)
  let v : σ → ZMod (p^5) := fun x => (((x : ℕ) : ZMod (p^5)))⁻¹
  let E : ℕ → ZMod (p^5) := fun k => ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i
  let P : ℕ → ZMod (p^5) := fun k => ∑ i, (v i) ^ k
  have hE : ∀ k, E k = ∑ t ∈ powersetCard k (univ : Finset σ), ∏ i ∈ t, v i := fun _ => rfl
  have hP : ∀ k, P k = ∑ i, (v i) ^ k := fun _ => rfl
  have hcardσ : (univ : Finset σ).card = m := by
    rw [Finset.card_univ, Fintype.card_coe, Nat.card_Icc]; omega
  have hPh1 : P 1 = HSums.h1 p m := by
    rw [hP, HSums.h1]
    simp only [pow_one]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 m) (fun n => (((n : ℕ) : ZMod (p^5)))⁻¹)]
  have hPh2 : P 2 = HSums.h2 p m := by
    rw [hP, HSums.h2]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 m) (fun n => (((n : ℕ) : ZMod (p^5)))⁻¹ ^ 2)]
  have hprod : ∏ i ∈ Finset.Icc 1 m, (1 + (q * a) * ((i : ZMod (p^5))⁻¹)) = ∏ x : σ, (1 + (q * a) * v x) := by
    rw [← Finset.prod_coe_sort (Finset.Icc 1 m) (fun n => 1 + (q * a) * (((n : ℕ) : ZMod (p^5)))⁻¹)]
  rw [hprod, prod_one_add_expand v (q * a)]
  rw [hcardσ]
  have hEzero : ∀ j, m < j → E j = 0 := by
    intro j hj; rw [hE, Finset.powersetCard_eq_empty.mpr (by rw [hcardσ]; omega), Finset.sum_empty]
  have hreduce : ∑ k ∈ range (m+1), (q*a) ^ k * E k = ∑ k ∈ range 5, (q*a) ^ k * E k := by
    rcases le_total (m+1) 5 with hc | hc
    · apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      rw [hEzero k (by omega), mul_zero]
    · symm
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      have : (q*a) ^ k = 0 := by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [mul_pow, pow_add, hq5]; ring
      rw [this, zero_mul]
  rw [hreduce]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hE0 : E 0 = 1 := by rw [hE]; simp [Finset.powersetCard_zero]
  have hE1P1 : E 1 = P 1 := by
    rw [hE, hP]; simp [Finset.powersetCard_one, Finset.sum_map, pow_one]
  have hn2 := newton2 v E P hE hP
  rw [hE0, hE1P1, hPh1, hPh2] at hn2
  rw [hE0, hE1P1, hPh1]
  set h1v := HSums.h1 p m with hh1
  set h2v := HSums.h2 p m with hh2
  set t := (2:ZMod (p^5))⁻¹ with ht
  have h2u : IsUnit (2 : ZMod (p^5)) := HSums.two_isUnit hp hp7
  have h2inv : t * (2:ZMod (p^5)) = 1 := by rw [ht]; exact ZMod.inv_mul_of_unit _ h2u
  have hE2 : E 2 = t * (h1v * h1v - h2v) := by
    have h : (2:ZMod (p^5)) * E 2 = h1v * h1v - h2v := by linear_combination hn2
    calc E 2 = t * ((2:ZMod (p^5)) * E 2) := by rw [← mul_assoc, h2inv, one_mul]
      _ = t * (h1v * h1v - h2v) := by rw [h]
  rw [hE2]
  linear_combination
    (a^3*(2*h1v*(t*(h1v*h1v-h2v))+2*(E 3))
     + q*a^4*((t*(h1v*h1v-h2v))^2+2*h1v*(E 3)+2*(E 4))
     + q^2*a^5*(2*h1v*(E 4)+2*(t*(h1v*h1v-h2v))*(E 3))
     + q^3*a^6*(2*(t*(h1v*h1v-h2v))*(E 4)+(E 3)^2)
     + q^4*a^7*(2*(E 3)*(E 4))
     + q^5*a^8*(E 4)^2) * hq5
    + (q^4*a^2*(h1v*h1v - h2v)) * h2inv

/-- `f(p+r) = (2p+r-1).choose (p+r)`. -/
def gg (p r : ℕ) : ℕ := (2*p+r-1).choose (p+r)

/-- Multiplicative recurrence for `choose`. -/
theorem grec (p k : ℕ) (hp1 : 1 ≤ p) (hk1 : 1 ≤ k) :
    (p+k-1).choose k * k = (p+k-2).choose (k-1) * (p+k-1) := by
  have h1 : (p+k-1).choose k * k.factorial * (p-1).factorial = (p+k-1).factorial := by
    have hk : k ≤ p+k-1 := by omega
    have H := Nat.choose_mul_factorial_mul_factorial hk
    rwa [show p+k-1-k = p-1 from by omega] at H
  have h2 : (p+k-2).choose (k-1) * (k-1).factorial * (p-1).factorial = (p+k-2).factorial := by
    have hk : k-1 ≤ p+k-2 := by omega
    have H := Nat.choose_mul_factorial_mul_factorial hk
    rwa [show p+k-2-(k-1) = p-1 from by omega] at H
  have hfk : k.factorial = k * (k-1).factorial := (Nat.mul_factorial_pred (by omega)).symm
  have hfn : (p+k-1).factorial = (p+k-1) * (p+k-2).factorial := by
    have H := Nat.mul_factorial_pred (show p+k-1 ≠ 0 from by omega)
    rw [show p+k-1-1 = p+k-2 from by omega] at H
    exact H.symm
  have hpos : 0 < (k-1).factorial * (p-1).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (p+k-1).choose k * k * ((k-1).factorial * (p-1).factorial)
      = (p+k-1).choose k * (k * (k-1).factorial) * (p-1).factorial := by ring
    _ = (p+k-1).choose k * k.factorial * (p-1).factorial := by rw [← hfk]
    _ = (p+k-1).factorial := h1
    _ = (p+k-1) * (p+k-2).factorial := hfn
    _ = (p+k-1) * ((p+k-2).choose (k-1) * (k-1).factorial * (p-1).factorial) := by rw [h2]
    _ = (p+k-2).choose (k-1) * (p+k-1) * ((k-1).factorial * (p-1).factorial) := by ring

theorem ggrec (p r : ℕ) (hp1 : 1 ≤ p) : gg p (r+1) * (p+r+1) = gg p r * (2*p+r) := by
  unfold gg
  rw [show 2*p+(r+1)-1 = 2*p+r from by omega, show p+(r+1) = p+r+1 from by omega]
  have h := Nat.succ_mul_choose_eq (2*p+r-1) (p+r)
  simp only [Nat.succ_eq_add_one] at h
  rw [show 2*p+r-1+1 = 2*p+r from by omega] at h
  rw [mul_comm ((2*p+r-1).choose (p+r)) (2*p+r)]
  exact h.symm

/-- Product relation: `f(p+r)·∏(q+t) = f(p)·∏(2q+t-1)`. -/
theorem prodrel (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∀ r, r ≤ p - 1 →
      (gg p r : ZMod (p^5)) * ∏ t ∈ Finset.Icc 1 r, (HSums.q p + (t:ZMod (p^5)))
        = (gg p 0 : ZMod (p^5)) * ∏ t ∈ Finset.Icc 1 r, (2*HSums.q p + (t:ZMod (p^5)) - 1) := by
  set q := HSums.q p with hq
  have hqp : ((p:ℕ):ZMod (p^5)) = q := by rw [hq, HSums.q]
  intro r
  induction r with
  | zero => intro _; rw [Finset.Icc_eq_empty (by norm_num : ¬ (1:ℕ) ≤ 0)]; simp
  | succ n ih =>
    intro hn
    have ihn := ih (by omega)
    rw [Finset.prod_Icc_succ_top (by omega : (1:ℕ) ≤ n+1),
        Finset.prod_Icc_succ_top (by omega : (1:ℕ) ≤ n+1)]
    have hgg := ggrec p n (by omega)
    have hggR := congrArg (fun z : ℕ => (z : ZMod (p^5))) hgg
    push_cast at hggR
    rw [hqp] at hggR
    push_cast
    linear_combination (∏ t ∈ Finset.Icc 1 n, (q + (t:ZMod (p^5)))) * hggR
        + (2*q + (n:ZMod (p^5))) * ihn

/-- `A r = ∏_{u=1}^{r-1}(1 + 2q·u⁻¹)`. -/
noncomputable def Aprod (p r : ℕ) : ZMod (p^5) :=
  ∏ u ∈ Finset.Icc 1 (r-1), (1 + (HSums.q p * 2) * ((u:ZMod (p^5))⁻¹))

/-- `B r = ∏_{t=1}^{r}(1 + q·t⁻¹)`. -/
noncomputable def Bprod (p r : ℕ) : ZMod (p^5) :=
  ∏ t ∈ Finset.Icc 1 r, (1 + HSums.q p * ((t:ZMod (p^5))⁻¹))

/-- Clean chain identity: `f(p+r)·r·B r = 2q·f(p)·A r`. -/
theorem chain (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p-1) :
    (gg p r : ZMod (p^5)) * (r:ZMod (p^5)) * Bprod p r
      = 2 * HSums.q p * (gg p 0 : ZMod (p^5)) * Aprod p r := by
  have hpr := prodrel p hp hp7 r hr2
  have Den_factor : (∏ t ∈ Finset.Icc 1 r, (HSums.q p + (t:ZMod (p^5))))
      = (∏ t ∈ Finset.Icc 1 r, (t:ZMod (p^5))) * Bprod p r := by
    rw [Bprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht; rw [Finset.mem_Icc] at ht
    have hu : (t:ZMod (p^5)) * (t:ZMod (p^5))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp t (by omega) (by omega))
    linear_combination (-(HSums.q p))*hu
  have Pt_factor : (∏ t ∈ Finset.Icc 1 r, (t:ZMod (p^5)))
      = (∏ u ∈ Finset.Icc 1 (r-1), (u:ZMod (p^5))) * (r:ZMod (p^5)) := by
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [Finset.prod_Icc_succ_top (by omega : (1:ℕ) ≤ (r-1)+1)]
    rw [show (r-1)+1 = r from by omega]
  have Num_factor : (∏ t ∈ Finset.Icc 1 r, (2*HSums.q p + (t:ZMod (p^5)) - 1))
      = 2*HSums.q p * ((∏ u ∈ Finset.Icc 1 (r-1), (u:ZMod (p^5))) * Aprod p r) := by
    have hshift : (∏ t ∈ Finset.Icc 1 r, (2*HSums.q p + (t:ZMod (p^5)) - 1))
        = ∏ u ∈ Finset.Icc 0 (r-1), (2*HSums.q p + (u:ZMod (p^5))) := by
      apply Finset.prod_nbij' (fun t => t - 1) (fun u => u + 1)
      · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; rw [Finset.mem_Icc] at ha; omega
      · intro a ha; rw [Finset.mem_Icc] at ha; omega
      · intro a ha; rw [Finset.mem_Icc] at ha
        rw [Nat.cast_sub (by omega : 1 ≤ a)]; push_cast; ring
    rw [hshift]
    rw [show Finset.Icc 0 (r-1) = insert 0 (Finset.Icc 1 (r-1)) from by
          ext x; rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]; omega]
    rw [Finset.prod_insert (by rw [Finset.mem_Icc]; omega)]
    have hfac : (∏ u ∈ Finset.Icc 1 (r-1), (2*HSums.q p + (u:ZMod (p^5))))
        = (∏ u ∈ Finset.Icc 1 (r-1), (u:ZMod (p^5))) * Aprod p r := by
      rw [Aprod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro u hu; rw [Finset.mem_Icc] at hu
      have hu1 : (u:ZMod (p^5)) * (u:ZMod (p^5))⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp u (by omega) (by omega))
      linear_combination (-(HSums.q p*2))*hu1
    rw [hfac]
    push_cast
    ring
  rw [Den_factor, Pt_factor, Num_factor] at hpr
  have huPu : IsUnit (∏ u ∈ Finset.Icc 1 (r-1), (u:ZMod (p^5))) :=
    IsUnit.prod_iff.mpr (fun u hu => by
      rw [Finset.mem_Icc] at hu; exact HSums.isUnit_cast hp u (by omega) (by omega))
  refine (huPu.mul_right_inj).mp ?_
  linear_combination hpr

/-- `f(p)^2 = 1 + 2q·H₁ - q²·H₂`. -/
theorem gp_sq (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (gg p 0 : ZMod (p^5))^2 = 1 + 2*(HSums.q p)*(HSums.H p 1) - (HSums.q p)^2*(HSums.H p 2) := by
  have hgg0 : gg p 0 = (p+p-1).choose p := by
    unfold gg; rw [show 2*p+0-1 = p+p-1 from by omega, show p+0 = p from by omega]
  rw [hgg0]
  set q := HSums.q p with hq
  set t2 := (2 : ZMod (p^5))⁻¹ with ht2
  have hpcast : ((p:ℕ) : ZMod (p^5)) = q := by rw [hq, HSums.q]
  have hq5 : q ^ 5 = 0 := HSums.q_pow_five p
  obtain ⟨a1, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨b, hH2⟩ := HSums.H_two_dvd hp hp7
  rw [← hq] at hH1 hH2
  have h2u : IsUnit (2 : ZMod (p^5)) := HSums.two_isUnit hp hp7
  have h2inv : t2 * (2:ZMod (p^5)) = 1 := by rw [ht2]; exact ZMod.inv_mul_of_unit _ h2u
  have hfp : ((p+p-1).choose p : ZMod (p^5)) = 1 + q * HSums.H p 1 - t2 * q^2 * HSums.H p 2 := by
    have hpp := prodq p hp hp7 1
    simp only [mul_one] at hpp
    rw [← hq, ← ht2] at hpp
    rw [key_prod p p hp hp7, hpcast]
    exact hpp
  rw [hfp, hH1, hH2]
  linear_combination ((a1 - t2*b)^2 * q) * hq5 - (q^3 * b) * h2inv

/-- Per-term expansion of `f(p+r)^2`. -/
theorem termC (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p-1) :
    (gg p r : ZMod (p^5))^2
      = 4*(gg p 0 : ZMod (p^5))^2 *
        ((HSums.q p)^2*((r:ZMod (p^5))⁻¹)^2
         + 2*(HSums.q p)^3*(HSums.h1 p (r-1)*((r:ZMod (p^5))⁻¹)^2 - ((r:ZMod (p^5))⁻¹)^3)
         + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4)) := by
  have hq5 : (HSums.q p)^5 = 0 := HSums.q_pow_five p
  have hchain := chain p hp hp7 r hr1 hr2
  have hsq : (gg p r : ZMod (p^5))^2 * (r:ZMod (p^5))^2 * (Bprod p r)^2
      = 4*(HSums.q p)^2*(gg p 0 : ZMod (p^5))^2*(Aprod p r)^2 := by
    linear_combination ((gg p r : ZMod (p^5))*(r:ZMod (p^5))*Bprod p r + 2*HSums.q p*(gg p 0 : ZMod (p^5))*Aprod p r) * hchain
  have hBdef : Bprod p r = ∏ i ∈ Finset.Icc 1 r, (1 + HSums.q p * ((i:ZMod (p^5))⁻¹)) := rfl
  have hAdef : Aprod p r = ∏ i ∈ Finset.Icc 1 (r-1), (1 + (HSums.q p * 2) * ((i:ZMod (p^5))⁻¹)) := rfl
  have hB2 := Pm_sq p r hp hp7 hr2
  rw [← hBdef] at hB2
  have hA := Pm_sq_gen p (r-1) hp hp7 (by omega) 2
  rw [← hAdef] at hA
  have hB3 : (HSums.q p)^3*(Bprod p r)^2 = (HSums.q p)^3 + 2*(HSums.q p)^4*(HSums.h1 p r) := by
    linear_combination HSums.q p*hB2 + (2*(HSums.h1 p r)^2 - HSums.h2 p r)*hq5
  have hB4 : (HSums.q p)^4*(Bprod p r)^2 = (HSums.q p)^4 := by
    linear_combination (HSums.q p)^2*hB2 + (2*(HSums.h1 p r)+HSums.q p*(2*(HSums.h1 p r)^2 - HSums.h2 p r))*hq5
  have hr1s : HSums.h1 p r = HSums.h1 p (r-1) + (r:ZMod (p^5))⁻¹ := by
    rw [HSums.h1, HSums.h1]
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ (r-1)+1)]
    rw [show (r-1)+1 = r from by omega]
  have hr2s : HSums.h2 p r = HSums.h2 p (r-1) + ((r:ZMod (p^5))⁻¹)^2 := by
    rw [HSums.h2, HSums.h2]
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ (r-1)+1)]
    rw [show (r-1)+1 = r from by omega]
  have star3 : (HSums.q p)^2*(Aprod p r)^2
      = ((HSums.q p)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2)) * (Bprod p r)^2 := by
    rw [hA]
    rw [show ((HSums.q p)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2)) * (Bprod p r)^2
          = (HSums.q p)^2*(Bprod p r)^2 + 2*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹)*((HSums.q p)^3*(Bprod p r)^2) + (2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2)*((HSums.q p)^4*(Bprod p r)^2) from by ring]
    rw [hB2, hB3, hB4, hr1s, hr2s]
    ring
  have huB : IsUnit (Bprod p r) := by
    rw [hBdef]
    exact IsUnit.prod_iff.mpr (fun i _ => isUnit_one_add_nilp _ (by rw [mul_pow, hq5, zero_mul]))
  have huB2 : IsUnit ((Bprod p r)^2) := huB.pow 2
  have hs : (r:ZMod (p^5)) * (r:ZMod (p^5))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (HSums.isUnit_cast hp r hr1 (by omega))
  have h1 : (gg p r : ZMod (p^5))^2 * (r:ZMod (p^5))^2 * (Bprod p r)^2
      = (4*(gg p 0 : ZMod (p^5))^2 * ((HSums.q p)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2))) * (Bprod p r)^2 := by
    rw [hsq]
    linear_combination 4*(gg p 0 : ZMod (p^5))^2 * star3
  have h2 : (gg p r : ZMod (p^5))^2 * (r:ZMod (p^5))^2
      = 4*(gg p 0 : ZMod (p^5))^2 * ((HSums.q p)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2)) :=
    (huB2.mul_left_inj).mp h1
  calc (gg p r : ZMod (p^5))^2
      = ((gg p r : ZMod (p^5))^2 * (r:ZMod (p^5))^2) * ((r:ZMod (p^5))⁻¹)^2 := by
        rw [mul_assoc, show (r:ZMod (p^5))^2*((r:ZMod (p^5))⁻¹)^2 = ((r:ZMod (p^5))*(r:ZMod (p^5))⁻¹)^2 from by ring, hs, one_pow, mul_one]
    _ = (4*(gg p 0 : ZMod (p^5))^2 * ((HSums.q p)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1) - (r:ZMod (p^5))⁻¹) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2 - 3*(HSums.h2 p (r-1)) - 4*(HSums.h1 p (r-1))*(r:ZMod (p^5))⁻¹ + 3*((r:ZMod (p^5))⁻¹)^2))) * ((r:ZMod (p^5))⁻¹)^2 := by rw [h2]
    _ = 4*(gg p 0 : ZMod (p^5))^2 * ((HSums.q p)^2*((r:ZMod (p^5))⁻¹)^2 + 2*(HSums.q p)^3*(HSums.h1 p (r-1)*((r:ZMod (p^5))⁻¹)^2 - ((r:ZMod (p^5))⁻¹)^3) + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4)) := by ring

/-- The `q⁴` coefficient sum of Part C. -/
noncomputable def Ec (p : ℕ) : ZMod (p^5) :=
  ∑ r ∈ Finset.Icc 1 (p-1),
    (2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4)

theorem Ec_dvd (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : ∃ c, Ec p = HSums.q p * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have D : p ∣ p ^ 5 := dvd_pow_self p (by norm_num)
  refine HSums.dvd_of_cast_zero hp _ D ?_
  rw [Ec, map_sum]
  have hstep : ∀ r ∈ Finset.Icc 1 (p-1),
      (ZMod.castHom D (ZMod p)) (2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4)
      = 2*((∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹))^2 * ((r:ZMod p)⁻¹)^2)
        - 3*((∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹)^2) * ((r:ZMod p)⁻¹)^2)
        - 4*((∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹)) * ((r:ZMod p)⁻¹)^3)
        + 3*(((r:ZMod p)⁻¹)^4) := by
    intro r hr; rw [Finset.mem_Icc] at hr
    have hm : r-1 < p := by omega
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [Star6.castHom_h1 hp D _ hm, Star6.castHom_h2 hp D _ hm, Star6.phinv hp D r (by omega) (by omega)]
    ring
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ r ∈ Finset.Icc 1 (p-1), (∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹))^2 * ((r:ZMod p)⁻¹)^2) = Star6.T1' p from rfl,
      show (∑ r ∈ Finset.Icc 1 (p-1), (∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹)^2) * ((r:ZMod p)⁻¹)^2) = Star6.A22' p from rfl,
      show (∑ r ∈ Finset.Icc 1 (p-1), (∑ i ∈ Finset.Icc 1 (r-1), ((i:ZMod p)⁻¹)) * ((r:ZMod p)⁻¹)^3) = Star6.A13' p from rfl,
      show (∑ r ∈ Finset.Icc 1 (p-1), ((r:ZMod p)⁻¹)^4) = Star6.H4' p from rfl]
  rw [Star6.T1'_zero hp hp7, Star6.A22'_zero hp hp7, Star6.A13'_zero hp hp7, Star6.H4'_zero hp7]
  ring

/- ## Part C (high range).

`∑_{r=1}^{p-1} f(p+r)² = 4q²H₂ + 8q³Ta` (exact, mod `p^5`).

This is the one remaining gap.  Its `q²` and `q³` coefficients (`4H₂`, `8Ta`) must
be established *exactly* in `R = ZMod (p^5)`, and its `q⁴` coefficient shown to vanish
mod `p`.  Concretely, using the unified product form and the substitution `s = p-r`,
`f(p+r) = 2q·s⁻¹·∏_{i≠s}(1+(2q-s)·i⁻¹)`, so
`∑_Hi = 4q²·∑_s s⁻²·[∏_{i≠s}(1+(2q-s)i⁻¹)]²`.
Writing `β_s := ∏_{i≠s}((i-s)·i⁻¹)` (a `q`-free unit), the `q²`-coefficient is
`4·∑_s s⁻²β_s²`, which equals `4H₂` only after a Wolstenholme/Wilson-type control of
`β_s²` **mod `p³`** (numerically `∑_s s⁻²β_s² ≡ H₂ (mod p³)` but *not* in `ℚ`), and the
`q³`-coefficient similarly combines the `β_s`-correction (via `q³·H₃ = 0`) with the
inner `∑(i-s)⁻¹` term to give `8Ta`.  This requires a development comparable in size to
`Star6` (reflection identities `reflect_j`, Wilson, and mod-`p³` congruences), which is
not completed here. -/
theorem partC (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc (p+1) (2*p-1), ((p+k-1).choose k : ZMod (p^5))^2
      = 4*(HSums.q p)^2 * HSums.H p 2 + 8*(HSums.q p)^3 * HSums.Ta p := by
  have hq5 : (HSums.q p)^5 = 0 := HSums.q_pow_five p
  have hreindex : ∑ k ∈ Finset.Icc (p+1) (2*p-1), ((p+k-1).choose k : ZMod (p^5))^2
      = ∑ r ∈ Finset.Icc 1 (p-1), (gg p r : ZMod (p^5))^2 := by
    apply Finset.sum_nbij' (fun k => k - p) (fun r => p + r)
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; omega
    · intro a ha; rw [Finset.mem_Icc] at ha
      have hgg : (p+a-1).choose a = gg p (a-p) := by
        unfold gg; rw [show 2*p+(a-p)-1 = p+a-1 from by omega, show p+(a-p) = a from by omega]
      rw [hgg]
  rw [hreindex]
  rw [Finset.sum_congr rfl (fun r hr => termC p hp hp7 r
        (by rw [Finset.mem_Icc] at hr; omega) (by rw [Finset.mem_Icc] at hr; omega))]
  rw [← Finset.mul_sum]
  have hRHSsum : (∑ r ∈ Finset.Icc 1 (p-1),
        ((HSums.q p)^2*((r:ZMod (p^5))⁻¹)^2
         + 2*(HSums.q p)^3*(HSums.h1 p (r-1)*((r:ZMod (p^5))⁻¹)^2 - ((r:ZMod (p^5))⁻¹)^3)
         + (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4)))
      = (HSums.q p)^2 * HSums.H p 2 + 2*(HSums.q p)^3*(HSums.Ta p - HSums.H p 3) + (HSums.q p)^4 * Ec p := by
    have e1 : (HSums.q p)^2 * HSums.H p 2 = ∑ r ∈ Finset.Icc 1 (p-1), (HSums.q p)^2*((r:ZMod (p^5))⁻¹)^2 := by
      rw [HSums.H, Finset.mul_sum]
    have e2 : 2*(HSums.q p)^3 * HSums.Ta p = ∑ r ∈ Finset.Icc 1 (p-1), 2*(HSums.q p)^3*(HSums.h1 p (r-1)*((r:ZMod (p^5))⁻¹)^2) := by
      rw [HSums.Ta, Finset.mul_sum]
    have e3 : 2*(HSums.q p)^3 * HSums.H p 3 = ∑ r ∈ Finset.Icc 1 (p-1), 2*(HSums.q p)^3*(((r:ZMod (p^5))⁻¹)^3) := by
      rw [HSums.H, Finset.mul_sum]
    have e4 : (HSums.q p)^4 * Ec p = ∑ r ∈ Finset.Icc 1 (p-1), (HSums.q p)^4*(2*(HSums.h1 p (r-1))^2*((r:ZMod (p^5))⁻¹)^2 - 3*(HSums.h2 p (r-1))*((r:ZMod (p^5))⁻¹)^2 - 4*(HSums.h1 p (r-1))*((r:ZMod (p^5))⁻¹)^3 + 3*((r:ZMod (p^5))⁻¹)^4) := by
      rw [Ec, Finset.mul_sum]
    rw [show (HSums.q p)^2 * HSums.H p 2 + 2*(HSums.q p)^3*(HSums.Ta p - HSums.H p 3) + (HSums.q p)^4 * Ec p
          = ((HSums.q p)^2 * HSums.H p 2) + (2*(HSums.q p)^3 * HSums.Ta p - 2*(HSums.q p)^3 * HSums.H p 3) + (HSums.q p)^4 * Ec p from by ring]
    rw [e1, e2, e3, e4, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _; ring
  rw [hRHSsum, gp_sq p hp hp7]
  obtain ⟨c1, hH1⟩ := HSums.H_one_dvd hp hp7
  obtain ⟨c2, hH2⟩ := HSums.H_two_dvd hp hp7
  obtain ⟨c3, hH3⟩ := HSums.H_three_dvd hp hp7
  obtain ⟨e, hEc⟩ := Ec_dvd p hp hp7
  have z1 : (HSums.q p)^3 * HSums.H p 3 = 0 := by rw [hH3]; linear_combination c3*hq5
  have z2 : (HSums.q p)^4 * Ec p = 0 := by rw [hEc]; linear_combination e*hq5
  have z3 : (HSums.q p)^3 * (HSums.H p 1 * HSums.H p 2) = 0 := by rw [hH1, hH2]; linear_combination (HSums.q p*c1*c2)*hq5
  have z4 : (HSums.q p)^4 * (HSums.H p 1 * (HSums.Ta p - HSums.H p 3)) = 0 := by rw [hH1]; linear_combination (HSums.q p*c1*(HSums.Ta p - HSums.H p 3))*hq5
  have z5 : (HSums.q p)^4 * (HSums.H p 2)^2 = 0 := by rw [hH2]; linear_combination (HSums.q p*c2^2)*hq5
  linear_combination (-8)*z1 + 4*z2 + 8*z3 + 16*z4 + (-4)*z5
      + (8*HSums.H p 1*Ec p - 8*HSums.H p 2*(HSums.Ta p - HSums.H p 3) - 4*HSums.q p*(HSums.H p 2)^2*Ec p
         - 4*HSums.q p*HSums.H p 2*Ec p + 4*HSums.q p*(HSums.H p 2)^2*Ec p)*hq5

/- ## Range splitting and assembly. -/

theorem split_sum {R : Type*} [AddCommMonoid R] (p : ℕ) (hp1 : 1 ≤ p) (g : ℕ → R) :
    ∑ k ∈ Finset.range (2*p+1), g k
      = g 0 + g p + g (2*p)
        + ∑ k ∈ Finset.Icc 1 (p-1), g k
        + ∑ k ∈ Finset.Icc (p+1) (2*p-1), g k := by
  have hLHi : Disjoint (Finset.Icc 1 (p-1)) (Finset.Icc (p+1) (2*p-1)) := by
    rw [Finset.disjoint_left]; intro a ha hb; rw [Finset.mem_Icc] at ha hb; omega
  have heq : Finset.range (2*p+1)
      = insert 0 (insert p (insert (2*p) (Finset.Icc 1 (p-1) ∪ Finset.Icc (p+1) (2*p-1)))) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_Icc]
    omega
  rw [heq]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Icc]; omega)]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Icc]; omega)]
  rw [Finset.sum_insert (by simp only [Finset.mem_union, Finset.mem_Icc]; omega)]
  rw [Finset.sum_union hLHi]
  abel

/-- **F3'** : the S2 decomposition mod `p^5`. -/
theorem S2_expand (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((HSums.S2 p : ℕ) : ZMod (p ^ 5))
      = 3 + 6 * (q p) * (H p 1) + 10 * (q p) ^ 3 * (Ta p) + (q p) ^ 4 * (Tbc p) := by
  have hcast : ((HSums.S2 p : ℕ) : ZMod (p^5))
      = ∑ k ∈ Finset.range (2*p+1), ((p+k-1).choose k : ZMod (p^5))^2 := by
    rw [HSums.S2, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro k _; push_cast; ring
  rw [hcast, split_sum p (by omega) (fun k => ((p+k-1).choose k : ZMod (p^5))^2)]
  -- combine Parts A, B, C
  have hAe : (((p+0-1).choose 0 : ZMod (p^5)))^2 + ((p+p-1).choose p : ZMod (p^5))^2
      + ((p+2*p-1).choose (2*p) : ZMod (p^5))^2
      = 3 + 6 * HSums.q p * HSums.H p 1 - 5 * (HSums.q p)^2 * HSums.H p 2 := partA p hp hp7
  have hBe := partB p hp hp7
  have hCe := partC p hp hp7
  obtain ⟨cb, hcb⟩ := Tb_dvd p hp hp7
  obtain ⟨ct, hct⟩ := Star6.Tbc_dvd p hp hp7
  have hq5 : (HSums.q p)^5 = 0 := HSums.q_pow_five p
  rw [hBe, hCe]
  rw [show (((p+0-1).choose 0 : ZMod (p^5)))^2 + ((p+p-1).choose p : ZMod (p^5))^2
        + ((p+2*p-1).choose (2*p) : ZMod (p^5))^2
        = 3 + 6 * HSums.q p * HSums.H p 1 - 5 * (HSums.q p)^2 * HSums.H p 2 from hAe]
  rw [hcb, hct]
  linear_combination (cb - ct) * hq5

end F3
end F3_sec

section Assembly_sec

open Nat Finset BigOperators

namespace Assembly

open HSums

/-- **F3'** : the S2 decomposition mod `p^5`. -/
theorem S2_expand (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((HSums.S2 p : ℕ) : ZMod (p ^ 5))
      = 3 + 6 * (q p) * (H p 1) + 10 * (q p) ^ 3 * (Ta p) + (q p) ^ 4 * (Tbc p) :=
  F3.S2_expand p hp hp7

/-- **★5** : `2·q·Ta ≡ 3·H2  (mod q^3)`. -/
theorem Ta_cong (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ d : ZMod (p ^ 5), 2 * (q p) * (Ta p) = 3 * (H p 2) + (q p) ^ 3 * d :=
  Star5.Ta_cong p hp hp7

/-- `S1_expand` restated for `HSums.S1 = C(3p,p)`. -/
theorem S1_expand' (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((HSums.S1 p : ℕ) : ZMod (p ^ 5))
      = 3 + 6 * (q p) * (H p 1) - 6 * (q p) ^ 2 * (H p 2) := by
  have hS1 : HSums.S1 p = (3 * p).choose p := by
    unfold HSums.S1
    have h : ∀ k, (p + k - 1).choose k = p.multichoose k := fun k => (Nat.multichoose_eq p k).symm
    simp_rw [h]
    have := Nat.sum_range_multichoose (2 * p) p
    rwa [show 2 * p + p = 3 * p by ring] at this
  rw [hS1]
  exact S1_expand p hp hp7

/-- The main linear supercongruence in `ZMod (p^5)`:
`4·S1 + 3·S2 ≡ 21`. -/
theorem lin_cast (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    4 * ((HSums.S1 p : ℕ) : ZMod (p ^ 5)) + 3 * ((HSums.S2 p : ℕ) : ZMod (p ^ 5)) = 21 := by
  rw [S1_expand' p hp hp7, S2_expand p hp hp7]
  -- pull in E1, ★5, ★6, H_three_dvd, H_four_dvd
  obtain ⟨c1, hE1⟩ := HSums.H_one_expand hp hp7
  obtain ⟨d, hTa⟩ := Ta_cong p hp hp7
  obtain ⟨c3, hH3⟩ := HSums.H_three_dvd hp hp7
  obtain ⟨c4, hH4⟩ := HSums.H_four_dvd hp hp7
  obtain ⟨cb, hTbc⟩ := Star6.Tbc_dvd p hp hp7
  have hq5 : (q p) ^ 5 = 0 := HSums.q_pow_five p
  have h2inv : (2 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (HSums.two_isUnit hp hp7)
  set Q := q p with hQ
  -- Clean form of E1 scaled by 42Q:  42·Q·H1 = -21·Q²·(H2 + Q·H3 + Q²·H4).
  have f1 : 42 * Q * H p 1 = -21 * Q ^ 2 * (H p 2 + Q * H p 3 + Q ^ 2 * H p 4) := by
    have e : 42 * Q * H p 1
        = -21 * Q ^ 2 * (H p 2 + Q * H p 3 + Q ^ 2 * H p 4) * (2 * (2 : ZMod (p ^ 5))⁻¹)
          + 42 * Q ^ 5 * c1 := by
      rw [hE1]; ring
    rw [h2inv, mul_one, hq5] at e
    rw [e]; ring
  -- Clean form of ★5 scaled:  30·Q³·Ta = 45·Q²·H2.
  have f2 : 30 * Q ^ 3 * Ta p = 45 * Q ^ 2 * H p 2 := by
    have e : 30 * Q ^ 3 * Ta p = 15 * Q ^ 2 * (2 * Q * Ta p) := by ring
    rw [hTa] at e
    have e2 : 30 * Q ^ 3 * Ta p = 45 * Q ^ 2 * H p 2 + 15 * Q ^ 5 * d := by
      rw [e]; ring
    rw [hq5] at e2; rw [e2]; ring
  -- q^5-vanishing facts.
  have g3 : Q ^ 3 * H p 3 = 0 := by rw [hH3]; rw [show Q ^ 3 * (Q ^ 2 * c3) = Q ^ 5 * c3 by ring, hq5, zero_mul]
  have g4 : Q ^ 4 * H p 4 = 0 := by rw [hH4]; rw [show Q ^ 4 * (Q * c4) = Q ^ 5 * c4 by ring, hq5, zero_mul]
  have gb : Q ^ 4 * Tbc p = 0 := by rw [hTbc]; rw [show Q ^ 4 * (Q * cb) = Q ^ 5 * cb by ring, hq5, zero_mul]
  -- Now assemble.
  linear_combination f1 + f2 + (-21 : ZMod (p ^ 5)) * g3 + (-21 : ZMod (p ^ 5)) * g4 + (3 : ZMod (p ^ 5)) * gb

/-- `HSums.S1 = C(3p,p)`. -/
lemma S1_eq (n : ℕ) : HSums.S1 n = (3 * n).choose n := by
  unfold HSums.S1
  have h : ∀ k, (n + k - 1).choose k = n.multichoose k := fun k => (Nat.multichoose_eq n k).symm
  simp_rw [h]
  have := Nat.sum_range_multichoose (2 * n) n
  rwa [show 2 * n + n = 3 * n by ring] at this

/-- `S1 p ≥ 3` for `p ≥ 7`. -/
lemma S1_ge (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : 3 ≤ HSums.S1 p := by
  obtain ⟨m, hm⟩ := choose_3p_p_wol p hp hp7
  rw [S1_eq, hm]; omega

/-- `S2 p ≥ 3` for `p ≥ 7`. -/
lemma S2_ge (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : 3 ≤ HSums.S2 p := by
  have hmem : (1 : ℕ) ∈ Finset.range (2 * p + 1) := by
    rw [Finset.mem_range]; omega
  have hle : ((p + 1 - 1).choose 1) ^ 2
      ≤ ∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2 :=
    Finset.single_le_sum (f := fun k => ((p + k - 1).choose k) ^ 2)
      (fun i _ => Nat.zero_le _) hmem
  have hval : ((p + 1 - 1).choose 1) ^ 2 = p ^ 2 := by
    have : p + 1 - 1 = p := by omega
    rw [this, Nat.choose_one_right]
  rw [hval] at hle
  show 3 ≤ HSums.S2 p
  unfold HSums.S2
  nlinarith [hle, hp7]

/-- **S2_wol** : `S2 p ≡ 3  (mod p^3)` (nat form). -/
theorem S2_wol (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ m : ℕ, HSums.S2 p = 3 + p ^ 3 * m := by
  -- cast to ZMod (p^3): S2 ≡ 3.
  obtain ⟨c1, hH1⟩ := HSums.H_one_dvd hp hp7
  have hexp := S2_expand p hp hp7
  -- rewrite H1 = q^2 c1, so S2 = 3 + q^3·(6 c1) + 10 q^3 Ta + q^4 Tbc = 3 + q^3·(...)
  have hq5 : (q p) ^ 5 = 0 := HSums.q_pow_five p
  have hS2q3 : ((HSums.S2 p : ℕ) : ZMod (p ^ 5))
      = 3 + (q p) ^ 3 * (6 * c1 + 10 * Ta p + (q p) * Tbc p) := by
    rw [hexp, hH1]; ring
  -- push to ZMod (p^3)
  have hdvd : p ^ 3 ∣ p ^ 5 := pow_dvd_pow p (by omega)
  have hcast : ((HSums.S2 p : ℕ) : ZMod (p ^ 3)) = 3 := by
    have hc := congrArg (ZMod.castHom hdvd (ZMod (p ^ 3))) hS2q3
    rw [map_natCast, map_add, map_mul, map_pow] at hc
    rw [show (ZMod.castHom hdvd (ZMod (p ^ 3))) (q p) = (p : ZMod (p ^ 3)) from by
          rw [HSums.q, map_natCast]] at hc
    rw [show ((p : ZMod (p ^ 3))) ^ 3 = 0 from by
          rw [← Nat.cast_pow]; exact ZMod.natCast_self _] at hc
    rw [map_ofNat] at hc
    rw [hc]; ring
  have hmod : HSums.S2 p ≡ 3 [MOD p ^ 3] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (show ((HSums.S2 p : ℕ) : ZMod (p ^ 3)) = ((3 : ℕ) : ZMod (p ^ 3)) from by
        rw [hcast]; norm_num)
  have hge := S2_ge p hp hp7
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hge] at hmod
  obtain ⟨m, hm⟩ := hmod
  exact ⟨m, by omega⟩

/-- **lin_cong** : `4·S1 p + 3·S2 p ≡ 21  (mod p^5)` (nat form). -/
theorem lin_cong (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ m : ℕ, 4 * HSums.S1 p + 3 * HSums.S2 p = 21 + p ^ 5 * m := by
  have hcast : ((4 * HSums.S1 p + 3 * HSums.S2 p : ℕ) : ZMod (p ^ 5)) = 21 := by
    push_cast
    exact lin_cast p hp hp7
  have hmod : 4 * HSums.S1 p + 3 * HSums.S2 p ≡ 21 [MOD p ^ 5] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (show ((4 * HSums.S1 p + 3 * HSums.S2 p : ℕ) : ZMod (p ^ 5)) = ((21 : ℕ) : ZMod (p ^ 5)) from by
        rw [hcast]; norm_num)
  have hge : 21 ≤ 4 * HSums.S1 p + 3 * HSums.S2 p := by
    have := S1_ge p hp hp7; have := S2_ge p hp hp7; omega
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hge] at hmod
  obtain ⟨m, hm⟩ := hmod
  exact ⟨m, by omega⟩

/-! ## Final reduction to the supercongruence. -/

/-- OEIS A357674. -/
def A357674 (n : ℕ) : ℕ :=
  let S1 := ∑ k ∈ Finset.range (2 * n + 1), (n + k - 1).choose k
  let S2 := ∑ k ∈ Finset.range (2 * n + 1), ((n + k - 1).choose k) ^ 2
  S1 ^ 4 * S2 ^ 3

lemma A_eq (n : ℕ) : A357674 n = (HSums.S1 n) ^ 4 * (HSums.S2 n) ^ 3 := rfl

lemma A357674_one : A357674 1 = 2187 := by decide

/-- The supercongruence for `p ≥ 7`. -/
theorem main_ge7 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (A357674 p : ZMod (p ^ 5)) = (A357674 1 : ZMod (p ^ 5)) := by
  rw [A357674_one]
  -- cast forms
  obtain ⟨m1, hm1⟩ := choose_3p_p_wol p hp hp7
  obtain ⟨m2, hm2⟩ := S2_wol p hp hp7
  have hS1nat : HSums.S1 p = 3 + p ^ 3 * m1 := by rw [S1_eq]; exact hm1
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := HSums.q_pow_five p
  have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 := by
    rw [show (p : ZMod (p ^ 5)) ^ 6 = (p : ZMod (p ^ 5)) ^ 5 * (p : ZMod (p ^ 5)) by ring, hp5, zero_mul]
  -- S1 = 3 + p^3 u, S2 = 3 + p^3 v in R
  have ha : (HSums.S1 p : ZMod (p ^ 5)) = 3 + (p : ZMod (p ^ 5)) ^ 3 * (m1 : ZMod (p ^ 5)) := by
    rw [hS1nat]; push_cast; ring
  have hb : (HSums.S2 p : ZMod (p ^ 5)) = 3 + (p : ZMod (p ^ 5)) ^ 3 * (m2 : ZMod (p ^ 5)) := by
    rw [hm2]; push_cast; ring
  have hlin := lin_cast p hp hp7
  set u := (m1 : ZMod (p ^ 5))
  set v := (m2 : ZMod (p ^ 5))
  set P := (p : ZMod (p ^ 5)) with hP
  -- 4(p^3 u) + 3(p^3 v) = 0
  have hz : 4 * (P ^ 3 * u) + 3 * (P ^ 3 * v) = 0 := by
    rw [ha, hb] at hlin; linear_combination hlin
  have hq2 : (P ^ 3) ^ 2 = 0 := by
    rw [show (P ^ 3) ^ 2 = P ^ 6 by ring]; exact hp6
  have hAcast : (A357674 p : ZMod (p ^ 5))
      = (HSums.S1 p : ZMod (p ^ 5)) ^ 4 * (HSums.S2 p : ZMod (p ^ 5)) ^ 3 := by
    rw [A_eq]; push_cast; ring
  rw [hAcast, ha, hb]
  -- Set a := P^3 u, b := P^3 v; use nilpotency (a^2 = b^2 = a*b = 0) with SMALL ring calls.
  have ha2 : (P ^ 3 * u) ^ 2 = 0 := by
    rw [show (P ^ 3 * u) ^ 2 = (P ^ 3) ^ 2 * u ^ 2 by ring, hq2, zero_mul]
  have hb2 : (P ^ 3 * v) ^ 2 = 0 := by
    rw [show (P ^ 3 * v) ^ 2 = (P ^ 3) ^ 2 * v ^ 2 by ring, hq2, zero_mul]
  have hab : (P ^ 3 * u) * (P ^ 3 * v) = 0 := by
    rw [show (P ^ 3 * u) * (P ^ 3 * v) = (P ^ 3) ^ 2 * (u * v) by ring, hq2, zero_mul]
  -- (3 + a)^4 = 81 + 108 a  (a^2 = 0)
  have e1 : (3 + P ^ 3 * u) ^ 4 = 81 + 108 * (P ^ 3 * u) := by
    have h : (3 + P ^ 3 * u) ^ 4
        = 81 + 108 * (P ^ 3 * u) + (P ^ 3 * u) ^ 2 * (54 + 12 * (P ^ 3 * u) + (P ^ 3 * u) ^ 2) := by
      ring
    rw [h, ha2]; ring
  -- (3 + b)^3 = 27 + 27 b  (b^2 = 0)
  have e2 : (3 + P ^ 3 * v) ^ 3 = 27 + 27 * (P ^ 3 * v) := by
    have h : (3 + P ^ 3 * v) ^ 3
        = 27 + 27 * (P ^ 3 * v) + (P ^ 3 * v) ^ 2 * (9 + (P ^ 3 * v)) := by
      ring
    rw [h, hb2]; ring
  rw [e1, e2]
  -- (81 + 108 a)(27 + 27 b) = 2187 + 2916 a + 2187 b  (a*b = 0)
  have e3 : (81 + 108 * (P ^ 3 * u)) * (27 + 27 * (P ^ 3 * v))
      = 2187 + 2916 * (P ^ 3 * u) + 2187 * (P ^ 3 * v) := by
    have h : (81 + 108 * (P ^ 3 * u)) * (27 + 27 * (P ^ 3 * v))
        = 2187 + 2916 * (P ^ 3 * u) + 2187 * (P ^ 3 * v)
          + ((P ^ 3 * u) * (P ^ 3 * v)) * 2916 := by ring
    rw [h, hab]; ring
  rw [e3]
  have hcast1 : ((2187 : ℕ) : ZMod (p ^ 5)) = 2187 := by push_cast; ring
  rw [hcast1]
  linear_combination (729 : ZMod (p ^ 5)) * hz

/-- **The conjecture** for `p ≥ 3`. -/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  by_cases h7 : p ≥ 7
  · rw [← ZMod.natCast_eq_natCast_iff]; exact main_ge7 p hp h7
  · interval_cases p <;> first | (exact absurd hp (by decide)) | decide

end Assembly
end Assembly_sec

theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  by_cases h7 : p ≥ 7
  · rw [← ZMod.natCast_eq_natCast_iff]
    exact Assembly.main_ge7 p hp h7
  · interval_cases p <;> first | (exact absurd hp (by decide)) | decide



