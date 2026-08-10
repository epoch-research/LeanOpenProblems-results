import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Sun

/- ============================================================
   Building block: harmonic-type sums mod p
   ============================================================ -/

variable {p : ℕ}

/-- Sum of `x^s` over all of `ZMod p` is 0 when `0 < s < p - 1`. -/
theorem sum_pow_zmod [Fact p.Prime] (s : ℕ) (h : s < p - 1) :
    ∑ x : ZMod p, x ^ s = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hc]; exact h

/-- Harmonic sum mod p: `∑_{x} (x⁻¹)^s = 0` for `1 ≤ s < p-1`. -/
theorem harmonic_modp [Fact p.Prime] (s : ℕ) (hs2 : s < p - 1) :
    ∑ x : ZMod p, (x⁻¹)^s = 0 := by
  have h1 : ∑ x : ZMod p, (x⁻¹)^s = ∑ x : ZMod p, x^s := by
    have h := Equiv.sum_comp (Function.Involutive.toPerm (Inv.inv : ZMod p → ZMod p) inv_inv)
      (fun y => y^s)
    simpa [Function.Involutive.coe_toPerm] using h
  rw [h1]; exact sum_pow_zmod s hs2

/-- Convert a sum over `ZMod p` into a sum over `range p` via the natural cast. -/
theorem zmod_sum_range {M : Type*} [AddCommMonoid M] [NeZero p] (f : ZMod p → M) :
    ∑ x : ZMod p, f x = ∑ r ∈ Finset.range p, f (r : ZMod p) := by
  apply Finset.sum_nbij' (i := fun x : ZMod p => x.val) (j := fun r : ℕ => (r : ZMod p))
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro b _; exact Finset.mem_univ _
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · intro a _; rw [ZMod.natCast_rightInverse a]

/-- `Icc 1 (p-1)` form: sum of `f` over `range p` equals `f 0 + ` sum over `Icc 1 (p-1)`. -/
theorem sum_range_eq_icc {M : Type*} [AddCommMonoid M] (hp : 0 < p) (g : ℕ → M) :
    ∑ r ∈ Finset.range p, g r = g 0 + ∑ r ∈ Finset.Icc 1 (p-1), g r := by
  have : Finset.range p = insert 0 (Finset.Icc 1 (p-1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [this, Finset.sum_insert (by simp)]

/-- `Icc`-form harmonic sum mod p: `∑_{r=1}^{p-1} (r⁻¹)^s = 0` for `1 ≤ s < p-1`. -/
theorem harmonic_modp_icc [Fact p.Prime] (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s < p - 1) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((r : ZMod p))⁻¹)^s = 0 := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hne : NeZero p := ⟨hp.ne'⟩
  have h := harmonic_modp s hs2
  rw [zmod_sum_range (fun x : ZMod p => (x⁻¹)^s)] at h
  rw [sum_range_eq_icc hp (fun r => (((r : ZMod p))⁻¹)^s)] at h
  simp only [Nat.cast_zero, inv_zero] at h
  rw [zero_pow (by omega : s ≠ 0), zero_add] at h
  exact h

/- ============================================================
   Wolstenholme mod p^2
   ============================================================ -/

/-- For `T : ZMod (p^2)` whose reduction mod `p` is `0`, we have `p * T = 0`. -/
theorem p_mul_eq_zero_of_castHom_zero (hp : 0 < p) (T : ZMod (p^2))
    (h : (ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)) T = 0) :
    (p : ZMod (p^2)) * T = 0 := by
  have hne : NeZero p := ⟨hp.ne'⟩
  have hpd : p ∣ T.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨c, hc⟩ := hpd
  have e1 : (p : ZMod (p^2)) * T = ((p * T.val : ℕ) : ZMod (p^2)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e1, hc]
  have e2 : p * (p * c) = p^2 * c := by ring
  rw [e2, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The natural reduction `ZMod (p^2) → ZMod p` as a ring hom. -/
local notation "red₂" => (ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p))

/-- `(jp + r)` is a unit in `ZMod (p^2)` when `1 ≤ r ≤ p-1`. -/
theorem isUnit_jp_add [Fact p.Prime] (j r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    IsUnit ((j * p + r : ℕ) : ZMod (p^2)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hpp : p.Prime := Fact.out
  have hrp : ¬ p ∣ (j * p + r) := by
    intro hd
    have : p ∣ r := (Nat.dvd_add_right ⟨j, by ring⟩).mp hd
    have := Nat.le_of_dvd (by omega) this
    omega
  have hcop : Nat.Coprime (j * p + r) p := (hpp.coprime_iff_not_dvd.mpr hrp).symm
  exact hcop.pow_right 2

/-- `r` is a unit in `ZMod (p^2)` for `1 ≤ r ≤ p-1`. -/
theorem isUnit_cast [Fact p.Prime] (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    IsUnit ((r : ℕ) : ZMod (p^2)) := by
  have := isUnit_jp_add 0 r h1 h2
  simpa using this

/-- pairing identity for inverses of units `a, b` in a comm ring with `ZMod`-style inverse. -/
theorem inv_add_inv_of_units (a b : ZMod (p^2)) (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  have hmul : (a * b) * (a⁻¹ * b⁻¹) = 1 := by
    have e : (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    rw [e, ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one]
  have hinv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := ZMod.inv_eq_of_mul_eq_one (p^2) _ _ hmul
  rw [hinv]
  have e1 : (a + b) * (a⁻¹ * b⁻¹) = b⁻¹ * (a * a⁻¹) + a⁻¹ * (b * b⁻¹) := by ring
  rw [e1, ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one, mul_one, add_comm]

/-- The reduction `red₂` preserves inverses of units. -/
theorem red₂_inv [Fact p.Prime] (x : ZMod (p^2)) (hx : IsUnit x) :
    red₂ (x⁻¹) = (red₂ x)⁻¹ := by
  have h1 : red₂ x * red₂ (x⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one]
  exact (ZMod.inv_eq_of_mul_eq_one p _ _ h1).symm

/-- `2` is a unit in `ZMod (p^2)` for odd prime `p`. -/
theorem isUnit_two [Fact p.Prime] (hp5 : 5 ≤ p) : IsUnit (2 : ZMod (p^2)) := by
  have hpp : p.Prime := Fact.out
  rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by norm_num, ZMod.isUnit_iff_coprime]
  have : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hpp]; omega
  exact this.pow_right 2

/-- Basic Wolstenholme: `∑_{r=1}^{p-1} r⁻¹ = 0` in `ZMod (p^2)`. -/
theorem wolstenholme_two [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((r : ℕ) : ZMod (p^2)))⁻¹ = 0 := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := hpp.pos
  set S := ∑ r ∈ Finset.Icc 1 (p-1), (((r : ℕ) : ZMod (p^2)))⁻¹ with hSdef
  -- reflection r ↦ p - r
  have hrefl : S = ∑ r ∈ Finset.Icc 1 (p-1), ((((p - r : ℕ)) : ZMod (p^2)))⁻¹ := by
    apply Finset.sum_nbij' (i := fun r => p - r) (j := fun r => p - r)
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha
      have : p - (p - a) = a := by omega
      rw [this]
  -- T : the paired sum
  set T := ∑ r ∈ Finset.Icc 1 (p-1),
      ((((r : ℕ) : ZMod (p^2)) * (((p - r : ℕ)) : ZMod (p^2))))⁻¹ with hTdef
  have h2S : 2 * S = (p : ZMod (p^2)) * T := by
    have : S + S = ∑ r ∈ Finset.Icc 1 (p-1),
        ((((r : ℕ) : ZMod (p^2)))⁻¹ + ((((p - r : ℕ)) : ZMod (p^2)))⁻¹) := by
      rw [Finset.sum_add_distrib, ← hrefl]
    rw [two_mul, this, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit (((r : ℕ) : ZMod (p^2))) := by
      exact isUnit_cast r hr.1 hr.2
    have hpru : IsUnit ((((p - r : ℕ)) : ZMod (p^2))) := by
      exact isUnit_cast (p - r) (by omega) (by omega)
    rw [inv_add_inv_of_units _ _ hru hpru]
    congr 1
    rw [← Nat.cast_add]
    have : r + (p - r) = p := by omega
    rw [this]
  -- reduce T mod p is zero
  have hTred : red₂ T = 0 := by
    rw [hTdef, map_sum]
    rw [show (0 : ZMod p) = -(∑ r ∈ Finset.Icc 1 (p-1), ((((r:ℕ):ZMod p))⁻¹)^2) by
        rw [harmonic_modp_icc 2 (by norm_num) (by omega)]; ring]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit (((r : ℕ) : ZMod (p^2)) * (((p - r : ℕ)) : ZMod (p^2))) := by
      apply IsUnit.mul
      · exact isUnit_cast r hr.1 hr.2
      · exact isUnit_cast (p - r) (by omega) (by omega)
    rw [red₂_inv _ hru, map_mul]
    -- red₂ (↑r) = ↑r, red₂ (↑(p-r)) = ↑(p-r) = -↑r in ZMod p
    have e1 : red₂ (((r : ℕ) : ZMod (p^2))) = ((r : ℕ) : ZMod p) := map_natCast _ r
    have e2 : red₂ ((((p - r : ℕ)) : ZMod (p^2))) = -(((r : ℕ) : ZMod p)) := by
      rw [map_natCast, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [e1, e2]
    rw [show ((r:ℕ):ZMod p) * -((r:ℕ):ZMod p) = -(((r:ℕ):ZMod p)^2) by ring]
    rw [inv_neg, inv_pow]
  -- conclude
  have hpT : (p : ZMod (p^2)) * T = 0 := p_mul_eq_zero_of_castHom_zero hp0 T hTred
  rw [hpT] at h2S
  exact (IsUnit.mul_right_eq_zero (isUnit_two hp5)).mp h2S

/-- Order-2 sum reduces to 0 mod p, hence `p *` it is `0` in `ZMod (p^2)`. -/
theorem p_mul_sumsq [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ZMod (p^2)) * (∑ r ∈ Finset.Icc 1 (p-1), (((r:ℕ):ZMod (p^2))⁻¹)^2) = 0 := by
  have hpp : p.Prime := Fact.out
  apply p_mul_eq_zero_of_castHom_zero hpp.pos
  rw [map_sum]
  rw [← harmonic_modp_icc (p := p) 2 (by norm_num) (by omega)]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_Icc] at hr
  rw [map_pow, red₂_inv _ (isUnit_cast r hr.1 hr.2), map_natCast]

/-- Shifted Wolstenholme: `∑_{r=1}^{p-1} (jp+r)⁻¹ = 0` in `ZMod (p^2)`. -/
theorem wolstenholme_shift [Fact p.Prime] (hp5 : 5 ≤ p) (j : ℕ) :
    ∑ r ∈ Finset.Icc 1 (p-1), (((j * p + r : ℕ) : ZMod (p^2)))⁻¹ = 0 := by
  have hpp : p.Prime := Fact.out
  have key : ∀ r ∈ Finset.Icc 1 (p-1),
      (((j * p + r : ℕ) : ZMod (p^2)))⁻¹
        = ((r:ℕ):ZMod (p^2))⁻¹ - (j * p : ZMod (p^2)) * (((r:ℕ):ZMod (p^2))⁻¹)^2 := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have hru : IsUnit ((r:ℕ):ZMod (p^2)) := isUnit_cast r hr.1 hr.2
    have hp2 : (p : ZMod (p^2))^2 = 0 := by
      rw [show ((p:ZMod (p^2)))^2 = ((p^2 : ℕ) : ZMod (p^2)) by push_cast; ring, ZMod.natCast_self]
    have hr1 : ((r:ℕ):ZMod (p^2)) * ((r:ℕ):ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hru
    have ha2 : ((j:ZMod (p^2)) * (p:ZMod (p^2)))^2 = 0 := by rw [mul_pow, hp2, mul_zero]
    apply ZMod.inv_eq_of_mul_eq_one
    push_cast
    linear_combination (1 - (j:ZMod (p^2))*(p:ZMod (p^2)) * ((r:ℕ):ZMod (p^2))⁻¹) * hr1
      - (((r:ℕ):ZMod (p^2))⁻¹)^2 * ha2
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [wolstenholme_two hp5]
  rw [show (j * p : ZMod (p^2)) = (j : ZMod (p^2)) * (p : ZMod (p^2)) by ring]
  rw [mul_assoc, p_mul_sumsq hp5, mul_zero, sub_zero]

end Sun


open Nat Finset BigOperators

namespace SunInt

/-- The numerator sum `S N = ∑_{k=0}^N (N+2k) C(N+k-1, N-1)^3`. -/
def Sb (N : ℕ) : ℕ :=
  ∑ k ∈ range (N + 1), (N + 2 * k) * (Nat.choose (N + k - 1) (N - 1)) ^ 3

/-- The integer-form summand `Term_k * C^2` for k ≥ 1. -/
-- absorption identity
theorem absorb {N k : ℕ} (hN : 1 ≤ N) :
    (N + k) * (N + k - 1).choose k = N * (N + k).choose k := by
  have hsym1 : (N + k - 1).choose (N - 1) = (N + k - 1).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k - 1 by omega)]; congr 1; omega
  have hsym2 : (N + k).choose N = (N + k).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k by omega)]; congr 1; omega
  have key := Nat.succ_mul_choose_eq (N + k - 1) (N - 1)
  -- succ (N+k-1) * choose (N+k-1) (N-1) = choose (succ (N+k-1)) (succ (N-1)) * succ (N-1)
  have e1 : Nat.succ (N + k - 1) = N + k := by omega
  have e2 : Nat.succ (N - 1) = N := by omega
  rw [e1, e2, hsym1, hsym2] at key
  -- key : (N + k) * (N+k-1).choose k = (N+k).choose k * N
  rw [key]; ring

theorem absorb2 {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (N + k - 1).choose k * k = (N + k - 1).choose (k - 1) * N := by
  have key := Nat.choose_succ_right_eq (N + k - 1) (k - 1)
  have e1 : (k - 1) + 1 = k := by omega
  have e2 : (N + k - 1) - (k - 1) = N := by omega
  rw [e1, e2] at key
  exact key

/-- Per-k identity (k ≥ 1): the term equals N times the integer summand. -/
theorem term_eq {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (N + 2 * k) * (N + k - 1).choose (N - 1) ^ 3
      = N * (((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2) := by
  have hsym1 : (N + k - 1).choose (N - 1) = (N + k - 1).choose k := by
    rw [← Nat.choose_symm (show k ≤ N + k - 1 by omega)]; congr 1; omega
  rw [hsym1]
  set C := (N + k - 1).choose k with hC
  have ha := absorb (N := N) (k := k) hN
  have hb := absorb2 (N := N) (k := k) hN hk
  -- ha : (N+k)*C = N*(N+k).choose k
  -- hb : C*k = (N+k-1).choose (k-1) * N
  -- Goal: (N+2k)*C^3 = N*((N+k).choose k + (N+k-1).choose (k-1))*C^2
  have expand : N * (((N + k).choose k + (N + k - 1).choose (k - 1)) * C ^ 2)
      = (N * (N + k).choose k + (N + k - 1).choose (k - 1) * N) * C ^ 2 := by ring
  rw [expand, ← ha, ← hb]
  ring

/-- The closed integer form of `a N`. -/
def aClosed (N : ℕ) : ℕ :=
  if N = 0 then 0
  else 1 + ∑ k ∈ Icc 1 N, ((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2

theorem range_split (N : ℕ) : range (N + 1) = insert 0 (Icc 1 N) := by
  ext x; simp only [mem_range, mem_insert, mem_Icc]; omega

/-- `Sb N = N * aClosed N` for `N ≥ 1`. -/
theorem Sb_eq (N : ℕ) (hN : 1 ≤ N) : Sb N = N * aClosed N := by
  rw [Sb, range_split, Finset.sum_insert (by simp), aClosed, if_neg (by omega)]
  have hk0 : (N + 2 * 0) * (N + 0 - 1).choose (N - 1) ^ 3 = N := by
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [Nat.choose_self, one_pow, mul_one]
  rw [hk0]
  have hrest : ∑ k ∈ Icc 1 N, (N + 2 * k) * (N + k - 1).choose (N - 1) ^ 3
      = N * ∑ k ∈ Icc 1 N, ((N + k).choose k + (N + k - 1).choose (k - 1)) * (N + k - 1).choose k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mem_Icc] at hk
    exact term_eq hN hk.1
  rw [hrest, Nat.mul_add, mul_one]

/-- The Spec-style division definition equals the closed form. -/
theorem aDiv_eq (N : ℕ) : (if N = 0 then 0 else Sb N / N) = aClosed N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [aClosed]
  · rw [if_neg (by omega), Sb_eq N h, Nat.mul_div_cancel_left _ (by omega)]

/- ============================================================
   The analytic core: Φ(m) = Sb(mp) - p·Sb(m), and the main divisibility.
   ============================================================ -/

variable {p : ℕ}

/-- The key integer `Φ(m) = Sb(mp) - p·Sb(m)`. -/
def Phi (p m : ℕ) : ℤ := (Sb (m * p) : ℤ) - p * (Sb m : ℤ)

/-- BASE CASE: `p ∤ m ⟹ p^4 ∣ Φ(m)`. -/
theorem base_case (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    (p : ℤ) ^ 4 ∣ Phi p m := by
  sorry

/-- TRANSFER: `p^(4(2+v_p(μ))) ∣ Φ(pμ) - p^4·Φ(μ)`. -/
theorem transfer (hp : p.Prime) (hp5 : 5 ≤ p) (μ : ℕ) (hμ : 1 ≤ μ) :
    (p : ℤ) ^ (4 * (2 + padicValNat p μ)) ∣ (Phi p (p * μ) - (p : ℤ) ^ 4 * Phi p μ) := by
  sorry

/-- `Φ(m) = (m·p)·(aClosed(m·p) - aClosed m)`. -/
theorem Phi_eq (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    Phi p m = (m * p : ℤ) * ((aClosed (m * p) : ℤ) - (aClosed m : ℤ)) := by
  have hp0 : 0 < p := hp.pos
  have hmp : 1 ≤ m * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold Phi
  rw [Sb_eq (m * p) hmp, Sb_eq m hm]
  push_cast
  ring

/-- MAIN LEMMA: `p^(4(1+v_p(m))) ∣ Φ(m)`, by strong induction on `v_p(m)`. -/
theorem main_lemma (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (p : ℤ) ^ (4 * (1 + padicValNat p m)) ∣ Phi p m := by
  -- strong induction on w = padicValNat p m
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  generalize hw : padicValNat p m = w
  induction w using Nat.strong_induction_on generalizing m with
  | _ w IH =>
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · -- w = 0: p ∤ m, base case
      subst hw0
      have hpm : ¬ p ∣ m := by
        intro hd
        have := (padicValNat.eq_zero_iff (p := p) (n := m)).mp (hw)
        rcases this with h | h | h
        · omega
        · omega
        · exact h hd
      simpa using base_case hp hp5 m hm hpm
    · -- w ≥ 1: m = p·μ
      have hpm : p ∣ m := by
        by_contra hd
        rw [padicValNat.eq_zero_of_not_dvd hd] at hw; omega
      obtain ⟨μ, hμeq⟩ := hpm
      have hμpos : 1 ≤ μ := by
        rcases Nat.eq_zero_or_pos μ with h | h
        · subst h; simp at hμeq; omega
        · exact h
      have hvμ : padicValNat p μ = w - 1 := by
        have : padicValNat p m = padicValNat p μ + 1 := by
          rw [hμeq, mul_comm, padicValNat.mul (by omega) (by omega), padicValNat.self hp1]
        omega
      -- IH applies to μ
      have hIH : (p : ℤ) ^ (4 * (1 + padicValNat p μ)) ∣ Phi p μ :=
        IH (padicValNat p μ) (by omega) μ hμpos rfl
      -- transfer
      have hT := transfer hp hp5 μ hμpos
      -- Φ(m) = Φ(pμ); decompose
      have hmpμ : m = p * μ := by rw [hμeq, mul_comm]
      rw [hmpμ]
      have key : Phi p (p * μ) = (p : ℤ) ^ 4 * Phi p μ + (Phi p (p * μ) - (p : ℤ) ^ 4 * Phi p μ) := by ring
      rw [key]
      apply dvd_add
      · -- p^(4(1+w)) ∣ p^4 * Φ(μ)
        have hexp : 4 * (1 + w) ≤ 4 + 4 * (1 + padicValNat p μ) := by rw [hvμ]; omega
        calc (p:ℤ)^(4*(1+w)) ∣ (p:ℤ)^(4 + 4*(1+padicValNat p μ)) := pow_dvd_pow _ hexp
          _ ∣ (p:ℤ)^4 * Phi p μ := by
                rw [pow_add]; exact mul_dvd_mul (dvd_refl _) hIH
      · -- p^(4(1+w)) ∣ err
        have hexp : 4 * (1 + w) ≤ 4 * (2 + padicValNat p μ) := by rw [hvμ]; omega
        exact dvd_trans (pow_dvd_pow _ hexp) hT

/-- The step congruence for the closed form: `p^(3(1+v_p m)) ∣ aClosed(mp) - aClosed m`. -/
theorem step_dvd (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (1 + padicValNat p m)) ∣ ((aClosed (m * p) : ℤ) - (aClosed m : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hmp : m * p ≠ 0 := by positivity
  set e := 1 + padicValNat p m with he
  -- v_p(m*p) = e
  have hve : padicValNat p (m * p) = e := by
    rw [padicValNat.mul (by omega) (by omega), padicValNat.self hp.one_lt, he, Nat.add_comm]
  -- m*p = p^e * c with p ∤ c
  set c := (m * p) / p ^ e with hc
  have hdvd : p ^ e ∣ m * p := by rw [← hve]; exact pow_padicValNat_dvd
  have hmpc : m * p = p ^ e * c := (Nat.mul_div_cancel' hdvd).symm
  have hpc : ¬ p ∣ c := by
    intro hdc
    obtain ⟨d, hd⟩ := hdc
    have : p ^ (e + 1) ∣ m * p := ⟨d, by rw [hmpc, hd]; ring⟩
    have := pow_succ_padicValNat_not_dvd (p := p) hmp
    rw [hve] at this
    exact this ‹p ^ (e+1) ∣ m * p›
  -- main lemma gives p^(4e) ∣ Phi p m = (m*p)*(D)
  have hML := main_lemma hp hp5 m hm
  rw [Phi_eq hp m hm] at hML
  -- hML : p^(4*(1+v_p m)) ∣ (↑m*↑p) * D ; note 4*(1+v_p m) = 4 e
  have he4 : 4 * (1 + padicValNat p m) = 4 * e := by rw [he]
  rw [he4] at hML
  set D := (aClosed (m * p) : ℤ) - (aClosed m : ℤ) with hD
  -- ↑m*↑p = p^e * ↑c, and p^(4e) = p^e * p^(3e)
  have hcoef : (m : ℤ) * (p : ℤ) = (p : ℤ) ^ e * (c : ℤ) := by
    rw [← Nat.cast_mul, hmpc]; push_cast; ring
  have h1 : (p : ℤ) ^ (4 * e) = (p : ℤ) ^ e * (p : ℤ) ^ (3 * e) := by rw [← pow_add]; ring_nf
  rw [hcoef, h1] at hML
  -- hML : p^e * p^(3e) ∣ (p^e * ↑c) * D
  have hML' : (p : ℤ) ^ e * (p : ℤ) ^ (3 * e) ∣ (p : ℤ) ^ e * ((c : ℤ) * D) := by
    have : (p : ℤ) ^ e * (c : ℤ) * D = (p : ℤ) ^ e * ((c : ℤ) * D) := by ring
    rw [this] at hML; exact hML
  have hpe0 : (p : ℤ) ^ e ≠ 0 := pow_ne_zero e (by exact_mod_cast hp0.ne')
  have hML2 : (p : ℤ) ^ (3 * e) ∣ (c : ℤ) * D :=
    (mul_dvd_mul_iff_left hpe0).mp hML'
  -- p^(3e) coprime to c, so p^(3e) ∣ D
  have hcop : IsCoprime ((p : ℤ) ^ (3 * e)) (c : ℤ) := by
    have : IsCoprime (p : ℤ) (c : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((hp.coprime_iff_not_dvd).mpr hpc)
    exact this.pow_left
  exact hcop.dvd_of_dvd_mul_left hML2

/-- Conjecture for the closed form. -/
theorem conj_closed (hp : p.Prime) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    aClosed (n * p ^ r) ≡ aClosed (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  set m := n * p ^ (r - 1) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmp : m * p = n * p ^ r := by
    rw [hm]
    have : p ^ (r - 1) * p = p ^ r := by
      rw [← pow_succ]; congr 1; omega
    rw [mul_assoc, this]
  -- v_p(m) ≥ r-1
  have hvm : r ≤ 1 + padicValNat p m := by
    have : padicValNat p m = padicValNat p n + (r - 1) := by
      rw [hm, padicValNat.mul (by omega) (by positivity), padicValNat.prime_pow]
    omega
  have hstep := step_dvd hp hp5 m hm1
  rw [hmp] at hstep
  -- p^(3r) ∣ p^(3(1+v_p m)) ∣ aClosed(np^r) - aClosed m
  have hbig : (p : ℤ) ^ (3 * r) ∣ ((aClosed (n * p ^ r) : ℤ) - (aClosed m : ℤ)) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hstep
  -- convert to ModEq
  rw [Nat.modEq_iff_dvd]
  have hcast : ((p ^ (3 * r) : ℕ) : ℤ) = (p : ℤ) ^ (3 * r) := by push_cast; ring
  rw [hcast]
  rw [show ((aClosed m : ℤ) - (aClosed (n * p ^ r) : ℤ)) = -(((aClosed (n*p^r):ℤ)) - aClosed m) by ring]
  exact (dvd_neg).mpr hbig

