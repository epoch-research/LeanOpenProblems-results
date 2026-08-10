import Submission.JacobRef
import Submission.Wolstenholme

/-!
# Jacobsthal–Kazandzidis tower congruence: `P_tower_dvd`

This file works towards a sorry-free proof of

  `p ^ (3*(t+1)) ∣ P A - P B · P (A-B)`  when `p^t ∣ A, B` and `B < A`, `p ≥ 5`.

We build the elementary mechanism: the coprime-to-`p` products `P n` factor as
`((p-1)!)^n · G n` with `G n = ∏_{j<n} F j`, `F m = ∏_{r=1}^{p-1}(1 + p m / r)`
(rational, a `p`-adic unit `≡ 1 mod p^3`).  The valuation bookkeeping is done
over `ℚ` with `padicValRat`.
-/

open Finset

namespace PTower

variable {p : ℕ}

/-! ## Harmonic sums over `ℚ` and their `p`-adic valuations -/

/-- The harmonic-type sum `∑_{r=1}^{p-1} r^{-j}` as a rational number. -/
noncomputable def Hs (p j : ℕ) : ℚ := ∑ r ∈ Icc 1 (p - 1), ((r : ℚ)⁻¹) ^ j

/-- Bridge: if the inverse-`j`-th-power sum vanishes in `ZMod (p^k)`, then the
rational harmonic sum `Hs p j` has `p`-adic valuation `≥ k`. -/
theorem le_padicValRat_Hs (p j k : ℕ) [Fact p.Prime]
    (hz : (∑ r ∈ Icc 1 (p - 1), ((r : ZMod (p ^ k))⁻¹) ^ j) = 0) :
    (k : ℤ) ≤ padicValRat p (Hs p j) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 := hp.two_le
  set s := Icc 1 (p - 1) with hs
  set u : ℕ := (p - 1).factorial with hu
  -- u coprime to p
  have hcop : Nat.Coprime u p := by
    rw [hu]; refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    rw [Nat.Prime.dvd_factorial hp]; omega
  -- r ∣ u for r ∈ s
  have hrdvd : ∀ r ∈ s, r ∣ u := by
    intro r hr; rw [hs, mem_Icc] at hr
    exact Nat.dvd_factorial (by omega) (by omega)
  have hrpos : ∀ r ∈ s, 0 < r := by
    intro r hr; rw [hs, mem_Icc] at hr; omega
  -- integer numerator
  set W : ℕ := ∑ r ∈ s, (u / r) ^ j with hW
  -- Hs p j = W / u^j
  have hu0 : (u : ℚ) ≠ 0 := by
    have : 0 < u := Nat.factorial_pos _; positivity
  have hHs : Hs p j = (W : ℚ) / (u : ℚ) ^ j := by
    rw [Hs, hW]
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr0 : (r : ℚ) ≠ 0 := by
      have := hrpos r hr; positivity
    have huv : ((u / r : ℕ) : ℚ) = (u : ℚ) / (r : ℚ) := by
      rw [Nat.cast_div (hrdvd r hr) hr0]
    rw [Nat.cast_pow, huv, div_pow, inv_pow]
    field_simp
  -- p^k ∣ W
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  have hunit : ∀ r ∈ s, IsUnit ((r : ℕ) : ZMod (p ^ k)) := by
    intro r hr
    rw [ZMod.isUnit_iff_coprime]
    rw [hs, mem_Icc] at hr
    have hnd : ¬ p ∣ r := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.Coprime.pow_right k ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  have hWzmod : ((W : ℕ) : ZMod (p ^ k)) = 0 := by
    rw [hW, Nat.cast_sum]
    simp only [Nat.cast_pow]
    have hrw : (∑ r ∈ s, ((u / r : ℕ) : ZMod (p ^ k)) ^ j)
        = ((u : ℕ) : ZMod (p ^ k)) ^ j * ∑ r ∈ s, (((r : ℕ) : ZMod (p ^ k))⁻¹) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have huv : ((u / r : ℕ) : ZMod (p ^ k)) = ((u : ℕ) : ZMod (p ^ k)) * ((r : ℕ) : ZMod (p ^ k))⁻¹ := by
        have hmul : (u / r : ℕ) * r = u := Nat.div_mul_cancel (hrdvd r hr)
        have hbb : ((r : ℕ) : ZMod (p ^ k)) * ((r : ℕ) : ZMod (p ^ k))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hunit r hr)
        have hprod : (((u / r : ℕ) : ZMod (p ^ k))) * ((r : ℕ) : ZMod (p ^ k)) = ((u : ℕ) : ZMod (p ^ k)) := by
          rw [← Nat.cast_mul, hmul]
        calc ((u / r : ℕ) : ZMod (p ^ k))
            = ((u / r : ℕ) : ZMod (p ^ k)) * (((r : ℕ) : ZMod (p ^ k)) * ((r : ℕ) : ZMod (p ^ k))⁻¹) := by
              rw [hbb, mul_one]
          _ = (((u / r : ℕ) : ZMod (p ^ k)) * ((r : ℕ) : ZMod (p ^ k))) * ((r : ℕ) : ZMod (p ^ k))⁻¹ := by ring
          _ = ((u : ℕ) : ZMod (p ^ k)) * ((r : ℕ) : ZMod (p ^ k))⁻¹ := by rw [hprod]
      rw [huv, mul_pow]
    rw [hrw, hz, mul_zero]
  have hpk : p ^ k ∣ W := by
    rw [← ZMod.natCast_eq_zero_iff]; exact hWzmod
  -- conclude valuation
  have hWne : W ≠ 0 := by
    rw [hW]
    have hmem : (p - 1) ∈ s := by rw [hs, mem_Icc]; omega
    have hterm : 0 < (u / (p-1))^j := by
      have hdp : 0 < u / (p-1) := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (hrdvd _ hmem)) (by omega)
      positivity
    have hpos := Finset.sum_pos' (f := fun r => (u / r) ^ j) (fun r _ => Nat.zero_le _) ⟨p-1, hmem, hterm⟩
    simpa using hpos.ne'
  have hval : (k : ℤ) ≤ (padicValNat p W : ℤ) := by
    exact_mod_cast (padicValNat_dvd_iff_le hWne).mp hpk
  rw [hHs]
  have hupow : (u : ℚ) ^ j ≠ 0 := pow_ne_zero _ hu0
  have hWQ : (W : ℚ) ≠ 0 := by exact_mod_cast hWne
  rw [padicValRat.div hWQ hupow]
  have hvu0 : padicValNat p u = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm h
  have hvu : padicValRat p ((u : ℚ) ^ j) = 0 := by
    rw [padicValRat.pow (by exact_mod_cast (by have : 0 < u := Nat.factorial_pos _; omega : (u:ℤ) ≠ 0))]
    rw [padicValRat.of_nat, hvu0]; simp
  rw [hvu, sub_zero, padicValRat.of_nat]
  exact hval

/-! ## Power-sum congruences and the divisibility of `D_i` -/

/-- Nilpotent binomial: if `x^2 = 0` then `(x+y)^(n+1) = y^(n+1) + (n+1) x y^n`. -/
theorem nilp_binom {R : Type*} [CommRing R] (x y : R) (hx : x ^ 2 = 0) (n : ℕ) :
    (x + y) ^ (n + 1) = y ^ (n + 1) + ((n + 1 : ℕ) : R) * (x * y ^ n) := by
  induction n with
  | zero => push_cast; ring
  | succ d ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (((d : R) + 1) * y ^ d) * hx

/-- `∑_{x : ZMod p} x^m` over the whole field vanishes for `m ≤ p-2`. -/
theorem sum_pow_univ_zero (p m : ℕ) [Fact p.Prime] (hm : m ≤ p - 2) :
    ∑ x : ZMod p, x ^ m = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; have := (Fact.out : p.Prime).two_le; omega

/-- Reindex a sum over `range p` (via `natCast`) to a sum over `ZMod p`. -/
theorem sum_range_zmod (p : ℕ) [NeZero p] {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ s ∈ range p, f (s : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (i := fun s => ((s : ℕ) : ZMod p)) (j := fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro x _; rw [mem_range]; exact ZMod.val_lt x
  · intro a ha; rw [mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- `∑_{k < p*c} k^m ≡ 0 (mod p)` for `m ≤ p-2`. -/
theorem block_psum (p m c : ℕ) [Fact p.Prime] (hm : m ≤ p - 2) :
    (∑ k ∈ range (p * c), (k : ZMod p) ^ m) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  induction c with
  | zero => simp
  | succ d ih =>
    rw [show p * (d + 1) = p * d + p by ring, Finset.sum_range_add, ih, zero_add]
    have : (∑ x ∈ range p, ((p * d + x : ℕ) : ZMod p) ^ m) = ∑ x ∈ range p, ((x : ℕ) : ZMod p) ^ m := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      congr 1
      push_cast
      rw [ZMod.natCast_self]; ring
    rw [this, sum_range_zmod p (fun y => y ^ m)]
    exact sum_pow_univ_zero p m hm

/-- `p^2 ∣ D_i` where `D_i = ∑_{k<C}((B+k)^i - k^i)`, given `p ∣ B`, `p ∣ C`,
`1 ≤ i ≤ p-1`. -/
theorem D_dvd (p B C i : ℕ) [Fact p.Prime] (hpB : p ∣ B) (hpC : p ∣ C)
    (hi1 : 1 ≤ i) (hip : i ≤ p - 1) :
    ((p : ℤ) ^ 2) ∣ ∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i) := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) from by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- Work in ZMod (p^2)
  -- (↑B)^2 = 0
  obtain ⟨b', rfl⟩ := hpB
  obtain ⟨c', rfl⟩ := hpC
  have hBsq : ((p * b' : ℕ) : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, show (p * b') ^ 2 = p ^ 2 * b' ^ 2 by ring, Nat.cast_mul, ZMod.natCast_self,
      zero_mul]
  -- rewrite the i-th power difference via nilp_binom (i = (i-1)+1)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ k : ℕ, ((((p * b' : ℕ) : ZMod (p ^ 2)) + ((k : ℕ) : ZMod (p ^ 2))) ^ (j + 1) - ((k : ℕ) : ZMod (p ^ 2)) ^ (j + 1))
      = ((j + 1 : ℕ) : ZMod (p ^ 2)) * (((p * b' : ℕ) : ZMod (p ^ 2)) * ((k : ℕ) : ZMod (p ^ 2)) ^ j) := by
    intro k
    rw [nilp_binom _ _ hBsq j]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- now p * b' factor and the inner sum divisible by p
  have hSm : ∑ k ∈ range (p * c'), ((k : ℕ) : ZMod (p ^ 2)) ^ j = 0 ∨ True := Or.inr trivial
  -- the inner sum: cast of an integer power sum divisible by p
  set Sm : ℕ := ∑ k ∈ range (p * c'), k ^ j with hSmdef
  have hpSm : p ∣ Sm := by
    have := block_psum p j c' (by omega)
    rw [← ZMod.natCast_eq_zero_iff]
    rw [hSmdef, Nat.cast_sum]
    simpa using this
  obtain ⟨M, hM⟩ := hpSm
  have hcast : (∑ k ∈ range (p * c'), ((k : ℕ) : ZMod (p ^ 2)) ^ j) = ((Sm : ℕ) : ZMod (p ^ 2)) := by
    rw [hSmdef, Nat.cast_sum]; push_cast; rfl
  rw [hcast, hM]
  push_cast
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination (((j : ZMod (p^2)) + 1) * (b' : ZMod (p^2)) * (M : ZMod (p^2))) * hp2

/-- `∑_{r=1}^{p-1} r^{-3} = 0` in `ZMod p` (Fermat / power-sum vanishing). -/
theorem sum_inv_cube (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hcard : ∑ x : ZMod p, x ^ 3 = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one (ZMod p) 3
    rw [ZMod.card]; omega
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ 3 = 0 := by
    rw [← hcard]
    exact Equiv.sum_comp
      (Equiv.mk (fun x => x⁻¹) (fun x => x⁻¹) (fun x => inv_inv x) (fun x => inv_inv x))
      (fun y => y ^ 3)
  rw [Wolst.sumIcc_eq_sumUniv p (fun x => (x⁻¹) ^ 3) (by simp)]
  exact hinv

/-- `v_p(H_1) ≥ 2` (Wolstenholme). -/
theorem two_le_val_H1 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (2 : ℤ) ≤ padicValRat p (Hs p 1) := by
  have h := le_padicValRat_Hs p 1 2 (by simp only [pow_one]; exact Wolst.sum_inv p hp5)
  exact_mod_cast h

/-- `v_p(H_2) ≥ 1`. -/
theorem one_le_val_H2 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (1 : ℤ) ≤ padicValRat p (Hs p 2) := by
  have h := le_padicValRat_Hs p 2 1 (by rw [pow_one]; exact Wolst.sum_inv_sq p hp5)
  exact_mod_cast h

/-- `v_p(H_3) ≥ 1`. -/
theorem one_le_val_H3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (1 : ℤ) ≤ padicValRat p (Hs p 3) := by
  have h := le_padicValRat_Hs p 3 1 (by rw [pow_one]; exact sum_inv_cube p hp5)
  exact_mod_cast h

/-! ## A `vge` valuation predicate on `ℚ` (handles zero cleanly) -/

/-- `vge p n q` : `q = 0` or `v_p(q) ≥ n`. -/
def vge (p : ℕ) (n : ℤ) (q : ℚ) : Prop := q = 0 ∨ n ≤ padicValRat p q

theorem vge_zero (p : ℕ) (n : ℤ) : vge p n 0 := Or.inl rfl

theorem vge_mono {p : ℕ} {m n : ℤ} (h : m ≤ n) {q : ℚ} (hq : vge p n q) : vge p m q := by
  rcases hq with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans h h1)

theorem vge_add {p : ℕ} [Fact p.Prime] {n : ℤ} {q r : ℚ} (hq : vge p n q) (hr : vge p n r) :
    vge p n (q + r) := by
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · simpa using (Or.inr hq : vge p n q)
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  · exact Or.inr (le_trans (le_min hq hr) (padicValRat.min_le_padicValRat_add hqr))

theorem vge_mul {p : ℕ} [Fact p.Prime] {m n : ℤ} {q r : ℚ} (hq : vge p m q) (hr : vge p n r) :
    vge p (m + n) (q * r) := by
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  by_cases hr0 : r = 0
  · exact Or.inl (by rw [hr0, mul_zero])
  rcases hq with rfl | hq
  · exact absurd rfl hq0
  rcases hr with rfl | hr
  · exact absurd rfl hr0
  exact Or.inr (by rw [padicValRat.mul hq0 hr0]; exact add_le_add hq hr)

theorem vge_sum {p : ℕ} [Fact p.Prime] {ι : Type*} {n : ℤ} (s : Finset ι) (F : ι → ℚ)
    (h : ∀ i ∈ s, vge p n (F i)) : vge p n (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vge_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- From integer divisibility to `vge`. -/
theorem vge_of_int_dvd {p : ℕ} [Fact p.Prime] {k : ℕ} {z : ℤ} (h : (p : ℤ) ^ k ∣ z) :
    vge p (k : ℤ) ((z : ℚ)) := by
  by_cases hz : z = 0
  · exact Or.inl (by rw [hz]; simp)
  refine Or.inr ?_
  have hzn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hpk : p ^ k ∣ z.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h; simpa [Int.natAbs_pow] using this
  have hle : k ≤ padicValNat p z.natAbs := (padicValNat_dvd_iff_le hzn).mp hpk
  rw [show ((z : ℚ)) = ((z : ℤ) : ℚ) from rfl, padicValRat.of_int]
  have : padicValInt p z = padicValNat p z.natAbs := rfl
  rw [this]; exact_mod_cast hle

/-- `v_p((p:ℚ)^i) = i`, hence `vge p i (p^i)`. -/
theorem vge_ppow {p : ℕ} [Fact p.Prime] (i : ℕ) : vge p (i : ℤ) ((p : ℚ) ^ i) := by
  have : ((p : ℚ) ^ i) = (((p ^ i : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact vge_of_int_dvd (by exact_mod_cast (dvd_refl ((p:ℤ)^i)))

/-- From `vge p 6 (N:ℚ)` conclude `p^6 ∣ N` for an integer `N`. -/
theorem int_dvd_of_vge {p : ℕ} [Fact p.Prime] {N : ℤ} (h : vge p 6 ((N : ℚ))) :
    (p : ℤ) ^ 6 ∣ N := by
  rcases h with h0 | h1
  · have : N = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  · by_cases hN : N = 0
    · rw [hN]; exact dvd_zero _
    have hNn : N.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    rw [show ((N : ℚ)) = ((N : ℤ) : ℚ) from rfl, padicValRat.of_int] at h1
    have h2 : (6 : ℤ) ≤ (padicValNat p N.natAbs : ℤ) := h1
    have h3 : 6 ≤ padicValNat p N.natAbs := by exact_mod_cast h2
    have hpk : p ^ 6 ∣ N.natAbs := (padicValNat_dvd_iff_le hNn).mpr h3
    have hthis : (p : ℤ) ^ 6 ∣ (N.natAbs : ℤ) := by exact_mod_cast hpk
    exact Int.dvd_natAbs.mp hthis

/-- `2 * ∑_{|T|=2} ∏ = (∑)^2 - ∑ sq` for any finite family. -/
theorem esymm2 (s : Finset ℕ) (a : ℕ → ℚ) :
    2 * ∑ T ∈ powersetCard 2 s, ∏ r ∈ T, a r = (∑ r ∈ s, a r) ^ 2 - (∑ r ∈ s, (a r) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [show powersetCard 2 (∅ : Finset ℕ) = ∅ from by simp]; simp
  | @insert x s hx ih =>
    have hdisj : Disjoint (powersetCard 2 s) (image (insert x) (powersetCard 1 s)) := by
      rw [Finset.disjoint_left]
      intro T hT hT2
      rw [Finset.mem_image] at hT2
      obtain ⟨U, hU, rfl⟩ := hT2
      exact hx ((mem_powersetCard.mp hT).1 (mem_insert_self x U))
    have hinj : ∀ U ∈ powersetCard 1 s, ∀ V ∈ powersetCard 1 s, insert x U = insert x V → U = V := by
      intro U hU V hV hUV
      have hxU : x ∉ U := fun hc => hx ((mem_powersetCard.mp hU).1 hc)
      have hxV : x ∉ V := fun hc => hx ((mem_powersetCard.mp hV).1 hc)
      have := congrArg (Finset.erase · x) hUV
      simpa [Finset.erase_insert hxU, Finset.erase_insert hxV] using this
    rw [powersetCard_succ_insert hx, Finset.sum_union hdisj, Finset.sum_image hinj]
    have hprod : ∀ T ∈ powersetCard 1 s, ∏ r ∈ insert x T, a r = a x * ∏ r ∈ T, a r := by
      intro T hT
      rw [Finset.prod_insert (fun hc => hx ((mem_powersetCard.mp hT).1 hc))]
    rw [Finset.sum_congr rfl hprod, ← Finset.mul_sum]
    have h1 : ∑ T ∈ powersetCard 1 s, ∏ r ∈ T, a r = ∑ r ∈ s, a r := by
      rw [powersetCard_one, Finset.sum_map]; simp
    rw [h1, Finset.sum_insert hx, Finset.sum_insert hx]
    ring_nf; ring_nf at ih; linarith [ih]

/-- `6 * ∑_{|T|=3} ∏ = (∑)^3 - 3(∑)(∑ sq) + 2(∑ cube)`. -/
theorem esymm3 (s : Finset ℕ) (a : ℕ → ℚ) :
    6 * ∑ T ∈ powersetCard 3 s, ∏ r ∈ T, a r
      = (∑ r ∈ s, a r) ^ 3 - 3 * (∑ r ∈ s, a r) * (∑ r ∈ s, (a r) ^ 2)
        + 2 * (∑ r ∈ s, (a r) ^ 3) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [show powersetCard 3 (∅ : Finset ℕ) = ∅ from by simp]; simp
  | @insert x s hx ih =>
    have hdisj : Disjoint (powersetCard 3 s) (image (insert x) (powersetCard 2 s)) := by
      rw [Finset.disjoint_left]
      intro T hT hT2
      rw [Finset.mem_image] at hT2
      obtain ⟨U, hU, rfl⟩ := hT2
      exact hx ((mem_powersetCard.mp hT).1 (mem_insert_self x U))
    have hinj : ∀ U ∈ powersetCard 2 s, ∀ V ∈ powersetCard 2 s, insert x U = insert x V → U = V := by
      intro U hU V hV hUV
      have hxU : x ∉ U := fun hc => hx ((mem_powersetCard.mp hU).1 hc)
      have hxV : x ∉ V := fun hc => hx ((mem_powersetCard.mp hV).1 hc)
      have := congrArg (Finset.erase · x) hUV
      simpa [Finset.erase_insert hxU, Finset.erase_insert hxV] using this
    have hrec : ∑ T ∈ powersetCard 3 (insert x s), ∏ r ∈ T, a r
        = (∑ T ∈ powersetCard 3 s, ∏ r ∈ T, a r) + a x * ∑ T ∈ powersetCard 2 s, ∏ r ∈ T, a r := by
      rw [powersetCard_succ_insert hx, Finset.sum_union hdisj, Finset.sum_image hinj]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [Finset.prod_insert (fun hc => hx ((mem_powersetCard.mp hT).1 hc))]
    rw [hrec, Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have he2 := esymm2 s a
    linear_combination ih + 3 * (a x) * he2

/-- `v_p((n:ℚ)) = 0` when `p ∤ n`. -/
theorem padicValRat_nat_eq_zero {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : ¬ p ∣ n) :
    padicValRat p ((n : ℚ)) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]; rfl

/-- Cancel a `p`-adic unit rational factor `c` (`v_p(c)=0`). -/
theorem vge_cancel_unit {p : ℕ} [Fact p.Prime] {n : ℤ} {c q : ℚ} (hc : c ≠ 0)
    (hcv : padicValRat p c = 0) (h : vge p n (c * q)) : vge p n q := by
  have hcinv : vge p 0 (c⁻¹) := by
    refine Or.inr ?_
    rw [show c⁻¹ = 1 / c from by rw [one_div], padicValRat.div one_ne_zero hc, hcv]
    simp
  have := vge_mul hcinv h
  rwa [show c⁻¹ * (c * q) = q from by field_simp, zero_add] at this

/-! ## The pairing identity `2H₁ = -pH₂ - p²H₃ + p³J₃` -/

/-- The `p`-adic integer tail `J₃ = ∑ 1/(r³(p-r))`. -/
noncomputable def J3 (p : ℕ) : ℚ := ∑ r ∈ Icc 1 (p - 1), 1 / ((r : ℚ) ^ 3 * ((p : ℚ) - (r : ℚ)))

theorem pairing (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    2 * Hs p 1 = -(p : ℚ) * Hs p 2 - (p : ℚ) ^ 2 * Hs p 3 + (p : ℚ) ^ 3 * J3 p := by
  have hp := (Fact.out : p.Prime)
  -- reindex ∑ 1/(p-r) = H₁
  have hre : ∑ r ∈ Icc 1 (p - 1), ((p : ℚ) - (r : ℚ))⁻¹ = Hs p 1 := by
    rw [Hs]
    refine Finset.sum_nbij' (i := fun r => p - r) (j := fun r => p - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha
      simp only [mem_Icc] at ha
      have hle : a ≤ p := by omega
      show ((p : ℚ) - (a : ℚ))⁻¹ = ((((p - a : ℕ)) : ℚ)⁻¹) ^ 1
      rw [pow_one, Nat.cast_sub hle]
  -- per-term identity
  have hterm : ∀ r ∈ Icc 1 (p - 1),
      ((r : ℚ)⁻¹) ^ 1 + ((p : ℚ) - (r : ℚ))⁻¹
        = -(p : ℚ) * ((r : ℚ)⁻¹) ^ 2 - (p : ℚ) ^ 2 * ((r : ℚ)⁻¹) ^ 3
          + (p : ℚ) ^ 3 * (1 / ((r : ℚ) ^ 3 * ((p : ℚ) - (r : ℚ)))) := by
    intro r hr
    rw [mem_Icc] at hr
    have hrpos : 0 < r := by omega
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hpr0 : (p : ℚ) - (r : ℚ) ≠ 0 := by
      have : (r : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : r < p)
      intro h; rw [sub_eq_zero] at h; exact absurd h.symm (ne_of_lt this)
    field_simp
    ring
  -- assemble
  have h2 : 2 * Hs p 1 = ∑ r ∈ Icc 1 (p - 1), (((r : ℚ)⁻¹) ^ 1 + ((p : ℚ) - (r : ℚ))⁻¹) := by
    rw [Finset.sum_add_distrib, hre, Hs, two_mul]
  rw [h2, Finset.sum_congr rfl hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [Hs, Hs, J3]

/-- `v_p(J₃) ≥ 0`: `J₃` is a `p`-adic integer. -/
theorem vge_J3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : vge p 0 (J3 p) := by
  have hp := (Fact.out : p.Prime)
  rw [J3]
  apply vge_sum
  intro r hr
  rw [mem_Icc] at hr
  -- 1/(r³(p-r)) : denominator coprime to p
  have hden : (((r ^ 3 * (p - r) : ℕ)) : ℚ) = (r : ℚ) ^ 3 * ((p : ℚ) - (r : ℚ)) := by
    have hle : r ≤ p := by omega
    push_cast [Nat.cast_sub hle]; ring
  have hcop : ¬ p ∣ (r ^ 3 * (p - r)) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
    · have := hp.dvd_of_dvd_pow h1
      have := Nat.le_of_dvd (by omega) this; omega
    · have := Nat.le_of_dvd (by omega) h2; omega
  refine Or.inr ?_
  rw [← hden, show (1 : ℚ) / ((r ^ 3 * (p - r) : ℕ) : ℚ) = (((r ^ 3 * (p - r) : ℕ) : ℚ))⁻¹ from by
    rw [one_div]]
  rw [show ((((r ^ 3 * (p - r) : ℕ) : ℚ)))⁻¹ = 1 / ((r ^ 3 * (p - r) : ℕ) : ℚ) from by rw [one_div]]
  have hne : (((r ^ 3 * (p - r) : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < r ^ 3 * (p - r) := by
      apply Nat.mul_pos (pow_pos (by omega) 3) (by omega)
    exact_mod_cast this.ne'
  rw [padicValRat.div one_ne_zero hne, padicValRat_nat_eq_zero hcop]
  simp

/-! ## The unit factor `F` and its elementary-symmetric expansion -/

/-- `F p m = ∏_{r=1}^{p-1} (1 + p m / r)`, a rational `p`-adic unit `≡ 1 (mod p^3)`. -/
noncomputable def Fp (p m : ℕ) : ℚ := ∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * (m : ℚ)) * (r : ℚ)⁻¹)

/-- `i`-th elementary symmetric function of the inverses `{1/r : 1 ≤ r ≤ p-1}`. -/
noncomputable def ei (p i : ℕ) : ℚ := ∑ T ∈ powersetCard i (Icc 1 (p - 1)), ∏ r ∈ T, (r : ℚ)⁻¹

theorem F_expand (p m : ℕ) (hp : 1 ≤ p) :
    Fp p m = ∑ i ∈ range p, ((p : ℚ) * (m : ℚ)) ^ i * ei p i := by
  have hcard : (Icc 1 (p - 1)).card + 1 = p := by rw [Nat.card_Icc]; omega
  rw [Fp, Finset.prod_one_add, Finset.sum_powerset, hcard]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ei, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hTcard : T.card = j := (mem_powersetCard.mp hT).2
  rw [Finset.prod_mul_distrib, Finset.prod_const, hTcard]

/-- `e_1 = H_1`. -/
theorem ei_one (p : ℕ) : ei p 1 = Hs p 1 := by
  rw [ei, powersetCard_one, Finset.sum_map, Hs]
  simp [pow_one]

/-- `2 e_2 = H_1^2 - H_2`. -/
theorem ei_two (p : ℕ) : 2 * ei p 2 = (Hs p 1) ^ 2 - Hs p 2 := by
  rw [ei, esymm2 (Icc 1 (p - 1)) (fun r => (r : ℚ)⁻¹), Hs, Hs]
  simp [pow_one]

/-- `v_p(e_i) ≥ 0`: `e_i` is a `p`-adic integer. -/
theorem vge_ei_zero (p : ℕ) [Fact p.Prime] (i : ℕ) : vge p 0 (ei p i) := by
  have hp := (Fact.out : p.Prime)
  rw [ei]
  apply vge_sum
  intro T hT
  have hTsub : T ⊆ Icc 1 (p - 1) := (mem_powersetCard.mp hT).1
  -- N = ∏ r, coprime to p
  set N : ℕ := ∏ r ∈ T, r with hN
  have hprodeq : (∏ r ∈ T, (r : ℚ)⁻¹) = ((N : ℚ))⁻¹ := by
    rw [hN, Nat.cast_prod, ← Finset.prod_inv_distrib]
  have hcopN : ¬ p ∣ N := by
    rw [hN]
    intro hdvd
    rw [hp.prime.dvd_finset_prod_iff] at hdvd
    obtain ⟨r, hr, hpr⟩ := hdvd
    have := hTsub hr
    rw [mem_Icc] at this
    have := Nat.le_of_dvd (by omega) hpr
    omega
  have hN0 : (N : ℚ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos (fun r hr => by
      have := hTsub hr; rw [mem_Icc] at this; omega)
    exact_mod_cast this.ne'
  rw [hprodeq]
  refine Or.inr ?_
  rw [show ((N : ℚ))⁻¹ = 1 / (N : ℚ) from by rw [one_div], padicValRat.div one_ne_zero hN0]
  have : padicValRat p ((N : ℚ)) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hcopN]; rfl
  rw [this]; simp

/-- `v_p(e_3) ≥ 1`. -/
theorem vge_e3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : vge p 1 (ei p 3) := by
  have hid : 6 * ei p 3 = (Hs p 1) ^ 3 - 3 * (Hs p 1) * (Hs p 2) + 2 * (Hs p 3) := by
    rw [ei, esymm3 (Icc 1 (p - 1)) (fun r => (r : ℚ)⁻¹)]
    rw [Hs, Hs, Hs]; simp [pow_one]
  have vH1 : vge p 2 (Hs p 1) := Or.inr (two_le_val_H1 p hp5)
  have vH2 : vge p 1 (Hs p 2) := Or.inr (one_le_val_H2 p hp5)
  have vH3 : vge p 1 (Hs p 3) := Or.inr (one_le_val_H3 p hp5)
  have v2 : vge p 0 ((2 : ℚ)) := Or.inr (by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by norm_num, padicValRat_nat_eq_zero (by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)])
  have vn3 : vge p 0 ((-3 : ℚ)) := Or.inr (by
    rw [show (-3 : ℚ) = -((3 : ℕ) : ℚ) from by norm_num, padicValRat.neg,
      padicValRat_nat_eq_zero (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)])
  have t1 : vge p 1 ((Hs p 1) ^ 3) := by
    rw [show (Hs p 1) ^ 3 = (Hs p 1) * ((Hs p 1) * (Hs p 1)) from by ring]
    exact vge_mono (by norm_num) (vge_mul vH1 (vge_mul vH1 vH1))
  have t2 : vge p 1 ((-3) * (Hs p 1) * (Hs p 2)) :=
    vge_mono (by norm_num) (vge_mul (vge_mul vn3 vH1) vH2)
  have t3 : vge p 1 (2 * (Hs p 3)) := vge_mul v2 vH3
  have hrhs : vge p 1 ((Hs p 1) ^ 3 - 3 * (Hs p 1) * (Hs p 2) + 2 * (Hs p 3)) := by
    have hsub : vge p 1 ((Hs p 1) ^ 3 - 3 * (Hs p 1) * (Hs p 2)) := by
      rw [sub_eq_add_neg, show -(3 * (Hs p 1) * (Hs p 2)) = (-3) * (Hs p 1) * (Hs p 2) from by ring]
      exact vge_add t1 t2
    exact vge_add hsub t3
  rw [← hid] at hrhs
  have hp := (Fact.out : p.Prime)
  have hnd6 : ¬ p ∣ 6 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from by norm_num at h ⊢; exact h) with h2 | h3
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  refine vge_cancel_unit (c := (6 : ℚ)) (by norm_num) ?_ hrhs
  rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) from by norm_num, padicValRat_nat_eq_zero hnd6]

/-! ## More `vge` calculus -/

theorem vge_one (p : ℕ) [Fact p.Prime] : vge p 0 ((1 : ℚ)) :=
  Or.inr (by
    rw [show (1 : ℚ) = ((1 : ℕ) : ℚ) from by norm_num, padicValRat.of_nat]
    exact_mod_cast Nat.zero_le _)

theorem vge_sub {p : ℕ} [Fact p.Prime] {n : ℤ} {q r : ℚ} (hq : vge p n q) (hr : vge p n r) :
    vge p n (q - r) := by
  rw [sub_eq_add_neg]
  refine vge_add hq ?_
  rcases hr with rfl | hr
  · exact Or.inl neg_zero
  · exact Or.inr (by rw [padicValRat.neg]; exact hr)

theorem vge_int0 {p : ℕ} [Fact p.Prime] (z : ℤ) : vge p 0 ((z : ℚ)) := by
  have := vge_of_int_dvd (p := p) (k := 0) (z := z) (by simp)
  simpa using this

theorem vge_nat1 {p : ℕ} [Fact p.Prime] {B : ℕ} (h : p ∣ B) : vge p 1 ((B : ℚ)) := by
  have hdvd : (p : ℤ) ^ 1 ∣ (B : ℤ) := by rw [pow_one]; exact_mod_cast h
  have := vge_of_int_dvd hdvd
  simpa using this

theorem vge_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) (n : ℤ)
    (h : ∀ i ∈ s, vge p n (f i)) : vge p (n * s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, mul_zero];
             exact vge_one p
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hmul := vge_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))
    rw [show n * ((s.card + 1 : ℕ) : ℤ) = n + n * (s.card : ℤ) from by push_cast; ring]
    exact hmul

theorem vge_pow_zero {p : ℕ} [Fact p.Prime] {q : ℚ} (h : vge p 0 q) (n : ℕ) :
    vge p 0 (q ^ n) := by
  have := vge_prod (range n) (fun _ => q) 0 (fun i _ => h)
  rw [Finset.prod_const, Finset.card_range, zero_mul] at this
  exact this

/-! ## The unit factorisation `P n = ((p-1)!)^n · G n` -/

/-- `uu p = (p-1)! = ∏_{r=1}^{p-1} r` as a rational, a `p`-adic unit. -/
noncomputable def uu (p : ℕ) : ℚ := ∏ r ∈ Icc 1 (p - 1), (r : ℚ)

theorem vge_uu (p : ℕ) [Fact p.Prime] : vge p 0 (uu p) := by
  rw [uu]
  have hfac : ∀ r ∈ Icc 1 (p - 1), vge p 0 ((r : ℚ)) := by
    intro r _
    refine Or.inr ?_
    rw [padicValRat.of_nat]
    exact_mod_cast Nat.zero_le _
  have := vge_prod (Icc 1 (p - 1)) (fun r => (r : ℚ)) 0 hfac
  rwa [zero_mul] at this

/-- Block identity `∏_{r=1}^{p-1}(p n + r) = uu p · F p n`. -/
theorem block_eq (p n : ℕ) :
    (∏ r ∈ Icc 1 (p - 1), ((p : ℚ) * (n : ℚ) + (r : ℚ))) = uu p * Fp p n := by
  rw [uu, Fp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  rw [mem_Icc] at hr
  have hrpos : 0 < r := by omega
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrpos.ne'
  field_simp
  ring

/-- The factorisation `(P p n : ℚ) = (uu p)^n · ∏_{j<n} F p j`. -/
theorem P_eq (p n : ℕ) (hp : 0 < p) :
    ((JacobRef.P p n : ℕ) : ℚ) = (uu p) ^ n * (∏ j ∈ range n, Fp p j) := by
  induction n with
  | zero => simp [JacobRef.P]
  | succ n ih =>
    rw [JacobRef.P_succ p n hp, Nat.cast_mul, ih, Finset.prod_range_succ]
    have hb : ((∏ r ∈ Icc 1 (p - 1), (p * n + r) : ℕ) : ℚ) = uu p * Fp p n := by
      rw [Nat.cast_prod, ← block_eq p n]
      apply Finset.prod_congr rfl
      intro r _; push_cast; ring
    rw [hb, pow_succ]
    ring

/-- `e_0 = 1`. -/
theorem ei_zero (p : ℕ) : ei p 0 = 1 := by
  rw [ei, Finset.powersetCard_zero]
  simp

/-- `v_p(e_2) ≥ 1`. -/
theorem vge_e2 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : vge p 1 (ei p 2) := by
  have hid : 2 * ei p 2 = (Hs p 1) ^ 2 - Hs p 2 := ei_two p
  have vH1 : vge p 2 (Hs p 1) := Or.inr (two_le_val_H1 p hp5)
  have vH2 : vge p 1 (Hs p 2) := Or.inr (one_le_val_H2 p hp5)
  have t1 : vge p 1 ((Hs p 1) ^ 2) := by
    rw [show (Hs p 1) ^ 2 = Hs p 1 * Hs p 1 from by ring]
    exact vge_mono (by norm_num) (vge_mul vH1 vH1)
  have vrhs : vge p 1 ((Hs p 1) ^ 2 - Hs p 2) := vge_sub t1 vH2
  rw [← hid] at vrhs
  refine vge_cancel_unit (c := (2 : ℚ)) (by norm_num) ?_ vrhs
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by norm_num, padicValRat_nat_eq_zero (by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega)]

/-- `v_p(F p m - 1) ≥ 3` for every `m`. -/
theorem Fp_sub_one_vge3 (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p 3 (Fp p m - 1) := by
  have hp1 : 1 ≤ p := by omega
  rw [F_expand p m hp1, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
  have hf0 : ((p : ℚ) * (m : ℚ)) ^ 0 * ei p 0 = 1 := by rw [pow_zero, one_mul, ei_zero]
  rw [hf0, show (1 : ℚ) + (∑ i ∈ Ico 1 p, ((p : ℚ) * (m : ℚ)) ^ i * ei p i) - 1
        = ∑ i ∈ Ico 1 p, ((p : ℚ) * (m : ℚ)) ^ i * ei p i from by ring]
  apply vge_sum
  intro i hi
  rw [Finset.mem_Ico] at hi
  have hppm : vge p (i : ℤ) (((p : ℚ) * (m : ℚ)) ^ i) := by
    rw [mul_pow]
    have h1 : vge p (i : ℤ) ((p : ℚ) ^ i) := vge_ppow i
    have h2 : vge p 0 (((m : ℚ)) ^ i) := vge_pow_zero (by
      rw [show ((m : ℚ)) = ((m : ℤ) : ℚ) from by push_cast; ring]; exact vge_int0 _) i
    have := vge_mul h1 h2
    rwa [add_zero] at this
  -- the coefficient valuation depends on i
  rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with h1 | h2 | h3
  · subst h1
    have he : vge p 2 (ei p 1) := by rw [ei_one]; exact Or.inr (two_le_val_H1 p hp5)
    have := vge_mul hppm he
    exact vge_mono (by norm_num) this
  · subst h2
    have he : vge p 1 (ei p 2) := vge_e2 p hp5
    have := vge_mul hppm he
    exact vge_mono (by norm_num) this
  · have he : vge p 0 (ei p i) := vge_ei_zero p i
    have := vge_mul hppm he
    exact vge_mono (by omega) this

theorem vge_Fp (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : vge p 0 (Fp p m) := by
  have h := Fp_sub_one_vge3 p m hp5
  rw [show Fp p m = 1 + (Fp p m - 1) from by ring]
  exact vge_add (vge_one p) (vge_mono (by norm_num) h)

/-! ## The power-sum differences `D_i` -/

/-- `D_i = ∑_{k<C} ((B+k)^i - k^i)` as a rational. -/
noncomputable def DD (B C i : ℕ) : ℚ :=
  ∑ k ∈ range C, (((B : ℚ) + (k : ℚ)) ^ i - (k : ℚ) ^ i)

theorem DD_zero (B C : ℕ) : DD B C 0 = 0 := by
  rw [DD]; simp

theorem DD_one (B C : ℕ) : DD B C 1 = (C : ℚ) * (B : ℚ) := by
  rw [DD]
  have : ∀ k, (((B : ℚ) + (k : ℚ)) ^ 1 - (k : ℚ) ^ 1) = (B : ℚ) := by intro k; ring
  simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem DD_two (B C A : ℕ) (hA : B + C = A) : DD B C 2 = (B : ℚ) * (C : ℚ) * ((A : ℚ) - 1) := by
  rw [DD]
  have e1 : ∀ k, (((B : ℚ) + (k : ℚ)) ^ 2 - (k : ℚ) ^ 2)
      = (B : ℚ) ^ 2 + 2 * (B : ℚ) * (k : ℚ) := by intro k; ring
  simp only [e1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
  have hs2 : (∑ k ∈ range C, (k : ℚ)) * 2 = (C : ℚ) * ((C : ℚ) - 1) := by
    rcases Nat.eq_zero_or_pos C with hC0 | hC1
    · subst hC0; simp
    · have h := Finset.sum_range_id_mul_two C
      have hcast : ((∑ k ∈ range C, k : ℕ) : ℚ) = ∑ k ∈ range C, (k : ℚ) := by push_cast; rfl
      have h2 : (((∑ k ∈ range C, k) * 2 : ℕ) : ℚ) = ((C * (C - 1) : ℕ) : ℚ) := by
        exact_mod_cast h
      rw [Nat.cast_mul, hcast, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub hC1, Nat.cast_one] at h2
      exact h2
  have hAB : (A : ℚ) = (B : ℚ) + (C : ℚ) := by exact_mod_cast hA.symm
  rw [nsmul_eq_mul, hAB]
  have : 2 * (B : ℚ) * (∑ k ∈ range C, (k : ℚ)) = (B : ℚ) * ((∑ k ∈ range C, (k : ℚ)) * 2) := by
    ring
  rw [this, hs2]
  ring

theorem vge_DD (p B C i : ℕ) [Fact p.Prime] (hpB : p ∣ B) (hpC : p ∣ C)
    (hi1 : 1 ≤ i) (hip : i ≤ p - 1) : vge p 2 (DD B C i) := by
  have hcast : DD B C i = (((∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i)) : ℤ) : ℚ) := by
    rw [DD, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k _; push_cast; ring
  rw [hcast]
  have := vge_of_int_dvd (D_dvd p B C i hpB hpC hi1 hip)
  simpa using this

/-! ## The single-block crux: `∑_{k<C}(F(B+k) - F k)` is `≡ 0 mod p^6` -/

theorem crux_identity (p B C : ℕ) (hp1 : 1 ≤ p) :
    (∑ k ∈ range C, (Fp p (B + k) - Fp p k))
      = ∑ i ∈ range p, (p : ℚ) ^ i * ei p i * DD B C i := by
  have key : ∀ k, Fp p (B + k) - Fp p k
      = ∑ i ∈ range p, (p : ℚ) ^ i * ei p i * (((B : ℚ) + (k : ℚ)) ^ i - (k : ℚ) ^ i) := by
    intro k
    rw [F_expand p (B + k) hp1, F_expand p k hp1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; rw [mul_pow, mul_pow]; push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [DD, Finset.mul_sum]

theorem Term12_vge (p B C A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpB : p ∣ B) (hpC : p ∣ C) (hpA : p ∣ A) (hBCA : B + C = A) :
    vge p 6 ((p : ℚ) ^ 1 * ei p 1 * DD B C 1 + (p : ℚ) ^ 2 * ei p 2 * DD B C 2) := by
  have hp := (Fact.out : p.Prime)
  rw [DD_one, DD_two B C A hBCA, ei_one]
  set H1 := Hs p 1
  set H2 := Hs p 2
  set H3 := Hs p 3
  set e2 := ei p 2
  set J := J3 p
  have hpair := pairing p hp5
  have he2 := ei_two p
  have h2T : 2 * ((p : ℚ) ^ 1 * H1 * ((C : ℚ) * (B : ℚ))
        + (p : ℚ) ^ 2 * e2 * ((B : ℚ) * (C : ℚ) * ((A : ℚ) - 1)))
      = (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * ((A : ℚ) - 1) * H1 ^ 2
        - (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * (A : ℚ) * H2
        - (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 3 * H3
        + (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 4 * J := by
    linear_combination ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * ((A : ℚ) - 1)) * he2
      + ((C : ℚ) * (B : ℚ) * (p : ℚ)) * hpair
  have vB : vge p 1 ((B : ℚ)) := vge_nat1 hpB
  have vC : vge p 1 ((C : ℚ)) := vge_nat1 hpC
  have vA : vge p 1 ((A : ℚ)) := vge_nat1 hpA
  have vH1 : vge p 2 H1 := Or.inr (two_le_val_H1 p hp5)
  have vH2 : vge p 1 H2 := Or.inr (one_le_val_H2 p hp5)
  have vH3 : vge p 1 H3 := Or.inr (one_le_val_H3 p hp5)
  have vJ : vge p 0 J := vge_J3 p hp5
  have vAm1 : vge p 0 ((A : ℚ) - 1) := by
    have h := vge_int0 (p := p) ((A : ℤ) - 1)
    simpa using h
  have vp2 : vge p 2 ((p : ℚ) ^ 2) := vge_ppow 2
  have vp3 : vge p 3 ((p : ℚ) ^ 3) := vge_ppow 3
  have vp4 : vge p 4 ((p : ℚ) ^ 4) := vge_ppow 4
  have vH1sq : vge p 4 (H1 ^ 2) := by
    rw [show H1 ^ 2 = H1 * H1 from by ring]; exact vge_mul vH1 vH1
  have T1 : vge p 6 ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * ((A : ℚ) - 1) * H1 ^ 2) :=
    vge_mono (by norm_num) (vge_mul (vge_mul (vge_mul (vge_mul vB vC) vp2) vAm1) vH1sq)
  have T2 : vge p 6 ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * (A : ℚ) * H2) :=
    vge_mono (by norm_num) (vge_mul (vge_mul (vge_mul (vge_mul vB vC) vp2) vA) vH2)
  have T3 : vge p 6 ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 3 * H3) :=
    vge_mono (by norm_num) (vge_mul (vge_mul (vge_mul vB vC) vp3) vH3)
  have T4 : vge p 6 ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 4 * J) :=
    vge_mono (by norm_num) (vge_mul (vge_mul (vge_mul vB vC) vp4) vJ)
  have vRHS : vge p 6 ((B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * ((A : ℚ) - 1) * H1 ^ 2
        - (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 2 * (A : ℚ) * H2
        - (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 3 * H3
        + (B : ℚ) * (C : ℚ) * (p : ℚ) ^ 4 * J) :=
    vge_add (vge_sub (vge_sub T1 T2) T3) T4
  rw [← h2T] at vRHS
  refine vge_cancel_unit (c := (2 : ℚ)) (by norm_num) ?_ vRHS
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by norm_num, padicValRat_nat_eq_zero (by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega)]

theorem crux (p B C A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpB : p ∣ B) (hpC : p ∣ C) (hpA : p ∣ A) (hBCA : B + C = A) :
    vge p 6 (∑ k ∈ range C, (Fp p (B + k) - Fp p k)) := by
  have hp := (Fact.out : p.Prime)
  have hp1 : 1 ≤ p := by omega
  rw [crux_identity p B C hp1,
    ← Finset.sum_filter_add_sum_filter_not (range p) (fun i => i = 1 ∨ i = 2)]
  refine vge_add ?_ ?_
  · have hfilter : ((range p).filter (fun i => i = 1 ∨ i = 2)) = {1, 2} := by
      ext i
      simp only [mem_filter, mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hfilter, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
    exact Term12_vge p B C A hp5 hpB hpC hpA hBCA
  · apply vge_sum
    intro i hi
    rw [mem_filter, mem_range] at hi
    obtain ⟨hilt, hine⟩ := hi
    have hip : i ≤ p - 1 := by omega
    rcases (by omega : i = 0 ∨ i = 3 ∨ 4 ≤ i) with h0 | h3 | h4
    · subst h0; rw [DD_zero, mul_zero]; exact vge_zero p 6
    · subst h3
      have vd : vge p 2 (DD B C 3) := vge_DD p B C 3 hpB hpC (by norm_num) (by omega)
      have ve : vge p 1 (ei p 3) := vge_e3 p hp5
      have vp : vge p 3 ((p : ℚ) ^ 3) := vge_ppow 3
      exact vge_mono (by norm_num) (vge_mul (vge_mul vp ve) vd)
    · have vd : vge p 2 (DD B C i) := vge_DD p B C i hpB hpC (by omega) hip
      have ve : vge p 0 (ei p i) := vge_ei_zero p i
      have vp : vge p (i : ℤ) ((p : ℚ) ^ i) := vge_ppow i
      exact vge_mono (by omega) (vge_mul (vge_mul vp ve) vd)

/-! ## Subset expansion: `∏ F(B+k) - ∏ F k ≡ 0 mod p^6` -/

theorem P1_sub_P0_vge6 (p B C A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpB : p ∣ B) (hpC : p ∣ C) (hpA : p ∣ A) (hBCA : B + C = A) :
    vge p 6 ((∏ k ∈ range C, Fp p (B + k)) - (∏ k ∈ range C, Fp p k)) := by
  have hp := (Fact.out : p.Prime)
  have hexp1 : (∏ k ∈ range C, Fp p (B + k))
      = ∑ T ∈ (range C).powerset, ∏ k ∈ T, (Fp p (B + k) - 1) := by
    rw [← Finset.prod_one_add]; apply Finset.prod_congr rfl; intro k _; ring
  have hexp0 : (∏ k ∈ range C, Fp p k)
      = ∑ T ∈ (range C).powerset, ∏ k ∈ T, (Fp p k - 1) := by
    rw [← Finset.prod_one_add]; apply Finset.prod_congr rfl; intro k _; ring
  rw [hexp1, hexp0, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (range C).powerset (fun T => T.card = 1)]
  refine vge_add ?_ ?_
  · -- card = 1 terms reproduce the crux sum
    have hfilt : ((range C).powerset.filter (fun T => T.card = 1)) = powersetCard 1 (range C) := by
      rw [Finset.powersetCard_eq_filter]
    rw [hfilt, Finset.powersetCard_one, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have hrw : ∀ x, ((∏ k ∈ ({x} : Finset ℕ), (Fp p (B + k) - 1))
          - ∏ k ∈ ({x} : Finset ℕ), (Fp p k - 1)) = Fp p (B + x) - Fp p x := by
      intro x; simp only [Finset.prod_singleton]; ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x)]
    exact crux p B C A hp5 hpB hpC hpA hBCA
  · -- card ≠ 1 terms are each ≡ 0 mod p^6
    apply vge_sum
    intro T hT
    rw [mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    rcases (by omega : T.card = 0 ∨ 2 ≤ T.card) with hc0 | hc2
    · rw [Finset.card_eq_zero] at hc0; subst hc0
      simp only [Finset.prod_empty, sub_self]; exact vge_zero p 6
    · have va : vge p (3 * T.card) (∏ k ∈ T, (Fp p (B + k) - 1)) :=
        vge_prod T _ 3 (fun k _ => Fp_sub_one_vge3 p (B + k) hp5)
      have vb : vge p (3 * T.card) (∏ k ∈ T, (Fp p k - 1)) :=
        vge_prod T _ 3 (fun k _ => Fp_sub_one_vge3 p k hp5)
      have h6 : (6 : ℤ) ≤ 3 * (T.card : ℤ) := by
        have : (2 : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast hc2
        omega
      exact vge_sub (vge_mono h6 va) (vge_mono h6 vb)

/-! ## The single-level (`t = 1`) tower congruence, modulus `p^6` -/

/-- **`t = 1` case.** If `p ≥ 5` is prime, `p ∣ A`, `p ∣ B`, and `B < A`, then
`p^6 ∣ P A - P B · P (A-B)`. -/
theorem P_dvd_p6 (p A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A) (hA : p ∣ A) (hB : p ∣ B) :
    (p : ℤ) ^ 6 ∣
      ((JacobRef.P p A : ℤ) - (JacobRef.P p B : ℤ) * (JacobRef.P p (A - B) : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C := A - B with hC
  have hBC : B + C = A := by rw [hC]; omega
  have hpC : p ∣ C := by rw [hC]; exact Nat.dvd_sub hA hB
  have hp0 : 0 < p := hp.pos
  have hNQ : (((JacobRef.P p A : ℤ) - (JacobRef.P p B : ℤ) * (JacobRef.P p C : ℤ) : ℤ) : ℚ)
      = (uu p) ^ A * (∏ j ∈ range B, Fp p j)
          * ((∏ k ∈ range C, Fp p (B + k)) - (∏ k ∈ range C, Fp p k)) := by
    push_cast
    rw [P_eq p A hp0, P_eq p B hp0, P_eq p C hp0, show A = B + C from hBC.symm,
      Finset.prod_range_add, pow_add]
    ring
  apply int_dvd_of_vge
  rw [hNQ]
  have v1 : vge p 0 ((uu p) ^ A) := vge_pow_zero (vge_uu p) A
  have v2 : vge p 0 (∏ j ∈ range B, Fp p j) := by
    have := vge_prod (range B) (fun j => Fp p j) 0 (fun j _ => vge_Fp p j hp5)
    rwa [zero_mul] at this
  have v3 : vge p 6 ((∏ k ∈ range C, Fp p (B + k)) - (∏ k ∈ range C, Fp p k)) :=
    P1_sub_P0_vge6 p B C A hp5 hB hpC hA hBC
  have := vge_mul (vge_mul v1 v2) v3
  simpa using this

end PTower
