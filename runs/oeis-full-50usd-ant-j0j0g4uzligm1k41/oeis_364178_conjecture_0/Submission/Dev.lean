import FormalConjectures.Util.ProblemImports

open Real
open Nat
open scoped BigOperators

/-!
# Toward the A364178 supercongruence `a(n p^r) ≡ a(n p^{r-1}) (mod p^{3r})`

This file develops verified machinery toward the conjecture in `Spec.lean`.

## Verified results (all depend only on `propext`, `Classical.choice`, `Quot.sound`)
* `Wolst.wolstenholme` : Wolstenholme's theorem `∑_{k=1}^{p-1} k⁻¹ ≡ 0 (mod p²)`, `p ≥ 5`.
* `Wolst.block_prod`   : the block-product congruence `∏_{j=1}^{p-1}(t p + j) ≡ (p-1)! (mod p³)`.
* `Wolst.fact_factor`  : `(p k)! = p^k · k! · ∏_{t<k} ∏_{j=1}^{p-1}(t p + j)`.
* `Wolst.kazandzidis_p3` : the **Kazandzidis / Ljunggren congruence**
    `C(p n, p m) ≡ C(n, m) (mod p³)` for `p ≥ 5`.
* `Wolst.block_reflect` : the reflected block identity
    `∏_{j=1}^{p-1}(t p + j) = ∏_{j=1}^{(p-1)/2}(j(p-j) + p² t(t+1))`.
* `Wolst.W1_sum_zero` : the reflected-form Wolstenholme vanishing
    `∑_{j=1}^{(p-1)/2} (j(p-j))⁻¹ ≡ 0 (mod p)`.
* `Wolst.sum_tri`, `Wolst.D1_identity`, `Wolst.sum_tri_split` : `3∑_{t<n} t(t+1) = n³-n`
    and the order-1 difference `∑_{t<n} - ∑_{t<m} - ∑_{t<n-m} = n·m·(n-m)`.
* `Wolst.block_prod_p4`, `Wolst.W_pow_congr_p4` : the refined block / `W_k` products `(mod p⁴)`,
    `∏(t p+j) ≡ (p-1)!·(1 + p² t(t+1)·∑(j(p-j))⁻¹)` and its `k`-fold product.
* `Wolst.kazandzidis_p4` : the **sharp Kazandzidis congruence one order further**,
    `C(p n, p m) ≡ C(n, m) (mod p⁴)` whenever `p ∣ n·m·(n-m)` (`p ≥ 5`).
    This realises the order-by-order mechanism of Step 2 below concretely: the `mod p³`
    part is unconditional (`kazandzidis_p3`) and the fourth order vanishes exactly because
    `W1_sum_zero` contributes a factor `p` on top of the `nm(n-m)` factor of `D1_identity`.

## Full proof strategy (established; formalization beyond current resource budget)
1. Even case `N = 2M`: `a(2M)` is the product of binomials
   `C(27M,12M)·C(15M,10M)·C(5M,3M) / (C(27M,20M)·C(7M,6M))` (verified numerically).
   The supercongruence then reduces to the *sharp* Kazandzidis congruence
   `C(p^r A, p^r B) ≡ C(p^{r-1}A, p^{r-1}B) (mod p^{3r})`, one factor at a time.
2. Sharp Kazandzidis via the **reflected form**
   `∏_{j=1}^{p-1}(1 + t p / j) = ∏_{j=1}^{(p-1)/2}(1 + p² t(t+1)/(j(p-j)))`:
   writing `log R = Σ_k (-1)^{k-1}/k · p^{2k} W_k · D_k(n,m)` with
   `D_k(n,m) = F_k(n) - F_k(m) - F_k(n-m)`, one shows (as *polynomial* identities)
   `nm(n-m) ∣ D_k` for all `k`, `D_1 = nm(n-m)`, and `W_1 = Σ 1/(j(p-j)) ≡ 0 (mod p)`.
   Hence every order `k` already has valuation `≥ 3 + v_p(nm(n-m))` — no
   cross-order (κ = 0) cancellation is needed. This is the key insight that makes
   the integer case tractable; it requires a p-adic logarithm for 1-units
   (not in Mathlib) plus Faulhaber closed forms.
3. Odd case `N = 2M+1`: `a(2M+1) = 2^{4M+2}·I(M)` carries an irreducible power of `2`,
   so it is NOT a product of ordinary binomials and genuinely requires Morita's
   p-adic Gamma function with its Gauss–Legendre multiplication formula.

Steps 2–3 (p-adic log + p-adic Gamma + the Γ→factorial reduction) constitute a
research-scale formalization exceeding the available budget.
-/

namespace Wolst

/-- Sum of `x^i` over all of `ZMod p` is `0` when `0 < i < p-1`. -/
theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] (i : ℕ) (h : i < p - 1) :
    ∑ x : ZMod p, x ^ i = 0 := by
  have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i
  rw [ZMod.card] at this
  exact this h

/-- Sum of squares of inverses over units of `ZMod p` is `0` for `p ≥ 5`. -/
theorem sum_inv_sq_zmod (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ ^ 2 = 0 := by
  -- reindex by inverse: sum of x^{-2} = sum of x^2
  have hb : ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ ^ 2 = ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ 2 := by
    rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ) (fun u => ((u : ZMod p)) ^ 2)]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
  rw [hb]
  -- sum of x^2 over units = sum over all - 0
  have : ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ 2 = ∑ x : ZMod p, x ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨(Units.val : (ZMod p)ˣ → ZMod p), Units.val_injective⟩))]
    · rw [Finset.sum_map]; rfl
    · intro x _ hx
      simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and] at hx
      have : ¬ IsUnit x := fun hu => hx ⟨hu.unit, rfl⟩
      have : x = 0 := by
        rcases eq_or_ne x 0 with h | h
        · exact h
        · exact absurd (isUnit_iff_ne_zero.mpr h) this
      simp [this]
  rw [this]
  exact sum_pow_zmod p 2 (by omega)

/-- The reduction ring hom `ZMod (p^2) → ZMod p`. -/
noncomputable def red (p : ℕ) : ZMod (p^2) →+* ZMod p :=
  ZMod.castHom (by exact dvd_pow_self p (by norm_num)) (ZMod p)

/-- `p * x = 0` in `ZMod (p^2)` iff `red x = 0`. -/
theorem p_mul_eq_zero_iff (p : ℕ) [hp : Fact p.Prime] (x : ZMod (p^2)) :
    (p : ZMod (p^2)) * x = 0 ↔ red p x = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hp0 : 0 < p := hp.out.pos
  have hx : ((x.val : ℕ) : ZMod (p^2)) = x := ZMod.natCast_rightInverse x
  constructor
  · intro h
    rw [red, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]
    rw [← hx, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    -- p^2 ∣ p * x.val  →  p ∣ x.val
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h2 : p * x.val = p * (p * c) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 h2
  · intro h
    rw [red, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    rw [← hx, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rcases h with ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

/-- For `1 ≤ k < p`, `(k : ZMod (p^2))` is a unit. -/
theorem isUnit_cast_of_lt (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) :
    IsUnit (k : ZMod (p^2)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (by
    intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))

/-- In `ZMod n`, for a unit `u`, if `u * v = 1` then `v = u⁻¹`. -/
theorem zmod_eq_inv_of_mul_eq_one {n : ℕ} {u v : ZMod n} (hu : IsUnit u) (h : u * v = 1) :
    v = u⁻¹ := by
  calc v = (u⁻¹ * u) * v := by rw [ZMod.inv_mul_of_unit u hu, one_mul]
    _ = u⁻¹ * (u * v) := by ring
    _ = u⁻¹ := by rw [h, mul_one]

/-- Product of inverses of units. -/
theorem zmod_mul_inv_units {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (hb : IsUnit b) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  symm
  apply zmod_eq_inv_of_mul_eq_one (ha.mul hb)
  calc a * b * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit a ha, ZMod.mul_inv_of_unit b hb, one_mul]

/-- Sum of two inverses of units. -/
theorem zmod_add_inv_units {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  rw [zmod_mul_inv_units ha hb]
  have h1 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by
    rw [← mul_assoc, ZMod.mul_inv_of_unit a ha, one_mul]
  have h2 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    rw [mul_comm a⁻¹ b⁻¹, ← mul_assoc, ZMod.mul_inv_of_unit b hb, one_mul]
  rw [add_mul, h1, h2, add_comm]

/-- Sum of squares of inverses over all of `ZMod p` is 0 (p ≥ 5). -/
theorem sum_inv_sq_field (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ x : ZMod p, (x⁻¹)^2 = 0 := by
  rw [show (∑ x : ZMod p, (x⁻¹)^2) = ∑ x : ZMod p, x^2 from
      Equiv.sum_comp (⟨fun x => x⁻¹, fun x => x⁻¹, inv_inv, inv_inv⟩ : ZMod p ≃ ZMod p)
        (fun x => x^2)]
  exact sum_pow_zmod p 2 (by omega)

/-- Sum of squares of inverses over `Ico 1 p` in `ZMod p` is 0 (p ≥ 5). -/
theorem sum_inv_sq_Ico (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹)^2 = 0 := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 p) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [show (∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹)^2)
      = ∑ x ∈ (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)), (x⁻¹)^2 from
      (Finset.sum_image (f := fun x : ZMod p => x⁻¹^2) hinj).symm]
  have himg : (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      rw [ZMod.natCast_eq_zero_iff]
      intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro hx
      have hval : x.val ≠ 0 := fun h => hx (by rw [← ZMod.natCast_rightInverse x, h]; simp)
      exact ⟨x.val, ⟨by omega, ZMod.val_lt x⟩, ZMod.natCast_rightInverse x⟩
  rw [himg, Finset.sum_sdiff_eq_sub (by simp)]
  simp only [Finset.sum_singleton, inv_zero]
  rw [sum_inv_sq_field p h5]; simp

/-- The reduction hom preserves the inverse of a unit. -/
theorem red_inv (p : ℕ) [hp : Fact p.Prime] {x : ZMod (p^2)} (hx : IsUnit x) :
    red p x⁻¹ = (red p x)⁻¹ := by
  apply zmod_eq_inv_of_mul_eq_one (hx.map (red p))
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

/-- Reflection: sum over `Ico 1 p` of `f k` equals sum of `f (p-k)`. -/
theorem sum_Ico_reflect {M : Type*} [AddCommMonoid M] (p : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.Ico 1 p, f k = ∑ k ∈ Finset.Ico 1 p, f (p - k) := by
  apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
  · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk; congr 1; omega

/-- Wolstenholme's theorem: `∑_{k=1}^{p-1} k⁻¹ = 0` in `ZMod (p^2)` for `p ≥ 5`. -/
theorem wolstenholme (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p^2)))⁻¹ = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hu2 : IsUnit (2 : ZMod (p^2)) := by
    have h := isUnit_cast_of_lt p 2 (by omega) (by omega)
    simpa using h
  set S : ZMod (p^2) := ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p^2)))⁻¹ with hS
  suffices h2 : (2 : ZMod (p^2)) * S = 0 by
    have hs : S = 2⁻¹ * ((2:ZMod (p^2)) * S) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit 2 hu2, one_mul]
    rw [hs, h2, mul_zero]
  have hSref : S = ∑ k ∈ Finset.Ico 1 p, (((p - k : ℕ)) : ZMod (p^2))⁻¹ := by
    rw [hS]; exact sum_Ico_reflect p (fun k => ((k : ZMod (p^2)))⁻¹)
  have hpair : (2 : ZMod (p^2)) * S
      = (p : ZMod (p^2)) * ∑ k ∈ Finset.Ico 1 p,
          ((k : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2)))⁻¹ := by
    rw [two_mul]
    nth_rewrite 2 [hSref]
    rw [hS, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have huk : IsUnit (k : ZMod (p^2)) := isUnit_cast_of_lt p k hk.1 hk.2
    have hupk : IsUnit (((p - k : ℕ)) : ZMod (p^2)) := isUnit_cast_of_lt p (p-k) (by omega) (by omega)
    rw [zmod_add_inv_units huk hupk]
    congr 1
    rw [← Nat.cast_add]; congr 1; omega
  rw [hpair, p_mul_eq_zero_iff, map_sum]
  have hterm : ∀ k ∈ Finset.Ico 1 p,
      red p ((k : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2)))⁻¹ = -(((k : ZMod p))⁻¹)^2 := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have huk : IsUnit (k : ZMod (p^2)) := isUnit_cast_of_lt p k hk.1 hk.2
    have hupk : IsUnit (((p - k : ℕ)) : ZMod (p^2)) := isUnit_cast_of_lt p (p-k) (by omega) (by omega)
    rw [red_inv p (huk.mul hupk), map_mul, map_natCast, map_natCast]
    have hpk : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hpk, mul_neg, inv_neg, mul_inv_rev, ← sq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sum_inv_sq_Ico p h5, neg_zero]

/-- reduction hom `ZMod (p^b) →+* ZMod (p^a)` for `a ≤ b`. -/
noncomputable def redp (p a b : ℕ) (h : a ≤ b) : ZMod (p^b) →+* ZMod (p^a) :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p^a))

/-- `p^k * x = 0` in `ZMod (p^m)` (with `k ≤ m`) iff `p^(m-k) ∣ x.val`. -/
theorem pk_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (m k : ℕ) (hkm : k ≤ m)
    (x : ZMod (p^m)) :
    (p^k : ZMod (p^m)) * x = 0 ↔ (p^(m-k) : ℕ) ∣ x.val := by
  haveI : NeZero (p^m) := ⟨pow_ne_zero m hp.out.ne_zero⟩
  have hp0 : 0 < p := hp.out.pos
  have hx : ((x.val : ℕ) : ZMod (p^m)) = x := ZMod.natCast_rightInverse x
  have hcast : ((p^k : ℕ) : ZMod (p^m)) = (p^k : ZMod (p^m)) := by push_cast; ring
  have hmk : k + (m - k) = m := by omega
  rw [← hcast]
  constructor
  · intro h
    rw [← hx, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have key : p^k * x.val = p^k * (p^(m-k) * c) := by
      rw [hc, ← mul_assoc, ← pow_add, hmk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 k) key
  · intro h
    rw [← hx, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc, ← mul_assoc, ← pow_add, hmk]

/-- If casting `x : ZMod (p^m)` to `ZMod (p^a)` gives `0`, then `p^a ∣ x.val`. -/
theorem cast_eq_zero_iff_dvd (p : ℕ) [hp : Fact p.Prime] (m a : ℕ) (ha : a ≤ m)
    (x : ZMod (p^m)) :
    redp p a m ha x = 0 ↔ (p^a : ℕ) ∣ x.val := by
  rw [redp, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]

/-- Expansion of `∏ (1 + c * w i)` over `range n` when `c^3 = 0`: only the
    zeroth, first and second order terms survive. -/
theorem prod_one_add_mul_cube {R : Type*} [CommRing R] (c : R) (hc : c^3 = 0)
    (w : ℕ → R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + c * w i)
      = 1 + c * (∑ i ∈ Finset.range n, w i)
          + c^2 * (∑ i ∈ Finset.range n, w i * (∑ j ∈ Finset.range i, w j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination
      (w n * (∑ i ∈ Finset.range n, w i * ∑ j ∈ Finset.range i, w j)) * hc

/-- `IsUnit (k : ZMod (p^m))` for `1 ≤ k < p`. -/
theorem isUnit_castm (p m : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) :
    IsUnit ((k : ℕ) : ZMod (p^m)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
    (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))

/-- The reduction hom preserves the inverse of a unit (general power version). -/
theorem redp_inv (p a b : ℕ) [hp : Fact p.Prime] (hab : a ≤ b) {x : ZMod (p^b)}
    (hx : IsUnit x) : redp p a b hab x⁻¹ = (redp p a b hab x)⁻¹ := by
  apply zmod_eq_inv_of_mul_eq_one (hx.map (redp p a b hab))
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

/-- Sum of inverses over `Ico 1 p` in `ZMod p` is `0` for `p ≥ 5`. -/
theorem sum_inv_Ico (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹) = 0 := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 p) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [show (∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹))
      = ∑ x ∈ (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)), x⁻¹ from
      (Finset.sum_image (f := fun x : ZMod p => x⁻¹) hinj).symm]
  have himg : (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      rw [ZMod.natCast_eq_zero_iff]
      intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro hx
      have hval : x.val ≠ 0 := fun h => hx (by rw [← ZMod.natCast_rightInverse x, h]; simp)
      exact ⟨x.val, ⟨by omega, ZMod.val_lt x⟩, ZMod.natCast_rightInverse x⟩
  rw [himg, Finset.sum_sdiff_eq_sub (by simp)]
  simp only [Finset.sum_singleton, inv_zero]
  have heq : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Equiv.sum_comp (⟨fun x => x⁻¹, fun x => x⁻¹, inv_inv, inv_inv⟩ : ZMod p ≃ ZMod p) (fun x => x)
  rw [heq, sub_zero]
  have := sum_pow_zmod p 1 (by omega)
  simpa using this

/-- Triangular sum identity: `2 * ∑ᵢ bᵢ (∑_{j<i} bⱼ) = (∑ b)² - ∑ b²`. -/
theorem tri_sum {R : Type*} [CommRing R] (b : ℕ → R) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, b i * (∑ j ∈ Finset.range i, b j))
      = (∑ i ∈ Finset.range n, b i)^2 - ∑ i ∈ Finset.range n, (b i)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (f := fun i => b i * ∑ j ∈ Finset.range i, b j),
        Finset.sum_range_succ (f := b), Finset.sum_range_succ (f := fun i => (b i)^2)]
    linear_combination ih

/-- Base-case block product: `∏_{j=1}^{p-1} (t·p + j) ≡ (p-1)! (mod p³)` for `p ≥ 5`. -/
theorem block_prod (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (t : ℕ) :
    ∏ j ∈ Finset.Ico 1 p, ((t*p + j : ℕ) : ZMod (p^3))
      = ((Nat.factorial (p-1) : ℕ) : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.out.ne_zero⟩
  set c : ZMod (p^3) := ((t*p : ℕ) : ZMod (p^3)) with hc_def
  -- c^3 = 0
  have hc3 : c^3 = 0 := by
    rw [hc_def, ← Nat.cast_pow]
    have : (t*p)^3 = (t^3) * p^3 := by ring
    rw [this, Nat.cast_mul]
    have : ((p^3 : ℕ) : ZMod (p^3)) = 0 := by
      rw [ZMod.natCast_self]
    rw [this, mul_zero]
  -- factor each term:  t*p + j = j * (1 + c * j⁻¹)
  have hstep : ∀ j ∈ Finset.Ico 1 p, ((t*p + j : ℕ) : ZMod (p^3))
      = (j : ZMod (p^3)) * (1 + c * ((j : ZMod (p^3)))⁻¹) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hu : IsUnit ((j:ℕ) : ZMod (p^3)) := isUnit_castm p 3 j hj.1 hj.2
    rw [mul_add, mul_one, ← mul_assoc, mul_comm ((j:ZMod (p^3))) c, mul_assoc,
      ZMod.mul_inv_of_unit _ hu, mul_one, hc_def]
    push_cast; ring
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib]
  -- ∏ j = (p-1)!
  have hfac : ∏ j ∈ Finset.Ico 1 p, ((j:ℕ) : ZMod (p^3)) = ((Nat.factorial (p-1):ℕ) : ZMod (p^3)) := by
    rw [← Nat.cast_prod]
    congr 1
    have hnat : ∏ j ∈ Finset.Ico 1 p, j = (p-1)! := by
      have := Finset.prod_Ico_id_eq_factorial (p-1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)] at this
    exact hnat
  rw [hfac]
  -- reduce to showing the second product = 1
  suffices hone : ∏ j ∈ Finset.Ico 1 p, (1 + c * ((j : ZMod (p^3)))⁻¹) = 1 by
    rw [hone, mul_one]
  -- reindex to range and expand
  rw [Finset.prod_Ico_eq_prod_range]
  rw [prod_one_add_mul_cube c hc3 (fun i => (((1+i : ℕ)) : ZMod (p^3))⁻¹) (p-1)]
  -- c = ↑t * ↑p
  have hcfact : c = ((t : ℕ) : ZMod (p^3)) * (p : ZMod (p^3)) := by
    rw [hc_def]; push_cast; ring
  -- the linear term:  c * S = 0  where S = ∑ j⁻¹ over range (p-1)
  have hlin : c * (∑ i ∈ Finset.range (p-1), (((1+i : ℕ)) : ZMod (p^3))⁻¹) = 0 := by
    set S : ZMod (p^3) := ∑ i ∈ Finset.range (p-1), (((1+i : ℕ)) : ZMod (p^3))⁻¹ with hS
    have hSval : (p^2 : ℕ) ∣ S.val := by
      rw [← cast_eq_zero_iff_dvd p 3 2 (by norm_num) S, hS, map_sum]
      have hcong : ∀ i ∈ Finset.range (p-1),
          redp p 2 3 (by norm_num) (((1+i : ℕ)) : ZMod (p^3))⁻¹
            = (((1+i : ℕ)) : ZMod (p^2))⁻¹ := by
        intro i hi
        have hu : IsUnit (((1+i:ℕ)) : ZMod (p^3)) :=
          isUnit_castm p 3 (1+i) (by omega) (by simp only [Finset.mem_range] at hi; omega)
        rw [redp_inv p 2 3 _ hu, map_natCast]
      rw [Finset.sum_congr rfl hcong]
      have hw := wolstenholme p h5
      rw [Finset.sum_Ico_eq_sum_range] at hw
      exact hw
    rw [hcfact, mul_assoc,
        show (p : ZMod (p^3)) * S = (p^1 : ZMod (p^3)) * S by norm_num,
        (pk_mul_eq_zero p 3 1 (by norm_num) S).mpr (by simpa using hSval), mul_zero]
  -- the quadratic term:  c² * B = 0  where B = ∑ᵢ wᵢ ∑_{j<i} wⱼ
  have hquad : c^2 * (∑ i ∈ Finset.range (p-1),
      (((1+i : ℕ)) : ZMod (p^3))⁻¹ * (∑ j ∈ Finset.range i, (((1+j : ℕ)) : ZMod (p^3))⁻¹)) = 0 := by
    set B : ZMod (p^3) := ∑ i ∈ Finset.range (p-1),
      (((1+i : ℕ)) : ZMod (p^3))⁻¹ * (∑ j ∈ Finset.range i, (((1+j : ℕ)) : ZMod (p^3))⁻¹) with hB
    have hBval : (p : ℕ) ∣ B.val := by
      have hp3 : p ∣ p^3 := dvd_pow_self p (by norm_num)
      set red1 : ZMod (p^3) →+* ZMod p := ZMod.castHom hp3 (ZMod p) with hred1
      have red1_inv : ∀ {x : ZMod (p^3)}, IsUnit x → red1 x⁻¹ = (red1 x)⁻¹ := by
        intro x hx
        apply zmod_eq_inv_of_mul_eq_one (hx.map red1)
        rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
      rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_val]
      show red1 B = 0
      -- reduce B into ZMod p and show it is 0 via the triangular-sum identity
      have hred : red1 B
          = ∑ i ∈ Finset.range (p-1),
              (((1+i:ℕ)):ZMod p)⁻¹ * (∑ j ∈ Finset.range i, (((1+j:ℕ)):ZMod p)⁻¹) := by
        rw [hB, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul, map_sum]
        have hui : IsUnit (((1+i:ℕ)) : ZMod (p^3)) :=
          isUnit_castm p 3 (1+i) (by omega) (by simp only [Finset.mem_range] at hi; omega)
        rw [red1_inv hui, hred1, ZMod.castHom_apply, ZMod.cast_natCast hp3]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have huj : IsUnit (((1+j:ℕ)) : ZMod (p^3)) :=
          isUnit_castm p 3 (1+j) (by omega)
            (by simp only [Finset.mem_range] at hi hj; omega)
        rw [red1_inv huj, hred1, ZMod.castHom_apply, ZMod.cast_natCast hp3]
      rw [hred]
      -- use 2 * (that) = (∑ b)² - ∑ b² = 0, and 2 is a unit
      have h2 := tri_sum (fun i => (((1+i:ℕ)):ZMod p)⁻¹) (p-1)
      have hsum0 : ∑ i ∈ Finset.range (p-1), (fun i => (((1+i:ℕ)):ZMod p)⁻¹) i = 0 := by
        have hw := sum_inv_Ico p h5
        rw [Finset.sum_Ico_eq_sum_range] at hw
        simpa using hw
      have hsq0 : ∑ i ∈ Finset.range (p-1), ((fun i => (((1+i:ℕ)):ZMod p)⁻¹) i)^2 = 0 := by
        have hw := sum_inv_sq_Ico p h5
        rw [Finset.sum_Ico_eq_sum_range] at hw
        simpa using hw
      rw [hsum0, hsq0, zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero] at h2
      have h2ne : (2 : ZMod p) ≠ 0 := by
        have h2c : ((2:ℕ):ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro h; exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        simpa using h2c
      exact (mul_eq_zero.mp h2).resolve_left h2ne
    have hc2 : c^2 = ((t^2 : ℕ) : ZMod (p^3)) * (p^2 : ZMod (p^3)) := by
      rw [hcfact]; push_cast; ring
    rw [hc2, mul_assoc,
        (pk_mul_eq_zero p 3 2 (by norm_num) B).mpr (by simpa using hBval), mul_zero]
  rw [hlin, hquad, add_zero, add_zero]

/-- Factorial factorization: `(p·k)! = p^k · k! · ∏_{t<k} ∏_{j=1}^{p-1}(tp+j)`. -/
theorem fact_factor (p : ℕ) (hp0 : 0 < p) (k : ℕ) :
    (p * k)! = p^k * k ! * ∏ t ∈ Finset.range k, ∏ j ∈ Finset.Ico 1 p, (t*p + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hAF : (p*k + 1).ascFactorial p
        = (∏ j ∈ Finset.Ico 1 p, (k*p + j)) * (p*(k+1)) := by
      have hpp : Nat.succ (p-1) = p := by omega
      have hrec := Nat.ascFactorial_succ (n := p*k+1) (k := p-1)
      rw [hpp] at hrec
      rw [hrec, Nat.ascFactorial_eq_prod_range, Finset.prod_Ico_eq_prod_range]
      have h1 : p*k + 1 + (p-1) = p*(k+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [h1, mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i _; ring
    calc (p * (k+1))! = (p*k + p)! := by ring_nf
      _ = (p*k)! * (p*k + 1).ascFactorial p := (Nat.factorial_mul_ascFactorial (p*k) p).symm
      _ = (p^k * k ! * ∏ t ∈ Finset.range k, ∏ j ∈ Finset.Ico 1 p, (t*p + j))
            * ((∏ j ∈ Finset.Ico 1 p, (k*p + j)) * (p*(k+1))) := by rw [ih, hAF]
      _ = p^(k+1) * (k+1) ! * ∏ t ∈ Finset.range (k+1), ∏ j ∈ Finset.Ico 1 p, (t*p + j) := by
            rw [Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
            ring

/-- The block-product `W_k := ∏_{t<k} ∏_{j=1}^{p-1}(tp+j)` is `≡ (p-1)!^k (mod p³)`. -/
theorem W_pow_congr (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (k : ℕ) :
    ((∏ t ∈ Finset.range k, ∏ j ∈ Finset.Ico 1 p, (t*p + j) : ℕ) : ZMod (p^3))
      = ((Nat.factorial (p-1) : ℕ) : ZMod (p^3))^k := by
  rw [Nat.cast_prod]
  rw [show ((Nat.factorial (p-1) : ℕ) : ZMod (p^3))^k
      = ∏ _t ∈ Finset.range k, ((Nat.factorial (p-1) : ℕ) : ZMod (p^3)) by
      rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_congr rfl
  intro t _
  rw [Nat.cast_prod]
  exact block_prod p h5 t

/-- **Reflected form of the block product** (a clean ℕ identity):
    `∏_{j=1}^{p-1}(t p + j) = ∏_{j=1}^{(p-1)/2} (j(p-j) + p²·t(t+1))`.
    Pairing `j ↔ p-j` turns each pair `(tp+j)(tp+p-j)` into `j(p-j) + p² t(t+1)`.
    This is the key structural identity behind the sharp Kazandzidis congruence:
    it exhibits an explicit factor of `p²`, and (over `ZMod p`) `∑ 1/(j(p-j)) ≡ 0`. -/
theorem block_reflect (p : ℕ) (hp3 : 3 ≤ p) (hodd : Odd p) (t : ℕ) :
    ∏ j ∈ Finset.Ico 1 p, (t*p + j)
      = ∏ j ∈ Finset.Ico 1 ((p+1)/2), (j*(p-j) + p^2*(t*(t+1))) := by
  have hb1 : 1 ≤ (p+1)/2 := by omega
  have hb2 : (p+1)/2 ≤ p := by omega
  have hsplit : Finset.Ico 1 p
      = Finset.Ico 1 ((p+1)/2) ∪ Finset.Ico ((p+1)/2) p :=
    (Finset.Ico_union_Ico_eq_Ico hb1 hb2).symm
  rw [hsplit, Finset.prod_union (Finset.Ico_disjoint_Ico_consecutive 1 ((p+1)/2) p)]
  have href : ∏ j ∈ Finset.Ico ((p+1)/2) p, (t*p + j)
      = ∏ j ∈ Finset.Ico 1 ((p+1)/2), (t*p + (p - j)) := by
    apply Finset.prod_nbij' (fun j => p - j) (fun j => p - j)
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢
      rcases hodd with ⟨w, hw⟩; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢
      rcases hodd with ⟨w, hw⟩; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
  rw [href, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hjp : j ≤ p := by omega
  zify [hjp]
  ring

/-- **Reflected-form Wolstenholme vanishing:** `∑_{j=1}^{(p-1)/2} (j(p-j))⁻¹ = 0` in `ZMod p`
    (`p ≥ 5`, `p` odd).  Each term equals `-(j⁻¹)²` (since `p-j = -j`), and the half–sum of
    squares of inverses is `0` because the full sum (`sum_inv_sq_Ico`) is `0 = 2·(half)`.
    This is the vanishing that promotes the explicit `p²` in the reflected block product to `p³`,
    i.e. the mechanism behind the *sharp* Kazandzidis exponent `3 + v_p(nm(n-m))`. -/
theorem W1_sum_zero (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (hodd : Odd p) :
    ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod p))⁻¹ = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set H := ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j:ZMod p))⁻¹)^2 with hH
  -- each term equals `-(j⁻¹)²`
  have hterm : ∀ j ∈ Finset.Ico 1 ((p+1)/2),
      (((j*(p-j) : ℕ) : ZMod p))⁻¹ = -(((j:ZMod p))⁻¹)^2 := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [Nat.cast_mul, mul_inv_rev]
    have hpk : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hpk, inv_neg, sq]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← hH, neg_eq_zero]
  -- full sum of squares of inverses splits as `H + H`
  have hb1 : 1 ≤ (p+1)/2 := by omega
  have hb2 : (p+1)/2 ≤ p := by omega
  have hsplit : Finset.Ico 1 p = Finset.Ico 1 ((p+1)/2) ∪ Finset.Ico ((p+1)/2) p :=
    (Finset.Ico_union_Ico_eq_Ico hb1 hb2).symm
  have hfull : ∑ j ∈ Finset.Ico 1 p, (((j:ZMod p))⁻¹)^2 = H + H := by
    rw [hsplit, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 ((p+1)/2) p)]
    congr 1
    rw [show (∑ j ∈ Finset.Ico ((p+1)/2) p, (((j:ZMod p))⁻¹)^2)
        = ∑ j ∈ Finset.Ico 1 ((p+1)/2), ((((p-j):ℕ):ZMod p)⁻¹)^2 from ?_]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hpk : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [hpk, inv_neg, neg_sq]
    · apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; rcases hodd with ⟨w,hw⟩; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; rcases hodd with ⟨w,hw⟩; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj
        rw [Nat.sub_sub_self (le_of_lt hj.2)]
  rw [sum_inv_sq_Ico p h5] at hfull
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2; omega
  have h2H : (2 : ZMod p) * H = 0 := by rw [two_mul, ← hfull]
  rcases mul_eq_zero.mp h2H with h | h
  · exact absurd h h20
  · exact h

/-- Faulhaber-type identity: `3·∑_{t<n} t(t+1) = n³ - n` (over `ℤ`). -/
theorem sum_tri (n : ℕ) : 3 * ∑ t ∈ Finset.range n, ((t:ℤ)*(t+1)) = (n:ℤ)^3 - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The order-1 difference `D₁(n,m) = ∑_{t<n} - ∑_{t<m} - ∑_{t<n-m}` of `t(t+1)` equals
    `n·m·(n-m)` (over `ℤ`, `m ≤ n`).  Together with `W1_sum_zero` (which contributes an extra
    factor `p` on top of the explicit `p²` in `block_reflect`) this is what yields the *sharp*
    Kazandzidis exponent `3 + v_p(n·m·(n-m))`, i.e. `p^{3r}` after iterating with
    `n = A·p^{r-1}`, `m = B·p^{r-1}`. -/
theorem D1_identity (n m : ℕ) (hmn : m ≤ n) :
    (∑ t ∈ Finset.range n, ((t:ℤ)*(t+1)))
      - (∑ t ∈ Finset.range m, ((t:ℤ)*(t+1)))
      - (∑ t ∈ Finset.range (n-m), ((t:ℤ)*(t+1)))
      = (n:ℤ) * m * ((n:ℤ) - m) := by
  have h3 : (3:ℤ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h3
  rw [mul_sub, mul_sub, sum_tri, sum_tri, sum_tri]
  have hc : ((n - m : ℕ) : ℤ) = (n:ℤ) - m := by rw [Nat.cast_sub hmn]
  rw [hc]; ring

/-- If all pairwise products `cᵢ·cⱼ` vanish (in particular each `cᵢ²=0`), then
    `∏(1+cᵢ) = 1 + ∑cᵢ`. -/
theorem prod_one_add_of_sq_zero {ι R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι) (c : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, c i * c j = 0) :
    ∏ i ∈ s, (1 + c i) = 1 + ∑ i ∈ s, c i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have hca : c a * ∑ i ∈ s, c i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
    linear_combination hca

/-- **Refined block product `(mod p⁴)`:** using the reflected form, with an explicit `p²` term,
    `∏_{j=1}^{p-1}(tp+j) ≡ (p-1)! · (1 + p²t(t+1)·∑_{j=1}^{(p-1)/2}(j(p-j))⁻¹) (mod p⁴)`.
    Combined with `W1_sum_zero` (the reflected sum `≡ 0 (mod p)`) this shows the correction is
    `≡ 0 (mod p³)`, and carries the extra `nm(n-m)` factor for the sharp exponent. -/
theorem block_prod_p4 (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (t : ℕ) :
    ((∏ j ∈ Finset.Ico 1 p, (t*p + j) : ℕ) : ZMod (p^4))
      = ((Nat.factorial (p-1) : ℕ) : ZMod (p^4))
        * (1 + ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4))
              * ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹) := by
  have hp3 : 3 ≤ p := by omega
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  set K : ZMod (p^4) := ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4)) with hK
  -- Kn² = 0 in ZMod(p⁴)
  have hK2 : K * K = 0 := by
    rw [hK, ← Nat.cast_mul]
    have hdvd : p^4 ∣ (p^2*(t*(t+1))) * (p^2*(t*(t+1))) := ⟨(t*(t+1))^2, by ring⟩
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  -- ∏_{j=1}^{(p-1)/2} j(p-j) = (p-1)!
  have hpp : ∏ j ∈ Finset.Ico 1 ((p+1)/2), (j*(p-j)) = (p-1)! := by
    have h0 := block_reflect p hp3 hodd 0
    simp only [zero_mul, mul_zero, zero_add, add_zero] at h0
    have hfp : ∏ j ∈ Finset.Ico 1 p, j = (p-1)! := by
      rcases Nat.exists_eq_succ_of_ne_zero (show p ≠ 0 by omega) with ⟨q, rfl⟩
      rw [Finset.prod_Ico_id_eq_factorial, Nat.succ_sub_one]
    rw [hfp] at h0
    exact h0.symm
  -- reflected form and per-term factoring
  rw [block_reflect p hp3 hodd t, Nat.cast_prod]
  have hfac : ∀ j ∈ Finset.Ico 1 ((p+1)/2),
      ((j*(p-j) + p^2*(t*(t+1)) : ℕ) : ZMod (p^4))
        = ((j*(p-j) : ℕ) : ZMod (p^4)) * (1 + K * (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hu : IsUnit (((j*(p-j) : ℕ) : ZMod (p^4))) := by
      rw [Nat.cast_mul]
      refine (isUnit_castm p 4 j (by omega) (by omega)).mul (isUnit_castm p 4 (p-j) (by omega) (by omega))
    set u : ZMod (p^4) := ((j*(p-j) : ℕ) : ZMod (p^4)) with hu'
    have huinv : u * u⁻¹ = 1 := ZMod.mul_inv_of_unit u hu
    rw [Nat.cast_add, hK]
    calc u + ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4))
        = u + ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4)) * (u * u⁻¹) := by rw [huinv, mul_one]
      _ = u * (1 + ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4)) * u⁻¹) := by ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  rw [prod_one_add_of_sq_zero (Finset.Ico 1 ((p+1)/2))
        (fun j => K * (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹)
        (by intro i _ j _
            calc (K * (((i*(p-i) : ℕ) : ZMod (p^4)))⁻¹) * (K * (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹)
                = (K*K) * ((((i*(p-i) : ℕ) : ZMod (p^4)))⁻¹ * (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹) := by ring
              _ = 0 := by rw [hK2, zero_mul])]
  rw [← Nat.cast_prod, hpp, Finset.mul_sum]

/-- **Kazandzidis / Ljunggren congruence (r = 1):** for `p ≥ 5` and `m ≤ n`,
    `C(pn, pm) ≡ C(n, m) (mod p³)`. -/
theorem kazandzidis_p3 (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (n m : ℕ) (hmn : m ≤ n) :
    (Nat.choose (p*n) (p*m) : ZMod (p^3)) = (Nat.choose n m : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.out.ne_zero⟩
  have hp0 : 0 < p := hp.out.pos
  set Wm := ∏ t ∈ Finset.range m, ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWm
  set Wnm := ∏ t ∈ Finset.range (n-m), ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWnm
  set Wn := ∏ t ∈ Finset.range n, ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWn
  -- integer identity  C(pn,pm) * (W_m * W_{n-m}) = C(n,m) * W_n
  have key : Nat.choose (p*n) (p*m) * (Wm * Wnm) = Nat.choose n m * Wn := by
    have hpm : p*m ≤ p*n := Nat.mul_le_mul_left p hmn
    have e1 := Nat.choose_mul_factorial_mul_factorial hpm
    have e2 := Nat.choose_mul_factorial_mul_factorial hmn
    have hsub : p*n - p*m = p*(n-m) := (Nat.mul_sub_left_distrib p n m).symm
    rw [hsub, fact_factor p hp0 n, fact_factor p hp0 m, fact_factor p hp0 (n-m)] at e1
    rw [← hWm, ← hWnm, ← hWn] at e1
    have hpow : p^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega
    -- cancel p^n * m! * (n-m)! from both sides
    have hbig : (p^n * (m ! * (n-m)!)) * (Nat.choose (p*n) (p*m) * (Wm * Wnm))
              = (p^n * (m ! * (n-m)!)) * (Nat.choose n m * Wn) := by
      have lhs_eq : (p^n * (m ! * (n-m)!)) * (Nat.choose (p*n) (p*m) * (Wm * Wnm))
          = Nat.choose (p*n) (p*m) * (p^m * m ! * Wm) * (p^(n-m) * (n-m)! * Wnm) := by
        rw [hpow]; ring
      have rhs_eq : (p^n * (m ! * (n-m)!)) * (Nat.choose n m * Wn)
          = (Nat.choose n m * m ! * (n-m)!) * (p^n * Wn) := by ring
      rw [lhs_eq, rhs_eq, e1, e2]; ring
    have hposc : 0 < p^n * (m ! * (n-m)!) :=
      Nat.mul_pos (pow_pos hp0 n) (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos (n-m)))
    exact Nat.eq_of_mul_eq_mul_left hposc hbig
  -- cast to ZMod (p^3) and use W ≡ (p-1)!^k
  set F : ZMod (p^3) := ((Nat.factorial (p-1) : ℕ) : ZMod (p^3)) with hF
  have hcast : (Nat.choose (p*n) (p*m) : ZMod (p^3)) * (F^m * F^(n-m))
      = (Nat.choose n m : ZMod (p^3)) * F^n := by
    have := congrArg (fun x : ℕ => (x : ZMod (p^3))) key
    simp only [Nat.cast_mul] at this
    rw [hWm, hWnm, hWn, W_pow_congr p h5 m, W_pow_congr p h5 (n-m), W_pow_congr p h5 n] at this
    exact this
  -- F is a unit, hence F^n is a unit
  have hFunit : IsUnit F := by
    rw [hF, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_
    rw [Nat.Prime.dvd_factorial hp.out]
    omega
  have hFn : IsUnit (F^n) := hFunit.pow n
  have hfold : F^m * F^(n-m) = F^n := by rw [← pow_add]; congr 1; omega
  rw [hfold] at hcast
  -- cancel F^n
  have h := congrArg (fun x => x * (F^n)⁻¹) hcast
  simp only [mul_assoc, ZMod.mul_inv_of_unit _ hFn, mul_one] at h
  exact h

/-- **`W_k` product refined `(mod p⁴)`:** `∏_{t<k} ∏_{j=1}^{p-1}(tp+j)
      ≡ (p-1)!^k · (1 + V · p²·∑_{t<k} t(t+1)) (mod p⁴)`, where
    `V = ∑_{j=1}^{(p-1)/2} (j(p-j))⁻¹`.  This is the mod-`p⁴` companion of `W_pow_congr`.
    Since `V ≡ 0 (mod p)` (`W1_sum_zero`) and `∑_{t<k} t(t+1)` differences equal `nm(n-m)`
    (`sum_tri`/`D1_identity`), this yields the sharp Kazandzidis correction. -/
theorem W_pow_congr_p4 (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (k : ℕ) :
    ((∏ t ∈ Finset.range k, ∏ j ∈ Finset.Ico 1 p, (t*p + j) : ℕ) : ZMod (p^4))
      = ((Nat.factorial (p-1) : ℕ) : ZMod (p^4))^k
        * (1 + (∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹)
              * ((p^2 * (∑ t ∈ Finset.range k, t*(t+1)) : ℕ) : ZMod (p^4))) := by
  set V : ZMod (p^4) := ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹ with hV
  rw [Nat.cast_prod]
  have hstep : ∀ t ∈ Finset.range k,
      ((∏ j ∈ Finset.Ico 1 p, (t*p + j) : ℕ) : ZMod (p^4))
        = ((Nat.factorial (p-1) : ℕ) : ZMod (p^4)) * (1 + ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4)) * V) := by
    intro t _; rw [hV]; exact block_prod_p4 p h5 t
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  congr 1
  rw [prod_one_add_of_sq_zero (Finset.range k)
        (fun t => ((p^2*(t*(t+1)) : ℕ) : ZMod (p^4)) * V)
        (by intro i _ j _
            calc (((p^2*(i*(i+1)) : ℕ) : ZMod (p^4)) * V) * (((p^2*(j*(j+1)) : ℕ) : ZMod (p^4)) * V)
                = (((p^2*(i*(i+1)) : ℕ) : ZMod (p^4)) * ((p^2*(j*(j+1)) : ℕ) : ZMod (p^4))) * (V*V) := by
                    ring
              _ = 0 := by
                    rw [← Nat.cast_mul,
                        (ZMod.natCast_eq_zero_iff _ _).mpr ⟨(i*(i+1))*(j*(j+1)), by ring⟩, zero_mul])]
  congr 1
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  rw [Finset.mul_sum, ← Nat.cast_sum]

/-- If `x*x = 0` then `1 + x` is a unit (with inverse `1 - x`). -/
theorem isUnit_one_add_sq_zero {R : Type*} [CommRing R] (x : R) (h : x * x = 0) :
    IsUnit (1 + x) := by
  have hh : (1 + x) * (1 - x) = 1 := by
    rw [show (1 + x) * (1 - x) = 1 - x * x from by ring, h, sub_zero]
  have hh' : (1 - x) * (1 + x) = 1 := by
    rw [show (1 - x) * (1 + x) = 1 - x * x from by ring, h, sub_zero]
  exact ⟨⟨1 + x, 1 - x, hh, hh'⟩, rfl⟩

/-- Nat splitting of the triangular sum: `∑_{t<n} t(t+1) = ∑_{t<m} + ∑_{t<n-m} + n·m·(n-m)`. -/
theorem sum_tri_split (n m : ℕ) (hmn : m ≤ n) :
    (∑ t ∈ Finset.range n, t*(t+1))
      = (∑ t ∈ Finset.range m, t*(t+1)) + (∑ t ∈ Finset.range (n-m), t*(t+1))
        + n*m*(n-m) := by
  have hD := D1_identity n m hmn
  have hcast : ∀ k : ℕ, (∑ t ∈ Finset.range k, ((t:ℤ)*(t+1)))
      = ((∑ t ∈ Finset.range k, t*(t+1) : ℕ) : ℤ) := by
    intro k
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _; push_cast; ring
  rw [hcast n, hcast m, hcast (n-m)] at hD
  have hnmsub : ((n-m:ℕ):ℤ) = (n:ℤ)-m := Nat.cast_sub hmn
  have hnm : ((n*m*(n-m):ℕ):ℤ) = (n:ℤ)*m*((n:ℤ)-m) := by
    rw [Nat.cast_mul, Nat.cast_mul, hnmsub]
  have hz : ((∑ t ∈ Finset.range n, t*(t+1) : ℕ):ℤ)
      = ((∑ t ∈ Finset.range m, t*(t+1) : ℕ):ℤ) + ((∑ t ∈ Finset.range (n-m), t*(t+1) : ℕ):ℤ)
        + ((n*m*(n-m):ℕ):ℤ) := by
    rw [hnm]; linarith [hD]
  exact_mod_cast hz

/-- The reflected sum `V = ∑_{j=1}^{(p-1)/2}(j(p-j))⁻¹` reduces to `0` under `ZMod(p⁴) → ZMod p`. -/
theorem V_red_zero (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    (ZMod.castHom (dvd_pow_self p (show (4:ℕ) ≠ 0 by norm_num)) (ZMod p))
      (∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹) = 0 := by
  rw [map_sum]
  rw [show (0:ZMod p)
      = ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod p))⁻¹ from
      (W1_sum_zero p h5 (hp.out.odd_of_ne_two (by omega))).symm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hu : IsUnit (((j*(p-j) : ℕ) : ZMod (p^4))) := by
    rw [Nat.cast_mul]
    exact (isUnit_castm p 4 j (by omega) (by omega)).mul
      (isUnit_castm p 4 (p-j) (by omega) (by omega))
  have hinv : (ZMod.castHom (dvd_pow_self p (show (4:ℕ) ≠ 0 by norm_num)) (ZMod p))
      (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹
      = ((ZMod.castHom (dvd_pow_self p (show (4:ℕ) ≠ 0 by norm_num)) (ZMod p))
          ((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹ := by
    apply zmod_eq_inv_of_mul_eq_one (hu.map _)
    rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  rw [hinv, map_natCast]

/-- **Sharp Kazandzidis `(mod p⁴)`:** for `p ≥ 5`, `m ≤ n`, if `p ∣ n·m·(n-m)` then
    `C(pn, pm) ≡ C(n, m) (mod p⁴)`.  (One order beyond `kazandzidis_p3`; the extra order comes
    from `W1_sum_zero` combined with the `nm(n-m)` factor of `D1_identity`.) -/
theorem kazandzidis_p4 (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (n m : ℕ) (hmn : m ≤ n)
    (hdvd : p ∣ n * m * (n - m)) :
    (Nat.choose (p*n) (p*m) : ZMod (p^4)) = (Nat.choose n m : ZMod (p^4)) := by
  haveI : NeZero (p^4) := ⟨pow_ne_zero 4 hp.out.ne_zero⟩
  have hp0 : 0 < p := hp.out.pos
  set Wm := ∏ t ∈ Finset.range m, ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWm
  set Wnm := ∏ t ∈ Finset.range (n-m), ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWnm
  set Wn := ∏ t ∈ Finset.range n, ∏ j ∈ Finset.Ico 1 p, (t*p + j) with hWn
  -- integer identity  C(pn,pm) * (W_m * W_{n-m}) = C(n,m) * W_n   (same as in kazandzidis_p3)
  have key : Nat.choose (p*n) (p*m) * (Wm * Wnm) = Nat.choose n m * Wn := by
    have hpm : p*m ≤ p*n := Nat.mul_le_mul_left p hmn
    have e1 := Nat.choose_mul_factorial_mul_factorial hpm
    have e2 := Nat.choose_mul_factorial_mul_factorial hmn
    have hsub : p*n - p*m = p*(n-m) := (Nat.mul_sub_left_distrib p n m).symm
    rw [hsub, fact_factor p hp0 n, fact_factor p hp0 m, fact_factor p hp0 (n-m)] at e1
    rw [← hWm, ← hWnm, ← hWn] at e1
    have hpow : p^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega
    have hbig : (p^n * (m ! * (n-m)!)) * (Nat.choose (p*n) (p*m) * (Wm * Wnm))
              = (p^n * (m ! * (n-m)!)) * (Nat.choose n m * Wn) := by
      have lhs_eq : (p^n * (m ! * (n-m)!)) * (Nat.choose (p*n) (p*m) * (Wm * Wnm))
          = Nat.choose (p*n) (p*m) * (p^m * m ! * Wm) * (p^(n-m) * (n-m)! * Wnm) := by
        rw [hpow]; ring
      have rhs_eq : (p^n * (m ! * (n-m)!)) * (Nat.choose n m * Wn)
          = (Nat.choose n m * m ! * (n-m)!) * (p^n * Wn) := by ring
      rw [lhs_eq, rhs_eq, e1, e2]; ring
    have hposc : 0 < p^n * (m ! * (n-m)!) :=
      Nat.mul_pos (pow_pos hp0 n) (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos (n-m)))
    exact Nat.eq_of_mul_eq_mul_left hposc hbig
  -- abbreviations
  set V : ZMod (p^4) := ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j*(p-j) : ℕ) : ZMod (p^4)))⁻¹ with hV
  set F : ZMod (p^4) := ((Nat.factorial (p-1) : ℕ) : ZMod (p^4)) with hF
  set Sm : ℕ := ∑ t ∈ Finset.range m, t*(t+1) with hSm
  set Snm : ℕ := ∑ t ∈ Finset.range (n-m), t*(t+1) with hSnm
  set Sn : ℕ := ∑ t ∈ Finset.range n, t*(t+1) with hSn
  -- the vanishing correction
  have hvanish : V * ((p^2*(n*m*(n-m)) : ℕ) : ZMod (p^4)) = 0 := by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ, show p^2*(p*Q) = p^3*Q from by ring, Nat.cast_mul, Nat.cast_pow,
        show V * ((p:ZMod (p^4))^3 * (Q:ZMod (p^4))) = (p:ZMod (p^4))^3 * (V * (Q:ZMod (p^4)))
          from by ring, pk_mul_eq_zero p 4 3 (by norm_num)]
    have hred : (ZMod.castHom (dvd_pow_self p (show (4:ℕ) ≠ 0 by norm_num)) (ZMod p))
        (V * (Q:ZMod (p^4))) = 0 := by
      rw [map_mul, hV, V_red_zero p h5, zero_mul]
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hred
    simpa using hred
  -- key facts about the 1-units
  have hbb : ((p^2*Sm : ℕ) : ZMod (p^4)) * ((p^2*Snm : ℕ) : ZMod (p^4)) = 0 := by
    rw [← Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr ⟨Sm*Snm, by ring⟩]
  have hSnid : ((p^2*Sn : ℕ) : ZMod (p^4))
      = ((p^2*Sm : ℕ) : ZMod (p^4)) + ((p^2*Snm : ℕ) : ZMod (p^4))
        + ((p^2*(n*m*(n-m)) : ℕ) : ZMod (p^4)) := by
    rw [← Nat.cast_add, ← Nat.cast_add]
    congr 1
    rw [hSn, hSm, hSnm, sum_tri_split n m hmn]; ring
  -- ↑Wm * ↑Wnm = ↑Wn in ZMod (p⁴)
  have hFpow : F^m * F^(n-m) = F^n := by rw [← pow_add]; congr 1; omega
  have hWeq : ((Wm : ℕ) : ZMod (p^4)) * ((Wnm : ℕ) : ZMod (p^4)) = ((Wn : ℕ) : ZMod (p^4)) := by
    rw [hWm, hWnm, hWn, W_pow_congr_p4 p h5 m, W_pow_congr_p4 p h5 (n-m), W_pow_congr_p4 p h5 n,
        ← hV, ← hF, ← hSm, ← hSnm, ← hSn]
    calc F^m * (1 + V * ((p^2*Sm:ℕ):ZMod (p^4))) * (F^(n-m) * (1 + V * ((p^2*Snm:ℕ):ZMod (p^4))))
        = (F^m * F^(n-m))
          * ((1 + V * ((p^2*Sm:ℕ):ZMod (p^4))) * (1 + V * ((p^2*Snm:ℕ):ZMod (p^4)))) := by ring
      _ = F^n * (1 + V * ((p^2*Sm:ℕ):ZMod (p^4)) + V * ((p^2*Snm:ℕ):ZMod (p^4))) := by
            rw [hFpow]; congr 1; linear_combination (V*V) * hbb
      _ = F^n * (1 + V * ((p^2*Sn:ℕ):ZMod (p^4))) := by
            congr 1; rw [hSnid]; linear_combination -hvanish
  -- cast key and cancel the unit ↑Wn
  have hcast : (Nat.choose (p*n) (p*m) : ZMod (p^4)) * (((Wm:ℕ):ZMod (p^4)) * ((Wnm:ℕ):ZMod (p^4)))
      = (Nat.choose n m : ZMod (p^4)) * ((Wn:ℕ):ZMod (p^4)) := by
    have := congrArg (fun x : ℕ => (x : ZMod (p^4))) key
    simpa only [Nat.cast_mul] using this
  rw [hWeq] at hcast
  -- ↑Wn is a unit
  have hFunit : IsUnit F := by
    rw [hF, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_
    rw [Nat.Prime.dvd_factorial hp.out]; omega
  have hVsq : (V * ((p^2*Sn : ℕ) : ZMod (p^4))) * (V * ((p^2*Sn : ℕ) : ZMod (p^4))) = 0 := by
    have haa : ((p^2*Sn : ℕ) : ZMod (p^4)) * ((p^2*Sn : ℕ) : ZMod (p^4)) = 0 := by
      rw [← Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr ⟨Sn*Sn, by ring⟩]
    calc (V * ((p^2*Sn : ℕ) : ZMod (p^4))) * (V * ((p^2*Sn : ℕ) : ZMod (p^4)))
        = (V*V) * (((p^2*Sn : ℕ) : ZMod (p^4)) * ((p^2*Sn : ℕ) : ZMod (p^4))) := by ring
      _ = 0 := by rw [haa, mul_zero]
  have hWnunit : IsUnit ((Wn : ℕ) : ZMod (p^4)) := by
    rw [hWn, W_pow_congr_p4 p h5 n, ← hV, ← hF, ← hSn]
    exact (hFunit.pow n).mul (isUnit_one_add_sq_zero _ hVsq)
  -- cancel ↑Wn
  have hfin := congrArg (fun x => x * (((Wn:ℕ):ZMod (p^4)))⁻¹) hcast
  simpa only [mul_assoc, ZMod.mul_inv_of_unit _ hWnunit, mul_one] using hfin

/-- Sum of 4th powers of inverses over all of `ZMod p` is `0` for `p ≥ 7`. -/
theorem sum_inv_4_field (p : ℕ) [Fact p.Prime] (h7 : 7 ≤ p) :
    ∑ x : ZMod p, (x⁻¹)^4 = 0 := by
  rw [show (∑ x : ZMod p, (x⁻¹)^4) = ∑ x : ZMod p, x^4 from
      Equiv.sum_comp (⟨fun x => x⁻¹, fun x => x⁻¹, inv_inv, inv_inv⟩ : ZMod p ≃ ZMod p)
        (fun x => x^4)]
  exact sum_pow_zmod p 4 (by omega)

/-- Sum of 4th powers of inverses over `Ico 1 p` in `ZMod p` is `0` for `p ≥ 7`. -/
theorem sum_inv_4_Ico (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹)^4 = 0 := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 p) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [show (∑ k ∈ Finset.Ico 1 p, (((k : ZMod p))⁻¹)^4)
      = ∑ x ∈ (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)), (x⁻¹)^4 from
      (Finset.sum_image (f := fun x : ZMod p => x⁻¹^4) hinj).symm]
  have himg : (Finset.Ico 1 p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      rw [ZMod.natCast_eq_zero_iff]
      intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro hx
      have hval : x.val ≠ 0 := fun h => hx (by rw [← ZMod.natCast_rightInverse x, h]; simp)
      exact ⟨x.val, ⟨by omega, ZMod.val_lt x⟩, ZMod.natCast_rightInverse x⟩
  rw [himg, Finset.sum_sdiff_eq_sub (by simp)]
  simp only [Finset.sum_singleton, inv_zero]
  rw [sum_inv_4_field p h7]; simp

/-- **Second reflected Wolstenholme vanishing** (`p ≥ 7`): the order-2 sum
    `∑_{j=1}^{(p-1)/2} ((j(p-j))⁻¹)² ≡ 0 (mod p)`.  (For `p = 5` this fails, since `(p-1) ∣ 4`;
    that is the source of the extra `+1` in the observed valuation at `p = 5`.)
    This is the next ingredient (beyond `W1_sum_zero`) for the `mod p⁶` order. -/
theorem W2_sum_zero (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) (hodd : Odd p) :
    ∑ j ∈ Finset.Ico 1 ((p+1)/2), ((((j*(p-j) : ℕ) : ZMod p))⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set H := ∑ j ∈ Finset.Ico 1 ((p+1)/2), (((j:ZMod p))⁻¹)^4 with hH
  -- each term equals `(j⁻¹)⁴`
  have hterm : ∀ j ∈ Finset.Ico 1 ((p+1)/2),
      ((((j*(p-j) : ℕ) : ZMod p))⁻¹)^2 = (((j:ZMod p))⁻¹)^4 := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [Nat.cast_mul, mul_inv_rev]
    have hpk : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hpk, inv_neg]; ring
  rw [Finset.sum_congr rfl hterm, ← hH]
  have hb1 : 1 ≤ (p+1)/2 := by omega
  have hb2 : (p+1)/2 ≤ p := by omega
  have hsplit : Finset.Ico 1 p = Finset.Ico 1 ((p+1)/2) ∪ Finset.Ico ((p+1)/2) p :=
    (Finset.Ico_union_Ico_eq_Ico hb1 hb2).symm
  have hfull : ∑ j ∈ Finset.Ico 1 p, (((j:ZMod p))⁻¹)^4 = H + H := by
    rw [hsplit, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 ((p+1)/2) p)]
    congr 1
    rw [show (∑ j ∈ Finset.Ico ((p+1)/2) p, (((j:ZMod p))⁻¹)^4)
        = ∑ j ∈ Finset.Ico 1 ((p+1)/2), ((((p-j):ℕ):ZMod p)⁻¹)^4 from ?_]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hpk : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [hpk, inv_neg]; ring
    · apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; rcases hodd with ⟨w,hw⟩; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; rcases hodd with ⟨w,hw⟩; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · intro j hj; simp only [Finset.mem_Ico] at hj
        rw [Nat.sub_sub_self (le_of_lt hj.2)]
  rw [sum_inv_4_Ico p h7] at hfull
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2; omega
  have h2H : (2 : ZMod p) * H = 0 := by rw [two_mul, ← hfull]
  rcases mul_eq_zero.mp h2H with h | h
  · exact absurd h h20
  · exact h

/-- `Nat.ModEq` form of `kazandzidis_p3`: `C(pn, pm) ≡ C(n, m) [MOD p³]` for `p ≥ 5`, `m ≤ n`. -/
theorem kazandzidis_p3_modeq (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (n m : ℕ) (hmn : m ≤ n) :
    Nat.choose (p*n) (p*m) ≡ Nat.choose n m [MOD p^3] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp (kazandzidis_p3 p h5 n m hmn)

/-- `Nat.ModEq` form of `kazandzidis_p4`: `C(pn, pm) ≡ C(n, m) [MOD p⁴]` when `p ∣ n·m·(n-m)`. -/
theorem kazandzidis_p4_modeq (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (n m : ℕ) (hmn : m ≤ n)
    (hdvd : p ∣ n * m * (n - m)) :
    Nat.choose (p*n) (p*m) ≡ Nat.choose n m [MOD p^4] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp (kazandzidis_p4 p h5 n m hmn hdvd)

/-- **Iterated Kazandzidis `(mod p³)`:** for every `r`, `C(pʳ n, pʳ m) ≡ C(n, m) [MOD p³]`
    (`p ≥ 5`, `m ≤ n`).  Proved by induction on `r` via `kazandzidis_p3_modeq`.  This already gives
    the `r = 1` supercongruence exponent `3`; the *sharp* strengthening to `p^{3r}` requires the
    conditional higher-order versions (`kazandzidis_p4`, ...) uniformly in `r`. -/
theorem kazandzidis_iter (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (r n m : ℕ) (hmn : m ≤ n) :
    Nat.choose (p^r * n) (p^r * m) ≡ Nat.choose n m [MOD p^3] := by
  induction r with
  | zero => simpa using Nat.ModEq.refl (Nat.choose n m)
  | succ k ih =>
    have hstep : Nat.choose (p^(k+1) * n) (p^(k+1) * m)
        ≡ Nat.choose (p^k * n) (p^k * m) [MOD p^3] := by
      have h := kazandzidis_p3_modeq p h5 (p^k * n) (p^k * m) (Nat.mul_le_mul_left (p^k) hmn)
      rw [show p * (p^k * n) = p^(k+1) * n from by ring,
          show p * (p^k * m) = p^(k+1) * m from by ring] at h
      exact h
    exact hstep.trans ih

/-- `kazandzidis_p3` with no `m ≤ n` hypothesis: for all `n m`, `C(pn,pm) ≡ C(n,m) [MOD p³]`
    (when `m > n` both binomials vanish). -/
theorem kazandzidis_p3_all (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (n m : ℕ) :
    Nat.choose (p*n) (p*m) ≡ Nat.choose n m [MOD p^3] := by
  by_cases h : m ≤ n
  · exact kazandzidis_p3_modeq p h5 n m h
  · push_neg at h
    have hp0 : 0 < p := hp.out.pos
    rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left h hp0)]

/-- `ZMod` form of `kazandzidis_iter`: `(C(pʳn,pʳm) : ZMod (p³)) = (C(n,m) : ZMod (p³))`. -/
theorem kazandzidis_iter_zmod (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (r n m : ℕ) (hmn : m ≤ n) :
    (Nat.choose (p^r * n) (p^r * m) : ZMod (p^3)) = (Nat.choose n m : ZMod (p^3)) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr (kazandzidis_iter p h5 r n m hmn)

end Wolst
