import Submission.MomentOrderConstants
import Submission.HigherDivisorSubpower

/-!
# From sharp divisor moments to smooth shifted primes

The finite decompositions and sieve remainders here are unconditional.
Any lower bound for the TOTAL shifted-prime moment is kept as an explicit
hypothesis. No settlement of Erdős 821 is asserted without that hypothesis.
-/

open Nat Filter
open scoped Classical BigOperators Topology

namespace Erdos821.HigherDivisors

open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def smoothPrimePool (X Y : ℕ) : Finset ℕ :=
  (X+1).primesBelow.filter (fun p => p-1 ∈ Nat.smoothNumbers Y)

lemma moment_le_rough_add_pool_card (k X Y : ℕ) (C : ℝ)
    (hC : ∀ p ∈ (X+1).primesBelow, (tau k (p-1) : ℝ) ≤ C) :
    shiftedPrimeMoment k X ≤ roughPrimeMoment k X Y + C*(smoothPrimePool X Y).card := by
  have he := Finset.sum_filter_add_sum_filter_not (X+1).primesBelow
    (fun p => p-1 ∈ Nat.smoothNumbers Y) (fun p => (tau k (p-1) : ℝ))
  have hr : ((X+1).primesBelow.filter (fun p => p-1 ∉ Nat.smoothNumbers Y)) =
      roughProgressionPrimes 1 Y X := by simp [roughProgressionPrimes]
  rw [hr] at he
  change (∑ p ∈ smoothPrimePool X Y, (tau k (p-1) : ℝ)) + roughPrimeMoment k X Y =
    shiftedPrimeMoment k X at he
  rw [← he]
  have hb : (∑ p ∈ smoothPrimePool X Y, (tau k (p-1) : ℝ)) ≤ C*(smoothPrimePool X Y).card := by
    calc
      _ ≤ ∑ _p ∈ smoothPrimePool X Y, C :=
        Finset.sum_le_sum (fun p hp => hC p (Finset.mem_filter.mp hp).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

def momentScaleX (t L : ℕ) : ℕ := 2^(128*t*L)
def momentScaleK (t L : ℕ) : ℕ := 2^(128*(t-1)*L)
def momentScaleY (L : ℕ) : ℕ := 2^(128*L)

lemma momentScaleX_eq (t L : ℕ) (ht : 1 ≤ t) :
    momentScaleX t L = momentScaleK t L * momentScaleY L := by
  unfold momentScaleX momentScaleK momentScaleY
  rw [← pow_add]
  congr 1
  have h := Nat.sub_add_cancel ht
  nlinarith

lemma momentScaleY_eq_square (L : ℕ) : momentScaleY L = (2^(64*L))^2 := by
  unfold momentScaleY
  rw [← pow_mul]
  congr 1
  ring

lemma momentScaleK_le_X (t L : ℕ) : momentScaleK t L ≤ momentScaleX t L := by
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left 128 (Nat.sub_le _ _))

lemma log_momentScaleX (t L : ℕ) :
    Real.log (momentScaleX t L) = 128*(t : ℝ)*(L : ℝ)*Real.log 2 := by
  simp only [momentScaleX, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]

lemma log_momentScaleK (t L : ℕ) (ht : 1 ≤ t) :
    Real.log (momentScaleK t L) = 128*((t : ℝ)-1)*(L : ℝ)*Real.log 2 := by
  simp only [momentScaleK, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul,
    Nat.cast_sub ht, Nat.cast_one]

lemma one_le_log_momentScaleX (t L : ℕ) (ht : 1 ≤ t) (hL : 1 ≤ L) :
    1 ≤ Real.log (momentScaleX t L) := by
  rw [log_momentScaleX]
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 128*(t : ℝ)*(L : ℝ) by positivity)
  nlinarith [mul_le_mul_of_nonneg_left htR (show (0 : ℝ) ≤ L by linarith)]

lemma harmonic_momentScaleK_le (t L : ℕ) :
    (harmonic (momentScaleK t L) : ℝ) ≤ (128*(t : ℝ)+1)*((L : ℝ)+1) := by
  have h := harmonic_le_one_add_log (momentScaleK t L)
  have hlog : Real.log (momentScaleK t L) ≤ 128*(t : ℝ)*(L : ℝ) := by
    have h := log_two_pow_le (128*(t-1)*L)
    apply h.trans
    exact_mod_cast Nat.mul_le_mul_right L (Nat.mul_le_mul_left 128 (Nat.sub_le t 1))
  have htR := Nat.cast_nonneg (α := ℝ) t
  have hLR := Nat.cast_nonneg (α := ℝ) L
  nlinarith

noncomputable def momentSieveError (k t L : ℕ) : ℝ :=
  (k : ℝ)*((2 : ℝ)^(64*L)+(2 : ℝ)^(16*L)+1)*(momentScaleK t L : ℝ)*
    (harmonic (momentScaleK t L) : ℝ)^(k-1)

/-- The full finite sieve remainder is negligible compared to X on these
scales, for each fixed order. Its constants may depend on that order. -/
theorem eventually_momentSieveError_le (k t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℕ in atTop, momentSieveError k t L ≤ c*(momentScaleX t L : ℝ) := by
  let D : ℕ := ⌈3*(k : ℝ)*(128*(t : ℝ)+1)^(k-1)/c⌉₊
  have hD : 3*(k : ℝ)*(128*(t : ℝ)+1)^(k-1) ≤ c*(D : ℝ) := by
    have h := Nat.le_ceil (3*(k : ℝ)*(128*(t : ℝ)+1)^(k-1)/c)
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_nat_poly_le_two_pow 1 D (k-1)] with L hpoly
  have hpolyR : (D : ℝ)*((L : ℝ)+1)^(k-1) ≤ (2 : ℝ)^L := by
    exact_mod_cast (by simpa only [one_mul] using hpoly : D*(L+1)^(k-1) ≤ 2^L)
  have hpow : (2 : ℝ)^L ≤ (2 : ℝ)^(64*L) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hH0 : 0 ≤ (harmonic (momentScaleK t L) : ℝ) := harmonic_real_nonneg _
  have hsmall : 3*(k : ℝ)*(harmonic (momentScaleK t L) : ℝ)^(k-1) ≤ c*(2 : ℝ)^(64*L) := by
    calc
      _ ≤ 3*(k : ℝ)*((128*(t : ℝ)+1)*((L : ℝ)+1))^(k-1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hH0 (harmonic_momentScaleK_le t L) _) (by positivity)
      _ = (3*(k : ℝ)*(128*(t : ℝ)+1)^(k-1))*((L : ℝ)+1)^(k-1) := by rw [mul_pow]; ring
      _ ≤ (c*(D : ℝ))*((L : ℝ)+1)^(k-1) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ c*(2 : ℝ)^L := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpolyR hc.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hc.le
  have hE : (2 : ℝ)^(64*L)+(2 : ℝ)^(16*L)+1 ≤ 3*(2 : ℝ)^(64*L) := by
    have h1 : (2 : ℝ)^(16*L) ≤ (2 : ℝ)^(64*L) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (1 : ℝ) ≤ (2 : ℝ)^(64*L) := one_le_pow₀ (by norm_num)
    linarith
  have hX : (momentScaleX t L : ℝ) = (momentScaleK t L : ℝ)*((2 : ℝ)^(64*L))^2 := by
    rw [momentScaleX_eq t L ht, momentScaleY_eq_square]
    push_cast
    rfl
  unfold momentSieveError
  calc
    _ ≤ (k : ℝ)*(3*(2 : ℝ)^(64*L))*(momentScaleK t L : ℝ)*
        (harmonic (momentScaleK t L) : ℝ)^(k-1) := by
      gcongr
    _ = (3*(k : ℝ)*(harmonic (momentScaleK t L) : ℝ)^(k-1))*
        ((2 : ℝ)^(64*L)*(momentScaleK t L : ℝ)) := by ring
    _ ≤ (c*(2 : ℝ)^(64*L))*((2 : ℝ)^(64*L)*(momentScaleK t L : ℝ)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = c*(momentScaleX t L : ℝ) := by rw [hX]; ring

/-- For every fixed root cutoff, an order can be chosen BEFORE the scale
so that the entire rough moment, including its sieve remainder, is below
half the factorial-scale main term. -/
theorem exists_order_eventually_rough_le (t : ℕ) (ht : 2 ≤ t) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ L : ℕ in atTop,
      roughPrimeMoment k (momentScaleX t L) (momentScaleY L) ≤
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ)) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  let ρ : ℝ := 1 - 1/(2*(t : ℝ))
  let κ : ℝ := 1/(128*(t : ℝ))
  have hρ : 0 ≤ ρ := by
    have h := (div_le_one (show (0 : ℝ) < 2*(t : ℝ) by positivity)).mpr
      (show (1 : ℝ) ≤ 2*(t : ℝ) by linarith)
    dsimp [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    have h : (0 : ℝ) < 1/(2*(t : ℝ)) := by positivity
    dsimp [ρ]
    linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨k, _, hk, hcoef⟩ := exists_order_rough_coefficient_lt_factorial ρ (64/κ^2) hρ hρ1 1
  let A : ℝ := 16/κ^2*(k : ℝ)*(Real.exp 1/(k : ℝ))^k*eulerCost k*ρ^k
  have hA : A ≤ 1/(4*(k.factorial : ℝ)) := by
    have h4 : 4*A < 1/(k.factorial : ℝ) := by
      convert hcoef using 1
      dsimp [A]
      ring
    have he : 1/(4*(k.factorial : ℝ)) = (1/(k.factorial : ℝ))/4 := by ring
    rw [he]
    linarith
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop k,
    eventually_momentSieveError_le k t (by omega) (1/(4*(k.factorial : ℝ))) (by positivity)] with L hkL herror
  have hL : 1 ≤ L := by omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hkLR : (k : ℝ) ≤ L := by exact_mod_cast hkL
  have hX : 0 < momentScaleX t L := by unfold momentScaleX; positivity
  have hK : 1 < momentScaleK t L := by
    unfold momentScaleK
    have he : 0 < 128*(t-1)*L := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hL
    exact Nat.one_lt_pow he.ne' (by decide)
  have hlog := one_le_log_momentScaleX t L (by omega) hL
  have hcofactor : Real.log (momentScaleK t L) + k ≤ ρ*Real.log (momentScaleX t L) := by
    rw [log_momentScaleK t L (by omega), log_momentScaleX]
    have hid : ρ*(128*(t : ℝ)*(L : ℝ)*Real.log 2) -
        128*((t : ℝ)-1)*(L : ℝ)*Real.log 2 = 64*(L : ℝ)*Real.log 2 := by
      dsimp [ρ]
      field_simp
      ring
    have hb := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
      (show (0 : ℝ) ≤ 64*(L : ℝ) by positivity)
    nlinarith
  have hsieve : κ*Real.log (momentScaleX t L) ≤ (L : ℝ)*Real.log 2 := by
    rw [log_momentScaleX]
    apply le_of_eq
    dsimp [κ]
    field_simp
  have hmain := rough_sieve_main_le_normalized k (momentScaleX t L) (momentScaleK t L) L
    hk hK (Real.log (momentScaleX t L)) ρ κ (by linarith) hκ hcofactor hsieve
  have hmain' : (k : ℝ)*(16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
      (eulerCost k*harmonicMoment k (momentScaleK t L)) ≤
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ)) := by
    apply hmain.trans
    have h := mul_le_mul_of_nonneg_right hA
      (show 0 ≤ (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2) by positivity)
    convert h using 1 <;> dsimp [A] <;> ring
  have hpower : (1 : ℝ) ≤ (Real.log (momentScaleX t L))^(k-2) := one_le_pow₀ hlog
  have herror' : momentSieveError k t L ≤
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ)) := by
    apply herror.trans
    have h := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ (momentScaleX t L : ℝ)/(4*(k.factorial : ℝ)) by positivity)
    convert h using 1 <;> ring
  have hs := roughPrimeMoment_sieve_bound (k-1) (momentScaleX t L) (momentScaleK t L)
    (momentScaleY L) L (momentScaleX_eq t L (by omega)).le (momentScaleK_le_X t L) hL
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hs
  have hsplit : (k : ℝ)*
      ((16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
        (eulerCost k*harmonicMoment k (momentScaleK t L)) +
        ((2 : ℝ)^(64*L)+(2 : ℝ)^(16*L)+1)*(momentScaleK t L : ℝ)*
          (harmonic (momentScaleK t L) : ℝ)^(k-1)) =
      (k : ℝ)*(16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
        (eulerCost k*harmonicMoment k (momentScaleK t L)) + momentSieveError k t L := by
    unfold momentSieveError
    ring
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, sub_add_cancel, hsplit] at hs
  have he : (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ)) =
      2*((momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ))) := by ring
  rw [he]
  linarith

lemma momentScaleX_small_rpow (t L : ℕ) (ht : 1 ≤ t) :
    (momentScaleX t L : ℝ)^(1/(2*(t : ℝ))) = (2 : ℝ)^(64*L) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have he : ((128*t*L : ℕ) : ℝ)*(1/(2*(t : ℝ))) = ((64*L : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  simp only [momentScaleX, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num), he, Real.rpow_natCast]

/-- The fixed-order divisor weights cost only a small power at these scales. -/
lemma exists_moment_weight_bound (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L n : ℕ, n ≤ momentScaleX t L →
      (tau k n : ℝ) ≤ C*(2 : ℝ)^(64*L) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hε : (0 : ℝ) < 1/(2*(t : ℝ)) := by positivity
  obtain ⟨C, hC, hweight⟩ := tau_succ_le_const_mul_rpow (k-1) (1/(2*(t : ℝ))) hε
  rw [Nat.sub_add_cancel hk] at hweight
  refine ⟨C, hC, ?_⟩
  intro L n hn
  calc
    (tau k n : ℝ) ≤ C*(n : ℝ)^(1/(2*(t : ℝ))) := hweight n
    _ ≤ C*(momentScaleX t L : ℝ)^(1/(2*(t : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hε.le) (by linarith)
    _ = _ := by rw [momentScaleX_small_rpow t L ht]

/-- The lower total moment is explicit in the implication; only the upper
rough estimate and subpower weight bounds are used unconditionally. -/
theorem eventually_smooth_count_of_moment_lower (k t : ℕ) (hk : 2 ≤ k) (ht : 2 ≤ t)
    (Hrough : ∀ᶠ L : ℕ in atTop,
      roughPrimeMoment k (momentScaleX t L) (momentScaleY L) ≤
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ))) :
    ∀ᶠ L : ℕ in atTop,
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L) →
      momentScaleK t L ≤ (smoothPrimePool (momentScaleX t L) (momentScaleY L)).card := by
  obtain ⟨C, hC, hweight⟩ := exists_moment_weight_bound k t (by omega) (by omega)
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hgrowth : ∀ᶠ L : ℕ in atTop, 2*C*(k.factorial : ℝ) < (2 : ℝ)^L :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_gt_atTop (2*C*(k.factorial : ℝ)))
  filter_upwards [Hrough, hgrowth, eventually_ge_atTop 1] with L hrough hgrowth hL hlower
  have hlog := one_le_log_momentScaleX t L (by omega) hL
  have hX : (0 : ℝ) < momentScaleX t L := by unfold momentScaleX; positivity
  have hK : (0 : ℝ) < momentScaleK t L := by unfold momentScaleK; positivity
  have hC0 : 0 ≤ C := by linarith
  have hbound : ∀ p ∈ (momentScaleX t L+1).primesBelow,
      (tau k (p-1) : ℝ) ≤ C*(2 : ℝ)^(64*L) := by
    intro p hp
    apply hweight L (p-1)
    have h := (Nat.mem_primesBelow.mp hp).1
    omega
  have htotal := moment_le_rough_add_pool_card k (momentScaleX t L) (momentScaleY L)
    (C*(2 : ℝ)^(64*L)) hbound
  have hlarge : 2*C*(k.factorial : ℝ) < (2 : ℝ)^(64*L) :=
    hgrowth.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hXeq : (momentScaleX t L : ℝ) = (momentScaleK t L : ℝ)*((2 : ℝ)^(64*L))^2 := by
    rw [momentScaleX_eq t L (by omega), momentScaleY_eq_square]
    push_cast
    rfl
  have hsmall : (C*(2 : ℝ)^(64*L))*(momentScaleK t L : ℝ) <
      (momentScaleX t L : ℝ)/(2*(k.factorial : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*(k.factorial : ℝ))).mpr
    have h := mul_lt_mul_of_pos_right hlarge
      (show 0 < (2 : ℝ)^(64*L)*(momentScaleK t L : ℝ) by positivity)
    rw [hXeq]
    convert h using 1 <;> ring
  have hhalf : (momentScaleX t L : ℝ)/(2*(k.factorial : ℝ)) ≤
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hlog (n := k-2)) hX.le
  by_contra hnot
  have hc : ((smoothPrimePool (momentScaleX t L) (momentScaleY L)).card : ℝ) ≤ momentScaleK t L := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ C*(2 : ℝ)^(64*L) by positivity)
  have he : (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) =
      2*((momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ))) := by ring
  rw [he] at hlower
  linarith

/-- This is the still-unproved arithmetic hypothesis, NOT a supplied axiom.
The divisor order and root parameter are fixed before choosing arbitrarily
large scales; no uniform-in-order asymptotic is demanded. -/
def SharpDyadicMomentLower : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ t : ℕ, 2 ≤ t → ∀ M : ℕ,
    ∃ L : ℕ, M ≤ L ∧
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L)

theorem dyadic_smooth_density_of_sharp_moments (H : SharpDyadicMomentLower)
    (t : ℕ) (ht : 5 ≤ t) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*L) ∧ p-1 ∈ Nat.smoothNumbers (2^L)) ∧
      2^((t-1)*L) ≤ P.card := by
  obtain ⟨k, hk, hrough⟩ := exists_order_eventually_rough_le t (by omega)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_smooth_count_of_moment_lower k t hk (by omega) hrough)
  obtain ⟨L, hL, hmoment⟩ := H k hk t (by omega) (max M N)
  have hML : M ≤ L := (le_max_left _ _).trans hL
  have hNL : N ≤ L := (le_max_right _ _).trans hL
  have hcount := hN L hNL hmoment
  refine ⟨128*L, (hML.trans (by omega)), smoothPrimePool (momentScaleX t L) (momentScaleY L), ?_, ?_⟩
  · intro p hp
    obtain ⟨hp, hps⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hpr⟩ := Nat.mem_primesBelow.mp hp
    have he : momentScaleX t L = 2^(t*(128*L)) := by unfold momentScaleX; congr 1; ring
    refine ⟨hpr, ?_, hps⟩
    rw [← he]
    omega
  · convert hcount using 1
    unfold momentScaleK
    congr 1
    ring

/-- A conditional implication, not a proof of the original conjecture:
all-order factorial-scale shifted-prime moments would suffice. -/
theorem erdos_821_of_sharp_dyadic_moments (H : SharpDyadicMomentLower) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_dyadic_smooth_prime_density (dyadic_smooth_density_of_sharp_moments H)

end Erdos821.HigherDivisors
