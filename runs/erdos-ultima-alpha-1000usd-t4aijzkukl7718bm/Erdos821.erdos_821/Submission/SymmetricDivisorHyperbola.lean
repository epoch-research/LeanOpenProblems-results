import Submission.MomentOrderConstants

/-!
# The symmetric higher-divisor hyperbola decomposition

Below the square of a cutoff there can be at most one large factor in an
ordered factorization. This gives an exact symmetric decomposition, including
the all-small-factor remainder. It supplies no estimate for prime-weighted
sums of that remainder and does not settle Erdős 821.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

noncomputable def lowZeta (H : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n ≤ H then ζ n else 0, by simp⟩

noncomputable def highZeta (H : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if H < n then ζ n else 0, by simp⟩

lemma lowZeta_add_highZeta (H : ℕ) : lowZeta H + highZeta H = ζ := by
  ext n
  simp only [add_apply, lowZeta, highZeta, coe_mk]
  by_cases h : n ≤ H
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma arith_pow_congr_below (f g : ArithmeticFunction ℕ) (k N : ℕ)
    (h : ∀ n ≤ N, f n = g n) : ∀ n ≤ N, (f^k) n = (g^k) n := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro n hn
    rw [_root_.pow_succ, _root_.pow_succ, mul_apply, mul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    obtain ⟨he, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, he.symm⟩
    have hb : ab.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.1, by simpa only [mul_comm] using he.symm⟩
    rw [ih ab.1 (ha.trans hn), h ab.2 (hb.trans hn)]

lemma lowZeta_pow_eq_tau (H k n : ℕ) (hn : n ≤ H) :
    (lowZeta H ^ k) n = tau k n := by
  apply arith_pow_congr_below (lowZeta H) ζ k H _ n hn
  intro m hm
  simp [lowZeta, hm]

lemma highZeta_pow_eq_zero (H k n : ℕ) (hn : n < (H+1)^k) :
    (highZeta H ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hn
    simp [this]
  | succ k ih =>
    rw [_root_.pow_succ', mul_apply]
    apply Finset.sum_eq_zero
    intro ab hab
    obtain ⟨he, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    by_cases ha : H < ab.1
    · have hb : ab.2 < (H+1)^k := by
        rw [_root_.pow_succ'] at hn
        have hmul := Nat.mul_le_mul_right ab.2 (show H+1 ≤ ab.1 by omega)
        nlinarith
      rw [ih ab.2 hb, mul_zero]
    · simp [highZeta, ha]

lemma arith_natCast_mul_apply (m : ℕ) (f : ArithmeticFunction ℕ) (n : ℕ) :
    ((m : ArithmeticFunction ℕ) * f) n = m * f n := by
  rw [← nsmul_eq_mul]
  induction m with
  | zero => simp
  | succ m ih => simp only [succ_nsmul, add_apply, ih]; nlinarith

lemma arith_sum_apply {ι : Type*} (S : Finset ι) (f : ι → ArithmeticFunction ℕ) (n : ℕ) :
    (∑ i ∈ S, f i) n = ∑ i ∈ S, f i n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert hi, ih]

lemma highZeta_pow_mul_eq_zero (H j k n : ℕ) (hj : 2 ≤ j)
    (hn : n < (H+1)^2) :
    (highZeta H ^ j * lowZeta H ^ k) n = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨he, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, he.symm⟩
  have ha' : ab.1 < (H+1)^j :=
    (ha.trans_lt hn).trans_le (Nat.pow_le_pow_right (by omega) hj)
  rw [highZeta_pow_eq_zero H j ab.1 ha', zero_mul]

lemma low_high_convolution (H k n : ℕ) (hn : n < (H+1)^2) :
    (lowZeta H ^ k * highZeta H) n =
      ∑ d ∈ n.divisors with H < n/d, tau k d := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => (lowZeta H ^ k) a * highZeta H b), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
  have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
  have hquot : n/d ≠ 0 := by intro h; rw [h, mul_zero] at he; exact hn0 he.symm
  by_cases h : H < n/d
  · have hdH : d ≤ H := by
      by_contra hdH
      have hm := Nat.mul_le_mul (show H+1 ≤ d from by omega) (show H+1 ≤ n/d by omega)
      nlinarith
    simp only [highZeta, coe_mk, if_pos h, zeta_apply_ne hquot, mul_one]
    exact lowZeta_pow_eq_tau H k d hdH
  · simp [highZeta, h]

/-- Exact hyperbola decomposition. The first term is the nonnegative
all-small-factor remainder; it must not be discarded in an equality. -/
theorem tau_symmetric_hyperbola (H k n : ℕ) (hn : n < (H+1)^2) :
    tau (k+1) n = (lowZeta H ^ (k+1)) n +
      (k+1) * ∑ d ∈ n.divisors with H < n/d, tau k d := by
  change ((ζ : ArithmeticFunction ℕ)^(k+1)) n = _
  rw [← lowZeta_add_highZeta H, add_comm (lowZeta H), add_pow, arith_sum_apply]
  simp_rw [mul_comm (_ * _) (↑_), arith_natCast_mul_apply]
  rw [Finset.sum_eq_add 0 1 (by decide)]
  · simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, one_mul,
      Nat.sub_zero, Nat.add_sub_cancel, pow_one]
    rw [mul_comm (highZeta H) (lowZeta H ^ k), low_high_convolution H k n hn]
  · intro j hj hne
    have hj2 : 2 ≤ j := by omega
    rw [highZeta_pow_mul_eq_zero H j (k+1-j) n hj2 hn, mul_zero]
  · simp
  · simp

/-- Symmetrizing a square-root truncation yields the factor k+1, not
an unbounded exponential factor in the divisor order. -/
theorem symmetrized_divisor_sum_le (H k n : ℕ) (hn : n < (H+1)^2) :
    (k+1) * ∑ d ∈ n.divisors with H < n/d, tau k d ≤ tau (k+1) n := by
  rw [tau_symmetric_hyperbola H k n hn]
  omega

/-- An all-small-factor term cannot contain a prime above the cutoff. -/
lemma lowZeta_pow_eq_zero_of_large_prime (H k n p : ℕ)
    (hp : p.Prime) (hHp : H < p) (hpn : p ∣ n) :
    (lowZeta H ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
    have hn1 : n ≠ 1 := by intro hn; rw [hn] at hpn; exact hp.not_dvd_one hpn
    simp [hn1]
  | succ k ih =>
    rw [_root_.pow_succ', mul_apply]
    apply Finset.sum_eq_zero
    intro ab hab
    obtain ⟨he, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    by_cases ha : ab.1 ≤ H
    · have hpa : ¬p ∣ ab.1 := by
        intro hpa
        have ha0 : 0 < ab.1 := by
          by_contra ha0
          have : ab.1 = 0 := by omega
          simp [this] at he
          exact hn0 he.symm
        have hpab := Nat.le_of_dvd ha0 hpa
        omega
      have hpb : p ∣ ab.2 := (hp.dvd_mul.mp (he ▸ hpn)).resolve_left hpa
      rw [ih ab.2 hpb, mul_zero]
    · simp [lowZeta, ha]

lemma lowZeta_pow_eq_zero_of_not_smooth (H k n : ℕ)
    (hn : n ∉ Nat.smoothNumbers (H+1)) : (lowZeta H ^ k) n = 0 := by
  have h : ¬∀ p, p.Prime → p ∣ n → p < H+1 :=
    fun h => hn (Nat.mem_smoothNumbers'.mpr h)
  push_neg at h
  obtain ⟨p, hp, hpn, hHp⟩ := h
  exact lowZeta_pow_eq_zero_of_large_prime H k n p hp (by omega) hpn

/-- The remainder vanishes on rough predecessors, but not on all integers. -/
theorem tau_symmetric_hyperbola_of_not_smooth (H k n : ℕ)
    (hn : n < (H+1)^2) (hns : n ∉ Nat.smoothNumbers (H+1)) :
    tau (k+1) n = (k+1) * ∑ d ∈ n.divisors with H < n/d, tau k d := by
  rw [tau_symmetric_hyperbola H k n hn,
    lowZeta_pow_eq_zero_of_not_smooth H (k+1) n hns, zero_add]

/-- Balancing two equal blocks of factors retains a divisor weight on
BOTH sides of the hyperbola. It is not an unweighted progression sum. -/
theorem tau_balanced_hyperbola (k n : ℕ) :
    tau (2*k) n =
      2 * (∑ d ∈ n.divisors with d < n/d, tau k d * tau k (n/d)) +
        ∑ d ∈ n.divisors with d = n/d, tau k d * tau k (n/d) := by
  let S := n.divisorsAntidiagonal
  let w : ℕ × ℕ → ℕ := fun ab => tau k ab.1 * tau k ab.2
  have hswap : (∑ ab ∈ S with ab.2 < ab.1, w ab) =
      ∑ ab ∈ S with ab.1 < ab.2, w ab := by
    apply Finset.sum_bij (fun ab _ => ab.swap)
    · intro ab hab
      obtain ⟨hab, hlt⟩ := Finset.mem_filter.mp hab
      exact Finset.mem_filter.mpr ⟨Nat.swap_mem_divisorsAntidiagonal.mpr hab, hlt⟩
    · intro ab hab cd hcd he
      exact Prod.swap_injective he
    · intro ab hab
      obtain ⟨hab, hlt⟩ := Finset.mem_filter.mp hab
      exact ⟨ab.swap, Finset.mem_filter.mpr
        ⟨Nat.swap_mem_divisorsAntidiagonal.mpr hab, hlt⟩, rfl⟩
    · intro ab hab
      exact Nat.mul_comm _ _
  have hsplit : (∑ ab ∈ S, w ab) =
      (∑ ab ∈ S with ab.1 < ab.2, w ab) +
        (∑ ab ∈ S with ab.2 < ab.1, w ab) +
          ∑ ab ∈ S with ab.1 = ab.2, w ab := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab hab
    rcases lt_trichotomy ab.1 ab.2 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [hswap] at hsplit
  have he : tau (2*k) n = ∑ ab ∈ S, w ab := by
    simp only [tau, two_mul, pow_add, mul_apply, S, w]
  rw [he, hsplit, ← two_mul]
  congr 1
  · congr 1
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Nat.sum_divisorsAntidiagonal
      (fun a b => if a < b then tau k a * tau k b else 0)
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Nat.sum_divisorsAntidiagonal
      (fun a b => if a = b then tau k a * tau k b else 0)

/-- Relative to the sharp factorial coefficient at order k+1, even the
symmetrized cutoff coefficient tends to zero for a fixed theta<1. -/
theorem tendsto_symmetrized_factorial_coefficient (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun k : ℕ => ((k+1).factorial : ℝ) *
      ((k+1 : ℝ)*θ^k/(k.factorial : ℝ))) atTop (𝓝 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hθ hθ1
  have h1 := (tendsto_self_mul_const_pow_of_lt_one hθ hθ1).const_mul 2
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1
  have h := (h2.add h1).add h0
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext k
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem eventually_symmetrized_coefficient_lt_factorial (θ c : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, (k+1 : ℝ)*θ^k/(k.factorial : ℝ) <
      c/((k+1).factorial : ℝ) := by
  filter_upwards [(tendsto_symmetrized_factorial_coefficient θ hθ hθ1).eventually_lt_const hc]
    with k hk
  have hf : (0 : ℝ) < (k+1).factorial := by exact_mod_cast Nat.factorial_pos (k+1)
  exact (lt_div_iff₀ hf).mpr (by simpa only [mul_comm] using hk)

end Erdos821.HigherDivisors
