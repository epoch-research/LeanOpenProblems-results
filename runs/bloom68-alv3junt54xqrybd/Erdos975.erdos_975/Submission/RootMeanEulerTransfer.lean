import Submission.RootMeanIdealEuler
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Absolutely convergent Euler corrections and transfer of linear means

This module proves the missing analytic implication: a multiplicative correction
with bounded prime-power coefficients, whose first prime coefficients vanish
outside a finite set, is absolutely summable with weight `1/n`. Exceptional
primes are allowed arbitrary (prime-dependent) finite local bounds.

The proof bounds finite Euler products and then uses bounded nonnegative partial
sums. In particular, global summability is a conclusion, not an assumption in
this implication. All results are generic coefficient lemmas; they do not assert
a new balanced-divisor conjecture.
-/

namespace Erdos975Support

open Filter
open scoped Topology

namespace EulerTransfer

/-- Weight an arithmetic function by `1/n`, with the usual value zero at zero. -/
noncomputable def reciprocal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ f n / (n : ℝ), by simp⟩

@[simp]
theorem reciprocal_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    reciprocal f n = f n / (n : ℝ) := rfl

theorem isMultiplicative_reciprocal (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) : (reciprocal f).IsMultiplicative := by
  refine ⟨by simp [hf.1], ?_⟩
  intro m n hmn
  simp only [reciprocal_apply, hf.2 hmn, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

/-- Absolute local mass after the constant term. -/
noncomputable def primePowerTail (f : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, ‖f (p ^ (k + 1))‖

/-- A converse to the absolutely convergent Euler-product formula, using only
local absolute convergence and summability of the local tails over primes. -/
theorem summable_norm_of_primePowerTail (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ ↦ ‖f (p ^ k)‖))
    (htail : Summable (fun p : Nat.Primes ↦ primePowerTail f p)) :
    Summable (fun n : ℕ ↦ ‖f n‖) := by
  classical
  let W : ℕ → ℝ := {p : ℕ | p.Prime}.indicator (primePowerTail f)
  have hW : Summable W := summable_subtype_iff_indicator.mp htail
  have hW0 (p : ℕ) : 0 ≤ W p :=
    Set.indicator_nonneg (fun _ _ ↦ tsum_nonneg (fun _ ↦ norm_nonneg _)) p
  have hfactor (p : ℕ) (hp : p.Prime) :
      (∑' k : ℕ, ‖f (p ^ k)‖) = 1 + W p := by
    rw [(hlocal p hp).tsum_eq_zero_add]
    simp [W, primePowerTail, hp, hf.1]
  have hnormmul {m n : ℕ} (hmn : m.Coprime n) :
      ‖f (m * n)‖ = ‖f m‖ * ‖f n‖ := by rw [hf.2 hmn, norm_mul]
  apply summable_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro N
  obtain ⟨hsmooth, hprod⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := fun n ↦ ‖f n‖) (by simp [hf.1])
      (fun h ↦ hnormmul h) (fun hp ↦ by simpa using hlocal _ hp) N
  have hind : Summable ((Nat.smoothNumbers N).indicator (fun n ↦ ‖f n‖)) :=
    summable_subtype_iff_indicator.mp (by simpa using hsmooth)
  calc
    (∑ n ∈ Finset.range N, ‖f n‖) =
        ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator (fun m ↦ ‖f m‖) n := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0, Nat.smoothNumbers]
      · have hns : n ∈ Nat.smoothNumbers N :=
          Nat.mem_smoothNumbers_iff_forall_le.mpr
            ⟨hn0, fun p hpn _ _ ↦ hpn.trans_lt (Finset.mem_range.mp hn)⟩
        simp [hns]
    _ ≤ ∑' n : ℕ, (Nat.smoothNumbers N).indicator (fun m ↦ ‖f m‖) n :=
      hind.sum_le_tsum _ (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ norm_nonneg _) n)
    _ = ∑' n : Nat.smoothNumbers N, ‖f n‖ := (tsum_subtype _ _).symm
    _ = ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, ‖f (p ^ k)‖ := hprod.tsum_eq
    _ = ∏ p ∈ Nat.primesBelow N, (1 + W p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hfactor p (Nat.prime_of_mem_primesBelow hp)
    _ ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (W p) :=
      Finset.prod_le_prod (fun p _ ↦ add_nonneg zero_le_one (hW0 p))
        (fun p _ ↦ by simpa [add_comm] using Real.add_one_le_exp (W p))
    _ = Real.exp (∑ p ∈ Nat.primesBelow N, W p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' p : ℕ, W p) := by
      apply Real.exp_le_exp.mpr
      exact hW.sum_le_tsum _ (fun p _ ↦ hW0 p)

/-- Bounded coefficients at one prime give absolute convergence of its weighted
local series, even at an exceptional prime. -/
theorem summable_reciprocal_primePower_of_bound (f : ArithmeticFunction ℝ)
    (p : ℕ) (hp : p.Prime) (C : ℝ) (hC : ∀ k : ℕ, |f (p ^ k)| ≤ C) :
    Summable (fun k : ℕ ↦ ‖reciprocal f (p ^ k)‖) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
  calc
    ‖reciprocal f (p ^ k)‖ = |f (p ^ k)| * ((p : ℝ)⁻¹) ^ k := by
      rw [reciprocal_apply, norm_div, Real.norm_natCast, Real.norm_eq_abs,
        Nat.cast_pow, div_eq_mul_inv, inv_pow]
    _ ≤ C * ((p : ℝ)⁻¹) ^ k := mul_le_mul_of_nonneg_right (hC k) (pow_nonneg hq0 k)

/-- Vanishing of the first prime coefficient improves a bounded local weighted
tail to `2 C / p²`. This is the second-order estimate used in the Euler product. -/
theorem primePowerTail_reciprocal_le (f : ArithmeticFunction ℝ)
    (p : ℕ) (hp : p.Prime) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k : ℕ, |f (p ^ k)| ≤ C) (hfp : f p = 0) :
    primePowerTail (reciprocal f) p ≤ 2 * C / (p : ℝ) ^ 2 := by
  let q : ℝ := (p : ℝ)⁻¹
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    simpa using (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr hp2
  have hq1 : q < 1 := by linarith
  have hgeom := summable_geometric_of_lt_one hq0 hq1
  have hlocal := summable_reciprocal_primePower_of_bound f p hp C hC
  have hshift : Summable (fun k : ℕ ↦ ‖reciprocal f (p ^ (k + 1))‖) :=
    hlocal.comp_injective (add_left_injective 1)
  have hshift2 : Summable (fun k : ℕ ↦ ‖reciprocal f (p ^ (k + 2))‖) :=
    hlocal.comp_injective (add_left_injective 2)
  have htail : primePowerTail (reciprocal f) p =
      ∑' k : ℕ, ‖reciprocal f (p ^ (k + 2))‖ := by
    rw [primePowerTail, hshift.tsum_eq_zero_add]
    simp [hfp, Nat.add_assoc]
  have hden : (1 - q)⁻¹ ≤ 2 := by
    have hpos : 0 < 1 - q := by linarith
    have hle : (1 / 2 : ℝ) ≤ 1 - q := by linarith
    have hi := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hle
    norm_num at hi ⊢
    exact hi
  calc
    primePowerTail (reciprocal f) p =
        ∑' k : ℕ, ‖reciprocal f (p ^ (k + 2))‖ := htail
    _ ≤ ∑' k : ℕ, (C * q ^ 2) * q ^ k := by
      apply hshift2.tsum_le_tsum _ (hgeom.mul_left (C * q ^ 2))
      intro k
      calc
        ‖reciprocal f (p ^ (k + 2))‖ = |f (p ^ (k + 2))| * q ^ (k + 2) := by
          rw [reciprocal_apply, norm_div, Real.norm_natCast, Real.norm_eq_abs,
            Nat.cast_pow, div_eq_mul_inv, inv_pow]
        _ ≤ C * q ^ (k + 2) := mul_le_mul_of_nonneg_right (hC _) (pow_nonneg hq0 _)
        _ = (C * q ^ 2) * q ^ k := by rw [pow_add]; ring
    _ = (C * q ^ 2) * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ (C * q ^ 2) * 2 := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 2 * C / (p : ℝ) ^ 2 := by simp [q, div_eq_mul_inv]; ring

/-- The local tails of a weighted correction are summable over all primes.
Only finitely many primes may fail the common bound or first-order cancellation. -/
theorem summable_primePowerTail_reciprocal (f : ArithmeticFunction ℝ)
    (S : Finset ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, |f (p ^ k)| ≤ C)
    (hzero : ∀ p : ℕ, p.Prime → p ∉ S → f p = 0) :
    Summable (fun p : Nat.Primes ↦ primePowerTail (reciprocal f) p) := by
  classical
  let W : ℕ → ℝ := {p : ℕ | p.Prime}.indicator (primePowerTail (reciprocal f))
  have hseries : Summable (fun p : ℕ ↦ 2 * C / (p : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left (2 * C)
  have hW : Summable W := by
    apply hseries.of_norm_bounded_eventually
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with p hpS
    by_cases hp : p.Prime
    · change ‖{p : ℕ | p.Prime}.indicator (primePowerTail (reciprocal f)) p‖ ≤ _
      rw [Set.indicator_of_mem (show p ∈ {p : ℕ | p.Prime} from hp),
        Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ primePowerTail (reciprocal f) p from
          tsum_nonneg (fun _ ↦ norm_nonneg _))]
      exact primePowerTail_reciprocal_le f p hp C hC0 (hgood p hp hpS) (hzero p hp hpS)
    · rw [show W p = 0 by simp [W, hp], norm_zero]
      exact div_nonneg (mul_nonneg (by norm_num) hC0) (sq_nonneg (p : ℝ))
  exact summable_subtype_iff_indicator.mpr hW

end EulerTransfer

/-- Absolute `1/n` summability from an exponent-uniform local bound and
first-order cancellation away from a finite set. The exceptional primes need
only individual finite bounds, not a common bound. -/
theorem summable_abs_div_of_primePower_bounds (h : ArithmeticFunction ℝ)
    (hh : h.IsMultiplicative) (S : Finset ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, |h (p ^ k)| ≤ C)
    (hzero : ∀ p : ℕ, p.Prime → p ∉ S → h p = 0)
    (hbad : ∀ p : ℕ, p.Prime → p ∈ S → ∃ Cₚ : ℝ, ∀ k : ℕ, |h (p ^ k)| ≤ Cₚ) :
    Summable (fun n : ℕ ↦ |h n| / (n : ℝ)) := by
  have hlocal (p : ℕ) (hp : p.Prime) :
      Summable (fun k : ℕ ↦ ‖EulerTransfer.reciprocal h (p ^ k)‖) := by
    by_cases hpS : p ∈ S
    · obtain ⟨Cₚ, hCₚ⟩ := hbad p hp hpS
      exact EulerTransfer.summable_reciprocal_primePower_of_bound h p hp Cₚ hCₚ
    · exact EulerTransfer.summable_reciprocal_primePower_of_bound h p hp C (hgood p hp hpS)
  have ht := EulerTransfer.summable_norm_of_primePowerTail (EulerTransfer.reciprocal h)
    (EulerTransfer.isMultiplicative_reciprocal h hh) hlocal
    (EulerTransfer.summable_primePowerTail_reciprocal h S C hC0 hgood hzero)
  exact ht.congr fun n ↦ by
    rw [EulerTransfer.reciprocal_apply, norm_div, Real.norm_natCast, Real.norm_eq_abs]

namespace EulerTransfer

/-- Finite local support and a coefficient bound imply a uniform local inverse
mass bound. The harmless factor `d+1` avoids needing a sharper ideal-specific
mass estimate. -/
theorem sum_abs_primePower_le (v : ArithmeticFunction ℝ) (d : ℕ)
    (p : ℕ) (hvzero : ∀ j : ℕ, d < j → v (p ^ j) = 0)
    (hvbound : ∀ j : ℕ, |v (p ^ j)| ≤ (2 : ℝ) ^ d) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), |v (p ^ j)|) ≤
      (d + 1 : ℝ) * (2 : ℝ) ^ d := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun j : ℕ ↦ j ≤ d)
    (fun j _ hj ↦ by
      by_contra h
      exact hj (by rw [hvzero j (Nat.lt_of_not_ge h), abs_zero]))]
  calc
    (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ ↦ j ≤ d), |v (p ^ j)|) ≤
        ∑ j ∈ Finset.range (d + 1), |v (p ^ j)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ ↦ abs_nonneg _)
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
    _ ≤ ∑ _j ∈ Finset.range (d + 1), (2 : ℝ) ^ d :=
      Finset.sum_le_sum fun j _ ↦ hvbound j
    _ = (d + 1 : ℝ) * (2 : ℝ) ^ d := by simp

/-- Convolution with a locally finite inverse preserves an exponent-uniform
bound at every prime, including the exceptional primes. -/
theorem abs_convolution_primePower_le (v r : ArithmeticFunction ℝ) (d : ℕ)
    (p : ℕ) (hp : p.Prime) (C : ℝ)
    (hvzero : ∀ j : ℕ, d < j → v (p ^ j) = 0)
    (hvbound : ∀ j : ℕ, |v (p ^ j)| ≤ (2 : ℝ) ^ d)
    (hrbound : ∀ j : ℕ, |r (p ^ j)| ≤ C) (k : ℕ) :
    |(v * r) (p ^ k)| ≤ ((d + 1 : ℝ) * (2 : ℝ) ^ d) * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hrbound 0)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun m n ↦ v m * r n), Nat.sum_divisors_prime_pow hp]
  calc
    |∑ j ∈ Finset.range (k + 1), v (p ^ j) * r (p ^ k / p ^ j)| ≤
        ∑ j ∈ Finset.range (k + 1), |v (p ^ j) * r (p ^ k / p ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), |v (p ^ j)| * C := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hp.pos]
      exact mul_le_mul_of_nonneg_left (hrbound _) (abs_nonneg _)
    _ = (∑ j ∈ Finset.range (k + 1), |v (p ^ j)|) * C :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ ((d + 1 : ℝ) * (2 : ℝ) ^ d) * C :=
      mul_le_mul_of_nonneg_right (sum_abs_primePower_le v d p hvzero hvbound k) hC0

/-- An inverse normalized at one has prime coefficient `-a(p)`. -/
theorem inverse_prime (a v : ArithmeticFunction ℝ) (ha1 : a 1 = 1)
    (hav : a * v = 1) (p : ℕ) (hp : p.Prime) : v p = -a p := by
  have hv1 : v 1 = 1 := by
    have hi := congrArg (fun b : ArithmeticFunction ℝ ↦ b 1) hav
    simpa only [ArithmeticFunction.mul_apply_one, ha1, one_mul,
      ArithmeticFunction.one_apply, if_pos rfl] using hi
  have hi := congrArg (fun b : ArithmeticFunction ℝ ↦ b p) hav
  change (a * v) p = (1 : ArithmeticFunction ℝ) p at hi
  rw [IdealEuler.dirichlet_mul_apply_prime _ _ p hp] at hi
  simp only [ha1, hv1, one_mul, mul_one, ArithmeticFunction.one_apply,
    if_neg hp.ne_one] at hi
  linarith

/-- Matching the prime coefficients of `r` and `a` cancels the first-order
coefficient of `v*r`; no agreement at higher prime powers is required. -/
theorem convolution_prime_eq_zero_of_agree (a r v : ArithmeticFunction ℝ)
    (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (p : ℕ) (hp : p.Prime) (hmatch : r p = a p) : (v * r) p = 0 := by
  have hv1 : v 1 = 1 := by
    have hi := congrArg (fun b : ArithmeticFunction ℝ ↦ b 1) hav
    simpa only [ArithmeticFunction.mul_apply_one, ha1, one_mul,
      ArithmeticFunction.one_apply, if_pos rfl] using hi
  rw [IdealEuler.dirichlet_mul_apply_prime _ _ p hp, hv1, hr1,
    inverse_prime a v ha1 hav p hp, hmatch]
  ring

/-- A positive-exponent bound and normalization at one give a bound for all
local exponents, without imposing `d>0`. -/
theorem abs_primePower_le_degree_add_one (r : ArithmeticFunction ℝ)
    (hr1 : r 1 = 1) (d p : ℕ)
    (hbound : ∀ k : ℕ, 1 ≤ k → |r (p ^ k)| ≤ (d : ℝ)) (k : ℕ) :
    |r (p ^ k)| ≤ (d + 1 : ℝ) := by
  by_cases hk : k = 0
  · simp only [hk, pow_zero, hr1, abs_one]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  · exact (hbound k (Nat.one_le_iff_ne_zero.mpr hk)).trans (by linarith)

end EulerTransfer

/-- Generic inverse-coefficient summability theorem. Inverse degree and
coefficient bounds hold at **all** primes; `r` has an individual bound at every
prime and the degree bound and coefficient match away from the finite set `S`.
There is no global summability hypothesis. -/
theorem summable_abs_dirichletCorrection_div (a r v : ArithmeticFunction ℝ)
    (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (hh : (v * r).IsMultiplicative) (d : ℕ) (S : Finset ℕ)
    (hvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, d < k → v (p ^ k) = 0)
    (hvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |v (p ^ k)| ≤ (2 : ℝ) ^ d)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, |r (p ^ k)| ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ,
      1 ≤ k → |r (p ^ k)| ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p) :
    Summable (fun n : ℕ ↦ |(v * r) n| / (n : ℝ)) := by
  apply summable_abs_div_of_primePower_bounds (v * r) hh S
    (((d + 1 : ℝ) * (2 : ℝ) ^ d) * (d + 1 : ℝ)) (by positivity)
  · intro p hp hpS k
    exact EulerTransfer.abs_convolution_primePower_le v r d p hp (d + 1 : ℝ)
      (hvzero p hp) (hvbound p hp)
      (EulerTransfer.abs_primePower_le_degree_add_one r hr1 d p (hrgood p hp hpS)) k
  · intro p hp hpS
    exact EulerTransfer.convolution_prime_eq_zero_of_agree a r v ha1 hr1 hav p hp
      (hmatch p hp hpS)
  · intro p hp _
    obtain ⟨Cₚ, hCₚ⟩ := hrbounded p hp
    exact ⟨((d + 1 : ℝ) * (2 : ℝ) ^ d) * Cₚ,
      EulerTransfer.abs_convolution_primePower_le v r d p hp Cₚ
        (hvzero p hp) (hvbound p hp) hCₚ⟩

/-- Upper bounds can replace absolute-value bounds when `r` is nonnegative,
as is the case for polynomial root counts. -/
theorem summable_abs_dirichletCorrection_div_of_nonneg (a r v : ArithmeticFunction ℝ)
    (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (hh : (v * r).IsMultiplicative) (d : ℕ) (S : Finset ℕ)
    (hvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, d < k → v (p ^ k) = 0)
    (hvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |v (p ^ k)| ≤ (2 : ℝ) ^ d)
    (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ,
      1 ≤ k → r (p ^ k) ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p) :
    Summable (fun n : ℕ ↦ |(v * r) n| / (n : ℝ)) := by
  apply summable_abs_dirichletCorrection_div a r v ha1 hr1 hav hh d S hvzero hvbound
  · intro p hp
    obtain ⟨Cₚ, hCₚ⟩ := hrbounded p hp
    exact ⟨Cₚ, fun k ↦ by simpa only [abs_of_nonneg (hrnonneg _)] using hCₚ k⟩
  · intro p hp hpS k hk
    simpa only [abs_of_nonneg (hrnonneg _)] using hrgood p hp hpS k hk
  · exact hmatch

namespace EulerTransfer

/-- The weighted Euler factor at one rational prime. -/
noncomputable def localFactor (f : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, reciprocal f (p ^ k)

/-- Absolute summability globally implies summability of all prime-power tails
jointly. The map `(p,k) ↦ p^(k+1)` is injective, so no prime is lost. -/
theorem summable_primePowerTail_of_summable_norm (f : ArithmeticFunction ℝ)
    (hsum : Summable (fun n : ℕ ↦ ‖f n‖)) :
    Summable (fun p : Nat.Primes ↦ primePowerTail f p) := by
  have hi : Function.Injective (fun x : Nat.Primes × ℕ ↦ (x.1 : ℕ) ^ (x.2 + 1)) := by
    rintro ⟨p, k⟩ ⟨q, l⟩ h
    obtain ⟨hpq, hkl⟩ := p.prop.pow_inj q.prop h
    exact Prod.ext (Subtype.ext hpq) hkl
  simpa only [primePowerTail, Function.comp_apply] using (hsum.comp_injective hi).prod

/-- Positive local Euler factors give a strictly positive total sum, not merely
a nonnegative limit of finite products. Summability of local deviations from
one gives a convergent logarithmic product with positive exponential. -/
theorem tsum_pos_of_positive_primePower_series (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hsum : Summable (fun n : ℕ ↦ ‖f n‖))
    (hpos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, f (p ^ k)) :
    0 < ∑' n : ℕ, f n := by
  let L : Nat.Primes → ℝ := fun p ↦ ∑' k : ℕ, f ((p : ℕ) ^ k)
  have hdelta : Summable (fun p : Nat.Primes ↦ L p - 1) := by
    apply (summable_primePowerTail_of_summable_norm f hsum).of_norm_bounded
    intro p
    have hlocal : Summable (fun k : ℕ ↦ ‖f ((p : ℕ) ^ k)‖) :=
      hsum.comp_injective (Nat.pow_right_injective p.prop.two_le)
    have hshift : Summable (fun k : ℕ ↦ ‖f ((p : ℕ) ^ (k + 1))‖) :=
      hlocal.comp_injective (add_left_injective 1)
    change ‖(∑' k : ℕ, f ((p : ℕ) ^ k)) - 1‖ ≤ primePowerTail f p
    rw [hlocal.of_norm.tsum_eq_zero_add]
    simp only [pow_zero, hf.1, add_sub_cancel_left]
    exact norm_tsum_le_tsum_norm hshift
  have hlog : Summable (fun p : Nat.Primes ↦ Real.log (L p)) := by
    apply (Real.summable_log_one_add_of_summable hdelta).congr
    intro p
    congr 1
    ring
  have hprod : HasProd L (Real.exp (∑' p : Nat.Primes, Real.log (L p))) :=
    Real.hasProd_of_hasSum_log (fun p ↦ hpos p p.prop) hlog.hasSum
  have heq := (hf.eulerProduct_hasProd hsum).unique hprod
  rw [heq]
  exact Real.exp_pos _

/-- The Cauchy product of local weighted series is the local Dirichlet
convolution factor. Only local summability is needed. -/
theorem localFactor_mul (a b : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime)
    (ha : Summable (fun k : ℕ ↦ reciprocal a (p ^ k)))
    (hb : Summable (fun k : ℕ ↦ reciprocal b (p ^ k))) :
    localFactor (a * b) p = localFactor a p * localFactor b p := by
  unfold localFactor
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha.norm hb.norm]
  apply tsum_congr
  intro k
  rw [reciprocal_apply, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun m n ↦ a m * b n), Nat.sum_divisors_prime_pow hp,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Nat.pow_div hjk hp.pos, reciprocal_apply, reciprocal_apply, div_mul_div_comm]
  congr 1
  rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_of_le hjk]

/-- Normalization and nonnegativity imply positivity of a convergent local
factor (the exponent-zero term is one). -/
theorem localFactor_pos_of_nonneg (f : ArithmeticFunction ℝ) (hf1 : f 1 = 1)
    (p : ℕ) (hnonneg : ∀ k : ℕ, 0 ≤ f (p ^ k))
    (hsum : Summable (fun k : ℕ ↦ reciprocal f (p ^ k))) :
    0 < localFactor f p := by
  have hnonneg' (k : ℕ) : 0 ≤ reciprocal f (p ^ k) :=
    div_nonneg (hnonneg k) (Nat.cast_nonneg _)
  have hle := hsum.sum_le_tsum {0} (fun k _ ↦ hnonneg' k)
  have h1 : 1 ≤ localFactor f p := by simpa [localFactor, hf1] using hle
  exact zero_lt_one.trans_le h1

/-- A local correction factor is exactly the ratio of the `r` and `a` factors.
This follows from the global inverse identity and a locally convergent Cauchy
product, not from a formal division of divergent Euler products. -/
theorem localFactor_correction_eq_div (a r v : ArithmeticFunction ℝ)
    (hav : a * v = 1) (p : ℕ) (hp : p.Prime)
    (ha : Summable (fun k : ℕ ↦ reciprocal a (p ^ k)))
    (hh : Summable (fun k : ℕ ↦ reciprocal (v * r) (p ^ k)))
    (hane : localFactor a p ≠ 0) :
    localFactor (v * r) p = localFactor r p / localFactor a p := by
  have har : a * (v * r) = r := by rw [← mul_assoc, hav, one_mul]
  have hi := localFactor_mul a (v * r) p hp ha hh
  rw [har] at hi
  apply (eq_div_iff hane).mpr
  rw [mul_comm]
  exact hi.symm

/-- Positive numerator and denominator local factors give a positive correction
factor. Absolute local convergence of the correction follows from its proved
bounds in applications. -/
theorem localFactor_correction_pos (a r v : ArithmeticFunction ℝ)
    (hav : a * v = 1) (p : ℕ) (hp : p.Prime)
    (ha : Summable (fun k : ℕ ↦ reciprocal a (p ^ k)))
    (hh : Summable (fun k : ℕ ↦ reciprocal (v * r) (p ^ k)))
    (hapos : 0 < localFactor a p) (hrpos : 0 < localFactor r p) :
    0 < localFactor (v * r) p := by
  rw [localFactor_correction_eq_div a r v hav p hp ha hh hapos.ne']
  exact div_pos hrpos hapos

end EulerTransfer

/-- The generic Euler-transfer conclusion, including strict positivity.
The only extra analytic hypotheses are convergence of the **local** `a` series
and positivity of the `a` and `r` local factors at every prime. Neither global
summability of the correction nor its positivity is assumed. -/
theorem summable_abs_dirichletCorrection_div_and_pos (a r v : ArithmeticFunction ℝ)
    (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (hh : (v * r).IsMultiplicative) (d : ℕ) (S : Finset ℕ)
    (hvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, d < k → v (p ^ k) = 0)
    (hvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |v (p ^ k)| ≤ (2 : ℝ) ^ d)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, |r (p ^ k)| ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ,
      1 ≤ k → |r (p ^ k)| ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p)
    (haLocal : ∀ p : ℕ, p.Prime →
      Summable (fun k : ℕ ↦ a (p ^ k) / ((p ^ k : ℕ) : ℝ)))
    (haPos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, a (p ^ k) / ((p ^ k : ℕ) : ℝ))
    (hrPos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, r (p ^ k) / ((p ^ k : ℕ) : ℝ)) :
    Summable (fun n : ℕ ↦ |(v * r) n| / (n : ℝ)) ∧
      0 < ∑' n : ℕ, (v * r) n / (n : ℝ) := by
  have hb := summable_abs_dirichletCorrection_div a r v ha1 hr1 hav hh d S
    hvzero hvbound hrbounded hrgood hmatch
  have hnorm : Summable (fun n : ℕ ↦ ‖EulerTransfer.reciprocal (v * r) n‖) :=
    hb.congr fun n ↦ by
      rw [EulerTransfer.reciprocal_apply, norm_div, Real.norm_natCast, Real.norm_eq_abs]
  have hpos := EulerTransfer.tsum_pos_of_positive_primePower_series
    (EulerTransfer.reciprocal (v * r)) (EulerTransfer.isMultiplicative_reciprocal _ hh) hnorm
    (fun p hp ↦ EulerTransfer.localFactor_correction_pos a r v hav p hp (haLocal p hp)
      (hnorm.comp_injective (Nat.pow_right_injective hp.two_le)).of_norm
      (haPos p hp) (hrPos p hp))
  exact ⟨hb, hpos⟩

/-- For nonnegative normalized root and ideal coefficients, both local
positivity hypotheses are proved. Local summability of `a` is still stated
explicitly; local summability of `r` is derived from its prime-power bounds. -/
theorem summable_abs_dirichletCorrection_div_and_pos_of_nonneg
    (a r v : ArithmeticFunction ℝ) (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (hh : (v * r).IsMultiplicative) (d : ℕ) (S : Finset ℕ)
    (hvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, d < k → v (p ^ k) = 0)
    (hvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |v (p ^ k)| ≤ (2 : ℝ) ^ d)
    (hanonneg : ∀ n : ℕ, 0 ≤ a n) (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ,
      1 ≤ k → r (p ^ k) ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p)
    (haLocal : ∀ p : ℕ, p.Prime →
      Summable (fun k : ℕ ↦ a (p ^ k) / ((p ^ k : ℕ) : ℝ))) :
    Summable (fun n : ℕ ↦ |(v * r) n| / (n : ℝ)) ∧
      0 < ∑' n : ℕ, (v * r) n / (n : ℝ) := by
  have hrbounded' (p : ℕ) (hp : p.Prime) :
      ∃ Cₚ : ℝ, ∀ k : ℕ, |r (p ^ k)| ≤ Cₚ := by
    obtain ⟨Cₚ, hCₚ⟩ := hrbounded p hp
    exact ⟨Cₚ, fun k ↦ by simpa only [abs_of_nonneg (hrnonneg _)] using hCₚ k⟩
  refine summable_abs_dirichletCorrection_div_and_pos a r v ha1 hr1 hav hh d S
    hvzero hvbound hrbounded' ?_ hmatch haLocal ?_ ?_
  · intro p hp hpS k hk
    simpa only [abs_of_nonneg (hrnonneg _)] using hrgood p hp hpS k hk
  · intro p hp
    exact EulerTransfer.localFactor_pos_of_nonneg a ha1 p (fun k ↦ hanonneg _) (haLocal p hp)
  · intro p hp
    obtain ⟨Cₚ, hCₚ⟩ := hrbounded' p hp
    exact EulerTransfer.localFactor_pos_of_nonneg r hr1 p (fun k ↦ hrnonneg _)
      (EulerTransfer.summable_reciprocal_primePower_of_bound r p hp Cₚ hCₚ).of_norm

/-- A positive ideal-coefficient mean transfers to `r` with the explicit
positive correction factor. The absolute summability needed by
`RootMeanConvolution` is proved from the local hypotheses in this theorem. -/
theorem tendsto_summatory_of_finiteEulerCorrection (a r v : ArithmeticFunction ℝ)
    (ha1 : a 1 = 1) (hr1 : r 1 = 1) (hav : a * v = 1)
    (hh : (v * r).IsMultiplicative) (d : ℕ) (S : Finset ℕ)
    (hvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, d < k → v (p ^ k) = 0)
    (hvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |v (p ^ k)| ≤ (2 : ℝ) ^ d)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, |r (p ^ k)| ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ,
      1 ≤ k → |r (p ^ k)| ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p)
    (haLocal : ∀ p : ℕ, p.Prime →
      Summable (fun k : ℕ ↦ a (p ^ k) / ((p ^ k : ℕ) : ℝ)))
    (haPos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, a (p ^ k) / ((p ^ k : ℕ) : ℝ))
    (hrPos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, r (p ^ k) / ((p ^ k : ℕ) : ℝ))
    {κ : ℝ} (hκ : 0 < κ)
    (haMean : Tendsto (fun N : ℕ ↦ arithmeticSummatory a N / (N : ℝ)) atTop (𝓝 κ)) :
    0 < ∑' n : ℕ, (v * r) n / (n : ℝ) ∧
      0 < κ * (∑' n : ℕ, (v * r) n / (n : ℝ)) ∧
      Tendsto (fun N : ℕ ↦ arithmeticSummatory r N / (N : ℝ)) atTop
        (𝓝 (κ * ∑' n : ℕ, (v * r) n / (n : ℝ))) := by
  obtain ⟨hb, hbpos⟩ := summable_abs_dirichletCorrection_div_and_pos a r v
    ha1 hr1 hav hh d S hvzero hvbound hrbounded hrgood hmatch haLocal haPos hrPos
  have hbNorm : Summable (fun n : ℕ ↦ ‖(v * r) n / (n : ℝ)‖) :=
    hb.congr fun n ↦ by rw [norm_div, Real.norm_natCast, Real.norm_eq_abs]
  have ht := tendsto_summatory_dirichletConvolution a (v * r) haMean hbNorm
  have har : a * (v * r) = r := by rw [← mul_assoc, hav, one_mul]
  rw [har] at ht
  exact ⟨hbpos, mul_pos hκ hbpos, ht⟩

end Erdos975Support
