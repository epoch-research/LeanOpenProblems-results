import Submission.FiniteBlockEntropy
import Submission.EntropyScaleSeries

/-! Entropy decrement on factorially growing scales. The information and entropy
recurrence is explicit; no arithmetic process is assumed to satisfy it here. -/

namespace Erdos371.EntropyDecrement
open Finset
open EntropyScales

/-- Nonnegative decrements of a nonnegative budget are summable when the
positive errors are summable. -/
lemma summable_decrements (e d r : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hd : ∀ n, 0 ≤ d n) (hr : ∀ n, 0 ≤ r n)
    (hs : Summable r) (hstep : ∀ n, e (n+1) ≤ e n - d n + r n) : Summable d := by
  apply summable_of_sum_range_le hd (c := e 0 + ∑' n, r n)
  intro N
  have hpoint (n : ℕ) : d n ≤ -(e (n+1)-e n) + r n := by linarith [hstep n]
  have hsum := sum_le_sum (fun n (_ : n ∈ range N) => hpoint n)
  rw [sum_add_distrib, sum_neg_distrib, sum_range_sub] at hsum
  have herr : ∑ n ∈ range N, r n ≤ ∑' n, r n := hs.sum_le_tsum _ (fun n _ => hr n)
  linarith [he N]

/-- A summable decrement must be smaller than any positive multiple of a
non-summable nonnegative weight, at arbitrarily late indices. -/
theorem exists_small_decrement (d w : ℕ → ℝ)
    (hs : Summable d)
    (hw : ∀ n, 0 ≤ w n) (hn : ¬Summable w) (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ n ≥ K, d n < ε * w n := by
  by_contra h
  push_neg at h
  have hdshift : Summable (fun n => d (n+K)) := (summable_nat_add_iff K).mpr hs
  have hh : Summable (fun n => ε * w (n+K)) := hdshift.of_nonneg_of_le
    (fun n => mul_nonneg hε.le (hw (n+K))) (fun n => h (n+K) (by omega))
  have hwshift : Summable (fun n => w (n+K)) := (summable_mul_left_iff hε.ne').mp hh
  exact hn ((summable_nat_add_iff K).mp hwshift)

/-- Abstract entropy decrement with any divergent weight sequence. -/
theorem exists_small_information (e d r w : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hd : ∀ n, 0 ≤ d n) (hr : ∀ n, 0 ≤ r n)
    (hs : Summable r) (hstep : ∀ n, e (n+1) ≤ e n - d n + r n)
    (hw : ∀ n, 0 ≤ w n) (hn : ¬Summable w) (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ n ≥ K, d n < ε * w n :=
  exists_small_decrement d w (summable_decrements e d r he hd hr hs hstep) hw hn ε hε K

/-- A concrete entropy-decrement conclusion at the scale needed for prime-band
information decoupling. The block recurrence is precisely what conditional
subadditivity and a linear residue-entropy bound must supply. -/
theorem factorial_scale_small_information
    (E I : ℕ → ℝ) (hE : ∀ H, 0 ≤ E H) (hI : ∀ H, 0 ≤ I H)
    (H₀ : ℕ) (hH₀ : 1 < H₀) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ n, E (factorialScale H₀ (n+1)) ≤
      C * factorialScale H₀ n + (n+2 : ℝ)^2 * (E (factorialScale H₀ n)-I (factorialScale H₀ n)))
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ n ≥ K, I (factorialScale H₀ n) <
      ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  let e (n : ℕ) : ℝ := E (factorialScale H₀ n) / factorialScale H₀ n
  let d (n : ℕ) : ℝ := I (factorialScale H₀ n) / factorialScale H₀ n
  let r (n : ℕ) : ℝ := C / (n+2 : ℝ)^2
  let w (n : ℕ) : ℝ := 1 / Real.log (factorialScale H₀ n : ℝ)
  have hpos (n : ℕ) : 0 < (factorialScale H₀ n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (show 0 < H₀ by omega) (factorialScale_ge H₀ n)
  have he : ∀ n, 0 ≤ e n := fun n => div_nonneg (hE _) (hpos n).le
  have hd : ∀ n, 0 ≤ d n := fun n => div_nonneg (hI _) (hpos n).le
  have hr : ∀ n, 0 ≤ r n := fun n => div_nonneg hC (sq_nonneg _)
  have hs : Summable r := by
    have hh : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by decide)
    have hshift := (summable_nat_add_iff 2).mpr (hh.mul_left C)
    simpa only [r, Nat.cast_add, Nat.cast_ofNat, mul_one_div] using hshift
  have hrec (n : ℕ) : e (n+1) ≤ e n - d n + r n := by
    change E (factorialScale H₀ (n+1)) / (factorialScale H₀ (n+1) : ℝ) ≤ _
    rw [factorialScale_succ H₀ n, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < (n+2)^2) (hpos n))).mpr
    have heq : (e n - d n + r n) * ((n+2 : ℝ)^2 * factorialScale H₀ n) =
        C * factorialScale H₀ n + (n+2 : ℝ)^2 *
          (E (factorialScale H₀ n)-I (factorialScale H₀ n)) := by
      dsimp [e,d,r]
      field_simp [(hpos n).ne']
      ring
    rw [heq]
    simpa only [factorialScale_succ] using hstep n
  obtain ⟨n, hn, hsmall⟩ := exists_small_information e d r w he hd hr hs hrec
    (fun n => (one_div_pos.mpr (log_factorialScale_pos H₀ n hH₀)).le)
    (not_summable_inv_log_factorialScale H₀ hH₀) ε hε K
  refine ⟨n, hn, ?_⟩
  change I (factorialScale H₀ n) / (factorialScale H₀ n : ℝ) <
    ε * (1 / Real.log (factorialScale H₀ n : ℝ)) at hsmall
  rw [div_lt_iff₀ (hpos n)] at hsmall
  convert hsmall using 1
  ring

/-- Finite-budget version: no limiting or infinite-process assumption is used. -/
lemma finite_small_decrement (e d r w : ℕ → ℝ) (K : ℕ) (B R ε : ℝ)
    (heK : 0 ≤ e K) (he0 : e 0 ≤ B)
    (herr : ∑ n ∈ range K, r n ≤ R)
    (hstep : ∀ n < K, e (n+1) ≤ e n - d n + r n)
    (hmass : B+R < ε * ∑ n ∈ range K, w n) :
    ∃ n < K, d n < ε * w n := by
  by_contra h
  push_neg at h
  have hsmall : ε * ∑ n ∈ range K, w n ≤ ∑ n ∈ range K, d n := by
    rw [mul_sum]
    exact sum_le_sum fun n hn => h n (mem_range.mp hn)
  have hsum : ∑ n ∈ range K, d n ≤
      ∑ n ∈ range K, (-(e (n+1)-e n)+r n) := by
    apply sum_le_sum
    intro n hn
    linarith [hstep n (mem_range.mp hn)]
  rw [sum_add_distrib, sum_neg_distrib, sum_range_sub] at hsum
  linarith

/-- A uniform finite horizon, depending only on the initial budget, error
sequence, and decrement weight, not on the sequence of entropies. -/
theorem exists_decrement_horizon (r w : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n) (hs : Summable r)
    (hw : ∀ n, 0 ≤ w n) (hn : ¬Summable w) (B ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (e d : ℕ → ℝ), (∀ n, 0 ≤ e n) → e 0 ≤ B →
      (∀ n < K, e (n+1) ≤ e n - d n + r n) →
        ∃ n < K, d n < ε * w n := by
  have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg hw).mp hn
  obtain ⟨K, hK, hlarge⟩ := Filter.exists_lt_of_tendsto_atTop htop 1 ((B+∑' n, r n)/ε)
  refine ⟨K, by omega, ?_⟩
  intro e d he he0 hstep
  apply finite_small_decrement e d r w K B (∑' n, r n) ε (he K) he0
    (hs.sum_le_tsum _ (fun n _ => hr n)) hstep
  apply (div_lt_iff₀ hε).mp at hlarge
  simpa only [mul_comm ε] using hlarge

lemma factorial_normalized_step (E I : ℕ → ℝ) (H₀ n : ℕ) (hH₀ : 0 < H₀) (C : ℝ)
    (hstep : E (factorialScale H₀ (n+1)) ≤
      C * factorialScale H₀ n + (n+2 : ℝ)^2 * (E (factorialScale H₀ n)-I (factorialScale H₀ n))) :
    E (factorialScale H₀ (n+1)) / factorialScale H₀ (n+1) ≤
      E (factorialScale H₀ n) / factorialScale H₀ n -
        I (factorialScale H₀ n) / factorialScale H₀ n + C / (n+2 : ℝ)^2 := by
  have hpos : 0 < (factorialScale H₀ n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hH₀ (factorialScale_ge H₀ n)
  rw [factorialScale_succ H₀ n, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < (n+2)^2) hpos)).mpr
  have heq : (E (factorialScale H₀ n) / factorialScale H₀ n -
        I (factorialScale H₀ n) / factorialScale H₀ n + C / (n+2 : ℝ)^2) *
          ((n+2 : ℝ)^2 * factorialScale H₀ n) =
      C * factorialScale H₀ n + (n+2 : ℝ)^2 *
        (E (factorialScale H₀ n)-I (factorialScale H₀ n)) := by
    field_simp [hpos.ne']
    ring
  rw [heq]
  simpa only [factorialScale_succ] using hstep

lemma summable_factorial_error (C : ℝ) : Summable (fun n : ℕ => C / (n+2 : ℝ)^2) := by
  have hh : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hshift := (summable_nat_add_iff 2).mpr (hh.mul_left C)
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one_div] using hshift

/-- Uniform finite-horizon entropy decrement on factorial scales. -/
theorem exists_factorial_decrement_horizon (H₀ : ℕ) (hH₀ : 1 < H₀) (B C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K > 0, ∀ (E I : ℕ → ℝ), (∀ H, 0 ≤ E H) → E H₀ ≤ B * H₀ →
      (∀ n < K, E (factorialScale H₀ (n+1)) ≤
        C * factorialScale H₀ n + (n+2 : ℝ)^2 *
          (E (factorialScale H₀ n)-I (factorialScale H₀ n))) →
        ∃ n < K, I (factorialScale H₀ n) <
          ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K, hK, hKdec⟩ := exists_decrement_horizon
    (fun n => C/(n+2 : ℝ)^2) (fun n => 1/Real.log (factorialScale H₀ n : ℝ))
    (fun n => div_nonneg hC (sq_nonneg _)) (summable_factorial_error C)
    (fun n => (one_div_pos.mpr (log_factorialScale_pos H₀ n hH₀)).le)
    (not_summable_inv_log_factorialScale H₀ hH₀) B ε hε
  refine ⟨K,hK,?_⟩
  intro E I hE hbudget hstep
  have hpos (n : ℕ) : 0 < (factorialScale H₀ n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (show 0 < H₀ by omega) (factorialScale_ge H₀ n)
  have hHpos : 0 < (H₀ : ℝ) := by exact_mod_cast (show 0 < H₀ by omega)
  have hbudget' : E (factorialScale H₀ 0) / factorialScale H₀ 0 ≤ B := by
    simp only [factorialScale, zero_add, Nat.factorial_one, one_pow, mul_one]
    exact (div_le_iff₀ hHpos).mpr hbudget
  obtain ⟨n,hn,hsmall⟩ := hKdec
    (fun n => E (factorialScale H₀ n) / factorialScale H₀ n)
    (fun n => I (factorialScale H₀ n) / factorialScale H₀ n)
    (fun n => div_nonneg (hE _) (hpos n).le) hbudget'
    (fun n hn => factorial_normalized_step E I H₀ n (by omega) C (hstep n hn))
  refine ⟨n,hn,?_⟩
  rw [div_lt_iff₀ (hpos n)] at hsmall
  convert hsmall using 1
  ring

#print axioms summable_decrements
#print axioms factorial_scale_small_information
#print axioms exists_factorial_decrement_horizon
end Erdos371.EntropyDecrement
