import Submission.DyadicLaplaceData
import Submission.SoftEndpointReduction
import Submission.CompetingCoverVariance

/-! An actual three-prime counterexample to dyadic submultiplicativity of
count Laplace transforms. This rules out an unrestricted auxiliary claim,
not the Jacobsthal conjecture or a fixed-small-parameter version. -/
namespace Erdos970.GapAverages.DyadicExample
open Finset Real

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def primes : Finset ℕ := {3, 7, 11}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]

def phase (a : Fin 231) : Phase primes := fun p =>
  ⟨a.val % p.val, Nat.mod_lt _ (primes_prime p.val p.property).pos⟩

lemma phase_injective : Function.Injective phase := by
  intro a b he
  have h3 := congrArg (fun r : Phase primes => (r ⟨3, by decide⟩).val) he
  have h7 := congrArg (fun r : Phase primes => (r ⟨7, by decide⟩).val) he
  have h11 := congrArg (fun r : Phase primes => (r ⟨11, by decide⟩).val) he
  change a.val ≡ b.val [MOD 3] at h3
  change a.val ≡ b.val [MOD 7] at h7
  change a.val ≡ b.val [MOD 11] at h11
  have h77 := (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 7 11)).mp ⟨h7,h11⟩
  have h231 := (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 3 (7*11))).mp ⟨h3,h77⟩
  exact Fin.ext (h231.eq_of_lt_of_lt a.isLt b.isLt)

lemma phase_card : Fintype.card (Phase primes) = 231 := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [prod_coe_sort primes (fun p : ℕ => p)]
  norm_num [primes]

noncomputable def phaseEquiv : Fin 231 ≃ Phase primes :=
  Equiv.ofBijective phase ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨phase_injective, by rw [Fintype.card_fin, phase_card]⟩)

lemma count_raw (m : ℕ) (a : Fin 231) :
    intervalCount primes m (phase a) = (rawCount m a.val : ℝ) := by
  simp [intervalCount, CoverFibers.point_eq_avoidance_indicator, phase, primes,
    Subtype.forall, rawCount]

lemma laplace_raw (t : ℝ) (m : ℕ) :
    countLaplace primes t m =
      (∑ a ∈ range 231, exp (-t*(rawCount m a : ℝ))) / 231 := by
  unfold countLaplace phaseMean
  rw [← phaseEquiv.sum_comp (fun r => exp (-t*intervalCount primes m r))]
  change (∑ a : Fin 231, exp (-t*intervalCount primes m (phase a))) / _ = _
  simp_rw [count_raw]
  rw [Fin.sum_univ_eq_sum_range (fun a => exp (-t*(rawCount m a : ℝ))) 231]
  congr 1
  rw [prod_coe_sort primes (fun p : ℕ => (p : ℝ))]
  norm_num [primes]

/-- Scale before evaluating: all finite computation is done over naturals. -/
lemma scaled_laplace (m B : ℕ) (hB : ∀ a ∈ range 231, rawCount m a ≤ B) :
    (64 : ℝ)^B * countLaplace primes (log 64) m = (weightedSum m B : ℝ)/231 := by
  rw [laplace_raw, ← mul_div_assoc, mul_sum]
  have he (a : ℕ) (ha : a ∈ range 231) :
      (64 : ℝ)^B * exp (-log 64*(rawCount m a : ℝ)) =
        (64 : ℝ)^(B-rawCount m a) := by
    rw [show -log 64*(rawCount m a : ℝ) = (rawCount m a : ℝ)*(-log 64) by ring,
      exp_nat_mul, exp_neg, exp_log (by norm_num : (0 : ℝ) < 64), inv_pow,
      ← pow_sub₀ (64 : ℝ) (by norm_num) (hB a ha)]
  rw [show (∑ a ∈ range 231, (64 : ℝ)^B * exp (-log 64*(rawCount m a : ℝ))) =
      ∑ a ∈ range 231, (64 : ℝ)^(B-rawCount m a) from sum_congr rfl he]
  congr 1
  simp only [weightedSum, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

lemma exact_laplace_26 : countLaplace primes (log 64) 26 =
    (362124420 : ℝ)/(231*64^16) := by
  have hh := scaled_laplace 26 16 (fun a ha => (count_bounds a ha).1)
  rw [weighted_values.1] at hh
  norm_num at hh ⊢
  linarith

lemma exact_laplace_52 : countLaplace primes (log 64) 52 =
    (146912027010 : ℝ)/(231*64^30) := by
  have hh := scaled_laplace 52 30 (fun a ha => (count_bounds a ha).2)
  rw [weighted_values.2] at hh
  norm_num at hh ⊢
  linarith

/-- The failure occurs at the explicit strictly positive parameter log 64. -/
theorem dyadic_laplace_failure :
    countLaplace primes (log 64) 26 ^ 2 < countLaplace primes (log 64) (2*26) := by
  rw [show 2*26 = (52 : ℕ) by norm_num, exact_laplace_26, exact_laplace_52]
  norm_num

theorem not_uniform_dyadic_laplace :
    ¬∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ t : ℝ, 0 < t → ∀ m : ℕ,
      countLaplace P t (2*m) ≤ countLaplace P t m ^ 2 := by
  intro h
  exact dyadic_laplace_failure.not_ge (h primes primes_prime (log 64)
    (log_pos (by norm_num)) 26)

#print axioms exact_laplace_26
#print axioms exact_laplace_52
#print axioms dyadic_laplace_failure
#print axioms not_uniform_dyadic_laplace
end Erdos970.GapAverages.DyadicExample
