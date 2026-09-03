import Submission.EulerMassUnrestrictedRatio
import Submission.BuchstabPrimeCoordinates

/-! Exact Euler coordinates for the first-hit measure. The arithmetic
weights telescope in these coordinates, and the coordinates differ from
prime logarithms by a uniform additive constant. No sieve positivity or
Jacobsthal endpoint is asserted in this file. -/
namespace Erdos970.FiniteSelberg
open Real Finset
set_option maxHeartbeats 1600000

lemma strictEulerMass_additive_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (p : ℕ) (hp : p.Prime) :
    |eulerMass p.primesBelow-C*log (p : ℝ)| ≤ 2*A+C := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hE := initialEulerMass_pos p
  obtain ⟨hl,hu⟩ := abs_le.mp (hrem p hp.two_le)
  have hlog : log (p : ℝ) ≤ p := log_le_self hp0.le
  have hAp : A ≤ A*(p : ℝ) := by nlinarith only [hA,hp1]
  have hCp := mul_le_mul_of_nonneg_left hlog hC.le
  have hdiv : initialEulerMass p/(p : ℝ) ≤ A+C := by
    apply (div_le_iff₀ hp0).mpr
    nlinarith only [hu,hAp,hCp]
  have hdiv0 : 0 ≤ initialEulerMass p/(p : ℝ) := div_nonneg hE.le hp0.le
  have hid : eulerMass p.primesBelow = initialEulerMass p-initialEulerMass p/(p : ℝ) := by
    rw [eulerMass_strict_prefix hp]
    dsimp only [initialEulerMass]
    ring
  rw [hid,abs_le]
  constructor <;> linarith only [hl,hu,hdiv,hdiv0,hA,hC]

end Erdos970.FiniteSelberg

namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset FiniteSelberg
set_option maxHeartbeats 1600000

noncomputable def eulerCoordinate (C : ℝ) (k : ℕ) : ℝ :=
  1/(C*prefixDensity primeMarginal k)

lemma eulerCoordinate_pos (C : ℝ) (hC : 0 < C) (k : ℕ) :
    0 < eulerCoordinate C k := one_div_pos.mpr (mul_pos hC (nthPrime_prefix_density_pos k))

lemma eulerCoordinate_eq_mass (C : ℝ) (k : ℕ) :
    eulerCoordinate C k = eulerMass (nthPrime k).primesBelow/C := by
  rw [eulerCoordinate,nthPrime_prefix_density]
  simp only [one_div,mul_inv_rev,inv_inv]
  ring

lemma eulerCoordinate_zero (C : ℝ) : eulerCoordinate C 0=1/C := by
  simp [eulerCoordinate,prefixDensity]

lemma eulerCoordinate_reciprocal (C : ℝ) (k : ℕ) :
    1/eulerCoordinate C k=C*prefixDensity primeMarginal k := by
  simp only [eulerCoordinate,one_div,inv_inv]

lemma prefixDensity_prime_succ (k : ℕ) :
    prefixDensity primeMarginal (k+1)=prefixDensity primeMarginal k*(1-primeMarginal k) :=
  prod_range_succ _ _

lemma eulerCoordinate_monotone (C : ℝ) (hC : 0 < C) : Monotone (eulerCoordinate C) := by
  apply monotone_nat_of_le_succ
  intro k
  have hd := nthPrime_prefix_density_pos k
  have hq := primeMarginal_pos k
  have hkeep := primeMarginal_lt_one k
  have hd' := nthPrime_prefix_density_pos (k+1)
  have hle : prefixDensity primeMarginal (k+1) ≤ prefixDensity primeMarginal k := by
    rw [prefixDensity_prime_succ]
    nlinarith only [hd,hq]
  exact one_div_le_one_div_of_le (mul_pos hC hd') (mul_le_mul_of_nonneg_left hle hC.le)

/-- The full first-hit weight is an exact reciprocal-coordinate increment.
No asymptotic constant is used in this equality. -/
theorem eulerCoordinate_weight (C : ℝ) (hC : 0 < C) (k i : ℕ) :
    eulerCoordinate C k*(1/eulerCoordinate C i-1/eulerCoordinate C (i+1)) =
      (primeMarginal i*prefixDensity primeMarginal i)/prefixDensity primeMarginal k := by
  rw [eulerCoordinate_reciprocal,eulerCoordinate_reciprocal,prefixDensity_prime_succ]
  unfold eulerCoordinate
  have hd := (nthPrime_prefix_density_pos k).ne'
  field_simp [hC.ne',hd]
  <;> ring

lemma eulerCoordinate_log_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A) (k : ℕ) :
    |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ (2*A+C)/C := by
  have hh := div_le_div_of_nonneg_right
    (strictEulerMass_additive_remainder C A hC hA hrem _ (nthPrime_prime k)) hC.le
  rw [eulerCoordinate_eq_mass]
  have he : eulerMass (nthPrime k).primesBelow/C-log (nthPrime k : ℝ) =
      (eulerMass (nthPrime k).primesBelow-C*log (nthPrime k : ℝ))/C := by
    field_simp
  rw [he,abs_div,abs_of_pos hC]
  exact hh

/-- One pair of positive constants works for every strict prime prefix. -/
theorem exists_eulerCoordinate_log_remainder : ∃ C > (0 : ℝ), ∃ B > (0 : ℝ),
    ∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B := by
  obtain ⟨C,hC,A,hA,hrem⟩ := exists_initialEulerMass_additive_remainder
  exact ⟨C,hC,(2*A+C)/C,by positivity,
    eulerCoordinate_log_remainder C A hC hA.le hrem⟩

/-- A shift of at least twice the coordinate discrepancy preserves the
actual square cutoff whenever the effective lower level is at least two. -/
lemma eulerCoordinate_square_guard (C B b s : ℝ) (hC : 0 < C)
    (hB : ∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B)
    (hb : 2*B ≤ b) (hs : 2 ≤ s) (k : ℕ) :
    primeKeep nthPrime k (exp (s*eulerCoordinate C k+b)) := by
  have hlog := (abs_le.mp (hB k)).1
  have hT := eulerCoordinate_pos C hC k
  have hh : 2*log (nthPrime k : ℝ) ≤ s*eulerCoordinate C k+b := by
    nlinarith only [hlog,hb,hs,hT]
  have he := exp_le_exp.mpr hh
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hid : exp (2*log (nthPrime k : ℝ))=(nthPrime k : ℝ)^2 := by
    simpa only [Nat.cast_ofNat,exp_log hp0] using exp_nat_mul (log (nthPrime k : ℝ)) 2
  rw [hid] at he
  exact he

#print axioms eulerCoordinate_weight
#print axioms exists_eulerCoordinate_log_remainder
#print axioms eulerCoordinate_square_guard
end Erdos970.RecursiveSieve.Buchstab
