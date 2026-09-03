import Submission.BuchstabQuantitativeProfile
import Submission.BuchstabUniformVariableTail

/-! Quantitative one-step main-term transfer with every remainder displayed.
The hypotheses on the actual child sums are explicit: these lemmas do not
assert a uniform comparison of all recursive depths with continuous profiles. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg ContinuousBuchstab MeasureTheory Set
set_option maxHeartbeats 1700000

noncomputable def profileQuadratureRemainder (C A s M L B : ℝ) : ℝ :=
  (4*(A+C)/(C*((s/M)*L)))*(1+1/(s/M))*B

/-- Exact decomposition into a terminal part and a profile-controlled part,
with a quantitative mesh-free error on the latter. -/
theorem quantitative_complete_prime_sum (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (k : ℕ) (s M : ℝ) (hs : 1 ≤ s) (hsM : s < M)
    (hL : 2 ≤ log (nthPrime k : ℝ))
    (hcut : 2 ≤ (s/M)*log (nthPrime k : ℝ))
    (hlarge : 2*(A+C) ≤ C*((s/M)*log (nthPrime k : ℝ)))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (s-1)))
    (hf0 : ∀ x, s-1 ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (s-1)))
    (F : ℕ → ℝ) (hF0 : ∀ p, p.Prime → 0 ≤ F p) (T : ℝ)
    (htail : eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), F p) ≤ T)
    (hprofile : ∀ p ∈ (Finset.Ioc (terminalCut M (s*log (nthPrime k : ℝ)))
      (nthPrime k)).filter Nat.Prime,
      F p ≤ ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*
        f (s*log (nthPrime k : ℝ)/log (p : ℝ)-1)) :
    eulerMass (nthPrime k).primesBelow*(∑ p ∈ (nthPrime k).primesBelow, F p) ≤
      T+tailIntegral f (s-1)/s+
        profileQuadratureRemainder C A s M (log (nthPrime k : ℝ)) (f (s-1)) := by
  let L := log (nthPrime k : ℝ)
  let Q := (Finset.Ioc (terminalCut M (s*L)) (nthPrime k)).filter Nat.Prime
  have hsplit : (∑ p ∈ (nthPrime k).primesBelow, F p) ≤
      (∑ p ∈ terminalPart M k (s*L), F p)+(∑ p ∈ Q, F p) := by
    have hh := sum_filter_add_sum_filter_not (nthPrime k).primesBelow
      (fun p => p ≤ terminalCut M (s*L)) F
    change _ ≤ (∑ p ∈ (nthPrime k).primesBelow.filter (fun p => p ≤ terminalCut M (s*L)), F p)+_
    rw [← hh]
    apply add_le_add le_rfl
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,hnot⟩ := mem_filter.mp hp
      obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hpk.le⟩,hpp⟩
    · intro p hp _
      exact hF0 p (mem_filter.mp hp).2
  have hQ0 : 0 ≤ ∑ p ∈ Q, F p :=
    sum_nonneg (fun p hp => hF0 p (mem_filter.mp hp).2)
  have hE : 0 ≤ eulerMass (nthPrime k).primesBelow :=
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  have hpart := mul_le_mul_of_nonneg_left hsplit hE
  rw [mul_add] at hpart
  have hEuler : eulerMass (nthPrime k).primesBelow ≤ initialEulerMass (nthPrime k) :=
    eulerMass_strict_prefix_le _ (nthPrime_prime k)
  have hqcomp := sum_le_sum hprofile
  have hqmass := mul_le_mul_of_nonneg_left hqcomp (initialEulerMass_pos (nthPrime k)).le
  have hquad := prime_profile_le_tailIntegral C A hC hA hrem s M L hs hsM hL hcut hlarge f hf hf0 hfi
  have hroot : expFloor 1 L=nthPrime k := by
    rw [expFloor,one_mul,exp_log (by exact_mod_cast (nthPrime_prime k).pos),Nat.floor_natCast]
  have hterm : expFloor (s/M) L=terminalCut M (s*L) := by
    unfold expFloor terminalCut
    congr 2
    ring
  rw [hroot,hterm] at hquad
  change initialEulerMass (nthPrime k)*
      (∑ p ∈ Q, ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)) ≤ _ at hquad
  have hmid := (mul_le_mul_of_nonneg_right hEuler hQ0).trans (hqmass.trans hquad)
  change _ ≤ T+tailIntegral f (s-1)/s+profileQuadratureRemainder C A s M L (f (s-1))
  dsimp only [profileQuadratureRemainder]
  linarith only [hpart,htail,hmid]

/-- One prime threshold works simultaneously for all depths and terminal
cutoffs. Given the displayed actual child-excess bound, the lower step has
exactly these two losses: terminal allowance and arithmetic quadrature. -/
theorem exists_quantitative_lower_step (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A) :
    ∃ H : ℕ, ∀ n k : ℕ, H ≤ nthPrime k → ∀ s M : ℝ, 2 ≤ s → 13 ≤ M → s < M →
      2 ≤ log (nthPrime k : ℝ) → 2 ≤ (s/M)*log (nthPrime k : ℝ) →
      2*(A+C) ≤ C*((s/M)*log (nthPrime k : ℝ)) →
      ∀ f : ℝ → ℝ, AntitoneOn f (Ici (s-1)) →
        (∀ x, s-1 ≤ x → 0 ≤ f x) → IntegrableOn f (Ioi (s-1)) →
      (∀ p ∈ (Finset.Ioc (terminalCut M (s*log (nthPrime k : ℝ))) (nthPrime k)).filter Nat.Prime,
        primeUpperExcess n (s*log (nthPrime k : ℝ)) p ≤
          ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*log (nthPrime k : ℝ)/log (p : ℝ)-1)) →
      prefixDensity primeMarginal k*
        (1-tailIntegral f (s-1)/s-terminalAllowance initialTailCoefficient M/s-
          profileQuadratureRemainder C A s M (log (nthPrime k : ℝ)) (f (s-1))) ≤
        referenceLower n k (exp (s*log (nthPrime k : ℝ))) := by
  obtain ⟨H,hH⟩ := exists_uniform_variable_upper_tail
  refine ⟨H,fun n k hk s M hs hM hsM hL hcut hlarge f hf hf0 hfi hprofile => ?_⟩
  have hs1 : 1 ≤ s := by linarith
  have hsum := quantitative_complete_prime_sum C A hC hA hrem k s M hs1 hsM hL hcut hlarge
    f hf hf0 hfi (primeUpperExcess n (s*log (nthPrime k : ℝ))) (primeUpperExcess_nonneg n _)
    (terminalAllowance initialTailCoefficient M/s) (hH M hM n k hk s hs1) hprofile
  apply referenceLower_ge_of_normalized_excess n k _ _ (primeKeep_exp k s hs)
  convert hsum using 1 <;> ring

/-- The upper step analog, with the actual child deficit as an explicit
hypothesis rather than an assumed continuous approximation. -/
theorem exists_quantitative_upper_step (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A) :
    ∃ H : ℕ, ∀ n k : ℕ, H ≤ nthPrime k → ∀ s M : ℝ, 1 ≤ s → 13 ≤ M → s < M →
      2 ≤ log (nthPrime k : ℝ) → 2 ≤ (s/M)*log (nthPrime k : ℝ) →
      2*(A+C) ≤ C*((s/M)*log (nthPrime k : ℝ)) →
      ∀ f : ℝ → ℝ, AntitoneOn f (Ici (s-1)) →
        (∀ x, s-1 ≤ x → 0 ≤ f x) → IntegrableOn f (Ioi (s-1)) →
      (∀ p ∈ (Finset.Ioc (terminalCut M (s*log (nthPrime k : ℝ))) (nthPrime k)).filter Nat.Prime,
        primeDeficit n (s*log (nthPrime k : ℝ)) p ≤
          ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*log (nthPrime k : ℝ)/log (p : ℝ)-1)) →
      referenceUpper (n+1) k (exp (s*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*
          (1+tailIntegral f (s-1)/s+terminalAllowance lowerTailCoefficient M/s+
            profileQuadratureRemainder C A s M (log (nthPrime k : ℝ)) (f (s-1))) := by
  obtain ⟨H,hH⟩ := exists_uniform_variable_lower_tail
  refine ⟨H,fun n k hk s M hs hM hsM hL hcut hlarge f hf hf0 hfi hprofile => ?_⟩
  have hsum := quantitative_complete_prime_sum C A hC hA hrem k s M hs hsM hL hcut hlarge
    f hf hf0 hfi (primeDeficit n (s*log (nthPrime k : ℝ))) (primeDeficit_nonneg n _)
    (terminalAllowance lowerTailCoefficient M/s) (hH M hM n k hk s hs) hprofile
  apply referenceUpper_succ_le_of_normalized_deficit n k
  convert hsum using 1 <;> ring

#print axioms quantitative_complete_prime_sum
#print axioms exists_quantitative_lower_step
#print axioms exists_quantitative_upper_step
end Erdos970.RecursiveSieve.Buchstab
