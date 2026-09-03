import Submission.BuchstabBaseProfile
import Submission.EulerMassScaling

/-! Exact conversion between indexed first-prime coordinates and arithmetic
prime-prefix sums. It connects the normalized source profiles to the verified
Buchstab engine, without an assumption of prime-set extremality. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k
noncomputable def primeMarginal (k : ℕ) : ℝ := 1/(nthPrime k : ℝ)

lemma nthPrime_prime (k : ℕ) : (nthPrime k).Prime := Nat.prime_nth_prime k
lemma nthPrime_strictMono : StrictMono nthPrime := Nat.nth_strictMono Nat.infinite_setOf_prime
lemma primeMarginal_pos (k : ℕ) : 0 < primeMarginal k := by
  have hp : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  exact one_div_pos.mpr hp
lemma primeMarginal_lt_one (k : ℕ) : primeMarginal k < 1 := by
  have hp : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  exact (div_lt_one (by linarith)).mpr hp

lemma nthPrime_prefix_image (k : ℕ) :
    (univ.image (fun i : Fin k => nthPrime i.val)) = (nthPrime k).primesBelow := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact Nat.mem_primesBelow.mpr ⟨nthPrime_strictMono i.isLt,nthPrime_prime i.val⟩
  · intro hp
    obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
    let i := Nat.count Nat.Prime p
    have he : nthPrime i = p := Nat.nth_count hpp
    have hi : i < k := by
      by_contra hn
      have hh := nthPrime_strictMono.monotone (show k ≤ i by omega)
      rw [he] at hh
      exact hpk.not_ge hh
    exact mem_image.mpr ⟨⟨i,hi⟩,mem_univ _,he⟩

lemma nthPrime_prefix_sum (f : ℕ → ℝ) (k : ℕ) :
    (∑ i : Fin k, f (nthPrime i.val)) = ∑ p ∈ (nthPrime k).primesBelow, f p := by
  have hinj : Function.Injective (fun i : Fin k => nthPrime i.val) :=
    nthPrime_strictMono.injective.comp Fin.val_injective
  rw [← nthPrime_prefix_image, sum_image hinj.injOn]

lemma nthPrime_prefix_density (k : ℕ) :
    prefixDensity primeMarginal k = 1/eulerMass (nthPrime k).primesBelow := by
  have hinj : Function.Injective (fun i : Fin k => nthPrime i.val) :=
    nthPrime_strictMono.injective.comp Fin.val_injective
  rw [inverse_eulerMass, ← nthPrime_prefix_image, prod_image hinj.injOn,
    Fin.prod_univ_eq_prod_range (fun i => 1-1/(nthPrime i : ℝ)) k]
  rfl

lemma nthPrime_prefix_density_pos (k : ℕ) : 0 < prefixDensity primeMarginal k := by
  rw [nthPrime_prefix_density]
  exact one_div_pos.mpr (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2))

lemma nthPrime_normalizer (k N : ℕ) :
    normalizer (fun i : Fin k => primeMarginal i.val)
      (divisorSupport (fun i : Fin k => nthPrime i.val) N) =
      primeNormalizer (nthPrime k).primesBelow N := by
  unfold primeMarginal
  rw [normalizer_eq_smallDivisorFamily (fun i : Fin k => nthPrime i.val) (fun i => nthPrime_prime i.val)
    (nthPrime_strictMono.injective.comp Fin.val_injective), nthPrime_prefix_image]
  rfl

/-- Normalized ceiling-cutoff bounds genuinely dominate the enlarged indexed
base source at the same divisor exponent. -/
theorem scaled_base_le_normalized_profile (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    scaledSelbergBase nthPrime k (exp (s*log (nthPrime k : ℝ))) ≤
      prefixDensity primeMarginal k * buchstabBaseRatio (nthPrime k) s := by
  have hD : 1 ≤ exp (s*log (nthPrime k : ℝ)) :=
    one_le_exp (mul_nonneg hs (log_natCast_nonneg _))
  have hh := scaledSelbergBase_le_ceiling nthPrime nthPrime_prime k _ hD
  rw [← buchstabPrimeCutoff_ceiling_sqrt] at hh
  change scaledSelbergBase nthPrime k _ ≤
    1/normalizer (fun i : Fin k => primeMarginal i.val)
      (divisorSupport (fun i : Fin k => nthPrime i.val) (buchstabPrimeCutoff (nthPrime k) s)) at hh
  rw [nthPrime_normalizer] at hh
  rw [nthPrime_prefix_density, buchstabBaseRatio]
  have hE : eulerMass (nthPrime k).primesBelow ≠ 0 :=
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).ne'
  have he : (1/eulerMass (nthPrime k).primesBelow)*
      (eulerMass (nthPrime k).primesBelow/primeNormalizer (nthPrime k).primesBelow (buchstabPrimeCutoff (nthPrime k) s)) =
      1/primeNormalizer (nthPrime k).primesBelow (buchstabPrimeCutoff (nthPrime k) s) := by field_simp
  rwa [he]

/-- Exact arithmetic measure underlying every subsequent sector comparison. -/
lemma nthPrime_density_weighted_sum (f : ℕ → ℝ) (k : ℕ) :
    (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*f (nthPrime i.val)) =
      ∑ p ∈ (nthPrime k).primesBelow, ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f p := by
  simp_rw [nthPrime_prefix_density]
  exact nthPrime_prefix_sum (fun p => ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f p) k

#print axioms scaled_base_le_normalized_profile
#print axioms nthPrime_density_weighted_sum
end Erdos970.RecursiveSieve.Buchstab
