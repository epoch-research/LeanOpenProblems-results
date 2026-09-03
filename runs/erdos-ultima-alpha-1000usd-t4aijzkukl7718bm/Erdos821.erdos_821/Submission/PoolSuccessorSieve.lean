import Submission.PoolCofactorScales
import Submission.CofactorSuccessorSieve

/-!
# A successor sieve retaining the multiplier pool

The discrepancy is summed only over products of sieve primes. Unit support
is imposed only when the analytic mean is applied, not in the sieve identity.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Sieve
set_option maxHeartbeats 4000000

noncomputable def poolSieveModuli (J : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (J.powerset.filter (fun U => (∏ p ∈ U, p) ≤ z^2)).image (fun U => ∏ p ∈ U, p)

lemma poolSieveModuli_subset (J : Finset ℕ) (z : ℕ) (hJ : ∀ p ∈ J, p.Prime) :
    poolSieveModuli J z ⊆ Icc 1 (z^2) := by
  intro d hd
  obtain ⟨U,hU,rfl⟩ := mem_image.mp hd
  obtain ⟨hU,hz⟩ := mem_filter.mp hU
  exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hJ p (mem_powerset.mp hU hp)).pos),hz⟩

lemma coprime_poolSieveModuli (c : ℕ) (J : Finset ℕ) (z : ℕ)
    (hc : ∀ p ∈ J, c.Coprime p) : ∀ d ∈ poolSieveModuli J z, c.Coprime d := by
  intro d hd
  obtain ⟨U,hU,rfl⟩ := mem_image.mp hd
  exact Nat.coprime_prod_right_iff.mpr
    (fun p hp => hc p (mem_powerset.mp (mem_filter.mp hU).1 hp))

noncomputable def poolPrimeSuccessorWeight (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (A B N z : ℕ) : ℝ :=
  ∑ x ∈ (P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N)) with
    (x.1*x.2.1*x.2.2+1).Prime ∧ z<x.1*x.2.1*x.2.2+1, f x.2.2

noncomputable def poolSuccessorDiscrepancy (f : ArithmeticFunction ℝ) (P : Finset ℕ)
    (A B N d : ℕ) : ℝ :=
  |poolCofactorWeight f P d (-1) A B N-
    (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)|

lemma pool_successor_congruence (d c a n : ℕ) :
    (((-1 : (ZMod d)ˣ) : ZMod d)*(c : ZMod d))*(a : ZMod d)*(n : ZMod d)=1 ↔
      d ∣ c*a*n+1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Units.val_neg,Units.val_one]
  constructor <;> intro h <;> linear_combination -h

lemma pool_successor_support_count (f : ArithmeticFunction ℝ) (P J : Finset ℕ)
    (A B N : ℕ) (hJ : ∀ p ∈ J, p.Prime) :
    (∑ x ∈ P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N),
      if ∀ p ∈ J, p ∣ x.1*x.2.1*x.2.2+1 then f x.2.2 else 0) =
        poolCofactorWeight f P (∏ p ∈ J, p) (-1) A B N := by
  simp only [poolCofactorWeight,sum_product,pool_successor_congruence,prod_primes_dvd_iff J hJ]

lemma pool_prime_successor_le_sifted (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (P J : Finset ℕ) (A B N z : ℕ) (hJ : ∀ p ∈ J, p.Prime ∧ p ≤ z) :
    poolPrimeSuccessorWeight f P A B N z ≤
      ∑ x ∈ (P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N)) with
        ∀ p ∈ J, ¬p ∣ x.1*x.2.1*x.2.2+1, f x.2.2 := by
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hf x.2.2)
  intro x hx
  obtain ⟨hxI,hprime,hz⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨hxI,?_⟩
  intro p hp hpd
  have he := (Nat.prime_dvd_prime_iff_eq (hJ p hp).1 hprime).mp hpd
  have hh := (hJ p hp).2
  omega

/-- The finite sieve keeps the subset of relevant moduli rather than
requiring distribution at nonsmooth moduli. -/
theorem exists_pool_successor_sieve_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → ∀ P J : Finset ℕ, ∀ A B N z : ℕ, 1 ≤ z →
      (∀ p ∈ J, p.Prime ∧ p ≤ z) →
      poolPrimeSuccessorWeight f P A B N z ≤
        (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N*(oneRootDenominator J z)⁻¹+
          C*((z^2 : ℕ) : ℝ)^ε*
            ∑ d ∈ poolSieveModuli J z, poolSuccessorDiscrepancy f P A B N d := by
  obtain ⟨C,hC,HC⟩ := exists_weighted_selberg_mean_bound ε hε
  refine ⟨C,hC,?_⟩
  intro f hf P J A B N z hz hJ
  let S := poolSieveModuli J z
  let R : ℕ → ℝ := fun d => if d ∈ S then poolSuccessorDiscrepancy f P A B N d else 0
  have hS : S ⊆ Icc 1 (z^2) := poolSieveModuli_subset J z (fun p hp => (hJ p hp).1)
  have hR : ∀ d ∈ Icc 1 (z^2), 0 ≤ R d := by
    intro d hd
    dsimp [R,poolSuccessorDiscrepancy]
    split_ifs <;> positivity
  have hdist : ∀ U ∈ J.powerset, (∏ p ∈ U, p) ≤ z^2 →
      |(∑ x ∈ P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N),
        if ∀ p ∈ U, p ∣ x.1*x.2.1*x.2.2+1 then f x.2.2 else 0)-
          (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N/((∏ p ∈ U, p : ℕ) : ℝ)| ≤
            R (∏ p ∈ U, p) := by
    intro U hU hUz
    have hmem : (∏ p ∈ U, p) ∈ S := mem_image.mpr ⟨U,mem_filter.mpr ⟨hU,hUz⟩,rfl⟩
    rw [pool_successor_support_count f P U A B N (fun p hp => (hJ p (mem_powerset.mp hU hp)).1)]
    simp only [R,if_pos hmem,poolSuccessorDiscrepancy,le_refl]
  have hsieve := HC (ℕ × (ℕ × ℕ)) (P ×ˢ (Icc (A+1) B ×ˢ Icc 1 N)) (fun x => f x.2.2)
    (fun x _ => hf x.2.2) J (fun p hp => (hJ p hp).1) z hz
    (fun p x => p ∣ x.1*x.2.1*x.2.2+1)
    ((P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N) R hR hdist
  have hsum : (∑ d ∈ Icc 1 (z^2), R d) = ∑ d ∈ S, poolSuccessorDiscrepancy f P A B N d := by
    dsimp [R]
    rw [← sum_filter]
    congr 1
    ext d
    constructor
    · intro hd
      exact (mem_filter.mp hd).2
    · intro hd
      exact mem_filter.mpr ⟨hS hd,hd⟩
  rw [hsum] at hsieve
  apply (pool_prime_successor_le_sifted f hf P J A B N z hJ).trans
  convert hsieve using 1
  simp only [sum_filter]
  apply sum_congr rfl
  intro x hx
  by_cases hh : ∀ p ∈ J, ¬p ∣ x.1*x.2.1*x.2.2+1
  · rw [if_pos hh,if_pos hh]
  · rw [if_neg hh,if_neg hh]

/-- Unit support follows from avoiding the individual sieve primes, even
when their products exceed the cutoff N. -/
lemma pool_sieve_unit_support (f : ArithmeticFunction ℝ) (P J : Finset ℕ) (N z : ℕ)
    (hP : ∀ c ∈ P, ∀ p ∈ J, c.Coprime p)
    (hf : ∀ n ∈ Icc 1 N, f n ≠ 0 → ∀ p ∈ J, n.Coprime p) :
    (∀ d ∈ poolSieveModuli J z, ∀ c ∈ P, c.Coprime d) ∧
      (∀ d ∈ poolSieveModuli J z, ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) := by
  constructor
  · intro d hd c hc
    exact coprime_poolSieveModuli c J z (hP c hc) d hd
  · intro d hd n hn hn0
    exact coprime_poolSieveModuli n J z (hf n hn hn0) d hd

end Erdos821.AnalyticSieve
