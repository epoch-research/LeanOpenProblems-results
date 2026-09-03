import Submission.BlockPrimeCount
import Submission.CyclicCorrelationTransfer

/-! Uniform finite prime-gap correlation transfer. The result controls the
conditional-minus-unconditional discrepancy, not either correlation by itself. -/
namespace Erdos371.FiniteInformation
open Finset BlockPrimes EntropyScales

instance halfBlockPrime_neZero (H : ℕ) (p : halfBlockPrimes H) : NeZero (p : ℕ) :=
  ⟨((mem_halfBlockPrimes.mp p.property).1).ne_zero⟩

lemma halfBlockPrimes_pairwise_coprime (H : ℕ) :
    Pairwise (fun p q : halfBlockPrimes H => Nat.Coprime (p : ℕ) (q : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (mem_halfBlockPrimes.mp p.property).1
    (mem_halfBlockPrimes.mp q.property).1).mpr
  exact fun he => hpq (Subtype.ext he)

lemma halfBlockPrimes_prod_dvd_primorial (H : ℕ) :
    (∏ p : halfBlockPrimes H, (p : ℕ)) ∣ primorial H := by
  have he : (∏ p : halfBlockPrimes H, (p : ℕ)) = ∏ p ∈ halfBlockPrimes H, p :=
    prod_coe_sort (halfBlockPrimes H) id
  rw [he]
  apply prod_dvd_prod_of_subset (halfBlockPrimes H) ((H+1).primesBelow) id
  intro p hp
  obtain ⟨hprime,hpH⟩ := mem_halfBlockPrimes.mp hp
  exact Nat.mem_primesBelow.mpr ⟨by omega,hprime⟩

/-- For every finite alphabet and tolerance, there is a bounded list of scales
such that one scale works simultaneously for EVERY bounded pair observable.
There is no primality-distribution hypothesis hidden in this theorem. -/
theorem cyclic_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (N : ℕ) [NeZero N],
      (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N → ∀ L : ZMod N → A,
        ∃ n < K, ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
          |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n), cyclicGapDiscrepancy N p L C) /
            (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  let δ : ℝ := ε^2 * Real.log 2 / 64
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hdec⟩ := cyclic_prime_residue_entropy_decrement (A := A) H₀ (by omega) δ hδ
  refine ⟨K,hK,?_⟩
  intro N _ hd L
  obtain ⟨n,hn,hinfo⟩ := hdec N hd L
  refine ⟨n,hn,?_⟩
  intro C hC
  let H := factorialScale H₀ n
  have hH : 8 ≤ H := hH₀.trans (factorialScale_ge H₀ n)
  have hnon := halfBlockPrimes_nonempty H (by omega)
  letI : Nonempty (halfBlockPrimes H) := ⟨⟨hnon.choose, hnon.choose_spec⟩⟩
  have hM : primorial H ∣ N :=
    (dvd_prod_of_mem (fun n => primorial (factorialScale H₀ n)) (mem_range.mpr hn)).trans hd
  have hb := cyclic_gap_average_sq_le_information (fun p : halfBlockPrimes H => (p : ℕ))
    (halfBlockPrimes_pairwise_coprime H) N (primorial H) H hM
    (halfBlockPrimes_prod_dvd_primorial H)
    (fun p => (mem_halfBlockPrimes.mp p.property).2) L C hC
  rw [sum_coe_sort (halfBlockPrimes H) (fun p => cyclicGapDiscrepancy N p L C)] at hb
  simp only [Fintype.card_coe] at hb
  have hcard : 0 < ((halfBlockPrimes H).card : ℝ) := by
    exact_mod_cast card_pos.mpr hnon
  have hlower := halfBlockPrimes_card_lower H hH
  have hscaled := mul_le_mul_of_nonneg_left hlower (by positivity : (0 : ℝ) ≤ ε^2/8)
  have hbound : δ * H / Real.log (H : ℝ) ≤ (ε^2/8)*((halfBlockPrimes H).card : ℝ) := by
    convert hscaled using 1
    dsimp [δ]
    ring
  have hi : mutualInformation
      (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight 1) L (cyclicResidue N (primorial H)) H) <
        (ε^2/8)*((halfBlockPrimes H).card : ℝ) := hinfo.trans_le hbound
  have hr : 8 * mutualInformation
      (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight 1) L (cyclicResidue N (primorial H)) H) /
        ((halfBlockPrimes H).card : ℝ) < ε^2 := by
    apply (div_lt_iff₀ hcard).mpr
    nlinarith
  have hs := hb.trans_lt hr
  change |(∑ p ∈ halfBlockPrimes H, cyclicGapDiscrepancy N p L C) /
    ((halfBlockPrimes H).card : ℝ)| < ε
  nlinarith [sq_abs ((∑ p ∈ halfBlockPrimes H, cyclicGapDiscrepancy N p L C) /
    ((halfBlockPrimes H).card : ℝ))]

#print axioms cyclic_prime_gap_transfer
end Erdos371.FiniteInformation
