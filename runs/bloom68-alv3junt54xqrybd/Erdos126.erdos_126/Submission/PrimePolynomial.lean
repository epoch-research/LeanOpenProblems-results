import Submission.CoherentBound
import Submission.ResidueBlocks
import Submission.Extremal

/-!
# A quadratic bound for the number of vertices

The prime residue representation supplies coherent paired systems.  The
logarithmic sum kernel is conditionally negative, and factorization of a
sum versus a distance makes the full Gram kernel strictly negative off
its diagonal.  The finite paired-system estimate therefore bounds the
number of positive vertices by twelve times the square of the sum-prime
budget.  Erasing zero gives a uniform bound with additive constant two.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- On a pair whose sum primes are contained in `S`, the excess kernel
is the logarithm of the sum minus the common prime baseline. -/
theorem primeExcessKernel_eq_log_sub_baseline (a : ι → ℕ) (S : Finset ℕ)
    (i j : ι) (hS : (a i + a j).primeFactors ⊆ S) :
    primeExcessKernel a S i j =
      Real.log ((a i + a j : ℕ) : ℝ) - primeBaselineSum a S i j := by
  have hfac : (∑ p ∈ S, Real.log (p : ℝ) * ((a i + a j).factorization p : ℝ)) =
      Real.log ((a i + a j : ℕ) : ℝ) := by
    simpa only [mul_comm] using sum_factorization_log_eq_log_of_subset (a i + a j) S hS
  unfold primeExcessKernel
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hfac]
  rfl

omit [Fintype ι] in
/-- The paired residue representation has a strictly negative off-diagonal
Gram kernel whenever all sum primes have been included. -/
theorem gram_negative_of_residue_representation
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (hinj : Function.Injective a)
    (S : Finset ℕ) (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    {τ : Type*} [Fintype τ] (b : τ → Paired.Block ι)
    (hcross : ∀ i j, Paired.crossSum b i j = primeExcessKernel a S i j)
    (hdiag : ∀ i j, a i ≠ a j → Paired.diagSum b i j ≤
      (∑ p ∈ S, Real.log (p : ℝ) * ((Nat.dist (a i) (a j)).factorization p : ℝ)) -
        primeBaselineSum a S i j) :
    ∀ i j, i ≠ j → Paired.gramSum b i j < 0 := by
  intro i j hij
  have hlabels : a i ≠ a j := fun h => hij (hinj h)
  have hdpos : 0 < Nat.dist (a i) (a j) := Nat.dist_pos_of_ne hlabels
  have hdlt : Nat.dist (a i) (a j) < a i + a j := by
    have hi := ha i
    have hj := ha j
    unfold Nat.dist
    omega
  have hlog : Real.log ((Nat.dist (a i) (a j) : ℕ) : ℝ) <
      Real.log ((a i + a j : ℕ) : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hdpos) (by exact_mod_cast hdlt)
  have hdlog : (∑ p ∈ S, Real.log (p : ℝ) *
      ((Nat.dist (a i) (a j)).factorization p : ℝ)) ≤
        Real.log ((Nat.dist (a i) (a j) : ℕ) : ℝ) := by
    simpa only [mul_comm] using sum_factorization_log_le_log (Nat.dist (a i) (a j)) S
  have hd := hdiag i j hlabels
  have hc := hcross i j
  rw [primeExcessKernel_eq_log_sub_baseline a S i j (hsupport i j hij)] at hc
  unfold Paired.gramSum
  linarith

/-- A finite injective positive natural family has fewer than `12 * |S|²`
vertices when `S` contains every prime factor of every distinct pair sum. -/
theorem card_lt_twelve_sq_sum_primes
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (hinj : Function.Injective a)
    (hn : 2 ≤ Fintype.card ι) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    (Fintype.card ι : ℝ) < 12 * (S.card : ℝ) ^ 2 := by
  classical
  obtain ⟨τ, inst, b, owner, hb, hcoh, hcross, hdiag⟩ :=
    ResidueBlocks.exists_representation a ha S hprime
  letI := inst
  have heq : Paired.crossSum b = primeExcessKernel a S :=
    funext fun i => funext fun j => hcross i j
  have hcnd : Paired.CND (Paired.crossSum b) := by
    rw [heq]
    exact primeExcessKernel_cnd a ha S hsupport
  have hoff := gram_negative_of_residue_representation a ha hinj S hsupport b hcross hdiag
  have hbound := Paired.polynomial_bound_of_coherent b owner hn hb hcnd hoff hcoh
  simpa only [Fintype.card_coe] using hbound

/-- The positive part of a natural finset is controlled by the support
of the original off-diagonal sum product. -/
theorem card_erase_zero_lt_twelve_sq_supportCount (A : Finset ℕ)
    (hA : 2 ≤ (A.erase 0).card) :
    (A.erase 0).card < 12 * supportCount A ^ 2 := by
  classical
  let S := (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors
  have hcard : 2 ≤ Fintype.card ↥(A.erase 0) := by simpa only [Fintype.card_coe] using hA
  have hpos (i : ↥(A.erase 0)) : 0 < (i : ℕ) := by
    have hi := (Finset.mem_erase.1 i.property).1
    omega
  have hs (i j : ↥(A.erase 0)) (hij : i ≠ j) :
      ((i : ℕ) + (j : ℕ)).primeFactors ⊆ S := by
    apply primeFactors_add_subset
    apply Finset.mem_offDiag.2
    refine ⟨(Finset.mem_erase.1 i.property).2, (Finset.mem_erase.1 j.property).2, ?_⟩
    exact fun h => hij (Subtype.ext h)
  have hbound := card_lt_twelve_sq_sum_primes (fun i : ↥(A.erase 0) => (i : ℕ))
    hpos Subtype.val_injective hcard S (fun p hp => Nat.prime_of_mem_primeFactors hp) hs
  have hreal : ((A.erase 0).card : ℝ) < 12 * (supportCount A : ℝ) ^ 2 := by
    simpa only [Fintype.card_coe, S, supportCount] using hbound
  exact_mod_cast hreal

/-- Uniform quadratic cardinality bound, including empty sets, singletons,
and the exceptional zero-support pair `{0, 1}`. -/
theorem quadratic_cardinality_bound (A : Finset ℕ) :
    A.card ≤ 12 * supportCount A ^ 2 + 2 := by
  have hcard : A.card ≤ (A.erase 0).card + 1 := by
    by_cases h0 : 0 ∈ A
    · have he := Finset.card_erase_add_one h0
      omega
    · rw [Finset.erase_eq_of_notMem h0]
      omega
  by_cases hA : 2 ≤ (A.erase 0).card
  · have hbound := card_erase_zero_lt_twelve_sq_supportCount A hA
    omega
  · omega

end Erdos126Aux
