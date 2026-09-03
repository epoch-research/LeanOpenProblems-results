import Submission.QuarterLaplaceDefs
import Submission.CyclicSieveCount

/-! Exact transfer of the five-prime cumulative counting formula to genuine
uniform residue phases. The finite numerical certificate is separate. -/
namespace Erdos970.GapAverages.QuarterExample
open Finset Real ParityDiscrepancy

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def primes : Finset ℕ := {3,7,11,19,23}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]

lemma prime_product : primeProduct primes = 100947 := by norm_num [primeProduct, primes]

lemma fullPrefix_fast (x : ℕ) : CyclicSieve.fullPrefix primes x = fastPrefix x := by
  have hs : ({23} : Finset ℕ).powerset = {∅,{23}} := by decide
  simp [CyclicSieve.fullPrefix, primes, sum_powerset_insert, hs, primeProduct,
    fastPrefix, KernelArithmetic.quotient_eq_div, positiveDivisors, negativeDivisors]
  ring

lemma fastCount_eq (m a : ℕ) : fastCount m a = CyclicSieve.natCount primes m a := by
  rw [fastCount, ← fullPrefix_fast, ← fullPrefix_fast]
  exact CyclicSieve.fullPrefix_diff_toNat primes primes_prime m a

lemma laplace_fast (t : ℝ) (m : ℕ) : countLaplace primes t m =
    (∑ a ∈ range 100947, exp (-t*(fastCount m a : ℝ))) / 100947 := by
  rw [CyclicSieve.cyclic_laplace primes primes_prime, prime_product]
  simp only [fastCount_eq, Nat.cast_ofNat]

lemma sum_blocks {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n m : ℕ) :
    (∑ a ∈ range (n*m), f a) = ∑ b ∈ range m, ∑ a ∈ range n, f (n*b+a) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma weightedChunks_eq (m B : ℕ) : weightedChunks m B =
    ∑ a ∈ range 100947, 2^(B-fastCount m a) := by
  rw [show 100947 = 100*1009+47 by norm_num, sum_range_add, sum_blocks]
  rfl

lemma scaled_laplace (m B : ℕ) (hB : ∀ a ∈ range 100947, fastCount m a ≤ B) :
    (2 : ℝ)^B * countLaplace primes (log 2) m = (weightedChunks m B : ℝ)/100947 := by
  rw [laplace_fast, ← mul_div_assoc, mul_sum, weightedChunks_eq]
  have he (a : ℕ) (ha : a ∈ range 100947) :
      (2 : ℝ)^B * exp (-log 2*(fastCount m a : ℝ)) =
        (2 : ℝ)^(B-fastCount m a) := by
    rw [show -log 2*(fastCount m a : ℝ) = (fastCount m a : ℝ)*(-log 2) by ring,
      exp_nat_mul, exp_neg, exp_log (by norm_num : (0 : ℝ) < 2), inv_pow,
      ← pow_sub₀ (2 : ℝ) (by norm_num) (hB a ha)]
  rw [show (∑ a ∈ range 100947, (2 : ℝ)^B * exp (-log 2*(fastCount m a : ℝ))) =
      ∑ a ∈ range 100947, (2 : ℝ)^(B-fastCount m a) from sum_congr rfl he]
  apply congrArg (fun x : ℝ => x/100947)
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

#print axioms fullPrefix_fast
#print axioms scaled_laplace
end Erdos970.GapAverages.QuarterExample
