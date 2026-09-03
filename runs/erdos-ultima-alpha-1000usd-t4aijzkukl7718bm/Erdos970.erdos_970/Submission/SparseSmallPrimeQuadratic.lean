import Submission.CoreTailSieve

/-! A quadratic bound when the set of primes at most twice the cardinality
budget is small enough for exact inclusion-exclusion. This restriction is not
known for arbitrary prime sets and is not asserted in Erdős 970. -/
namespace Erdos970.CoreTailSieve
open Finset

lemma large_prime_tail_half (R : Finset ℕ) (k : ℕ) (hk : 0 < k)
    (hcard : R.card ≤ k) (hlarge : ∀ p ∈ R, 2 * k < p) :
    (∑ p ∈ R, 1 / (p : ℝ)) ≤ 1 / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htwo : (0 : ℝ) < 2 * k := by positivity
  calc
    _ ≤ ∑ _p ∈ R, (1 : ℝ) / (2 * k) := by
      apply sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le htwo
      exact_mod_cast (hlarge p hp).le
    _ = (R.card : ℝ) / (2 * k) := by simp [div_eq_mul_inv]
    _ ≤ (k : ℝ) / (2 * k) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) htwo.le
    _ = 1 / 2 := by field_simp

/-- The exact restricted quadratic estimate: s counts the primes at most 2*k.
The hypothesis (s+1)*2^s<=k is retained explicitly. -/
theorem cover_length_quadratic_of_sparse_small (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (k : ℕ) (hk : 0 < k) (hcard : P.card ≤ k)
    (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p])
    (hsmall : ((P.filter (fun p => p ≤ 2 * k)).card + 1) *
      2 ^ (P.filter (fun p => p ≤ 2 * k)).card ≤ k) :
    m ≤ 4 * k ^ 2 := by
  classical
  let Q := P.filter (fun p => p ≤ 2 * k)
  let R := P.filter (fun p => ¬p ≤ 2 * k)
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hR : ∀ p ∈ R, p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hdis : Disjoint Q R := by
    apply disjoint_left.mpr
    intro p hpQ hpR
    exact (mem_filter.mp hpR).2 (mem_filter.mp hpQ).2
  have hunion : Q ∪ R = P := filter_union_filter_not_eq _ _
  have hRc : R.card ≤ k := (card_filter_le P _).trans hcard
  have htail := large_prime_tail_half R k hk hRc (fun p hp => by
    have hh := (mem_filter.mp hp).2
    omega)
  have hm := cover_length_le Q R hQ hR hdis r m (by simpa [hunion] using hcover) htail
  have hsmall' : (Q.card + 1) * 2 ^ Q.card ≤ k := hsmall
  have hmul := Nat.mul_le_mul hsmall' (show R.card + 1 ≤ k + 1 by omega)
  have hk' : k + 1 ≤ 2 * k := by omega
  nlinarith

/-- A genuinely superquadratic cover would necessarily have a nonsparse small
core. This necessary condition is not claimed to be sufficient for a cover. -/
theorem small_core_necessary (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : 0 < k) (hcard : P.card ≤ k) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) (hm : 4 * k ^ 2 < m) :
    k < ((P.filter (fun p => p ≤ 2 * k)).card + 1) *
      2 ^ (P.filter (fun p => p ≤ 2 * k)).card := by
  by_contra hbad
  have hh := cover_length_quadratic_of_sparse_small P hP k hk hcard r m hcover
    (by omega)
  omega

/-- At quadratic length plus one, every prime set satisfying the explicit
small-core restriction has a survivor, for every choice of residues. -/
theorem survivor_of_sparse_small (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : 0 < k) (hcard : P.card ≤ k)
    (hsmall : ((P.filter (fun p => p ≤ 2 * k)).card + 1) *
      2 ^ (P.filter (fun p => p ≤ 2 * k)).card ≤ k) (r : ℕ → ℕ) :
    ∃ i < 4 * k ^ 2 + 1, ∀ p ∈ P, ¬i ≡ r p [MOD p] := by
  by_contra hbad
  push_neg at hbad
  have hh := cover_length_quadratic_of_sparse_small P hP k hk hcard r
    (4 * k ^ 2 + 1) hbad hsmall
  omega

#print axioms cover_length_quadratic_of_sparse_small
#print axioms small_core_necessary
#print axioms survivor_of_sparse_small
end Erdos970.CoreTailSieve
