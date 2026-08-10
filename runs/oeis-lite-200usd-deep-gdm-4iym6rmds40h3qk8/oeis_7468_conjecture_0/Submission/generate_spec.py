import math

def sieve(n_primes):
    limit = int(n_primes * (math.log(n_primes) + 12)) if n_primes > 1 else 10
    is_prime = [True] * limit
    primes = []
    for p in range(2, limit):
        if is_prime[p]:
            primes.append(p)
            if len(primes) == n_primes:
                break
            for i in range(p*p, limit, p):
                is_prime[i] = False
    return primes

n_max = 38
# We only need primes up to the max index for n = 37.
# For n = 37, start_idx = 37 * 36 / 2 = 666, and we need 37 primes starting there, so indices 666 to 702.
# Thus we need exactly 703 primes.
total_primes_needed = 100
primes = sieve(total_primes_needed)

out = []
out.append("import FormalConjectures.Util.ProblemImports")
out.append("set_option maxRecDepth 100000")
out.append("set_option linter.unusedSimpArgs false")
out.append("")
out.append("/--")
out.append("A007468: Sum of next $n$ primes.")
out.append("The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.")
out.append("$$a(n) = \\sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \\operatorname{prime}_i$$")
out.append("We use the Mathlib $k$-th prime function: $\\operatorname{prime}(k) = \\text{Nat.nth Nat.Prime } k$, indexed from 0.")
out.append("The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.")
out.append("-/")
out.append("noncomputable def a (n : ℕ) : ℕ :=")
out.append("  let start_idx : ℕ := (n * (n - 1)) / 2")
out.append("  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)")
out.append("")
out.append("theorem nth_of_count {p : ℕ → Prop} [DecidablePred p] {n c : ℕ} (hp : p n) (hc : Nat.count p n = c) : Nat.nth p c = n := by")
out.append("  subst hc")
out.append("  exact Nat.nth_count hp")
out.append("")

# Generate nth_prime lemmas
print("Generating nth_prime lemmas...")
for k, p in enumerate(primes):
    out.append(f"lemma nth_prime_{k} : Nat.nth Nat.Prime {k} = {p} := nth_of_count (by decide) (by decide)")

out.append("")

# Generate a_n_eq lemmas
print("Generating a_n_eq lemmas...")
for n in range(1, 14):
    start_idx = n * (n - 1) // 2
    v = sum(primes[start_idx : start_idx + n])
    out.append(f"lemma a_{n}_eq : a {n} = {v} := by")
    out.append(f"  unfold a")
    out.append(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]")
    out.append(f"  norm_num")
    simp_lemmas = ", ".join(f"nth_prime_{start_idx + i}" for i in range(n))
    out.append(f"  try simp only [{simp_lemmas}]")
    out.append("")

# Generate the main conjecture theorem
print("Generating main theorem...")
out.append("theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by")
out.append("  intro n hn hsq")
out.append("  by_cases h_lt : n < 14")
out.append("  · interval_cases n")
for n in range(1, 14):
    start_idx = n * (n - 1) // 2
    v = sum(primes[start_idx : start_idx + n])
    out.append(f"    · have h_{n} : a {n} = {v} := a_{n}_eq")
    out.append(f"      rw [h_{n}] at hsq")
    out.append(f"      have h_not : ¬ IsSquare {v} := by norm_num")
    out.append(f"      exact (h_not hsq).elim")
out.append("  · sorry")
out.append("")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(out))
print("Done!")
