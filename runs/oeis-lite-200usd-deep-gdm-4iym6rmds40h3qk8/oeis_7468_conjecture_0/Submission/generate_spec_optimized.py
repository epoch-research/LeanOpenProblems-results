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
total_primes_needed = 741
primes = sieve(total_primes_needed)

out = []
out.append("import FormalConjectures.Util.ProblemImports")
out.append("set_option maxRecDepth 3000")
out.append("set_option linter.all false")
out.append("set_option linter.unusedSimpArgs false")
out.append("")
out.append("/--")
out.append("A007468: Sum of next $n$ primes.")
out.append("The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.")
out.append("$$a(n) = \\sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \\operatorname{prime}_i$$")
out.append("We use the Mathlib $k$-th prime function: $\\operatorname{prime}(k) = \\text{Nat.nth Nat.Prime } k$, indexed from 0.")
out.append("The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.")
out.append("-/")
out.append("noncomputable def a (n : Nat) : Nat :=")
out.append("  let start_idx : Nat := (n * (n - 1)) / 2")
out.append("  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)")
out.append("")
out.append("theorem nth_of_count {p : Nat → Prop} [DecidablePred p] {n c : Nat} (hp : p n) (hc : Nat.count p n = c) : Nat.nth p c = n := by")
out.append("  subst hc")
out.append("  exact Nat.nth_count hp")
out.append("")

out.append("theorem count_prime_0 : Nat.count Nat.Prime 0 = 0 := rfl")
out.append("theorem count_prime_1 : Nat.count Nat.Prime 1 = 0 := by rw [Nat.count_succ, count_prime_0]; rfl")
out.append("theorem count_prime_2 : Nat.count Nat.Prime 2 = 0 := by rw [Nat.count_succ, count_prime_1]; rfl")

# Generate count_prime lemmas for primes
print("Generating count_prime lemmas for primes...")
for k in range(1, len(primes)):
    pk = primes[k]
    prev_p = primes[k-1]
    gap = pk - prev_p
    
    # Generate the proof steps
    rw_succs = ", ".join(["Nat.count_succ"] * gap)
    
    if_terms = []
    for j in range(prev_p, pk):
        is_j_prime = j in primes
        if is_j_prime:
            if_terms.append(f"if_pos (show Nat.Prime {j} by decide)")
        else:
            if_terms.append(f"if_neg (show ¬ Nat.Prime {j} by decide)")
    rw_ifs = ", ".join(if_terms)
    
    out.append(f"theorem count_prime_{pk} : Nat.count Nat.Prime {pk} = {k} := by")
    out.append(f"  rw [{rw_succs}]")
    out.append(f"  rw [count_prime_{prev_p}]")
    out.append(f"  rw [{rw_ifs}]")
    out.append("")

out.append("")

# Generate nth_prime lemmas
print("Generating nth_prime lemmas...")
for k, p in enumerate(primes):
    out.append(f"theorem nth_prime_{k} : Nat.nth Nat.Prime {k} = {p} := nth_of_count (by decide) count_prime_{p}")

out.append("")

# Generate a_n_eq lemmas
print("Generating a_n_eq lemmas...")
for n in range(1, 39):
    start_idx = n * (n - 1) // 2
    v = sum(primes[start_idx : start_idx + n])
    out.append(f"theorem a_{n}_eq : a {n} = {v} := by")
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
out.append("  by_cases h_lt : n < 39")
out.append("  · interval_cases n")
for n in range(1, 39):
    start_idx = n * (n - 1) // 2
    v = sum(primes[start_idx : start_idx + n])
    if n == 38:
        out.append(f"    · rfl")
    else:
        out.append(f"    · have h_{n} : a {n} = {v} := a_{n}_eq")
        out.append(f"      rw [h_{n}] at hsq")
        out.append(f"      have h_not : ¬ IsSquare {v} := by norm_num")
        out.append(f"      exact (h_not hsq).elim")
out.append("  · sorry")
out.append("")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(out))
print("Done!")
