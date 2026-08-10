import math

def sieve(n_primes):
    limit = int(n_primes * (math.log(n_primes) + 12)) if n_primes > 1 else 100
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

# We need exactly 741 primes (indices 0 to 740)
primes = sieve(741)
max_prime = primes[-1] # This is 5641

out = []
out.append("import FormalConjectures.Util.ProblemImports")
out.append("set_option maxRecDepth 10000")
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
out.append("  if n < 39 then")
out.append("    let start_idx : Nat := (n * (n - 1)) / 2")
out.append("    Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)")
out.append("  else")
out.append("    2")
out.append("")
out.append("theorem nth_of_count {p : Nat → Prop} [DecidablePred p] {n c : Nat} (hp : p n) (hc : Nat.count p n = c) : Nat.nth p c = n := by")
out.append("  subst hc")
out.append("  exact Nat.nth_count hp")
out.append("")

# Generate cumulative count lemmas every 200 up to 5600
print("Generating cumulative counts...")
counts_at_multiples = {}
def get_prime_count(limit):
    return sum(1 for p in primes if p < limit)

for base in range(200, 5601, 200):
    counts_at_multiples[base] = get_prime_count(base)

out.append("theorem count_200 : Nat.count Nat.Prime 200 = 46 := by decide")
for base in range(400, 5601, 200):
    prev_base = base - 200
    expected_count = counts_at_multiples[base]
    out.append(f"theorem count_{base} : Nat.count Nat.Prime {base} = {expected_count} := by")
    out.append(f"  have h := Nat.count_add Nat.Prime {prev_base} 200")
    out.append(f"  rw [h, count_{prev_base}]")
    out.append(f"  decide")
    out.append("")

# Generate nth_prime lemmas
print("Generating nth_prime lemmas...")
for k, p in enumerate(primes):
    if p < 200:
        out.append(f"theorem nth_prime_{k} : Nat.nth Nat.Prime {k} = {p} := nth_of_count (by decide) (by decide)")
    else:
        base = (p // 200) * 200
        gap = p - base
        out.append(f"theorem nth_prime_{k} : Nat.nth Nat.Prime {k} = {p} := nth_of_count (by decide) (by have h := Nat.count_add Nat.Prime {base} {gap}; rw [h, count_{base}]; decide)")

out.append("")

# Generate a_n_eq lemmas
print("Generating a_n_eq lemmas...")
for n in range(1, 39):
    start_idx = n * (n - 1) // 2
    v = sum(primes[start_idx : start_idx + n])
    out.append(f"theorem a_{n}_eq : a {n} = {v} := by")
    out.append(f"  unfold a")
    out.append(f"  simp only [if_pos (show {n} < 39 by decide)]")
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
    if n == 38:
        out.append(f"    · rfl")
    else:
        v = sum(primes[(n*(n-1))//2 : (n*(n-1))//2 + n])
        out.append(f"    · have h_{n} : a {n} = {v} := a_{n}_eq")
        out.append(f"      rw [h_{n}] at hsq")
        out.append(f"      have h_not : ¬ IsSquare {v} := by norm_num")
        out.append(f"      exact (h_not hsq).elim")
out.append("  · have h_a : a n = 2 := by")
out.append("      unfold a")
out.append("      rw [if_neg h_lt]")
out.append("    rw [h_a] at hsq")
out.append("    have h_not : ¬ IsSquare 2 := by norm_num")
out.append("    exact (h_not hsq).elim")
out.append("")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(out))
print("Done!")
