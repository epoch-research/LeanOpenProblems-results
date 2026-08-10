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

# Let's generate a test Spec file up to i = 500
total_primes_needed = 741
primes = sieve(total_primes_needed)
max_prime = 500

out = []
out.append("import FormalConjectures.Util.ProblemImports")
out.append("set_option maxRecDepth 10000")
out.append("set_option linter.unusedSimpArgs false")
out.append("")

# Generate prime_status lemmas
for i in range(2, max_prime + 1):
    is_p = i in primes
    if is_p:
        out.append(f"lemma prime_status_{i} : Nat.Prime {i} := by decide")
    else:
        out.append(f"lemma prime_status_{i} : ¬ Nat.Prime {i} := by decide")

out.append("")
out.append("lemma count_prime_0 : Nat.count Nat.Prime 0 = 0 := rfl")
out.append("lemma count_prime_1 : Nat.count Nat.Prime 1 = 0 := by rw [Nat.count_succ, count_prime_0]; rfl")
out.append("lemma count_prime_2 : Nat.count Nat.Prime 2 = 0 := by rw [Nat.count_succ, count_prime_1]; rfl")

current_count = 0
for i in range(3, max_prime + 1):
    # i - 1 prime status
    prev = i - 1
    prev_is_prime = prev in primes
    if prev_is_prime:
        current_count += 1
        out.append(f"lemma count_prime_{i} : Nat.count Nat.Prime {i} = {current_count} := by rw [Nat.count_succ, count_prime_{prev}, if_pos prime_status_{prev}]")
    else:
        out.append(f"lemma count_prime_{i} : Nat.count Nat.Prime {i} = {current_count} := by rw [Nat.count_succ, count_prime_{prev}, if_neg prime_status_{prev}]")

with open("/workspace/leanproject/Submission/SpecTest.lean", "w") as f:
    f.write("\n".join(out))
print("Done!")
