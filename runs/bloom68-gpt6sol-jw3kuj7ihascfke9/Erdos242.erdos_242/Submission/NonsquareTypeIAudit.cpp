// Bounded, exact audit of the FULL Type-I condition for n = 24 k + 1.
// It does NOT prove that every nonsquare n (or every prime n) has a witness.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -o /tmp/nonsquare_typei Submission/NonsquareTypeIAudit.cpp
// Run:   /tmp/nonsquare_typei 10000000000 64
// No third-party libraries or probabilistic primality tests are used.
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;
using u128 = __uint128_t;

static std::string decimal(u128 v) {
  std::string out;
  do { out.push_back(char('0' + v % 10)); v /= 10; } while (v);
  std::reverse(out.begin(), out.end());
  return out;
}

// spf[t] = its smallest prime factor if composite, otherwise 0.
// Each composite t <= limit has a prime factor <= sqrt(t), so this sieve
// really distinguishes primes from composites (including for large t).
static std::vector<u32> smallest_prime_factors(u64 limit) {
  std::vector<u32> spf(limit + 1, 0);
  for (u64 p = 2; p <= limit / p; ++p) {
    if (spf[p]) continue;
    for (u64 v = p * p; v <= limit; v += p)
      if (!spf[v]) spf[v] = u32(p);
  }
  return spf;
}

// Decide exactly whether some POSITIVE c | x^2 satisfies a | (4c+1).
// At every stage, residue r in "residues" is achieved by the saved positive
// "values[r]" dividing the squared product of the processed prime powers.
// Prime factors of a cannot occur in c because gcd(c,a)=1 for a | 4c+1.
static bool find_type_i(u64 x, u32 a, const std::vector<u32> &spf,
                        u128 &witness) {
  assert(x > 0 && x < spf.size() && a >= 3 && a % 4 == 3);
  // a = 4j+3, so 4 * ((a+1)/4) = a+1; target = -1/4 mod a.
  const u32 target = a - (a + 1) / 4;
  std::vector<u32> residues(1, 1);
  std::vector<unsigned char> seen(a, 0);
  std::vector<u128> values(a, 0);
  seen[1] = 1;
  values[1] = 1;
  if (target == 1) { witness = 1; return true; }
  for (u64 remaining = x; remaining > 1; ) {
    const u64 p = spf[remaining] ? spf[remaining] : remaining;
    unsigned int e = 0;
    do { remaining /= p; ++e; } while (remaining % p == 0);
    if (a % p == 0) continue;  // c containing p could not hit the unit target.
    const std::size_t old_length = residues.size();
    u64 power_mod_a = 1;
    u128 prime_power = 1;
    for (unsigned int h = 1; h <= 2 * e; ++h) {
      power_mod_a = power_mod_a * (p % a) % a;
      prime_power *= p;
      for (std::size_t i = 0; i < old_length; ++i) {
        const u32 r = u32(residues[i] * power_mod_a % a);
        if (seen[r]) continue;
        seen[r] = 1;
        values[r] = values[residues[i]] * prime_power;
        residues.push_back(r);
        if (r == target) {
          witness = values[r];
          // These independent integer checks make a positive answer an
          // immediately checkable certificate even if the DP had a bug.
          assert(witness > 0 && u128(x) * x % witness == 0);
          assert((4 * witness + 1) % a == 0);
          return true;
        }
      }
    }
  }
  return false;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: %s MAX_N FIRST_J_COUNT\n", argv[0]);
    return 2;
  }
  const u64 max_n = std::strtoull(argv[1], nullptr, 10);
  const u64 J = std::strtoull(argv[2], nullptr, 10);
  if (max_n < 25 || J < 1 || J > 100000 || max_n > 10000000000ULL) {
    std::fprintf(stderr, "require 25 <= MAX_N <= 10^10 and 1 <= FIRST_J_COUNT <= 100000\n");
    return 2;
  }
  // For n=24k+1 and 0<=j<min(6k,J), x=6k+1+j <= max_n/4+J+1.
  const auto started = std::chrono::steady_clock::now();
  const auto spf = smallest_prime_factors(max_n / 4 + J + 2);
  std::fprintf(stderr, "sieve_seconds=%.2f sieve_limit=%llu\n",
               std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count(),
               (unsigned long long)(spf.size()-1));
  u64 squares = 0, nonsquares = 0, missing = 0, max_j = 0, record_n = 0;
  std::vector<u64> counts(J, 0);
  for (u64 k = 1; 24 * k + 1 <= max_n; ++k) {
    const u64 n = 24 * k + 1;
    const u64 root = u64(std::sqrt((long double)n));
    if (root * root == n || (root + 1) * (root + 1) == n) {
      ++squares;
      continue;  // Squares have NO full Type-I witness, by Jacobi reciprocity.
    }
    ++nonsquares;
    const u64 first_x = 6 * k + 1;
    const u64 stop = std::min(6 * k, J);  // 2x<n iff j<6k.
    u64 j = 0;
    for (; j < stop; ++j) {
      u128 c = 0;
      if (!find_type_i(first_x + j, u32(4 * j + 3), spf, c)) continue;
      ++counts[j];
      if (j > max_j) {
        max_j = j;
        record_n = n;
        std::printf("RECORD n=%llu j=%llu x=%llu a=%llu c=%s\n",
          (unsigned long long)n, (unsigned long long)j,
          (unsigned long long)(first_x+j), (unsigned long long)(4*j+3),
          decimal(c).c_str());
        std::fflush(stdout);
      }
      break;
    }
    if (j == stop) {
      ++missing;
      std::printf("NO_WITNESS_IN_FIRST_%llu n=%llu (complete_interval=%s)\n",
        (unsigned long long)J, (unsigned long long)n, stop==6*k?"YES":"NO");
      std::fflush(stdout);
    }
  }
  u64 count_total = 0;
  for (u64 j = 0; j < J; ++j) count_total += counts[j];
  assert(count_total + missing == nonsquares);
  std::printf("DONE max_n=%llu J=%llu nonsquares=%llu squares=%llu"
              " no_witness_in_first_J=%llu max_first_j=%llu at_n=%llu seconds=%.2f\n",
    (unsigned long long)max_n, (unsigned long long)J,
    (unsigned long long)nonsquares, (unsigned long long)squares,
    (unsigned long long)missing, (unsigned long long)max_j,
    (unsigned long long)record_n,
    std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count());
  for (u64 j = 0; j < J; ++j) if (counts[j] != 0)
    std::printf("j=%llu number=%llu\n", (unsigned long long)j,
                (unsigned long long)counts[j]);
  return missing ? 1 : 0;
}
