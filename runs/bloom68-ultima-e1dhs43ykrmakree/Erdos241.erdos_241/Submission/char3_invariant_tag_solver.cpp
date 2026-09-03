// Exact solver for Singer-subset tag coherence. No external dependencies.
// Build: g++ -O3 -std=c++17 -Wall -Wextra -pedantic singer_half_tag_coherence.cpp -o /tmp/singer_half_tag_solver
// Input: n k m, then m rows of n signed coefficients. All row sums must be 0.
// CLI: solver INPUT TIMEOUT_MS PROOF_PATH_OR_- [NODE_CAP]; 0 means no limit.
// All tags are arbitrary in Z/k; ONLY tag[0]=0 is fixed, by translation.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Clock = std::chrono::steady_clock;
using Mask = std::uint64_t;
int mod(int a, int k) { int r = a % k; return r < 0 ? r + k : r; }
int inverse(int a, int m) {
    if (m == 1) return 0;
    for (int x = 1; x < m; ++x) if ((a * x) % m == 1) return x;
    throw std::runtime_error("inverse does not exist");
}
// Roots of a*x+b=0 mod k: empty if gcd(a,k) does not divide b;
// otherwise a complete coset of size gcd(a,k), NOT just one inverse root.
Mask forbidden_roots(int a, int b, int k) {
    a = mod(a, k); b = mod(b, k);
    const int d = std::gcd(a, k);
    if (b % d != 0) return 0;
    const int step = k / d;
    const int x0 = mod((-b / d) * inverse(a / d, step), step);
    Mask out = 0;
    for (int t = 0; t < d; ++t) out |= Mask(1) << (x0 + t * step);
    return out;
}
struct Constraint { std::vector<std::pair<int, int>> terms; };
enum Status { UNSAT, SAT, TIMEOUT };
struct Solver {
    int n, k;
    std::vector<Constraint> cs;
    std::vector<int> value, solution, proof;
    std::vector<std::vector<Mask>> roots;
    std::vector<std::uint64_t> powers;
    Mask full;
    bool write_proof;
    std::uint64_t nodes = 0, leaves = 0, covered = 0, root_removals = 0, node_cap;
    int max_depth = 0;
    double timeout_ms;
    Clock::time_point start;
    Solver(int n_, int k_, std::vector<Constraint> cs_, double timeout_,
           bool proof_, std::uint64_t cap = 0)
        : n(n_), k(k_), cs(std::move(cs_)), value(n, -1),
          roots(k, std::vector<Mask>(k)), powers(n + 1, 1),
          full((Mask(1) << k) - 1), write_proof(proof_), node_cap(cap), timeout_ms(timeout_) {
        if (n < 1 || n > 30 || k < 2 || k > 32) throw std::runtime_error("unsupported n or k");
        for (int a = 0; a < k; ++a) for (int b = 0; b < k; ++b)
            roots[a][b] = forbidden_roots(a, b, k);
        for (int j = 1; j <= n; ++j) {
            if (powers[j-1] > UINT64_MAX / std::uint64_t(k)) throw std::runtime_error("coverage counter overflow");
            powers[j] = powers[j-1] * k;
        }
        value[0] = 0;
    }
    double elapsed_ms() const {
        return std::chrono::duration<double, std::milli>(Clock::now() - start).count();
    }
    Status contradiction(int assigned) {
        ++leaves;
        covered += powers[n - assigned];
        if (write_proof) proof.push_back(-1);
        return UNSAT;
    }
    Status dfs(int assigned) {
        if ((node_cap && nodes >= node_cap) || (timeout_ms > 0 && elapsed_ms() >= timeout_ms)) return TIMEOUT;
        ++nodes; max_depth = std::max(max_depth, assigned - 1);
        std::vector<Mask> domain(n, full);
        std::vector<int> score(n, 0);
        for (const auto& c : cs) {
            int b = 0, unassigned = 0, last = -1, a = 0;
            for (auto [i, coefficient] : c.terms) {
                if (value[i] < 0) { ++unassigned; last = i; a = coefficient; }
                else b += coefficient * value[i];
            }
            b = mod(b, k);
            if (unassigned == 0) {
                if (b == 0) return contradiction(assigned);
            } else if (unassigned == 1) {
                Mask old = domain[last];
                domain[last] &= ~roots[mod(a, k)][b];
                root_removals += __builtin_popcountll(old ^ domain[last]);
                if (domain[last] == 0) return contradiction(assigned);
            } else {
                const int weight = 1 << std::max(0, 6 - unassigned);
                for (auto [i, coefficient] : c.terms) {
                    (void)coefficient;
                    if (value[i] < 0) score[i] += weight;
                }
            }
        }
        if (assigned == n) { solution = value; return SAT; }
        int chosen = -1, smallest = k + 1, best_score = -1;
        for (int i = 0; i < n; ++i) if (value[i] < 0) {
            const int size = __builtin_popcountll(domain[i]);
            if (size < smallest || (size == smallest && score[i] > best_score)) {
                chosen = i; smallest = size; best_score = score[i];
            }
        }
        if (chosen < 0) throw std::runtime_error("no branch variable");
        // The omitted values are exactly those ruled out by one-unassigned rows.
        covered += std::uint64_t(k - smallest) * powers[n - assigned - 1];
        if (write_proof) proof.push_back(chosen);
        for (int x = 0; x < k; ++x) if ((domain[chosen] >> x) & 1) {
            value[chosen] = x;
            Status s = dfs(assigned + 1);
            value[chosen] = -1;
            if (s != UNSAT) return s;
        }
        return UNSAT;
    }
    Status run() { start = Clock::now(); return dfs(1); }
};

bool brute(int n, int k, const std::vector<Constraint>& cs) {
    std::vector<int> xs(n, 0);
    std::function<bool(int)> rec = [&](int pos) {
        if (pos == n) {
            for (const auto& c : cs) {
                int sum = 0; for (auto [i, a] : c.terms) sum += a * xs[i];
                if (mod(sum, k) == 0) return false;
            }
            return true;
        }
        for (int x = 0; x < k; ++x) { xs[pos] = x; if (rec(pos + 1)) return true; }
        return false;
    };
    return rec(1);
}
void self_test() {
    for (int k = 2; k <= 32; ++k) for (int a = -3; a <= 3; ++a) for (int b = -2*k; b <= 2*k; ++b) {
        Mask expected = 0;
        for (int x = 0; x < k; ++x) if (mod(a*x+b, k) == 0) expected |= Mask(1) << x;
        if (forbidden_roots(a, b, k) != expected) throw std::runtime_error("root test failed");
    }
    std::mt19937 rng(24111017);
    for (int test = 0; test < 2000; ++test) {
        const int n = 2 + rng() % 4, k = 2 + rng() % 7, m = rng() % 25;
        std::vector<Constraint> cs;
        for (int j = 0; j < m; ++j) {
            std::vector<int> coeff(n, 0);
            for (int t = 0; t < 3; ++t) { ++coeff[rng()%n]; --coeff[rng()%n]; }
            Constraint c;
            for (int i = 0; i < n; ++i) if (coeff[i]) c.terms.emplace_back(i, coeff[i]);
            cs.push_back(c);
        }
        Solver s(n, k, cs, 0, true);
        Status ans = s.run();
        if ((ans == SAT) != brute(n, k, cs)) throw std::runtime_error("brute-force comparison failed");
        if (ans == UNSAT && s.covered != s.powers[n-1]) throw std::runtime_error("coverage failed");
    }
    std::cout << "{\"root_tables\":\"PASS\",\"random_bruteforce_cases\":2000,\"status\":\"PASS\"}\n";
}
int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") { self_test(); return 0; }
        if (argc < 4 || argc > 5) throw std::runtime_error("usage: solver INPUT TIMEOUT_MS PROOF_PATH_OR_- [NODE_CAP]");
        std::ifstream in(argv[1]);
        int n, k, m;
        if (!(in >> n >> k >> m) || n < 1 || n > 30 || k < 2 || k > 32 || m < 0) throw std::runtime_error("bad input header");
        std::vector<Constraint> cs;
        for (int j = 0; j < m; ++j) {
            Constraint c; int sum = 0;
            for (int i = 0; i < n; ++i) {
                int a; if (!(in >> a) || a < -3 || a > 3) throw std::runtime_error("bad coefficient");
                sum += a; if (a) c.terms.emplace_back(i, a);
            }
            if (sum != 0) throw std::runtime_error("translation normalization requires row sum 0");
            cs.push_back(c);
        }
        std::string trailing;
        if (in >> trailing) throw std::runtime_error("trailing input");
        const double timeout = std::stod(argv[2]);
        const bool do_proof = std::string(argv[3]) != "-";
        const std::uint64_t node_cap = argc == 5 ? std::stoull(argv[4]) : 0;
        Solver solver(n, k, cs, timeout, do_proof, node_cap);
        Status status = solver.run();
        const double elapsed = solver.elapsed_ms();
        if (status == UNSAT && solver.covered != solver.powers[n-1]) throw std::runtime_error("incomplete assignment coverage");
        if (status == UNSAT && do_proof) {
            std::ofstream out(argv[3]);
            if (!out) throw std::runtime_error("cannot open proof");
            out << "SHTC1 " << n << ' ' << k << ' ' << m << '\n';
            for (int token : solver.proof) out << token << '\n';
            if (!out) throw std::runtime_error("cannot write proof");
        }
        std::cout << std::fixed << std::setprecision(3)
                  << "{\"status\":\"" << (status == SAT ? "SAT" : status == UNSAT ? "UNSAT" : "TIMEOUT")
                  << "\",\"nodes\":" << solver.nodes << ",\"conflict_leaves\":" << solver.leaves
                  << ",\"covered_assignments\":" << solver.covered << ",\"normalized_assignments\":" << solver.powers[n-1]
                  << ",\"one_variable_root_removals\":" << solver.root_removals
                  << ",\"max_depth_after_fixed_tag\":" << solver.max_depth << ",\"elapsed_ms\":" << elapsed
                  << ",\"tags\":[";
        for (std::size_t i = 0; i < solver.solution.size(); ++i) std::cout << (i ? "," : "") << solver.solution[i];
        std::cout << "]}\n";
        return 0;
    } catch (const std::exception& e) { std::cerr << "ERROR: " << e.what() << '\n'; return 2; }
}
