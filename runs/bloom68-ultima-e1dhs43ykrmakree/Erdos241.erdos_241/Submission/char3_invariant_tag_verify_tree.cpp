// Independent fast checker for SHTC1 refutation trees. NOT a solver.
// Build: g++ -O3 -std=c++17 -Wall -Wextra -pedantic singer_half_tag_verify_tree.cpp -o /tmp/singer_half_tag_tree_checker
// Usage: checker independently_reconstructed_input.txt uncompressed_proof.txt
// Recomputes forbidden roots by enumerating all residues, rather than dividing.
// The proof supplies only branch variables / conflict leaves; every allowed
// child must be present. No search heuristic or inferred UNSAT flag is trusted.
#include <array>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using Mask = std::uint64_t;
struct Checker {
    int n, k, m;
    std::vector<std::vector<std::pair<int,int>>> rows;
    std::array<int,30> x;
    std::array<std::array<Mask,32>,32> forbidden{};
    std::array<std::uint64_t,31> powers{};
    std::string body;
    std::size_t cursor = 0;
    std::uint64_t nodes = 0, leaves = 0;
    int depth = 0;
    Mask full;
    static void require(bool ok, const char* why) { if (!ok) throw std::runtime_error(why); }
    static int residue(int a, int k) { return (a % k + k) % k; }
    Checker(const char* input_path, const char* proof_path) {
        std::ifstream input(input_path), proof(proof_path);
        require(bool(input >> n >> k >> m), "input header");
        require(n > 0 && n <= 30 && k >= 2 && k <= 32 && m >= 0, "input dimensions");
        for (int j = 0; j < m; ++j) {
            std::vector<std::pair<int,int>> row;
            int sum = 0;
            for (int i = 0; i < n; ++i) {
                int a;
                require(bool(input >> a) && a >= -3 && a <= 3, "input coefficient");
                sum += a;
                if (a != 0) row.emplace_back(i, a);
            }
            require(sum == 0, "translation normalization invalid");
            rows.push_back(row);
        }
        std::string extra;
        require(!(input >> extra), "trailing input");
        std::string magic;
        int pn, pk, pm;
        require(bool(proof >> magic >> pn >> pk >> pm), "proof header");
        require(magic == "SHTC1" && pn == n && pk == k && pm == m, "proof dimensions");
        body.assign(std::istreambuf_iterator<char>(proof), {});
        x.fill(-1); x[0] = 0;
        full = (Mask(1) << k)-1;
        for (int a = 0; a < k; ++a) for (int b = 0; b < k; ++b)
            for (int value = 0; value < k; ++value)
                if ((a*value+b) % k == 0) forbidden[a][b] |= Mask(1) << value;
        powers[0] = 1;
        for (int i = 1; i <= n; ++i) {
            require(powers[i-1] <= UINT64_MAX / std::uint64_t(k), "counter overflow");
            powers[i] = powers[i-1]*k;
        }
    }
    void whitespace() {
        while (cursor < body.size() && std::isspace(static_cast<unsigned char>(body[cursor]))) ++cursor;
    }
    int token() {
        whitespace();
        require(cursor < body.size(), "truncated proof");
        int sign = 1;
        if (body[cursor] == '-') { sign = -1; ++cursor; }
        require(cursor < body.size() && std::isdigit(static_cast<unsigned char>(body[cursor])), "bad proof token");
        int value = 0;
        while (cursor < body.size() && std::isdigit(static_cast<unsigned char>(body[cursor]))) {
            value = value*10+(body[cursor++]-'0');
            require(value <= 1000, "oversized token");
        }
        require(cursor == body.size() || std::isspace(static_cast<unsigned char>(body[cursor])), "bad token delimiter");
        return sign*value;
    }
    std::uint64_t visit(int assigned) {
        const int branch = token();
        ++nodes; if (assigned-1 > depth) depth = assigned-1;
        std::array<Mask,30> domains;
        domains.fill(full);
        bool conflict = false;
        for (const auto& row : rows) {
            int unknown = 0, last = -1, coeff = 0, sum = 0;
            for (auto [i, a] : row) {
                if (x[i] == -1) { ++unknown; last = i; coeff = a; }
                else sum += a*x[i];
            }
            const int b = residue(sum, k);
            if (unknown == 0 && b == 0) { conflict = true; break; }
            if (unknown == 1) {
                domains[last] &= ~forbidden[residue(coeff, k)][b];
                if (domains[last] == 0) { conflict = true; break; }
            }
        }
        if (conflict) {
            require(branch == -1, "conflict must terminate this branch");
            ++leaves;
            return powers[n-assigned];
        }
        require(assigned < n, "satisfying assignment in refutation");
        require(branch >= 0 && branch < n && x[branch] == -1, "invalid branch variable");
        const Mask domain = domains[branch];
        std::uint64_t coverage = (k-__builtin_popcountll(domain))*powers[n-assigned-1];
        for (int value = 0; value < k; ++value) if (domain & (Mask(1) << value)) {
            x[branch] = value;
            coverage += visit(assigned+1);
        }
        x[branch] = -1;
        require(coverage == powers[n-assigned], "incomplete subtree coverage");
        return coverage;
    }
    void run() {
        const auto covered = visit(1);
        whitespace();
        require(cursor == body.size(), "surplus proof nodes");
        require(covered == powers[n-1], "incomplete total coverage");
        std::cout << "{\"nodes\":" << nodes << ",\"conflict_leaves\":" << leaves
                  << ",\"max_depth_after_fixed_tag\":" << depth
                  << ",\"covered_assignments\":" << covered << "}\n";
    }
};
int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::runtime_error("usage: checker INPUT PROOF");
        Checker checker(argv[1], argv[2]);
        checker.run();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "INVALID CERTIFICATE: " << e.what() << '\n';
        return 1;
    }
}
