#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

const int num_P = 15;
int P[num_P] = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59};
int C[num_P];

// We want to cover all x with x%q in {0, 2, C[q], C[q]+2}
// Since 0 and 2 are always covered, we only need to cover x not 0,2 mod any q.
// We can use a recursive function that passes down the list of uncovered x.
// BUT the number of uncovered x modulo Prod(P) is too large!
// Instead, we can build the tree of uncovered residues.

// A node in the CRT tree
struct Node {
    long long count;
};

// This is just standard Covering System search.
// Actually, is there a known covering system for Goldbach with Twin Primes?
// Yes! Brier (1998) or similar?
// But wait, the question asks about A266952!
// A266952 is EXACTLY this sequence.
// OEIS A266952: "Least prime p such that p-2, 6n-p, 6n+2-p are also primes, or 0 if no such prime exists."
// The author is "V. Raman, Jan 05 2016".
// Comment: "Up to 10^5, the only indices for which a(n)=0 are {0, 1, 16, 67, 86, 131, 151, 186, 191, 211, 226, 541, 701}. I conjecture that this list is finite, and probably complete."
// Has it been proven since 2016?
// If it is an open conjecture, I CANNOT prove it. I CANNOT disprove it unless there's a covering system.
