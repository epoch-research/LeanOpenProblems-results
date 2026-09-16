import subprocess

# We want to cover all x with 0, 2, cq, cq+2 modulo q
# This is equivalent to: for each x, there is some q where x is covered.
# We write a C++ program with a SAT solver (CaDiCaL or Kissat) to find a covering.

cpp_code = """
#include <iostream>
#include <vector>
#include <fstream>
#include <cstdlib>

using namespace std;

int primes[] = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
int num_p = 23;

int main() {
    ofstream out("cover.cnf");
    // Variables: for each q in primes, cq can be 0..q-1.
    // So sum(primes) variables.
    int var_count = 0;
    vector<vector<int>> cq_vars(num_p);
    for (int i=0; i<num_p; i++) {
        for (int j=0; j<primes[i]; j++) {
            var_count++;
            cq_vars[i].push_back(var_count);
        }
    }
    
    vector<vector<int>> clauses;
    
    // Exactly one cq per prime
    for (int i=0; i<num_p; i++) {
        vector<int> clause;
        for (int j=0; j<primes[i]; j++) clause.push_back(cq_vars[i][j]);
        clauses.push_back(clause);
        for (int j=0; j<primes[i]; j++) {
            for (int k=j+1; k<primes[i]; k++) {
                clauses.push_back({-cq_vars[i][j], -cq_vars[i][k]});
            }
        }
    }
    
    // For every x, it must be covered.
    // Instead of all x, we can just randomly sample x, or use a small bound.
    // Wait, covering ALL x is hard to write in SAT if we don't know the exact x.
    // A covering system exists iff the density of uncovered elements is 0.
    
    out << "p cnf " << var_count << " " << clauses.size() << "\\n";
    for (auto& c : clauses) {
        for (int lit : c) out << lit << " ";
        out << "0\\n";
    }
    out.close();
    return 0;
}
"""
with open("sat_cover.cpp", "w") as f:
    f.write(cpp_code)
subprocess.run(["g++", "-O3", "sat_cover.cpp", "-o", "sat_cover"])
subprocess.run(["./sat_cover"])
