#include <iostream>
#include <vector>
#include <unordered_set>

inline uint64_t A030101(uint64_t n) {
    if (n == 0) return 0;
    uint64_t rev = 0;
    while (n > 0) {
        rev = (rev << 1) | (n & 1);
        n >>= 1;
    }
    return rev;
}

int main() {
    uint64_t N = 500000000ULL; // 500 million
    
    // We want to find any even number E attained in the first 50 million terms,
    // for which E - 1 is not attained in the first 500 million terms.
    
    // To do this, we can first run 500 million terms and store all attained values in a hash set,
    // or we can use a vector of bool for a range of values.
    // Let us use a vector of bool for values up to 100 million.
    uint64_t MAX_VAL = 100000000ULL;
    std::vector<bool> attained(MAX_VAL, false);
    
    // We also want to record when even numbers are first attained.
    std::vector<uint64_t> first_attained_even(MAX_VAL, 0);
    
    uint64_t a_prev2 = 0;
    uint64_t a_prev1 = 1;
    
    for (uint64_t i = 2; i < N; ++i) {
        uint64_t a_curr = (a_prev2 ^ A030101(a_prev1)) + 1;
        if (a_curr < MAX_VAL) {
            attained[a_curr] = true;
            if (a_curr % 2 == 0 && first_attained_even[a_curr] == 0) {
                first_attained_even[a_curr] = i;
            }
        }
        a_prev2 = a_prev1;
        a_prev1 = a_curr;
    }
    
    std::cout << "Search results:" << std::endl;
    for (uint64_t E = 2; E < MAX_VAL; E += 2) {
        if (first_attained_even[E] > 0 && first_attained_even[E] < 50000000ULL) {
            // E is attained in first 50 million terms.
            // Check if E - 1 is NOT attained in 500 million terms.
            if (!attained[E - 1]) {
                std::cout << "Found candidate: E = " << E << " (p = " << E-1 << ")" << std::endl;
                std::cout << "  E first attained at index " << first_attained_even[E] << std::endl;
            }
        }
    }
    std::cout << "Done." << std::endl;
    return 0;
}
