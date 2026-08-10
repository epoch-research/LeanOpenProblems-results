#include <iostream>
#include <vector>

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
    uint64_t N = 10000000000ULL; // 10 billion
    
    // We want to find any even number E attained in 10 billion terms,
    // for which E - 1 is NOT attained.
    // Let us use a vector of bool for values up to 2 million.
    uint64_t MAX_VAL = 2000000ULL;
    std::vector<bool> attained(MAX_VAL, false);
    
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
        
        if (i % 2000000000ULL == 0) {
            std::cout << "Reached " << i << " terms..." << std::endl;
        }
    }
    
    std::cout << "Search results for E attained, E-1 not attained:" << std::endl;
    for (uint64_t E = 2; E < MAX_VAL; E += 2) {
        if (first_attained_even[E] > 0) {
            if (!attained[E - 1]) {
                std::cout << "Found candidate: E = " << E << " (p = " << E-1 << ")" << std::endl;
                std::cout << "  E first attained at index " << first_attained_even[E] << std::endl;
            }
        }
    }
    std::cout << "Done." << std::endl;
    return 0;
}
