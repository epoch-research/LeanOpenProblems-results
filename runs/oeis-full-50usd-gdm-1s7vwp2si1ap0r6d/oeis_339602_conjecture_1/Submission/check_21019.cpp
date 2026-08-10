#include <iostream>

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
    uint64_t a_prev2 = 0;
    uint64_t a_prev1 = 1;
    
    uint64_t count_21019 = 0;
    uint64_t count_21020 = 0;
    
    for (uint64_t i = 2; i < N; ++i) {
        uint64_t a_curr = (a_prev2 ^ A030101(a_prev1)) + 1;
        if (a_curr == 21019) {
            count_21019++;
            std::cout << "21019 attained at " << i << ", count = " << count_21019 << std::endl;
        }
        if (a_curr == 21020) {
            count_21020++;
            std::cout << "21020 attained at " << i << ", count = " << count_21020 << std::endl;
        }
        a_prev2 = a_prev1;
        a_prev1 = a_curr;
    }
    std::cout << "Final counts in 10 billion terms: 21019: " << count_21019 << ", 21020: " << count_21020 << std::endl;
    return 0;
}
