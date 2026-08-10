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
    
    // We want to find any odd number p < 100000 that is NOT attained.
    std::vector<bool> attained(100000, false);
    
    uint64_t a_prev2 = 0;
    uint64_t a_prev1 = 1;
    
    for (uint64_t i = 2; i < N; ++i) {
        uint64_t a_curr = (a_prev2 ^ A030101(a_prev1)) + 1;
        if (a_curr < 100000) {
            attained[a_curr] = true;
        }
        a_prev2 = a_prev1;
        a_prev1 = a_curr;
    }
    
    std::cout << "Odd numbers under 100000 not attained:" << std::endl;
    for (int p = 1; p < 100000; p += 2) {
        if (!attained[p]) {
            std::cout << p << " ";
        }
    }
    std::cout << std::endl;
    return 0;
}
