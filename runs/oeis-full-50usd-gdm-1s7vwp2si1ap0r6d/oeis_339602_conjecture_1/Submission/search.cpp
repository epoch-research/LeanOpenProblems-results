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
    uint64_t a_prev2 = 0;
    uint64_t a_prev1 = 1;
    
    uint64_t targets[] = {22353, 24701, 25641, 25865, 26107, 26277, 27325, 28391};
    int num_targets = 8;
    
    for (uint64_t i = 2; i < N; ++i) {
        uint64_t a_curr = (a_prev2 ^ A030101(a_prev1)) + 1;
        for (int t = 0; t < num_targets; ++t) {
            if (a_curr == targets[t]) {
                std::cout << targets[t] << " attained at " << i << std::endl;
            }
        }
        a_prev2 = a_prev1;
        a_prev1 = a_curr;
    }
    return 0;
}
