#include <stdio.h>

long long g(long long m) {
    if (m % 3 == 0) {
        return 2 * (m / 3);
    } else if (m % 3 == 1) {
        return 4 * (m / 3) + 1;
    } else {
        return 4 * (m / 3) + 3;
    }
}

int main() {
    long long curr = 85;
    long long min_val = 85;
    for (long long i = 1; i <= 1000000000LL; i++) {
        curr = g(curr);
        if (curr < min_val) {
            min_val = curr;
            printf("New minimum %lld at step %lld\n", min_val, i);
        }
        if (curr < 85) {
            printf("Found value < 85: %lld at step %lld\n", curr, i);
            return 0;
        }
    }
    printf("Checked 1 billion steps, minimum is still %lld\n", min_val);
    return 0;
}
