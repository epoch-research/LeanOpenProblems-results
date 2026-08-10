#include <stdio.h>
#include <stdlib.h>

long long f(long long k) {
    if (k % 2 == 0) {
        return (3 * k) / 2;
    } else if (k % 4 == 1) {
        return (3 * k + 1) / 4;
    } else {
        return (3 * k - 1) / 4;
    }
}

int main() {
    long long x = 64;
    for (long long i = 1; i <= 2000000000LL; i++) {
        x = f(x);
        if (x == 64) {
            printf("Found cycle back to 64 at step %lld!\n", i);
            return 0;
        }
        if (x < 1) {
            printf("Non-positive value %lld at step %lld\n", x, i);
            return 0;
        }
    }
    printf("No cycle back to 64 up to 2 billion steps.\n");
    return 0;
}
