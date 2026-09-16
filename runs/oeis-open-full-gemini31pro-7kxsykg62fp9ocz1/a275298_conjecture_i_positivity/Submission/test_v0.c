#include <stdio.h>
#include <math.h>

int main() {
    int max_n = 100000;
    int *cov = calloc(max_n + 1, sizeof(int));
    for(long long w=0; w*w*w + w*w <= max_n; w++) {
        long long base = w*w*w + w*w;
        for(long long y=0; base + y*y <= max_n; y++) {
            long long base2 = base + y*y;
            for(long long z=y; base2 + z*z <= max_n; z++) {
                if (w < z) {
                    cov[base2 + z*z] = 1;
                }
            }
        }
    }
    for(int i=1; i<=max_n; i++) {
        if(!cov[i]) {
            printf("Counterexample for v=0: %d\n", i);
            return 0;
        }
    }
    printf("No counterexample up to %d\n", max_n);
    return 0;
}
