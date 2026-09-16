#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
    int max_n = 100000;
    for (int max_w = 2; max_w <= 10; max_w++) {
        int *cov = calloc(max_n + 1, sizeof(int));
        for(long long w=0; w<=max_w; w++) {
            for(long long v=0; w*w*w + (w+v*v)*(w+v*v) <= max_n; v++) {
                long long base = w*w*w + (w+v*v)*(w+v*v);
                for(long long y=0; base + y*y <= max_n; y++) {
                    long long base2 = base + y*y;
                    for(long long z=y; base2 + z*z <= max_n; z++) {
                        if (w < z) {
                            cov[base2 + z*z] = 1;
                        }
                    }
                }
            }
        }
        int found = 0;
        for(int i=1; i<=max_n; i++) {
            if(!cov[i]) {
                found = i;
                break;
            }
        }
        free(cov);
        if (found) {
            printf("Counterexample for w <= %d: %d\n", max_w, found);
        } else {
            printf("No counterexample up to %d for w <= %d\n", max_n, max_w);
            break;
        }
    }
    return 0;
}
