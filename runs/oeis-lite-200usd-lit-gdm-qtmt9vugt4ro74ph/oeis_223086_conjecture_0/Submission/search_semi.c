#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
    int max_M = 2000;
    int max_B = 1000;
    
    char *R = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    // We want to try various M and B
    for (int M = 3; M <= max_M; M += 3) {
        for (int B = 129; B <= max_B; B++) {
            memset(R, 0, M);
            int head = 0, tail = 0;
            
            // S initially contains 85 % M, and also we need to see what else
            // Wait, we can do a BFS starting from 85 % M
            int start = 85 % M;
            R[start] = 1;
            queue[tail++] = start;
            
            int possible = 1;
            while (head < tail) {
                int r = queue[head++];
                
                // For this residue r, we must ensure that any x < B with x % M == r
                // maps to a valid state.
                // Since x < B and x % M == r, there is at most one such x for each multiplier q:
                // x = q * M + r < B.
                for (int q = 0; q * M + r < B; q++) {
                    long long x = q * M + r;
                    long long gx = g(x);
                    if (gx < 85) {
                        possible = 0;
                        goto next_pair;
                    }
                    if (gx < B) {
                        int gr = gx % M;
                        if (!R[gr]) {
                            R[gr] = 1;
                            queue[tail++] = gr;
                        }
                    }
                }
                
                // Also, we must check the boundary condition:
                // For any x >= B with x % M == r, we don't have to check everything,
                // but wait: does the definition of the invariant require that for ANY x >= B,
                // if x % M == r, then g(x) is valid?
                // Actually, if P(x) = (x >= B) or (x % M in R):
                // If x >= B, then we don't assume x % M in R. P(x) is already true because x >= B.
                // Under the transition, we need P(g(x)) to be true, which is (g(x) >= B) or (g(x) % M in R).
                // So for any x >= B (regardless of whether x % M in R), we must have:
                // g(x) >= B or g(x) % M in R.
                // Since g(x) < B can only happen for x in [B, 3B/2] with x % 3 == 0,
                // we must ensure that for all x in [B, 3B/2] with x % 3 == 0:
                // g(x) >= B or g(x) % M in R.
                // Since this condition must hold for ALL x in [B, 3B/2] with x % 3 == 0,
                // let's check this!
                // If for some such x, g(x) < B, then g(x) % M MUST be in R.
                // But wait, since R is being built dynamically, if g(x) % M is not in R,
                // we can either add it to R (and thus we must queue it!),
                // or fail if it's not possible.
                // Let's add any such g(x) % M to R and queue it!
            }
            
            // After the BFS is done, we must check if all boundary elements satisfy the condition:
            // For all x in [B, 3B/2] with x % 3 == 0:
            // if g(x) < B, then g(x) % M MUST be in R.
            // If some g(x) % M is not in R, we can add it to R and restart or continue the BFS.
            // Actually, let's just add them to the queue initially!
            // Yes! Start the BFS with {85 % M} AND { g(x) % M | x in [B, 3B/2], x % 3 == 0, g(x) < B }!
            
            next_pair:;
        }
    }
    
    printf("Done search.\n");
    free(R);
    free(queue);
    return 0;
}
