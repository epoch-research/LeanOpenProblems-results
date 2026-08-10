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
    int max_M = 50000;
    int max_B = 5000;
    
    char *R = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    for (int M = 3; M <= max_M; M += 3) {
        for (int B = 129; B <= max_B; B += 1) {
            memset(R, 0, M);
            int head = 0, tail = 0;
            
            // Initial set of residues: 85 % M
            int r85 = 85 % M;
            R[r85] = 1;
            queue[tail++] = r85;
            
            // Also add all incoming g(x) % M for x in [B, 3B/2] with x % 3 == 0 and g(x) < B
            for (int x = B; x <= 3 * B / 2; x++) {
                if (x % 3 == 0) {
                    long long gx = g(x);
                    if (gx < B) {
                        int gr = gx % M;
                        if (!R[gr]) {
                            R[gr] = 1;
                            queue[tail++] = gr;
                        }
                    }
                }
            }
            
            int possible = 1;
            while (head < tail) {
                int r = queue[head++];
                
                // For this residue r, we must check all x < B with x % M == r
                for (int q = 0; q * M + r < B; q++) {
                    long long x = q * M + r;
                    long long gx = g(x);
                    if (gx < 85) {
                        possible = 0;
                        break;
                    }
                    if (gx < B) {
                        int gr = gx % M;
                        if (!R[gr]) {
                            R[gr] = 1;
                            queue[tail++] = gr;
                        }
                    }
                }
                if (!possible) break;
            }
            
            if (possible) {
                printf("FOUND SEMI-MODULAR INVARIANT!\n");
                printf("M = %d, B = %d\n", M, B);
                printf("R residues size: %d\n", tail);
                printf("Residues: ");
                for (int r = 0; r < M; r++) {
                    if (R[r]) printf("%d ", r);
                }
                printf("\n");
                free(R);
                free(queue);
                return 0;
            }
        }
    }
    
    printf("No semi-modular invariant found.\n");
    free(R);
    free(queue);
    return 0;
}
