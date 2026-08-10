#include <stdio.h>
#include <stdlib.h>
#include <string.h>

long long f(long long k) {
    if (k % 2 == 0) {
        return (3 * k) / 2;
    } else if (k % 4 == 1) {
        return (3 * k + 1) / 4;
    } else {
        return (3 * k - 1) / 4;
    }
}

void search_for_B(int B, int max_M) {
    char *S = malloc(B);
    int *S_queue = malloc(B * sizeof(int));
    
    char *R = malloc(max_M);
    int *R_queue = malloc(max_M * sizeof(int));
    
    for (int M = 4; M <= max_M; M += 4) {
        memset(S, 0, B);
        memset(R, 0, M);
        
        int S_head = 0, S_tail = 0;
        int R_head = 0, R_tail = 0;
        
        if (96 < B) {
            S[96] = 1;
            S_queue[S_tail++] = 96;
        } else {
            int r = 96 % M;
            R[r] = 1;
            R_queue[R_tail++] = r;
        }
        
        int possible = 1;
        while (S_head < S_tail || R_head < R_tail) {
            if (S_head < S_tail) {
                int s = S_queue[S_head++];
                if (s == 64) {
                    possible = 0;
                    break;
                }
                long long fs = f(s);
                if (fs < B) {
                    if (!S[fs]) {
                        S[fs] = 1;
                        S_queue[S_tail++] = fs;
                    }
                } else {
                    int r = fs % M;
                    if (!R[r]) {
                        R[r] = 1;
                        R_queue[R_tail++] = r;
                    }
                }
            }
            
            if (R_head < R_tail) {
                int r = R_queue[R_head++];
                if (r == 64 % M && 64 >= B) {
                    // 64 is in the modular set and B <= 64, which is bad
                    possible = 0;
                    break;
                }
                
                // Add modular transitions of r under f
                // Since M is a multiple of 4:
                // Case 1: r is even. Then x is even, so f(x) = 3x/2.
                // Modulo transitions depend on q % 2:
                if (r % 2 == 0) {
                    for (int q = 0; q < 2; q++) {
                        long long val = ((3LL * q * M) / 2 + (3LL * r) / 2) % M;
                        int gr = val;
                        if (!R[gr]) {
                            R[gr] = 1;
                            R_queue[R_tail++] = gr;
                        }
                    }
                } else if (r % 4 == 1) {
                    int base = (3 * r + 1) / 4;
                    for (int q = 0; q < 4; q++) {
                        long long val = ((3LL * q * M) / 4 + base) % M;
                        int gr = val;
                        if (!R[gr]) {
                            R[gr] = 1;
                            R_queue[R_tail++] = gr;
                        }
                    }
                } else { // r % 4 == 3
                    int base = (3 * r - 1) / 4;
                    for (int q = 0; q < 4; q++) {
                        long long val = ((3LL * q * M) / 4 + base) % M;
                        int gr = val;
                        if (!R[gr]) {
                            R[gr] = 1;
                            R_queue[R_tail++] = gr;
                        }
                    }
                }
                
                // Check all x >= B that map to < B
                // 1. x % 4 == 1 with x < 4B/3
                for (int x = B; x < (4 * B) / 3 + 2; x++) {
                    if (x % 4 == 1 && x % M == r) {
                        long long fx = f(x);
                        if (fx < B) {
                            if (!S[fx]) {
                                S[fx] = 1;
                                S_queue[S_tail++] = fx;
                            }
                        }
                    }
                }
                // 2. x % 4 == 3 with x < (4B+1)/3
                for (int x = B; x < (4 * B + 1) / 3 + 2; x++) {
                    if (x % 4 == 3 && x % M == r) {
                        long long fx = f(x);
                        if (fx < B) {
                            if (!S[fx]) {
                                S[fx] = 1;
                                S_queue[S_tail++] = fx;
                            }
                        }
                    }
                }
            }
        }
        
        if (possible) {
            printf("FOUND COMBINED FORWARD INVARIANT!\n");
            printf("B = %d, M = %d\n", B, M);
            printf("S size: %d\n", S_tail);
            printf("S: ");
            for (int i = 0; i < B; i++) {
                if (S[i]) printf("%d ", i);
            }
            printf("\n");
            printf("R size: %d\n", R_tail);
            printf("R: ");
            for (int i = 0; i < M; i++) {
                if (R[i]) printf("%d ", i);
            }
            printf("\n");
            free(S); free(S_queue);
            free(R); free(R_queue);
            return;
        }
    }
    printf("No forward combined invariant found for B = %d up to M = %d.\n", B, max_M);
    free(S); free(S_queue);
    free(R); free(R_queue);
}

int main() {
    int max_M = 100000;
    int Bs[] = {80, 100, 150, 200, 300};
    for (int i = 0; i < 5; i++) {
        search_for_B(Bs[i], max_M);
    }
    return 0;
}
