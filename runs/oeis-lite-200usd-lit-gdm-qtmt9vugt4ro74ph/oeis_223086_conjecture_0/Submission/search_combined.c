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
    int max_M = 1000;
    int max_B = 1000;
    
    // S will be represented as an array of visited states < B
    char *S = malloc(max_B);
    int *S_queue = malloc(max_B * sizeof(int));
    
    // R will be represented as an array of visited residues < M
    char *R = malloc(max_M);
    int *R_queue = malloc(max_M * sizeof(int));
    
    for (int M = 3; M <= max_M; M += 3) {
        for (int B = 129; B <= max_B; B++) {
            memset(S, 0, B);
            memset(R, 0, M);
            
            int S_head = 0, S_tail = 0;
            int R_head = 0, R_tail = 0;
            
            // Start with 85
            if (85 < B) {
                S[85] = 1;
                S_queue[S_tail++] = 85;
            } else {
                int r = 85 % M;
                R[r] = 1;
                R_queue[R_tail++] = r;
            }
            
            int possible = 1;
            while (S_head < S_tail || R_head < R_tail) {
                // Process S queue
                if (S_head < S_tail) {
                    int s = S_queue[S_head++];
                    long long gs = g(s);
                    if (gs < 85) {
                        possible = 0;
                        break;
                    }
                    if (gs < B) {
                        if (!S[gs]) {
                            S[gs] = 1;
                            S_queue[S_tail++] = gs;
                        }
                    } else {
                        int r = gs % M;
                        if (!R[r]) {
                            R[r] = 1;
                            R_queue[R_tail++] = r;
                        }
                    }
                }
                
                // Process R queue
                if (R_head < R_tail) {
                    int r = R_queue[R_head++];
                    
                    // 1. Add modular transitions of r under g
                    int nxt[3];
                    // Since x = q * M + r, and M is a multiple of 3, the three cases for q % 3:
                    for (int q = 0; q < 3; q++) {
                        long long x = (long long)q * M + r;
                        long long val;
                        if (x % 3 == 0) {
                            val = 2 * (x / 3);
                        } else if (x % 3 == 1) {
                            val = 4 * (x / 3) + 1;
                        } else {
                            val = 4 * (x / 3) + 3;
                        }
                        int gr = val % M;
                        if (!R[gr]) {
                            R[gr] = 1;
                            R_queue[R_tail++] = gr;
                        }
                    }
                    
                    // 2. Check all x in [B, 3B/2] with x % 3 == 0 and x % M == r
                    for (int x = B; x <= 3 * B / 2; x++) {
                        if (x % 3 == 0 && x % M == r) {
                            long long gx = g(x);
                            if (gx < 85) {
                                possible = 0;
                                break;
                            }
                            if (gx < B) {
                                if (!S[gx]) {
                                    S[gx] = 1;
                                    S_queue[S_tail++] = gx;
                                }
                            }
                        }
                    }
                    if (!possible) break;
                }
            }
            
            if (possible) {
                printf("FOUND COMBINED INVARIANT!\n");
                printf("M = %d, B = %d\n", M, B);
                printf("S size: %d\n", S_tail);
                printf("S elements: ");
                for (int i = 85; i < B; i++) {
                    if (S[i]) printf("%d ", i);
                }
                printf("\n");
                printf("R size: %d\n", R_tail);
                printf("R residues: ");
                for (int i = 0; i < M; i++) {
                    if (R[i]) printf("%d ", i);
                }
                printf("\n");
                free(S); free(S_queue);
                free(R); free(R_queue);
                return 0;
            }
        }
    }
    
    printf("No combined invariant found.\n");
    free(S); free(S_queue);
    free(R); free(R_queue);
    return 0;
}
