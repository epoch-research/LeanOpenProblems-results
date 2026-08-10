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

void search_for_B(int B, int max_M) {
    char *S = malloc(B);
    int *S_queue = malloc(B * sizeof(int));
    
    char *R = malloc(max_M);
    int *R_queue = malloc(max_M * sizeof(int));
    
    for (int M = 3; M <= max_M; M += 3) {
        memset(S, 0, B);
        memset(R, 0, M);
        
        int S_head = 0, S_tail = 0;
        int R_head = 0, R_tail = 0;
        
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
            
            if (R_head < R_tail) {
                int r = R_queue[R_head++];
                
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
                
                for (int x = B; x <= 3 * B / 2; x++) {
                    if (x % 3 == 0 && x % M == r) {
                        long long gx = g(x);
                        if (gx < B) {
                            if (!S[gx]) {
                                S[gx] = 1;
                                S_queue[S_tail++] = gx;
                            }
                        }
                    }
                }
            }
        }
        
        if (possible) {
            printf("FOUND COMBINED INVARIANT!\n");
            printf("B = %d, M = %d\n", B, M);
            printf("S size: %d\n", S_tail);
            printf("R size: %d\n", R_tail);
            free(S); free(S_queue);
            free(R); free(R_queue);
            return;
        }
    }
    printf("No invariant found for B = %d up to M = %d.\n", B, max_M);
    free(S); free(S_queue);
    free(R); free(R_queue);
}

int main() {
    int max_M = 100000;
    int Bs[] = {1000, 1500, 2000};
    for (int i = 0; i < 3; i++) {
        search_for_B(Bs[i], max_M);
    }
    return 0;
}
