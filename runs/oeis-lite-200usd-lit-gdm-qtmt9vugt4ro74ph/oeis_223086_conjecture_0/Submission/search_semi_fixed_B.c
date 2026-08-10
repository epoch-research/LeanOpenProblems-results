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
    char *R = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    for (int M = 3; M <= max_M; M += 3) {
        memset(R, 0, M);
        int head = 0, tail = 0;
        
        int r85 = 85 % M;
        R[r85] = 1;
        queue[tail++] = r85;
        
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
            printf("B = %d, M = %d\n", B, M);
            printf("R residues size: %d\n", tail);
            printf("Residues: ");
            for (int r = 0; r < M; r++) {
                if (R[r]) printf("%d ", r);
            }
            printf("\n");
            free(R);
            free(queue);
            return;
        }
    }
    printf("No invariant found for B = %d up to M = %d.\n", B, max_M);
    free(R);
    free(queue);
}

int main() {
    int max_M = 200000;
    int Bs[] = {129, 135, 150, 180, 256, 512};
    for (int i = 0; i < 6; i++) {
        search_for_B(Bs[i], max_M);
    }
    return 0;
}
