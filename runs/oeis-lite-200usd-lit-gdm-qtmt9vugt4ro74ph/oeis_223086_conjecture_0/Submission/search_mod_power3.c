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
    int D[14] = {87, 90, 93, 96, 99, 102, 105, 108, 111, 114, 117, 120, 123, 126};
    
    // We try M = 3^n for n = 1 to 11
    long long M = 3;
    for (int n = 1; n <= 11; n++) {
        char *visited = malloc(M);
        long long *queue = malloc(M * sizeof(long long));
        
        memset(visited, 0, M);
        long long head = 0, tail = 0;
        
        // Mark forbidden residues (D % M and < 85 % M)
        for (int i = 0; i < 85; i++) {
            visited[i % M] = 2;
        }
        for (int i = 0; i < 14; i++) {
            visited[D[i] % M] = 2;
        }
        
        long long start = 85 % M;
        if (visited[start] == 2) {
            printf("n = %d (M = %lld): Start is forbidden\n", n, M);
            free(visited); free(queue);
            M *= 3;
            continue;
        }
        
        visited[start] = 1;
        queue[tail++] = start;
        
        int possible = 1;
        while (head < tail) {
            long long curr = queue[head++];
            
            // Transitions of curr modulo M
            // Since x = q * M + curr, and M is a multiple of 3:
            // Since M is a multiple of 3, x % 3 = curr % 3 is completely determined!
            // So we only need to check the transition for each choice of q % 3.
            long long nxt[3];
            for (int q = 0; q < 3; q++) {
                long long x = q * M + curr;
                long long val;
                if (x % 3 == 0) {
                    val = 2 * (x / 3);
                } else if (x % 3 == 1) {
                    val = 4 * (x / 3) + 1;
                } else {
                    val = 4 * (x / 3) + 3;
                }
                nxt[q] = val % M;
            }
            
            for (int i = 0; i < 3; i++) {
                long long img = nxt[i];
                if (visited[img] == 2) {
                    possible = 0;
                    break;
                }
                if (visited[img] == 0) {
                    visited[img] = 1;
                    queue[tail++] = img;
                }
            }
            if (!possible) break;
        }
        
        if (possible) {
            printf("FOUND INV MODULO 3^%d = %lld!\n", n, M);
            printf("States size: %lld\n", tail);
            free(visited); free(queue);
            return 0;
        } else {
            printf("n = %d (M = %lld): No invariant, reached forbidden state\n", n, M);
        }
        
        free(visited); free(queue);
        M *= 3;
    }
    
    return 0;
}
