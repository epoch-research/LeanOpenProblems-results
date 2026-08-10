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
    
    // We try M = 2^n for n = 1 to 15
    long long M = 2;
    for (int n = 1; n <= 15; n++) {
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
            M *= 2;
            continue;
        }
        
        visited[start] = 1;
        queue[tail++] = start;
        
        int possible = 1;
        while (head < tail) {
            long long curr = queue[head++];
            
            // Transitions of curr modulo M
            // x = q * M + curr.
            // Since x % 3 can be 0, 1, or 2, and M is a power of 2 (so gcd(M, 3) = 1):
            // there exists a unique q % 3 for each choice of x % 3.
            // So we can just try all 3 possible residues of x % 3!
            long long nxt[3];
            int nxt_count = 0;
            for (int r3 = 0; r3 < 3; r3++) {
                // Find q in {0, 1, 2} such that (q * M + curr) % 3 == r3
                int q_found = -1;
                for (int q = 0; q < 3; q++) {
                    if ((q * M + curr) % 3 == r3) {
                        q_found = q;
                        break;
                    }
                }
                if (q_found != -1) {
                    long long x = q_found * M + curr;
                    long long val;
                    if (r3 == 0) {
                        val = 2 * (x / 3);
                    } else if (r3 == 1) {
                        val = 4 * (x / 3) + 1;
                    } else {
                        val = 4 * (x / 3) + 3;
                    }
                    nxt[nxt_count++] = val % M;
                }
            }
            
            for (int i = 0; i < nxt_count; i++) {
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
            printf("FOUND INV MODULO 2^%d = %lld!\n", n, M);
            printf("States size: %lld\n", tail);
            free(visited); free(queue);
            return 0;
        } else {
            printf("n = %d (M = %lld): No invariant, reached forbidden state\n", n, M);
        }
        
        free(visited); free(queue);
        M *= 2;
    }
    
    return 0;
}
